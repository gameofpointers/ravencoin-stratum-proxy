import asyncio
from copy import deepcopy
import json
import time
import sys
import os
import urllib.parse

import base58
try:
    import sha3
except ImportError:
    # Fallback to pycryptodome if pysha3 is not available
    from Crypto.Hash import keccak as sha3_module
    class sha3:
        @staticmethod
        def keccak_256():
            return sha3_module.new(digest_bits=256)

from aiohttp import ClientSession
from aiorpcx import (
    RPCSession,
    JSONRPCConnection,
    JSONRPCAutoDetect,
    Request,
    serve_rs,
    handler_invocation,
    RPCError,
    TaskGroup,
)
from functools import partial
from hashlib import sha256
from typing import Set, List, Optional


KAWPOW_EPOCH_LENGTH = 7500
hashratedict = {}


def var_int(i: int) -> bytes:
    # https://en.bitcoin.it/wiki/Protocol_specification#Variable_length_integer
    # https://github.com/bitcoin/bitcoin/blob/efe1ee0d8d7f82150789f1f6840f139289628a2b/src/serialize.h#L247
    # "CompactSize"
    assert i >= 0, i
    if i < 0xFD:
        return i.to_bytes(1, "little")
    elif i <= 0xFFFF:
        return b"\xfd" + i.to_bytes(2, "little")
    elif i <= 0xFFFFFFFF:
        return b"\xfe" + i.to_bytes(4, "little")
    else:
        return b"\xff" + i.to_bytes(8, "little")


def op_push(i: int) -> bytes:
    if i < 0x4C:
        return i.to_bytes(1, "little")
    elif i <= 0xFF:
        return b"\x4c" + i.to_bytes(1, "little")
    elif i <= 0xFFFF:
        return b"\x4d" + i.to_bytes(2, "little")
    else:
        return b"\x4e" + i.to_bytes(4, "little")


def dsha256(b):
    return sha256(sha256(b).digest()).digest()


def merkle_from_txids(txids: List[bytes]):
    # https://github.com/maaku/python-bitcoin/blob/master/bitcoin/merkle.py
    if not txids:
        return dsha256(b"")
    if len(txids) == 1:
        return txids[0]
    while len(txids) > 1:
        txids.append(txids[-1])
        txids = list(dsha256(l + r) for l, r in zip(*(iter(txids),) * 2))
    return txids[0]

def merkle_root_from_coinbase_and_branch(
    coinbase_tx: bytes,
    branch: List[bytes],
    index: int,
) -> bytes:
    """
    coinbase_tx: raw coinbase tx bytes
    branch: merkle branch as a list of sibling hashes (bytes, 32 each),
            starting from the leaf level up toward the root.
            Each hash should be the internal merkle hash form
            (i.e. dsha256(tx) order, *not* reversed for display).
    index: position of the coinbase tx in the block's tx array (0-based)

    returns: merkle root (internal byte order)
    """

    # Start with the leaf hash = double-SHA256 of the coinbase tx bytes
    h = dsha256(coinbase_tx)

    # Walk up the tree
    for sibling in branch:
        if index % 2 == 0:
            # we are a left node, sibling is right
            h = dsha256(h + sibling)
        else:
            # we are a right node, sibling is left
            h = dsha256(sibling + h)
        index //= 2

    return h

class TemplateState:
    # These refer to the block that we are working on
    height: int = -1

    timestamp: int = -1

    # The address of the miner that first connects is
    # the one that is used
    pub_h160: Optional[bytes] = None

    # We store the following in hex because they are
    # Used directly in API to the miner
    bits: Optional[str] = None
    target: Optional[str] = None
    headerHash: Optional[str] = None

    version: int = -1
    prevHash: Optional[bytes] = None
    externalTxs: List[str] = []
    seedHash: Optional[bytes] = None
    header: Optional[bytes] = None
    coinbase_tx: Optional[bytes] = None
    coinbase_txid: Optional[bytes] = None

    coinb1: Optional[str] = None
    extraNonce1: str = "00000000" # length 4
    extraNonce2: str = "0000000000000000" # length 8
    coinb2: Optional[str] = None
    merkle_branch: List[str] = []

    current_commitment: Optional[str] = None

    new_sessions: Set[RPCSession] = set()
    all_sessions: Set[RPCSession] = set()

    awaiting_update = False

    job_counter = 0
    bits_counter = 0

    def __repr__(self):
        return f"Height:\t\t{self.height}\nAddress h160:\t\t{self.pub_h160}\nBits:\t\t{self.bits}\nTarget:\t\t{self.target}\nHeader Hash:\t\t{self.headerHash}\nVersion:\t\t{self.version}\nPrevious Header:\t\t{self.prevHash.hex()}\nExtra Txs:\t\t{self.externalTxs}\nSeed Hash:\t\t{self.seedHash.hex()}\nHeader:\t\t{self.header.hex()}\nCoinbase:\t\t{self.coinbase_tx.hex()}\nCoinbase txid:\t\t{self.coinbase_txid.hex()}\nNew sessions:\t\t{self.new_sessions}\nSessions:\t\t{self.all_sessions}"

    def build_block(self, nonce: str, mixHash: str) -> str:
        return (
            self.header.hex()
            + nonce
            + mixHash
            + var_int(len(self.externalTxs) + 1).hex()
            + self.coinbase_tx.hex()
            + "".join(self.externalTxs)
        )


def add_old_state_to_queue(queue, state, drop_after: int):
    id = hex(state.job_counter)[2:]
    if id in queue[1]:
        return
    queue[0].append(id)
    queue[1][id] = state
    while len(queue[0]) > drop_after:
        del queue[1][queue[0].pop(0)]


def lookup_old_state(queue, id: str) -> Optional[TemplateState]:
    return queue[1].get(id, None)


class StratumSession(RPCSession):
    def __init__(
        self,
        state: TemplateState,
        old_states,
        testnet: bool,
        verbose: bool,
        node_url: str,
        node_username: str,
        node_password: str,
        node_port: int,
        transport,
    ):
        connection = JSONRPCConnection(JSONRPCAutoDetect)
        super().__init__(transport, connection=connection)
        self._state = state
        self._testnet = testnet
        self._verbose = verbose

        self._old_states = old_states

        self._node_url = node_url
        self._node_username = node_username
        self._node_password = node_password
        self._node_port = node_port

        self.name = None

        self.handlers = {
            "mining.subscribe": self.handle_subscribe,
            "mining.authorize": self.handle_authorize,
            "mining.submit": self.handle_submit,
            "eth_submitHashrate": self.handle_eth_submitHashrate,
        }

    async def handle_request(self, request):
        if isinstance(request, Request):
            handler = self.handlers.get(request.method, None)
            if not handler:
                return
        else:
            # Do not fail on unknown method
            return
        return await handler_invocation(handler, request)()

    async def connection_lost(self):
        worker = str(self).strip(">").split()[3]
        if self._verbose:
            if self.name:
                print(f"Connection lost: {self.name} ({worker})")
            else:
                print(f"Connection lost: {worker}")
        hashratedict.pop(worker, None)
        self._state.new_sessions.discard(self)
        self._state.all_sessions.discard(self)
        return await super().connection_lost()

    async def handle_subscribe(self, *args):
        if self not in self._state.all_sessions:
            self._state.new_sessions.add(self)
        self._state.bits_counter += 1
        # We dont support resuming sessions, ensure unique work for unique miners
        return [None, self._state.bits_counter.to_bytes(2, "big").hex()]

    async def handle_authorize(self, username: str, password: str):
        # Skip address validation, just extract worker name if present
        split = username.split(".")
        if len(split) > 1:
            self.name = split[1]
        return True

    async def handle_submit(
        self,
        worker: str,
        job_id: str,
        nonce_hex: str,
        header_hex: str,
        mixhash_hex: str,
    ):
        if self._verbose:
            print("Possible solution")
            print(worker)
            print(job_id)
            print(header_hex)

        # We can still propogate old jobs; there may be a chance that they get used
        state = self._state

        if job_id != hex(state.job_counter)[2:]:
            if self._verbose:
                print("An old job was submitted, trying old states")
            old_state = lookup_old_state(self._old_states, job_id)
            if old_state is not None:
                state = old_state
            else:
                raise RPCError(20, "Miner submitted an old job that we did not have")

        if nonce_hex[:2].lower() == "0x":
            nonce_hex = nonce_hex[2:]
     
        nonce_hex = bytes.fromhex(nonce_hex)[::-1].hex()

        if mixhash_hex[:2].lower() == "0x":
            mixhash_hex = mixhash_hex[2:]
        mixhash_hex = bytes.fromhex(mixhash_hex)[::-1].hex()

        block_hex = state.build_block(nonce_hex, mixhash_hex)

        # Quai expects hex values with 0x prefix
        if not block_hex.startswith("0x"):
            block_hex = "0x" + block_hex

        data = {
            "jsonrpc": "2.0",
            "id": "0",
            "method": "quai_submitBlock",
            "params": [block_hex],
        }
        headers = {"Content-Type": "application/json"}
        async with ClientSession() as session:
            async with session.post(
                f"http://{self._node_username}:{self._node_password}@{self._node_url}:{self._node_port}",
                data=json.dumps(data),
                headers=headers,
            ) as resp:
                json_resp = await resp.json()

                with open(
                    f"./submit_history/{state.height}_{state.job_counter}.txt", "w"
                ) as f:
                    data = f"Response:\n{json.dumps(json_resp, indent=2)}\n\nState:\n{state.__repr__()}"
                    f.write(data)

                if self._verbose:
                    print(json_resp)

                if json_resp.get("error", None):
                    raise RPCError(20, json_resp["error"])

                result = json_resp.get("result", None)
                if self._verbose:
                    if result == "inconclusive":
                        # inconclusive - valid submission but other block may be better, etc.
                        print("Valid block but inconclusive")
                    elif result == "duplicate":
                        print("Valid block but duplicate")
                    elif result == "duplicate-inconclusive":
                        print("Valid block but duplicate-inconclusive")
                    elif result == "inconclusive-not-best-prevblk":
                        print("Valid block but inconclusive-not-best-prevblk")

                if result not in (
                    None,
                    "inconclusive",
                    "duplicate",
                    "duplicate-inconclusive",
                    "inconclusive-not-best-prevblk",
                ):
                    raise RPCError(20, json_resp["result"])

        # Use the height from state directly
        msg = f"Found block (may or may not be accepted by the chain): {state.height}"
        print(msg)
        await self.send_notification("client.show_message", (msg,))

        # Immediately fetch new block template after submission
        if self._verbose:
            print("Fetching new block template after submission")
        await stateUpdater(
            self._state,
            self._old_states,
            20,  # drop_after - same as the store value in main
            self._verbose,
            self._node_url,
            self._node_username,
            self._node_password,
            self._node_port,
            force_update=True,  # Force new work even if height hasn't changed
        )

        return True

    async def handle_eth_submitHashrate(self, hashrate: str, clientid: str):
        """Record reported hashrate without querying the upstream node.

        Quai's RPC doesn't expose getmininginfo, so the previous implementation
        spammed the logs with JSONDecodeError. We simply track per-worker
        hashrate locally and skip network statistics entirely.
        """

        try:
            hashrate_int = int(hashrate, 16)
        except ValueError:
            print("Received malformed hashrate payload, ignoring")
            return

        worker = str(self).strip(">").split()[3]
        hashratedict.update({worker: hashrate_int})
        totalHashrate = 0

        print(f"----------------------------")
        # print(self._state.worker)
        for x, y in hashratedict.items():
            totalHashrate += y
            print(f"Reported Hashrate: {round(y / 1000000, 2)}Mh/s for ID: {x}")
        print(f"----------------------------")
        print(f"Total Reported Hashrate: {round(totalHashrate / 1000000, 2)}Mh/s")

        if totalHashrate == 0:
            print("Mining software has yet to send data")
            return True

        msg = (
            "Estimated time to find: unavailable (network stats disabled)"
        )
        print(msg)
        await self.send_notification("client.show_message", (msg,))
        return True


async def stateUpdater(
    state: TemplateState,
    old_states,
    drop_after,
    verbose,
    node_url: str,
    node_username: str,
    node_password: str,
    node_port: int,
    force_update: bool = False,
):
    data = {"jsonrpc": "2.0", "id": "0", "method": "quai_getBlockTemplate", "params": []}
    headers = {"Content-Type": "application/json"}
    async with ClientSession() as session:
        async with session.post(
            f"http://{node_username}:{node_password}@{node_url}:{node_port}",
            data=json.dumps(data),
            headers=headers,
        ) as resp:
            try:
                if verbose:
                    print(f"GetBlockTemplate response status: {resp.status}")
                    print(f"GetBlockTemplate response content-type: {resp.content_type}")

                # Try to get response text first to debug
                response_text = await resp.text()
                if verbose:
                    print(f"GetBlockTemplate response: {response_text[:500]}")  # Print first 500 chars

                json_obj = json.loads(response_text)
                if json_obj.get("error", None):
                    raise Exception(json_obj.get("error", None))

                version_int: int = int(json_obj["result"]["version"], 16) if isinstance(json_obj["result"]["version"], str) else json_obj["result"]["version"]
                height_int: int = int(json_obj["result"]["height"], 16) if isinstance(json_obj["result"]["height"], str) else json_obj["result"]["height"]
                bits_hex: str = json_obj["result"]["bits"]
                if isinstance(bits_hex, str) and bits_hex.startswith("0x"):
                    bits_hex = bits_hex[2:]
                # Ensure bits_hex has even length for fromhex() and is 8 chars (4 bytes)
                bits_hex = bits_hex.zfill(8)

                if verbose:
                    print(f"Parsed version: {version_int}, height: {height_int}, bits: {bits_hex}")
                prev_hash_hex: str = json_obj["result"]["previousblockhash"]
                if prev_hash_hex.startswith("0x"):
                    prev_hash_hex = prev_hash_hex[2:]

                # Quai format doesn't have transactions list, witness commitment, or nested coinbaseaux
                txs_list: List = json_obj["result"].get("transactions", [])
                witness_hex: str = json_obj["result"].get("default_witness_commitment", "")

                target_hex: str = json_obj["result"]["target"]
                if target_hex.startswith("0x"):
                    target_hex = target_hex[2:]

                merkle_branch: List = json_obj["result"].get("merkleBranch", [])
                state.merkle_branch = [bytes.fromhex(h)[::-1] for h in merkle_branch]

                coinb1: str = json_obj["result"].get("coinb1", "")
                coinb2: str = json_obj["result"].get("coinb2", "")

                if coinb1.startswith("0x"):
                    coinb1 = coinb1[2:]
                if coinb2.startswith("0x"):
                    coinb2 = coinb2[2:]

                state.coinb1 = coinb1
                state.coinb2 = coinb2

                ts = int(time.time())
                new_witness = witness_hex != state.current_commitment
                state.current_commitment = witness_hex
                state.target = target_hex
                state.bits = bits_hex
                state.version = version_int
                state.prevHash = bytes.fromhex(prev_hash_hex)[::-1]

                new_block = False

                original_state = None

                # The following will only change when there is a new block.
                # Force update is unnecessary
                if state.height == -1 or state.height != height_int:
                    original_state = deepcopy(state)
                    # New block, update everything
                    if verbose:
                        print("New block, update state")
                    new_block = True

                    # Generate seed hash #
                    if state.height == -1 or height_int > state.height:
                        if not state.seedHash:
                            seed_hash = bytes(32)
                            for _ in range(height_int // KAWPOW_EPOCH_LENGTH):
                                k = sha3.keccak_256()
                                k.update(seed_hash)
                                seed_hash = k.digest()
                            if verbose:
                                print(f"Initialized seedhash to {seed_hash.hex()}")
                            state.seedHash = seed_hash
                        elif state.height % KAWPOW_EPOCH_LENGTH == 0:
                            # Hashing is expensive, so want use the old val
                            k = sha3.keccak_256()
                            k.update(state.seedHash)
                            seed_hash = k.digest()
                            if verbose:
                                print(f"updated seed hash to {seed_hash.hex()}")
                            state.seedHash = seed_hash
                    elif state.height > height_int:
                        # Maybe a chain reorg?

                        # If the difference between heights is greater than how far we are into the epoch
                        if (
                            state.height % KAWPOW_EPOCH_LENGTH
                            - (state.height - height_int)
                            < 0
                        ):
                            # We must go back an epoch; recalc
                            seed_hash = bytes(32)
                            for _ in range(height_int // KAWPOW_EPOCH_LENGTH):
                                k = sha3.keccak_256()
                                k.update(seed_hash)
                                seed_hash = k.digest()
                            if verbose:
                                print(f"Reverted seedhash to {seed_hash}")
                            state.seedHash = seed_hash

                    # Done with seed hash #
                    state.height = height_int

                # The following occurs during both new blocks & new txs & nothing happens for 60s (magic number)
                # OR when force_update is True (e.g., after block submission)
                if (
                    new_block
                    or new_witness
                    or state.timestamp + 60 < ts
                    or force_update
                ):
                    # Generate coinbase #

                    if original_state is None:
                        original_state = deepcopy(state)

                    # Create coinbase tx
                    state.coinbase_tx = bytes.fromhex(state.coinb1) + bytes.fromhex(state.extraNonce1) + bytes.fromhex(state.extraNonce2) + bytes.fromhex(state.coinb2)

                    state.coinbase_txid = dsha256(state.coinbase_tx)

                    # Create merkle & update txs
                    txids = [state.coinbase_txid]
                    incoming_txs = []
                    for tx_data in txs_list:
                        incoming_txs.append(tx_data["data"])
                        txids.append(bytes.fromhex(tx_data["txid"])[::-1])
                    state.externalTxs = incoming_txs
                    merkle = merkle_from_txids(txids)

                    # Done create merkle & update txs

                    state.header = (
                        version_int.to_bytes(4, "little")
                        + state.prevHash
                        + merkle
                        + ts.to_bytes(4, "little")
                        + bytes.fromhex(bits_hex)[::-1]
                        + state.height.to_bytes(4, "little")
                    )

                    state.headerHash = dsha256(state.header)[::-1].hex()
                    state.timestamp = ts

                    state.job_counter += 1
                    add_old_state_to_queue(old_states, original_state, drop_after)

                    for session in state.all_sessions:
                        print(f"[NOTIFY] Sending mining.notify to existing session: {session}")
                        print(f"  job_id: {hex(state.job_counter)[2:]}")
                        print(f"  headerHash: {state.headerHash}")
                        print(f"  seedHash: {state.seedHash.hex()}")
                        print(f"  target: {target_hex}")
                        print(f"  clean_jobs: True")
                        print(f"  height: {state.height}")
                        print(f"  bits: {bits_hex}")
                        await session.send_notification(
                            "mining.set_target", (target_hex,)
                        )
                        await session.send_notification(
                            "mining.notify",
                            (
                                hex(state.job_counter)[2:],
                                state.headerHash,
                                state.seedHash.hex(),
                                target_hex,
                                True,
                                state.height,
                                bits_hex,
                            ),
                        )

                for session in state.new_sessions:
                    state.all_sessions.add(session)
                    print(f"[NOTIFY] Sending mining.notify to NEW session: {session}")
                    print(f"  job_id: {hex(state.job_counter)[2:]}")
                    print(f"  headerHash: {state.headerHash}")
                    print(f"  seedHash: {state.seedHash.hex()}")
                    print(f"  target: {target_hex}")
                    print(f"  clean_jobs: True")
                    print(f"  height: {state.height}")
                    print(f"  bits: {bits_hex}")
                    await session.send_notification("mining.set_target", (target_hex,))
                    await session.send_notification(
                        "mining.notify",
                        (
                            hex(state.job_counter)[2:],
                            state.headerHash,
                            state.seedHash.hex(),
                            target_hex,
                            True,
                            state.height,
                            bits_hex,
                        ),
                    )

                state.new_sessions.clear()

            except Exception as e:
                print(f"Failed to query blocktemplate from node: {e}")
                import traceback

                traceback.print_exc()
                print(
                    "Sleeping for 5 seconds before retry."
                )
                await asyncio.sleep(5)


if __name__ == "__main__":

    def check_bool(x) -> bool:
        if isinstance(x, str):
            return x.lower()[0] == "t"
        return bool(x)

    if len(sys.argv) < 7:
        print(
            "arguments must be: proxy_port, node_ip, node_username, node_password, node_port, listen_externally, (optional: testnet, verbose)"
        )
        exit(0)

    proxy_port = int(sys.argv[1])
    node_url = str(sys.argv[2])
    node_username = urllib.parse.quote(str(sys.argv[3]), safe="")
    node_password = urllib.parse.quote(str(sys.argv[4]), safe="")
    node_port = int(sys.argv[5])
    should_listen_externaly = check_bool(sys.argv[6])
    testnet = False
    verbose = False
    if len(sys.argv) > 7:
        testnet = check_bool(sys.argv[7])

    if len(sys.argv) > 8:
        verbose = check_bool(sys.argv[8])

    if not os.path.exists("./submit_history"):
        os.mkdir("./submit_history")

    print("Starting stratum converter")

    # The shared state
    state = TemplateState()
    # Stores old state info
    historical_states = [list(), dict()]
    # only save 20 historic states (magic number)
    store = 20

    session_generator = partial(
        StratumSession,
        state,
        historical_states,
        testnet,
        verbose,
        node_url,
        node_username,
        node_password,
        node_port,
    )

    async def updateState():
        while True:
            await stateUpdater(
                state,
                historical_states,
                store,
                verbose,
                node_url,
                node_username,
                node_password,
                node_port,
            )
            # Check for new blocks / new transactions every 0.1 seconds
            # stateUpdater should fast fail if no differences
            await asyncio.sleep(0.1)

    async def beginServing():
        server = await serve_rs(
            session_generator,
            None if should_listen_externaly else "127.0.0.1",
            proxy_port,
            reuse_address=True,
        )
        await server.serve_forever()

    async def execute():
        async with TaskGroup(wait=any) as group:
            await group.spawn(updateState())
            await group.spawn(beginServing())

        for task in group.tasks:
            if not task.cancelled():
                exc = task.exception()
                if exc:
                    raise exc

    asyncio.run(execute())
