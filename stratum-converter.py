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
    JSONRPCLoose,
    JSONRPCv1,
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


def adjust_target_for_difficulty_multiplier(target_hex: str, multiplier: int) -> str:
    """
    Divides the target by the multiplier to increase difficulty.
    Lower target = higher difficulty.

    Args:
        target_hex: The network target as a hex string (without 0x prefix)
        multiplier: The difficulty multiplier (e.g., 10 for 10x harder)

    Returns:
        Adjusted target as hex string (without 0x prefix), zero-padded to 64 chars
    """
    # Convert hex target to integer
    target_int = int(target_hex, 16)

    # Divide by multiplier to make it harder (lower target = higher difficulty)
    adjusted_target_int = target_int // multiplier

    # Convert back to hex and ensure it's 64 characters (32 bytes)
    adjusted_target_hex = hex(adjusted_target_int)[2:].zfill(64)

    return adjusted_target_hex


def target_to_difficulty(target_hex: str) -> float:
    """
    Convert a target hash to a difficulty value.

    Bitcoin difficulty formula: difficulty = max_target / current_target
    where max_target (difficulty 1) = 0x00000000ffff0000000000000000000000000000000000000000000000000000

    Args:
        target_hex: The target as a hex string (without 0x prefix)

    Returns:
        The difficulty as a float
    """
    # Bitcoin difficulty 1 target (0x1d00ffff in compact form)
    max_target = 0x00000000ffff0000000000000000000000000000000000000000000000000000

    # Convert current target to int
    current_target = int(target_hex, 16)

    # Avoid division by zero
    if current_target == 0:
        return float('inf')

    # Calculate difficulty
    difficulty = max_target / current_target

    return difficulty


def target_to_compact_bits(target_int: int) -> str:
    """
    Convert a target integer to compact bits format (nBits).

    Bitcoin compact format: 0xNNSSFFFF where:
    - NN = size (number of bytes)
    - SSFFFF = significant bytes (big-endian)

    Args:
        target_int: The target as an integer

    Returns:
        Compact bits as hex string (8 characters, e.g. "1d00ffff")
    """
    # Convert to bytes (big-endian)
    target_bytes = target_int.to_bytes(32, 'big')

    # Find first non-zero byte
    first_nonzero = 0
    for i, byte in enumerate(target_bytes):
        if byte != 0:
            first_nonzero = i
            break

    # Calculate size (number of bytes from first non-zero to end)
    size = 32 - first_nonzero

    # Get the significant bytes (first 3 non-zero bytes)
    significant = target_bytes[first_nonzero:first_nonzero+3]

    # If the high bit is set, we need to add a zero byte and increase size
    if significant[0] & 0x80:
        size += 1
        significant = b'\x00' + significant[:2]

    # Pad to 3 bytes if needed
    significant = significant.ljust(3, b'\x00')

    # Build compact form: size (1 byte) + significant (3 bytes)
    compact = bytes([size]) + significant

    return compact.hex()


def encode_uint32(value: int) -> str:
    """Encode a uint32 as an 8-character hex string (little-endian)"""
    return value.to_bytes(4, 'little').hex()


def parse_script_push_op(script: bytes, cursor: int) -> tuple:
    """
    Parse a Bitcoin script push operation and return (data, new_cursor).
    Handles OP_PUSH1-75, OP_PUSHDATA1, OP_PUSHDATA2, etc.

    Returns: (data_bytes, new_cursor_position)
    """
    if cursor >= len(script):
        raise ValueError("Script cursor out of bounds")

    opcode = script[cursor]
    cursor += 1

    if opcode <= 75:
        # Direct push of 1-75 bytes
        data_len = opcode
    elif opcode == 0x4c:  # OP_PUSHDATA1
        if cursor >= len(script):
            raise ValueError("OP_PUSHDATA1 missing length byte")
        data_len = script[cursor]
        cursor += 1
    elif opcode == 0x4d:  # OP_PUSHDATA2
        if cursor + 1 >= len(script):
            raise ValueError("OP_PUSHDATA2 missing length bytes")
        data_len = int.from_bytes(script[cursor:cursor+2], 'little')
        cursor += 2
    elif opcode == 0x4e:  # OP_PUSHDATA4
        if cursor + 3 >= len(script):
            raise ValueError("OP_PUSHDATA4 missing length bytes")
        data_len = int.from_bytes(script[cursor:cursor+4], 'little')
        cursor += 4
    else:
        raise ValueError(f"Unsupported opcode: 0x{opcode:02x}")

    if cursor + data_len > len(script):
        raise ValueError(f"Script push data exceeds script bounds")

    data = script[cursor:cursor + data_len]
    cursor += data_len

    return (data, cursor)


def find_extranonce_positions_in_coinbase_script(coinbase_script: bytes) -> tuple:
    """
    Find the positions of extraNonce1 and extraNonce2 in the coinbase scriptSig.

    Format (BIP34 compliant):
    OP_PUSH<n> <height(variable bytes)> ← BIP34 height (MINIMAL encoding, 1-5 bytes)
    OP_PUSH4   <fabe6d6d(4 bytes)>      ← Magic marker
    OP_PUSH32  <AuxPowHash(32 bytes)>   ← Seal hash
    OP_PUSH4   <merkle_size(4 bytes)>
    OP_PUSH4   <merkle_nonce(4 bytes)>
    OP_PUSH4   <extraNonce1(4 bytes)>   <- We want to find this position
    OP_PUSH8   <extraNonce2(8 bytes)>   <- And this position

    Returns: (extranonce1_start, extranonce1_end, extranonce2_start, extranonce2_end)
    """
    cursor = 0

    # Skip height (variable length BIP34 encoding)
    height_data, cursor = parse_script_push_op(coinbase_script, cursor)
    # Height can be 0-5 bytes depending on block height

    # Skip magic (OP_PUSH4 + 4 bytes = "fabe6d6d")
    magic_data, cursor = parse_script_push_op(coinbase_script, cursor)
    if len(magic_data) != 4 or magic_data != bytes([0xfa, 0xbe, 0x6d, 0x6d]):
        raise ValueError(f"Invalid magic marker: expected fabe6d6d, got {magic_data.hex()}")

    # Skip seal hash (OP_PUSH32 + 32 bytes)
    seal_data, cursor = parse_script_push_op(coinbase_script, cursor)
    if len(seal_data) != 32:
        raise ValueError(f"Invalid seal hash length: expected 32, got {len(seal_data)}")

    # Skip merkle_size (OP_PUSH4 + 4 bytes)
    merkle_size_data, cursor = parse_script_push_op(coinbase_script, cursor)
    if len(merkle_size_data) != 4:
        raise ValueError(f"Invalid merkle_size length: expected 4, got {len(merkle_size_data)}")

    # Skip merkle_nonce (OP_PUSH4 + 4 bytes)
    merkle_nonce_data, cursor = parse_script_push_op(coinbase_script, cursor)
    if len(merkle_nonce_data) != 4:
        raise ValueError(f"Invalid merkle_nonce length: expected 4, got {len(merkle_nonce_data)}")

    # Found extraNonce1 position
    if coinbase_script[cursor] != 0x04:
        raise ValueError(f"Expected OP_PUSH4 at extraNonce1, got 0x{coinbase_script[cursor]:02x}")
    cursor += 1  # Skip the OP_PUSH4
    extranonce1_start = cursor
    extranonce1_end = cursor + 4
    cursor += 4

    # Found extraNonce2 position
    if coinbase_script[cursor] != 0x08:
        raise ValueError(f"Expected OP_PUSH8 at extraNonce2, got 0x{coinbase_script[cursor]:02x}")
    cursor += 1  # Skip the OP_PUSH8
    extranonce2_start = cursor
    extranonce2_end = cursor + 8

    return (extranonce1_start, extranonce1_end, extranonce2_start, extranonce2_end)


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

    # Stratum coinbase split (for miner extraNonce insertion)
    coinbase1: Optional[bytes] = None
    coinbase2: Optional[bytes] = None
    coinbase2_script_between_len: int = 0

    current_commitment: Optional[str] = None
    coinbase_aux: Optional[str] = None
    payout_script: Optional[str] = None

    new_sessions: Set[RPCSession] = set()
    all_sessions: Set[RPCSession] = set()

    awaiting_update = False

    job_counter = 0
    bits_counter = 0

    # Mining algorithm selection
    mining_algo: str = "kawpow"  # "kawpow" or "sha"

    # Miner-specific bits (for SHA mining with custom difficulty)
    miner_bits: Optional[str] = None

    def __repr__(self):
        return f"Height:\t\t{self.height}\nAddress h160:\t\t{self.pub_h160}\nBits:\t\t{self.bits}\nTarget:\t\t{self.target}\nHeader Hash:\t\t{self.headerHash}\nVersion:\t\t{self.version}\nPrevious Header:\t\t{self.prevHash.hex()}\nExtra Txs:\t\t{self.externalTxs}\nSeed Hash:\t\t{self.seedHash.hex()}\nHeader:\t\t{self.header.hex()}\nCoinbase:\t\t{self.coinbase_tx.hex()}\nCoinbase txid:\t\t{self.coinbase_txid.hex()}\nNew sessions:\t\t{self.new_sessions}\nSessions:\t\t{self.all_sessions}"

    def build_block(self, nonce: str, mixHash: str = "") -> str:
        if self.mining_algo == "sha":
            # Build 80-byte SHA256d header (no mixHash)
            # header(76) + nonce(4) = 80 bytes
            full_header = self.header.hex() + nonce
            print(f"[DEBUG] SHA header construction:")
            print(f"  header length: {len(self.header)} bytes ({len(self.header.hex())} hex chars)")
            print(f"  nonce length: {len(nonce)//2} bytes ({len(nonce)} hex chars)")
            print(f"  total header: {len(full_header)//2} bytes")
        else:
            # Build 120-byte KAWPOW/Ravencoin header with mixHash
            # Ravencoin format: version(4) + prevHash(32) + merkle(32) + time(4) + bits(4) + height(4) + nonce(8) + mixHash(32) + height(4)
            # self.header already contains: version(4) + prevHash(32) + merkle(32) + time(4) + bits(4) + height(4) = 80 bytes
            # We need to add: nonce(8) + mixHash(32) = 40 bytes to get 120 bytes total
            full_header = self.header.hex() + nonce + mixHash
            print(f"[DEBUG] KAWPOW header construction:")
            print(f"  header length: {len(self.header)} bytes ({len(self.header.hex())} hex chars)")
            print(f"  nonce length: {len(nonce)//2} bytes ({len(nonce)} hex chars)")
            print(f"  mixHash length: {len(mixHash)//2} bytes ({len(mixHash)} hex chars)")
            print(f"  total header: {len(full_header)//2} bytes (expected 120)")

        tx_count = len(self.externalTxs) + 1
        tx_count_varint = var_int(tx_count).hex()
        coinbase_hex = self.coinbase_tx.hex()
        external_txs_hex = "".join(self.externalTxs)

        block_hex = (
            full_header
            + tx_count_varint
            + coinbase_hex
            + external_txs_hex
        )

        print(f"  tx_count: {tx_count}")
        print(f"  tx_count_varint: {tx_count_varint} ({len(tx_count_varint)//2} bytes)")
        print(f"  coinbase first 20 bytes: {coinbase_hex[:40]}")
        print(f"  external_txs count: {len(self.externalTxs)}")
        print(f"  total block: {len(block_hex)//2} bytes")
        return block_hex

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
        difficulty_multiplier: int,
        transport,
    ):
        connection = JSONRPCConnection(JSONRPCv1)
        super().__init__(transport, connection=connection)
        self._state = state
        self._testnet = testnet
        self._verbose = verbose

        self._old_states = old_states

        self._node_url = node_url
        self._node_username = node_username
        self._node_password = node_password
        self._node_port = node_port
        self._difficulty_multiplier = difficulty_multiplier

        self.name = None

        self.handlers = {
            "mining.subscribe": self.handle_subscribe,
            "mining.authorize": self.handle_authorize,
            "mining.submit": self.handle_submit,
            "eth_submitHashrate": self.handle_eth_submitHashrate,
            # Common Stratum v1 extras many miners (incl. Bitaxe) send
            "mining.configure": self.handle_configure,
            "mining.suggest_difficulty": self.handle_suggest_difficulty,
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
        """Respond to mining.subscribe.

        - For SHA: return standard Stratum v1 triple with extranonces.
        - For KAWPOW: preserve legacy behavior known to work with common miners.
        """
        if self not in self._state.all_sessions:
            self._state.new_sessions.add(self)

        # Increment a simple counter to use as subscription ids
        self._state.bits_counter += 1
        sub_id = self._state.bits_counter.to_bytes(2, "big").hex()

        if self._state.mining_algo == "sha":
            # Generate a per-session extranonce1 (4 bytes), miners insert EN1/EN2 into coinbase
            en1_bytes = os.urandom(4)
            self.extranonce1 = en1_bytes.hex()
            self.extranonce2_size = 8  # bytes

            return [
                [["mining.set_difficulty", sub_id], ["mining.notify", sub_id]],
                self.extranonce1,
                self.extranonce2_size,
            ]
        else:
            # Legacy 2-tuple many KAWPOW miners accept: [subscription_details, extranonce1]
            # We don't use extranonces in KAWPOW; return an id placeholder.
            return [None, sub_id]

    async def handle_authorize(self, username: str, password: str):
        # Skip address validation, just extract worker name if present
        split = username.split(".")
        if len(split) > 1:
            self.name = split[1]
        return True

    async def handle_configure(self, requested_caps, params_obj=None):
        """Handle Stratum v1 mining.configure.

        Bitaxe uses overt AsicBoost - we must allow bit 29 (0x20000000).
        """
        result = {}
        if isinstance(requested_caps, list):
            for cap in requested_caps:
                if cap == "version-rolling":
                    # Allow overt AsicBoost (bit 29) - required for Bitaxe
                    mask_int = 0x20000000  # AsicBoost bit
                    # Optionally also allow BIP320 general-purpose bits (bits 13-28)
                    # mask_int |= 0x1fffe000  # Uncomment to allow GP bits

                    mask = f"{mask_int:08x}"

                    result["version-rolling"] = True
                    result["version-rolling.mask"] = mask

                    # Preserve miner's min-bit-count if requested
                    if isinstance(params_obj, dict):
                        min_bits = params_obj.get("version-rolling.min-bit-count")
                        if min_bits is not None:
                            result["version-rolling.min-bit-count"] = min_bits

                    if self._verbose:
                        print(f"[CONFIGURE] Version rolling enabled with mask: 0x{mask} (AsicBoost bit 29)")
                elif cap == "minimum-difficulty":
                    # We don't enforce a minimum difficulty, but acknowledge
                    result["minimum-difficulty"] = True
        return result

    async def handle_suggest_difficulty(self, difficulty):
        """Acknowledge miner's suggested difficulty.

        For solo-mining we still set network difficulty via mining.notify,
        but responding True prevents miners from disconnecting.
        """
        try:
            # Some miners send as int, others as float
            _ = float(difficulty)
        except Exception:
            pass
        return True

    async def handle_submit(self, *params):
        if self._verbose:
            print("Possible solution")
            print(params)

        # We can still propogate old jobs; there may be a chance that they get used
        state = self._state

        # Unpack parameters depending on mining algo
        if state.mining_algo == "sha":
            # Expected (Stratum v1): worker, job_id, extranonce2, ntime, nonce [, version]
            if len(params) < 5:
                raise RPCError(20, f"mining.submit requires at least 5 params for SHA, got {len(params)}")
            worker, job_id, en2_hex, ntime_hex, nonce_hex, *rest = params

            # Version-rolling optional
            version_hex = rest[0] if rest else None

            # Validate job id and possibly lookup old state
            if job_id != hex(state.job_counter)[2:]:
                if self._verbose:
                    print("An old job was submitted, trying old states")
                old_state = lookup_old_state(self._old_states, job_id)
                if old_state is not None:
                    state = old_state
                else:
                    raise RPCError(20, "Miner submitted an old job that we did not have")

            # Normalize hex strings - remove 0x prefix
            for name, v in [("en2_hex", en2_hex), ("ntime_hex", ntime_hex), ("nonce_hex", nonce_hex)]:
                if isinstance(v, str) and v.startswith("0x"):
                    v = v[2:]
                # assign back
                if name == "en2_hex":
                    en2_hex = v
                elif name == "ntime_hex":
                    ntime_hex = v
                else:
                    nonce_hex = v
            if version_hex and version_hex.startswith("0x"):
                version_hex = version_hex[2:]

            # Ensure proper sizes (these are already in the correct byte order from miner)
            en2_hex = en2_hex.zfill(16)  # 8 bytes
            ntime_hex = ntime_hex.zfill(8)  # 4 bytes
            nonce_hex = nonce_hex.zfill(8)  # 4 bytes

            if self._verbose:
                print(f"[SHA SUBMIT] Raw parameters from miner:")
                print(f"  worker: {worker}")
                print(f"  job_id: {job_id}")
                print(f"  en2_hex: {en2_hex}")
                print(f"  ntime_hex: {ntime_hex}")
                print(f"  nonce_hex: {nonce_hex}")
                print(f"  version_hex: {version_hex if version_hex else 'None (using template version)'}")

            # Use per-session extranonce1 from subscribe (4 bytes)
            en1_hex = getattr(self, "extranonce1", None)
            if not en1_hex:
                # Fallback: use zeros
                en1_hex = "00" * 4

            # Reconstruct full coinbase using standard Stratum v1 concatenation
            # coinbase = coinbase1 || EN1 || EN2 || coinbase2
            coinbase = (
                (state.coinbase1 or b"")
                + bytes.fromhex(en1_hex)
                + bytes.fromhex(en2_hex)
                + (state.coinbase2 or b"")
            )

            coinbase_txid = dsha256(coinbase)

            if self._verbose:
                print(f"[SHA SUBMIT] Coinbase reconstruction:")
                print(f"  coinbase1 length: {len(state.coinbase1 or b'')} bytes")
                print(f"  en1_hex: {en1_hex} (4 bytes)")
                print(f"  en2_hex: {en2_hex} (8 bytes)")
                print(f"  coinbase2 length: {len(state.coinbase2 or b'')} bytes")
                print(f"  total coinbase length: {len(coinbase)} bytes")

                # Extract and display the scriptSig for verification
                # Coinbase structure: version(4) + vin_count(1) + prevout(36) + script_len(varint) + script + sequence(4) + ...
                try:
                    offset = 4 + 1 + 32 + 4  # version + vin_count + prevout_hash + prevout_index
                    script_len_varint = coinbase[offset:offset+9]  # Read up to 9 bytes for varint
                    # Decode varint to get actual script length
                    if script_len_varint[0] < 0xfd:
                        script_len = script_len_varint[0]
                        varint_size = 1
                    elif script_len_varint[0] == 0xfd:
                        script_len = int.from_bytes(script_len_varint[1:3], 'little')
                        varint_size = 3
                    elif script_len_varint[0] == 0xfe:
                        script_len = int.from_bytes(script_len_varint[1:5], 'little')
                        varint_size = 5
                    else:
                        script_len = int.from_bytes(script_len_varint[1:9], 'little')
                        varint_size = 9

                    script_start = offset + varint_size
                    script_end = script_start + script_len
                    scriptsig = coinbase[script_start:script_end]
                    print(f"  scriptSig length: {len(scriptsig)} bytes")
                    print(f"  scriptSig: {scriptsig.hex()}")
                except Exception as e:
                    print(f"  (could not extract scriptSig: {e})")

                print(f"  coinbase_txid: {coinbase_txid.hex()}")
                print(f"  coinbase_txid (reversed): {coinbase_txid[::-1].hex()}")

            # Recompute merkle with this coinbase
            txids = [coinbase_txid]
            for tx_hex in (state.externalTxs or []):
                try:
                    # Compute txid directly from raw tx hex
                    txids.append(dsha256(bytes.fromhex(tx_hex)))
                except Exception:
                    pass
            merkle = merkle_from_txids(txids)

            if self._verbose:
                print(f"[SHA SUBMIT] Merkle root computation:")
                print(f"  Number of transactions: {len(txids)}")
                print(f"  Merkle root (computed): {merkle.hex()}")
                print(f"  Merkle root (reversed for header): {merkle[::-1].hex()}")

            # Build 80-byte header (Bitcoin SHA256d)
            # IMPORTANT: Miner returns ASCII hex as sent in mining.notify (big-endian representation)
            # We must convert to little-endian bytes for the actual Bitcoin header

            # Version: miner sends big-endian hex (e.g. "20000000"), convert to LE bytes
            version_bytes = bytes.fromhex(version_hex)[::-1] if version_hex else state.version.to_bytes(4, "little")

            # Ntime: miner sends big-endian hex, convert to LE bytes
            ntime_bytes = bytes.fromhex(ntime_hex)[::-1]

            # Nonce: miner sends big-endian hex, convert to LE bytes
            nonce_bytes = bytes.fromhex(nonce_hex)[::-1]

            # Bits: use miner_bits if set (for custom difficulty), otherwise use network bits
            # This is critical: we must use the same bits we sent to the miner in mining.notify
            bits_to_use = state.miner_bits if state.miner_bits else state.bits
            bits_bytes = bytes.fromhex(bits_to_use or "00000000")[::-1]

            # Merkle root must be reversed for Bitcoin header (like prevHash)
            merkle_reversed = merkle[::-1]

            header_no_nonce = (
                version_bytes
                + state.prevHash  # Already reversed when stored
                + merkle_reversed  # CRITICAL: Must reverse merkle for header!
                + ntime_bytes
                + bits_bytes
            )
            full_header = header_no_nonce + nonce_bytes

            if self._verbose:
                print(f"[SHA SUBMIT] Header construction:")
                print(f"  version_bytes: {version_bytes.hex()} (from version_hex: {version_hex if version_hex else 'template'})")
                print(f"  prevHash: {state.prevHash.hex()} ({len(state.prevHash)} bytes)")
                print(f"  merkle_reversed: {merkle_reversed.hex()} ({len(merkle_reversed)} bytes)")
                print(f"  ntime_bytes: {ntime_bytes.hex()} (from ntime_hex: {ntime_hex})")
                print(f"  bits_bytes: {bits_bytes.hex()} (using: {bits_to_use}, network: {state.bits})")
                print(f"  nonce_bytes: {nonce_bytes.hex()} (from nonce_hex: {nonce_hex})")
                print(f"  TOTAL header: {full_header.hex()}")
                print(f"  Header length: {len(full_header)} bytes")

            # Build full block hex (header + tx count + txs)
            tx_count = len(state.externalTxs or []) + 1
            block_hex = (
                full_header.hex()
                + var_int(tx_count).hex()
                + coinbase.hex()
                + ("".join(state.externalTxs) if state.externalTxs else "")
            )

            if self._verbose:
                print(f"[SHA SUBMIT] Block construction:")
                print(f"  tx_count: {tx_count}")
                print(f"  coinbase length: {len(coinbase)} bytes")
                print(f"  block_hex length: {len(block_hex)//2} bytes")
                print(f"  block_hex (first 80 bytes - header): {block_hex[:160]}")
        else:
            # KAWPOW mining: expected params: worker, job_id, nonce[, header, mixhash]
            if len(params) < 3:
                raise RPCError(20, f"mining.submit requires at least 3 params for KAWPOW, got {len(params)}")
            worker, job_id, nonce_hex, *rest = params

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
            nonce_int = int(nonce_hex, 16)
            nonce_hex = nonce_int.to_bytes(8, 'little').hex()

            header_hex = rest[0] if len(rest) >= 1 else ""
            mixhash_hex = rest[1] if len(rest) >= 2 else ""

            if mixhash_hex[:2].lower() == "0x":
                mixhash_hex = mixhash_hex[2:]
            # Ensure it's 32 bytes
            mixhash_hex = mixhash_hex.zfill(64)
            # Reverse mixhash bytes for Ravencoin wire format
            mixhash_hex = bytes.fromhex(mixhash_hex)[::-1].hex()

            if self._verbose:
                print(f"Submit KAWPOW - nonce_hex: {nonce_hex}, mixhash_hex: {mixhash_hex}")
                print(f"Submit KAWPOW - nonce_int: {nonce_int}, header_hash: {state.headerHash}")

            block_hex = state.build_block(nonce_hex, mixhash_hex)

        # Before submitting upstream, verify PoW against our target
        # Use big-endian for hash comparison (standard for Bitcoin)
        try:
            # Double SHA256 of the header
            pow_hash_bytes = dsha256(full_header)

            # Compare hash as big-endian integer
            pow_hash_int = int.from_bytes(pow_hash_bytes, 'big')

            # For SHA mining: use fixed difficulty 100 target
            max_target = 0x00000000ffff0000000000000000000000000000000000000000000000000000
            if state.mining_algo == "sha":
                # Fixed difficulty 100 target
                miner_target_int = max_target // 100
            else:
                # Network target for other algos
                net_target_hex = self._state.target or "00" * 32
                miner_target_int = int(net_target_hex, 16)

            # Calculate share difficulty (how difficult this share actually is)
            share_difficulty = max_target / pow_hash_int if pow_hash_int > 0 else float('inf')

            # Validate share meets our target (difficulty 100 for SHA)
            share_valid = pow_hash_int <= miner_target_int

            # For network submission, also check against network difficulty
            net_target_hex = self._state.target or "00" * 32
            net_target_int = int(net_target_hex, 16)
            block_valid = pow_hash_int <= net_target_int  # Only valid blocks are submitted upstream

            if self._verbose:
                print("[SHA SUBMIT] PoW Verification:")
                print(f"  header_hex: {full_header.hex()}")
                print(f"  pow_hash (internal): {pow_hash_bytes.hex()}")
                print(f"  pow_hash (display): {pow_hash_bytes[::-1].hex()}")
                print(f"  pow_hash_int: {pow_hash_int}")
                if state.mining_algo == "sha":
                    print(f"  miner_target_int (diff 100): {miner_target_int}")
                    print(f"  net_target_int: {net_target_int}")
                else:
                    print(f"  target_int: {miner_target_int}")
                print(f"  share_difficulty: {share_difficulty:.2f}")
                print(f"  share_valid (meets diff 100): {share_valid}")
                if state.mining_algo == "sha":
                    print(f"  block_valid (meets network diff): {block_valid}")

            if not share_valid:
                # Share does not meet difficulty target - reject it
                if self._verbose:
                    required_diff = 100.0 if state.mining_algo == "sha" else target_to_difficulty(net_target_hex)
                    print(f"[SHA SUBMIT] REJECTED: Low-difficulty share (diff {share_difficulty:.2f} < required diff {required_diff})")

                    # Diagnostic: check if version rolling might be the issue
                    if version_hex:
                        v_subm = int(version_hex, 16)
                        print(f"[DIAG] Testing version variants for debugging:")
                        print(f"  Submitted version: 0x{v_subm:08x}")

                        for v_try in [v_subm, v_subm | 0x20000000]:
                            v_bytes = v_try.to_bytes(4, "big")[::-1]
                            hdr_try = v_bytes + state.prevHash + merkle_reversed + ntime_bytes + bits_bytes + nonce_bytes
                            hash_try = dsha256(hdr_try)
                            hash_int_try = int.from_bytes(hash_try, 'big')
                            if hash_int_try <= net_target_int:
                                print(f"  version 0x{v_try:08x}: MEETS TARGET (diff {max_target / hash_int_try:.2f})")
                                if v_try != v_subm:
                                    print(f"    ⚠️  Firmware mismatch? Bitaxe may be hashing with different version!")
                            else:
                                print(f"  version 0x{v_try:08x}: does not meet target (diff {max_target / hash_int_try:.2f})")

                # Stratum v1 error code 23: "low-difficulty share"
                raise RPCError(23, "low-difficulty share")

            if block_valid:
                if self._verbose:
                    print(f"[SHA SUBMIT] *** VALID BLOCK (diff {share_difficulty:.2f}) - Submitting upstream! ***")
        except RPCError:
            # Re-raise RPCError (rejection) to send to miner
            raise
        except Exception as e:
            print(f"Warning: local PoW verification failed: {e}")
            import traceback
            traceback.print_exc()
            # Don't reject on internal errors, accept the share
            return True

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
                    error_msg = json_resp["error"]
                    if isinstance(error_msg, dict):
                        error_msg = error_msg.get("message", str(error_msg))
                    raise RPCError(20, str(error_msg))

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

        # Get height from block hex
        block_height = int.from_bytes(
            bytes.fromhex(
                block_hex[(4 + 32 + 32 + 4 + 4) * 2 : (4 + 32 + 32 + 4 + 4 + 4) * 2]
            ),
            "little",
            signed=False,
        )
        msg = f"Found block (may or may not be accepted by the chain): {block_height}"
        print(msg)
        await self.send_notification("client.show_message", (msg,))

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
    difficulty_multiplier: int,
):
    # Build the getBlockTemplate request with rules parameter
    request_params = {
        "rules": [state.mining_algo]
    }
    data = {"jsonrpc": "2.0", "id": "0", "method": "quai_getBlockTemplate", "params": [request_params]}
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
                    print(f"GetBlockTemplate response: {response_text[:2000]}")  # Print first 2000 chars

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
                coinbase_sats_int: int = int(json_obj["result"]["coinbasevalue"], 16) if isinstance(json_obj["result"]["coinbasevalue"], str) else json_obj["result"]["coinbasevalue"]
                witness_hex: str = json_obj["result"].get("default_witness_commitment", "")
                coinbase_aux_hex: str = json_obj["result"].get("coinbaseaux", "")
                if not isinstance(coinbase_aux_hex, str):
                    coinbase_aux_hex = ""
                if coinbase_aux_hex.startswith("0x"):
                    coinbase_aux_hex = coinbase_aux_hex[2:]
                payout_script_hex: str = json_obj["result"].get("payoutscript", "")
                if not isinstance(payout_script_hex, str):
                    payout_script_hex = ""
                if payout_script_hex.startswith("0x"):
                    payout_script_hex = payout_script_hex[2:]

                # If payout script is empty, use a default P2PKH script
                # This is a placeholder - miners should configure their own address
                if not payout_script_hex or payout_script_hex == "":
                    # Default to a burn address script: OP_DUP OP_HASH160 <20 zeros> OP_EQUALVERIFY OP_CHECKSIG
                    payout_script_hex = "76a914" + "00" * 20 + "88ac"
                    if verbose:
                        print(f"WARNING: Using default payout script (burn address). Configure proper payout address!")

                target_hex: str = json_obj["result"]["target"]
                if target_hex.startswith("0x"):
                    target_hex = target_hex[2:]
                merkle_branch: List = json_obj["result"].get("merkleBranch", [])

                ts = int(time.time())
                new_witness = witness_hex != state.current_commitment
                state.current_commitment = witness_hex
                new_coinbase_aux = coinbase_aux_hex != state.coinbase_aux
                state.coinbase_aux = coinbase_aux_hex
                new_payout_script = payout_script_hex != state.payout_script
                state.payout_script = payout_script_hex
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

                    # Generate seed hash (only for KAWPOW) #
                    if state.mining_algo != "sha":
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
                    else:
                        # SHA mining doesn't use seed hash
                        state.seedHash = bytes(32)  # Keep as placeholder

                    # Done with seed hash #
                    state.height = height_int

                # The following occurs during both new blocks & new txs & nothing happens for 60s (magic number)
                # Also trigger when there are new sessions waiting for work
                if (
                    new_block
                    or new_witness
                    or new_coinbase_aux
                    or new_payout_script
                    or state.timestamp + 60 < ts
                    or len(state.new_sessions) > 0
                ):
                    # Generate coinbase #

                    if original_state is None:
                        original_state = deepcopy(state)

                    # Use the coinbase scriptSig provided by go-quai
                    # go-quai's BuildCoinbaseScriptSigWithNonce already creates the proper format
                    coinbase_script_full = bytes.fromhex(coinbase_aux_hex)

                    coinbase_txin = (
                        bytes(32)  # Previous output hash (null for coinbase)
                        + b"\xff" * 4  # Previous output index (all 0xff for coinbase)
                        + var_int(len(coinbase_script_full))  # Script length
                        + coinbase_script_full  # The scriptSig from go-quai
                        + b"\xff" * 4  # Sequence
                    )

                    payout_script = bytes.fromhex(payout_script_hex)


                    # Concerning the default_witness_commitment:
                    # https://github.com/bitcoin/bips/blob/master/bip-0141.mediawiki#commitment-structure
                    # Because the coinbase tx is '00'*32 in witness commit,
                    # We can take what the node gives us directly without changing it
                    # (This assumes that the txs are in the correct order, but I think
                    # that is a safe assumption)

                    # Build coinbase for Ravencoin (no witness commitment needed)
                    # For Ravencoin, we only need one output - the payout to the miner
                    coinbase_outputs = (
                        b"\x01"  # Output count = 1
                        + coinbase_sats_int.to_bytes(8, "little")  # Amount
                        + var_int(len(payout_script))  # Script length
                        + payout_script  # Payout script
                    )

                    state.coinbase_tx = (
                        int(1).to_bytes(4, "little")  # Version
                        + b"\x01"  # Input count = 1
                        + coinbase_txin  # Coinbase input
                        + coinbase_outputs  # Outputs
                        + bytes(4)  # Lock time
                    )
                    state.coinbase_txid = dsha256(state.coinbase_tx)

                    if verbose:
                        print(f"[DEBUG] Coinbase construction:")
                        print(f"  coinbase_tx length: {len(state.coinbase_tx)} bytes")
                        print(f"  coinbase_tx first 40 bytes: {state.coinbase_tx[:40].hex()}")
                        print(f"  Expected start: 01000000 01 (version + input_count)")

                    # Build coinbase1 and coinbase2 ONLY for SHA mining (stratum protocol)
                    # KAWPOW doesn't use extraNonce - it gets the full header
                    if state.mining_algo == "sha":
                        # For SHA mining, use single-push extranonce (EN1||EN2 = 12 bytes)
                        # Standard Stratum v1: coinbase = coinbase1 + EN1 + EN2 + coinbase2
                        try:
                            en1_start, _, _, en2_end = find_extranonce_positions_in_coinbase_script(coinbase_script_full)

                            # The opcodes are just before the data
                            ex1_op_pos = en1_start - 1  # Position of OP_PUSH4

                            # Split: everything before the first push opcode, everything after EN2
                            prefix = coinbase_script_full[:ex1_op_pos]
                            suffix = coinbase_script_full[en2_end:]

                            # Use a single OP_PUSH12 for EN1||EN2 (4 + 8 = 12 bytes)
                            OP_PUSH12 = b"\x0c"  # 12 <= 75, so direct push opcode

                            # New script length includes: prefix + OP_PUSH12 + 12 data bytes + suffix
                            new_script_len = len(prefix) + 1 + 12 + len(suffix)
                            script_len_varint = var_int(new_script_len)

                            state.coinbase1 = (
                                int(1).to_bytes(4, "little")  # Version
                                + b"\x01"  # Input count = 1
                                + bytes(32)  # Previous output hash (null for coinbase)
                                + b"\xff" * 4  # Previous output index (all 0xff for coinbase)
                                + script_len_varint  # Script length for NEW script
                                + prefix  # Script prefix (height, magic, seal, merkle_size, merkle_nonce)
                                + OP_PUSH12  # Single push for EN1||EN2
                                # Miner inserts: EN1 (4 bytes) + EN2 (8 bytes) = 12 bytes
                            )

                            state.coinbase2 = (
                                suffix  # Script suffix (after EN2)
                                + b"\xff" * 4  # Sequence
                                + coinbase_outputs  # Outputs
                                + bytes(4)  # Lock time
                            )

                            # No "between" region anymore with single push
                            state.coinbase2_script_between_len = 0

                            if verbose:
                                print(f"[SHA COINBASE] Using single-push extranonce (12 bytes)")
                                print(f"  prefix length: {len(prefix)} bytes")
                                print(f"  suffix length: {len(suffix)} bytes")
                                print(f"  new script length: {new_script_len} bytes")

                        except Exception as e:
                            print(f"Error parsing coinbase scriptSig for SHA mining: {e}")
                            # Fall back to no extraNonce support if parsing fails
                            state.coinbase1 = state.coinbase_tx
                            state.coinbase2 = b""
                            state.coinbase2_script_between_len = 0

                    # Create merkle & update txs
                    txids = [state.coinbase_txid]
                    incoming_txs = []
                    for tx_data in txs_list:
                        incoming_txs.append(tx_data["data"])
                        txids.append(bytes.fromhex(tx_data["txid"]))
                    state.externalTxs = incoming_txs
                    merkle = merkle_from_txids(txids)

                    # Done create merkle & update txs

                    if state.mining_algo == "sha":
                        # SHA256d header: 80 bytes (Bitcoin format)
                        # version(4) + prevHash(32) + merkleRoot(32) + time(4) + bits(4) + nonce(4)
                        # merkleRoot is serialized little-endian in the header
                        state.header = (
                            version_int.to_bytes(4, "little")
                            + state.prevHash
                            + merkle[::-1]  # <-- REVERSE THE MERKLE ROOT
                            + ts.to_bytes(4, "little")
                            + bytes.fromhex(bits_hex)[::-1]
                            # Note: Nonce will be added by the miner (not included in template)
                        )
                    else:
                        # KAWPOW header: 76 bytes before nonce + mixhash
                        # version(4) + prevHash(32) + merkleRoot(32) + time(4) + bits(4) + height(4)
                        # (nonce and mixHash added by miner)
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

                    # Calculate miner difficulty/target
                    # For SHA miners we control share difficulty via mining.set_difficulty only.
                    # FIXED: Use difficulty 100 for SHA mining (ignore network difficulty)
                    if state.mining_algo == "sha":
                        # Set fixed difficulty of 100 for testing
                        miner_difficulty = 100.0
                        # Calculate target for difficulty 100: max_target / 100
                        max_target = 0x00000000ffff0000000000000000000000000000000000000000000000000000
                        miner_target_int = max_target // 100
                        miner_target_hex = hex(miner_target_int)[2:].zfill(64)
                        # Convert to compact bits format for mining.notify
                        miner_bits_hex = target_to_compact_bits(miner_target_int)
                        # Store miner bits in state so we can use them for header reconstruction
                        state.miner_bits = miner_bits_hex
                    else:
                        # KAWPOW miners use target directly
                        miner_target_hex = adjust_target_for_difficulty_multiplier(target_hex, difficulty_multiplier)
                        miner_difficulty = target_to_difficulty(miner_target_hex)

                    if verbose:
                        print(f"Target calculation:")
                        print(f"  Network target: {target_hex}")
                        print(f"  Miner target (÷{difficulty_multiplier}): {miner_target_hex}")
                        print(f"  Network target int: {int(target_hex, 16)}")
                        print(f"  Miner target int: {int(miner_target_hex, 16)}")
                        print(f"  Miner difficulty: {miner_difficulty}")

                    for session in state.all_sessions:
                        print(f"[NOTIFY] Sending mining.notify to existing session: {session}")
                        print(f"  job_id: {hex(state.job_counter)[2:]}")
                        print(f"  headerHash: {state.headerHash}")
                        if state.mining_algo != "sha":
                            print(f"  seedHash: {state.seedHash.hex()}")
                        print(f"  network target: {target_hex}")
                        print(f"  miner target ({difficulty_multiplier}x harder): {miner_target_hex}")
                        print(f"  clean_jobs: True")
                        print(f"  height: {state.height}")
                        print(f"  bits: {bits_hex}")
                        print(f"  mining_algo: {state.mining_algo}")
                        if state.mining_algo == "sha":
                            # SHA miners: only send difficulty (Bitaxe and most SHA miners ignore set_target)
                            await session.send_notification("mining.set_difficulty", (miner_difficulty,))
                        else:
                            # KAWPOW miners use mining.set_target with hex target
                            await session.send_notification(
                                "mining.set_target", (miner_target_hex,)
                            )
                        if state.mining_algo == "sha":
                            # SHA mining uses standard Stratum protocol
                            # mining.notify(job_id, prevhash, coinbase1, coinbase2, merkle_branch, version, nbits, ntime, clean_jobs)
                            # IMPORTANT: Stratum v1 sends version/nbits/ntime as ASCII hex "as-put-into-header"
                            # These are the exact byte sequences miners will write to the header
                            version_hex = f"{version_int:08x}"  # e.g. "20000000" for version 0x20000000
                            nbits_hex = miner_bits_hex  # Use difficulty 100 bits instead of network bits
                            ntime_hex = f"{ts:08x}"  # e.g. "68f86424" for timestamp

                            print(f"[NOTIFY DETAIL] Stratum fields being sent:")
                            print(f"  version: {version_hex} (from version_int {version_int:#x})")
                            print(f"  nbits: {nbits_hex} (difficulty 100, network bits: {bits_hex})")
                            print(f"  ntime: {ntime_hex} (from timestamp {ts})")
                            print(f"  coinbase1: {len(state.coinbase1)} bytes")
                            print(f"  coinbase2: {len(state.coinbase2)} bytes")

                            await session.send_notification(
                                "mining.notify",
                                (
                                    hex(state.job_counter)[2:],  # job_id
                                    state.prevHash[::-1].hex(),  # prevhash (big-endian for stratum)
                                    state.coinbase1.hex(),  # coinbase1
                                    state.coinbase2.hex(),  # coinbase2
                                    [],  # merkle_branch (empty for now, only coinbase in block)
                                    version_hex,  # version as-in-header
                                    nbits_hex,  # nbits as-in-header
                                    ntime_hex,  # ntime as-in-header
                                    True,  # clean_jobs
                                ),
                            )
                        else:
                            # KAWPOW mining uses seedHash
                            await session.send_notification(
                                "mining.notify",
                                (
                                    hex(state.job_counter)[2:],
                                    state.headerHash,
                                    state.seedHash.hex(),
                                    miner_target_hex,
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
                        if state.mining_algo != "sha":
                            print(f"  seedHash: {state.seedHash.hex()}")
                        print(f"  network target: {target_hex}")
                        print(f"  miner target ({difficulty_multiplier}x harder): {miner_target_hex}")
                        print(f"  clean_jobs: True")
                        print(f"  height: {state.height}")
                        print(f"  bits: {bits_hex}")
                        print(f"  mining_algo: {state.mining_algo}")
                        if state.mining_algo == "sha":
                            # SHA miners: only send difficulty (Bitaxe and most SHA miners ignore set_target)
                            await session.send_notification("mining.set_difficulty", (miner_difficulty,))
                        else:
                            # KAWPOW miners use mining.set_target with hex target
                            await session.send_notification("mining.set_target", (miner_target_hex,))
                        if state.mining_algo == "sha":
                            # SHA mining uses standard Stratum protocol
                            # mining.notify(job_id, prevhash, coinbase1, coinbase2, merkle_branch, version, nbits, ntime, clean_jobs)
                            # IMPORTANT: Stratum v1 sends version/nbits/ntime as ASCII hex "as-put-into-header"
                            # These are the exact byte sequences miners will write to the header
                            version_hex = f"{version_int:08x}"  # e.g. "20000000" for version 0x20000000
                            nbits_hex = miner_bits_hex  # Use difficulty 100 bits instead of network bits
                            ntime_hex = f"{ts:08x}"  # e.g. "68f86424" for timestamp

                            print(f"[NOTIFY DETAIL] Stratum fields being sent:")
                            print(f"  version: {version_hex} (from version_int {version_int:#x})")
                            print(f"  nbits: {nbits_hex} (difficulty 100, network bits: {bits_hex})")
                            print(f"  ntime: {ntime_hex} (from timestamp {ts})")
                            print(f"  coinbase1: {len(state.coinbase1)} bytes")
                            print(f"  coinbase2: {len(state.coinbase2)} bytes")

                            await session.send_notification(
                                "mining.notify",
                                (
                                    hex(state.job_counter)[2:],  # job_id
                                    state.prevHash[::-1].hex(),  # prevhash (big-endian for stratum)
                                    state.coinbase1.hex(),  # coinbase1
                                    state.coinbase2.hex(),  # coinbase2
                                    [],  # merkle_branch (empty for now, only coinbase in block)
                                    version_hex,  # version as-in-header
                                    nbits_hex,  # nbits as-in-header
                                    ntime_hex,  # ntime as-in-header
                                    True,  # clean_jobs
                                ),
                            )
                        else:
                            # KAWPOW mining uses seedHash
                            await session.send_notification(
                                "mining.notify",
                                (
                                    hex(state.job_counter)[2:],
                                    state.headerHash,
                                    state.seedHash.hex(),
                                    miner_target_hex,
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
            "arguments must be: proxy_port, node_ip, node_username, node_password, node_port, listen_externally, (optional: testnet, verbose, difficulty_multiplier, mining_algo)"
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
    difficulty_multiplier = 10  # Default to 10x difficulty
    mining_algo = "kawpow"  # Default to KAWPOW

    if len(sys.argv) > 7:
        testnet = check_bool(sys.argv[7])

    if len(sys.argv) > 8:
        verbose = check_bool(sys.argv[8])

    if len(sys.argv) > 9:
        difficulty_multiplier = int(sys.argv[9])

    if len(sys.argv) > 10:
        mining_algo = str(sys.argv[10]).lower()
        if mining_algo not in ["kawpow", "sha", "scrypt"]:
            print(f"Invalid mining algorithm: {mining_algo}. Must be 'kawpow', 'sha', or 'scrypt'")
            exit(1)

    if not os.path.exists("./submit_history"):
        os.mkdir("./submit_history")

    print("Starting stratum converter")
    print(f"Mining algorithm: {mining_algo.upper()}")
    print(f"Difficulty multiplier: {difficulty_multiplier}x (miners will search for blocks {difficulty_multiplier}x harder than network difficulty)")

    # The shared state
    state = TemplateState()
    state.mining_algo = mining_algo  # Set the mining algorithm
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
        difficulty_multiplier,
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
                difficulty_multiplier,
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
