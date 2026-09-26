#!/usr/bin/env python3
"""Prototype a PC-preserving translation of the four active SPHINCS images.

This only translates the image literals. It does not change the abstract
scheme, prove a VM simulation, or make unaligned HASH lengths admissible.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path

ACTIVE = {
    "SphincsMaskedImages.lean": ("keygen", "sign"),
    "SphincsImages.lean": ("expand", "verify"),
}
CHUNK_RE = re.compile(
    r"(?:private )?def (?P<name>\w+Chunk\d+) : List \(BitVec 32\) := \[(?P<body>.*?)\]",
    re.S,
)
WORD_RE = re.compile(r"0x[0-9a-fA-F]{8}")
ECALL = 0x00000073
ADDI_T0_0 = 0x00000293
ADDI_T0_1 = 0x00100293
ADDI_A0_0 = 0x00000513
ADDI_A0_1 = 0x00100513


@dataclass(frozen=True)
class Word:
    value: int
    start: int
    end: int


def register_write(word: int, register: int) -> bool:
    return word & 0x7F in (0x13, 0x37, 0x03, 0x33) and (word >> 7) & 31 == register


def signed_imm12(word: int) -> int:
    value = word >> 20
    return value - 4096 if value >= 2048 else value


def encode_addi(rd: int, rs: int, imm: int) -> int:
    assert -2048 <= imm <= 2047
    return ((imm & 0xFFF) << 20) | (rs << 15) | (rd << 7) | 0x13


def encode_lui(rd: int, upper: int) -> int:
    assert 0 <= upper < (1 << 20)
    return (upper << 12) | (rd << 7) | 0x37


def length_loader(code: list[Word], ecall_index: int) -> tuple[list[int], int]:
    """Find and evaluate the adjacent static x11 constant load before ECALL."""
    writes = []
    for j in range(ecall_index - 2, max(-1, ecall_index - 12), -1):
        value = code[j].value
        if register_write(value, 11):
            writes.append(j)
            opcode = value & 0x7F
            if opcode == 0x37 or (opcode == 0x13 and (value >> 15) & 31 == 0):
                break
    assert 1 <= len(writes) <= 2, (ecall_index, writes)
    writes.reverse()
    if len(writes) == 1:
        value = code[writes[0]].value
        assert value & 0x7F == 0x13 and (value >> 15) & 31 == 0
        assert (value >> 12) & 7 == 0
        return writes, signed_imm12(value)
    high, low = (code[j].value for j in writes)
    assert high & 0x7F == 0x37 and low & 0x7F == 0x13
    assert (low >> 15) & 31 == 11 and (low >> 12) & 7 == 0
    return writes, (high & 0xFFFFF000) + signed_imm12(low)


def encoded_length_loader(writes: list[int], byte_length: int) -> list[int]:
    if len(writes) == 1:
        return [encode_addi(11, 0, byte_length)]
    upper = (byte_length + 2048) >> 12
    lower = byte_length - (upper << 12)
    return [encode_lui(11, upper), encode_addi(11, 11, lower)]


def digest(code: list[int]) -> str:
    return hashlib.sha256(b"".join(word.to_bytes(4, "little") for word in code)).hexdigest()
