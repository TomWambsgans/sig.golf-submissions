#!/usr/bin/env python3
"""Translate old ECALLs to PC-preserving, 64-byte-aligned beta service stubs."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Optional

from legacy_asm import (
    ADDI_A0_0, ADDI_A0_1, ADDI_T0_0, ADDI_T0_1,
    CHUNK_RE, ECALL, WORD_RE, length_loader, Word,
)

BASE_PC = 0x1000
MAX_IMAGE_BYTES = 1 << 20
SRLI_A1_3 = (3 << 20) | (11 << 15) | (5 << 12) | (11 << 7) | 0x13
SLLI_A1_3 = (3 << 20) | (11 << 15) | (1 << 12) | (11 << 7) | 0x13
XORI_A0_1 = (1 << 20) | (10 << 15) | (4 << 12) | (10 << 7) | 0x13

def addi(rd: int, rs: int, imm: int) -> int:
    assert -2048 <= imm < 2048
    return ((imm & 4095) << 20) | (rs << 15) | (rd << 7) | 0x13

def lw(rd: int, rs: int, imm: int) -> int:
    return (imm << 20) | (rs << 15) | (6 << 12) | (rd << 7) | 0x03

def ld(rd: int, rs: int, imm: int) -> int:
    assert 0 <= imm < 2048
    return (imm << 20) | (rs << 15) | (3 << 12) | (rd << 7) | 0x03

def sw(rs: int, base: int, imm: int) -> int:
    return ((imm >> 5) << 25) | (rs << 20) | (base << 15) | (2 << 12) | ((imm & 31) << 7) | 0x23

def sd(rs: int, base: int, imm: int) -> int:
    assert 0 <= imm < 2048
    return ((imm >> 5) << 25) | (rs << 20) | (base << 15) | (3 << 12) | ((imm & 31) << 7) | 0x23

def padding_words(byte_length: int) -> tuple[list[int], list[int], list[int], int]:
    """Save, zero, restore the exact suffix; return pre/post/registers/pad count."""
    pad = (-byte_length) % 64
    if pad == 0:
        return [], [], [], 0
    before: list[int] = []
    after: list[int] = []
    restores: list[tuple[int, int]] = []
    used: list[int] = []
    if byte_length == 131124:
        # MAC input begins at 0x18; its pad begins at 0x2004c, beyond I-immediate range.
        base, offset = 30, 0
        before += [lui(30, 0x20000), addi(30, 30, 0x4c)]
    else:
        # All ordinary HASH inputs begin at 0x40000 and have at most 1080 bytes.
        base, offset = 10, byte_length
        assert byte_length + pad <= 2048
    if byte_length % 8 == 4:
        used.append(16)
        before += [lw(16, base, offset), sw(0, base, offset)]
        restores.append((sw(16, base, offset), 16))
        offset += 4
        pad -= 4
    else:
        assert byte_length % 8 == 0
    assert pad % 8 == 0
    for j in range(pad // 8):
        reg = 16 + len(used)
        used.append(reg)
        before += [ld(reg, base, offset + 8 * j), sd(0, base, offset + 8 * j)]
        restores.append((sd(reg, base, offset + 8 * j), reg))
    # Reverse the save order and clear each register immediately. This is
    # exactly the recursive restoreMany order in the Lean padding theorem.
    for store, reg in reversed(restores):
        after += [store, addi(reg, 0, 0)]
    if base == 30:
        after.append(addi(30, 0, 0))
    return before, after, used, (-byte_length) % 64

def lui(rd: int, value: int) -> int:
    assert value % 4096 == 0
    return value | (rd << 7) | 0x37


def jal(offset: int) -> int:
    """Encode JAL x0, offset (signed 21-bit byte displacement)."""
    assert offset % 2 == 0 and -(1 << 20) <= offset < (1 << 20), offset
    imm = offset & ((1 << 21) - 1)
    return (
        ((imm >> 20) & 1) << 31
        | ((imm >> 1) & 0x3FF) << 21
        | ((imm >> 11) & 1) << 20
        | ((imm >> 12) & 0xFF) << 12
        | 0x6F
    )


def jal_offset(word: int) -> int:
    assert word & 0x7F == 0x6F, hex(word)
    imm = (
        ((word >> 31) & 1) << 20
        | ((word >> 21) & 0x3FF) << 1
        | ((word >> 20) & 1) << 11
        | ((word >> 12) & 0xFF) << 12
    )
    return imm - (1 << 21) if imm & (1 << 20) else imm


def direct_target(index: int, word: int) -> Optional[int]:
    opcode = word & 0x7F
    pc = BASE_PC + 4 * index
    if opcode == 0x6F:
        return pc + jal_offset(word)
    if opcode == 0x63:
        imm = (
            ((word >> 31) & 1) << 12
            | ((word >> 7) & 1) << 11
            | ((word >> 25) & 0x3F) << 5
            | ((word >> 8) & 0xF) << 1
        )
        return pc + (imm - (1 << 13) if imm & (1 << 12) else imm)
    return None


def parse_code(source: str, name: str) -> list[Word]:
    chunks = {}
    for match in CHUNK_RE.finditer(source):
        body = match.group("body")
        chunks[match.group("name")] = [
            Word(int(word.group(), 16), match.start("body") + word.start(),
                 match.start("body") + word.end())
            for word in WORD_RE.finditer(body)
        ]
    names = sorted(
        (chunk for chunk in chunks if re.fullmatch(name + r"Chunk\d+", chunk)),
        key=lambda chunk: int(chunk.split("Chunk")[1]),
    )
    assert names and [int(chunk.split("Chunk")[1]) for chunk in names] == list(range(len(names)))
    return [word for chunk in names for word in chunks[chunk]]


def translate(code: list[Word], name: str) -> tuple[list[int], list[dict]]:
    original = [word.value for word in code]
    patched = original.copy()
    stubs: list[int] = []
    sites: list[dict] = []
    ecall_indices = [i for i, word in enumerate(original) if word == ECALL]
    original_edges = [
        (BASE_PC + 4 * i, direct_target(i, word))
        for i, word in enumerate(original) if direct_target(i, word) is not None
    ]
    assert not [i for i, word in enumerate(original) if word & 0x7F == 0x67], (
        name, "indirect JALR exists"
    )
    for i in ecall_indices:
        original_pc = BASE_PC + 4 * i
        stub_pc = BASE_PC + 4 * (len(original) + len(stubs))
        forward = stub_pc - original_pc
        patched[i] = jal(forward)
        assert original_pc + jal_offset(patched[i]) == stub_pc
        if original[i - 1] == ADDI_T0_1:
            # All current image HASH lengths are static, divisible by eight
            # bits, and loaded without a control-flow edge before ECALL.
            writes, bits = length_loader(code, i)
            assert bits > 0 and bits % 8 == 0
            assert all(original[j] & 0x7F not in (0x63, 0x6F, 0x67)
                       for j in range(writes[0], i))
            setup_start = BASE_PC + 4 * writes[0]
            assert not [(src, dst) for src, dst in original_edges
                        if setup_start <= dst <= original_pc], (
                name, hex(original_pc), "direct edge enters HASH setup"
            )
            byte_length = bits // 8
            # On the old path t0=1. The stub temporarily changes only a1/t0,
            # then returns with both registers equal to their old values.
            return_pc = original_pc + 4
            before, after, used, padding = padding_words(byte_length)
            assert not used or max(used) < 30
            body = before + [SRLI_A1_3]
            if padding:
                body.append(addi(11, 11, padding))
            body += [ADDI_T0_0, ECALL]
            if padding:
                body.append(addi(11, 11, -padding))
            body += [SLLI_A1_3, ADDI_T0_1] + after
            jump_pc = stub_pc + len(body) * 4
            backward = return_pc - jump_pc
            body.append(jal(backward))
            assert jump_pc + jal_offset(body[-1]) == return_pc
            stubs.extend(body)
            sites.append({
                "kind": "HASH", "original_pc": hex(original_pc),
                "stub_pc": hex(stub_pc), "stub_ecall_pc": hex(stub_pc + 4 * body.index(ECALL)),
                "return_pc": hex(return_pc), "forward_jal_bytes": forward,
                "return_jal_bytes": backward,
                "old_bits": bits, "new_bytes": byte_length + padding,
                "padding_bytes": padding, "scratch_registers": used,
                "beta_length_aligned": (byte_length + padding) % 64 == 0,
                "stub_words": [hex(word) for word in body],
            })
        else:
            assert i >= 2 and original[i - 2] == ADDI_T0_0
            assert original[i - 1] in (ADDI_A0_0, ADDI_A0_1)
            # A jump to the first HALT setup instruction is intentional; a
            # jump past it could bypass selector or exit-code initialization.
            assert not [(src, dst) for src, dst in original_edges
                        if original_pc - 8 < dst <= original_pc], (
                name, hex(original_pc), "direct edge skips HALT setup"
            )
            old_success = original[i - 1] == ADDI_A0_1
            # The source a0 is already a literal 0 or 1. XORI flips it.
            body = [ADDI_T0_1, XORI_A0_1, ECALL]
            stubs.extend(body)
            sites.append({
                "kind": "HALT", "original_pc": hex(original_pc),
                "stub_pc": hex(stub_pc), "stub_ecall_pc": hex(stub_pc + 8),
                "old_success": old_success, "new_success": old_success,
                "forward_jal_bytes": forward,
                "stub_words": [hex(word) for word in body],
            })
    translated = patched + stubs
    assert len(translated) == len(original) + sum(len(s["stub_words"]) for s in sites)
    assert len(translated) * 4 < MAX_IMAGE_BYTES
    assert [i for i in range(len(original)) if translated[i] != original[i]] == ecall_indices
    assert sum(word == ECALL for word in translated) == len(ecall_indices)
    assert all(translated[(int(s["stub_ecall_pc"], 16) - BASE_PC) // 4] == ECALL for s in sites)
    stub_starts = {int(site["stub_pc"], 16) for site in sites}
    old_end = BASE_PC + 4 * len(original)
    translated_edges = [
        (BASE_PC + 4 * i, direct_target(i, word))
        for i, word in enumerate(translated) if direct_target(i, word) is not None
    ]
    assert all(dst in stub_starts for src, dst in translated_edges if dst >= old_end), (
        name, "direct edge enters stub interior"
    )
    assert all(src < old_end for src, dst in translated_edges if dst >= old_end), (
        name, "stub-to-stub direct edge"
    )
    return translated, sites
