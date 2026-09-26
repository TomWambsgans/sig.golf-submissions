"""Emulator of the sig.golf beta VM (SigGolf/Riscv.lean + SigGolf/Programs.lean).

* decode: SigGolf.Riscv.decodeInstruction (word ops / SRAIW / exact ECALL, EBREAK words) on top of
  RiscvZkvm.Interpreter.decode.  Unsupported words decode to None (fetch failure, 0 cycles).
* step semantics: execInstrBr + memoryArgumentsValid (accessValid: addr + n <= 2^24 and
  addr % n == 0), EBREAK -> failure (1 cycle), ECALL t0=0 HASH (8 cycles / 64-byte block, no
  instruction charge), t0=1 HALT (1 cycle, success iff a0 == 0), anything else failure (1 cycle).
* fuel counts executed steps (instructions + HASH + HALT); running out is 'unfinished'.
* loader: initialState (data at data_base via writeBytesAsWords, then inputs in inputBuffers order,
  sp = data_base); readOutput per phase.
"""
import hashlib

MEM_BYTES = 1 << 24
MASK = (1 << 64) - 1
CACHE_BYTES = 1 << 17
MAX_IMAGE_BYTES = 1 << 20
CYCLE_LIMIT = 1 << 32


def sext(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


# ---------------------------------------------------------------- decode
def _base_decode(w):
    """RiscvZkvm.Interpreter.decode (opcode 0x73 and 0x3b never reach here)."""
    op = w & 0x7f
    rd = (w >> 7) & 31
    f3 = (w >> 12) & 7
    rs1 = (w >> 15) & 31
    rs2 = (w >> 20) & 31
    f7 = (w >> 25) & 0x7f
    f6 = (w >> 26) & 0x3f
    shamt = (w >> 20) & 0x3f
    shamtw = (w >> 20) & 0x1f
    immI = sext(w >> 20, 12)
    if op == 0x33:
        t = {(0x00, 0): 'ADD', (0x20, 0): 'SUB', (0x00, 1): 'SLL', (0x00, 2): 'SLT',
             (0x00, 3): 'SLTU', (0x00, 4): 'XOR', (0x00, 5): 'SRL', (0x20, 5): 'SRA',
             (0x00, 6): 'OR', (0x00, 7): 'AND', (0x01, 0): 'MUL', (0x01, 1): 'MULH',
             (0x01, 2): 'MULHSU', (0x01, 3): 'MULHU', (0x01, 4): 'DIV', (0x01, 5): 'DIVU',
             (0x01, 6): 'REM', (0x01, 7): 'REMU'}.get((f7, f3))
        return (t, rd, rs1, rs2) if t else None
    if op == 0x13:
        if f3 in (0, 2, 3, 4, 6, 7):
            return ({0: 'ADDI', 2: 'SLTI', 3: 'SLTIU', 4: 'XORI', 6: 'ORI', 7: 'ANDI'}[f3], rd, rs1, immI)
        if f3 == 1:
            return ('SLLI', rd, rs1, shamt) if f6 == 0 else None
        if f3 == 5:
            if f6 == 0:
                return ('SRLI', rd, rs1, shamt)
            if f6 == 0x10:
                return ('SRAI', rd, rs1, shamt)
            return None
        return None
    if op == 0x1b:
        if f3 == 0:
            return ('ADDIW', rd, rs1, immI)
        if f3 == 1:
            return ('SLLIW', rd, rs1, shamtw) if f7 == 0 else None
        if f3 == 5:
            return ('SRLIW', rd, rs1, shamtw) if f7 == 0 else None
        return None
    if op == 0x37:
        return ('LUI', rd, (w >> 12) & 0xfffff)
    if op == 0x17:
        return ('AUIPC', rd, (w >> 12) & 0xfffff)
    if op == 0x6f:
        imm = (((w >> 31) & 1) << 20) | (((w >> 12) & 255) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 1023) << 1)
        return ('JAL', rd, sext(imm, 21))
    if op == 0x67:
        return ('JALR', rd, rs1, immI) if f3 == 0 else None
    if op == 0x63:
        imm = (((w >> 31) & 1) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 63) << 5) | (((w >> 8) & 15) << 1)
        t = {0: 'BEQ', 1: 'BNE', 4: 'BLT', 5: 'BGE', 6: 'BLTU', 7: 'BGEU'}.get(f3)
        return (t, rs1, rs2, sext(imm, 13)) if t else None
    if op == 0x03:
        t = {0: 'LB', 1: 'LH', 2: 'LW', 3: 'LD', 4: 'LBU', 5: 'LHU', 6: 'LWU'}.get(f3)
        return (t, rd, rs1, immI) if t else None
    if op == 0x23:
        immS = sext(((w >> 25) << 5) | ((w >> 7) & 31), 12)
        t = {0: 'SB', 1: 'SH', 2: 'SW', 3: 'SD'}.get(f3)
        return (t, rs1, rs2, immS) if t else None   # (base, data, off)
    if op == 0x0f:
        return ('FENCE',) if f3 == 0 else None
    return None


def decode(w):
    """SigGolf.Riscv.decodeInstruction."""
    w &= 0xffffffff
    op = w & 0x7f
    if op == 0x73:
        if w == 0x00000073:
            return ('ECALL',)
        if w == 0x00100073:
            return ('EBREAK',)
        return None
    rd = (w >> 7) & 31
    rs1 = (w >> 15) & 31
    rs2 = (w >> 20) & 31
    f3 = (w >> 12) & 7
    f7 = (w >> 25) & 0x7f
    if op == 0x3b:
        t = {(0, 0): 'ADDW', (0x20, 0): 'SUBW', (0, 1): 'SLLW', (0, 5): 'SRLW', (0x20, 5): 'SRAW',
             (1, 0): 'MULW', (1, 4): 'DIVW', (1, 5): 'DIVUW', (1, 6): 'REMW', (1, 7): 'REMUW'}.get((f7, f3))
        return (t, rd, rs1, rs2) if t else None
    if op == 0x1b and f3 == 5 and f7 == 0x20:
        return ('SRAIW', rd, rs1, (w >> 20) & 31)
    return _base_decode(w)


def describe(d):
    return tuple(d)


# ---------------------------------------------------------------- execution
MULDIV = {'MUL', 'MULH', 'MULHSU', 'MULHU', 'DIV', 'DIVU', 'REM', 'REMU',
          'MULW', 'DIVW', 'DIVUW', 'REMW', 'REMUW'}


class Oracle:
    """sha256 stand-in for the random oracle H on 64k-byte inputs; logs every query."""

    def __init__(self, log=True, fn=None):
        self.log = [] if log else None
        self.calls = 0
        self.compressions = 0
        self.fn = fn or (lambda y: hashlib.sha256(y).digest())

    def __call__(self, data):
        assert len(data) > 0 and len(data) % 64 == 0
        self.calls += 1
        self.compressions += len(data) // 64
        if self.log is not None:
            self.log.append(bytes(data))
        return self.fn(bytes(data))


class Result:
    def __init__(self, exit, cycles, steps, oracle, mem, regs, pc):
        self.exit = exit            # 'success' | 'failure' | 'unfinished'
        self.cycles = cycles
        self.steps = steps
        self.oracle = oracle
        self.hash_calls = oracle.calls
        self.compressions = oracle.compressions
        self.mem = mem
        self.regs = regs
        self.pc = pc

    def read(self, addr, n):
        return bytes(self.mem[addr:addr + n])


def _s64(x):
    return x - (1 << 64) if x >> 63 else x


def _div(a, b, bits):
    m = (1 << bits) - 1
    if b == 0:
        return m
    sa, sb = sext(a, bits), sext(b, bits)
    q = abs(sa) // abs(sb)
    if (sa < 0) != (sb < 0):
        q = -q
    return q & m


def _rem(a, b, bits):
    m = (1 << bits) - 1
    if b == 0:
        return a & m
    sa, sb = sext(a, bits), sext(b, bits)
    r = abs(sa) % abs(sb)
    if sa < 0:
        r = -r
    return r & m


# opcode ids for the fast interpreter
OPS = ['ADD', 'SUB', 'SLL', 'SLT', 'SLTU', 'XOR', 'SRL', 'SRA', 'OR', 'AND', 'MUL', 'MULH',
       'MULHSU', 'MULHU', 'DIV', 'DIVU', 'REM', 'REMU', 'ADDI', 'SLTI', 'SLTIU', 'XORI', 'ORI',
       'ANDI', 'SLLI', 'SRLI', 'SRAI', 'ADDIW', 'SLLIW', 'SRLIW', 'LUI', 'AUIPC', 'JAL', 'JALR',
       'BEQ', 'BNE', 'BLT', 'BGE', 'BLTU', 'BGEU', 'LB', 'LH', 'LW', 'LD', 'LBU', 'LHU', 'LWU',
       'SB', 'SH', 'SW', 'SD', 'FENCE', 'ECALL', 'EBREAK', 'ADDW', 'SUBW', 'SLLW', 'SRLW', 'SRAW',
       'MULW', 'DIVW', 'DIVUW', 'REMW', 'REMUW', 'SRAIW']
OPID = {n: i for i, n in enumerate(OPS)}


def run(code, mem, regs, oracle, fuel=CYCLE_LIMIT, pc=0x1000, trace=None):
    """Execute until HALT/failure/out-of-fuel. mem: bytearray(2^24) (mutated); regs: list of 32 ints."""
    prog = []
    for w in code:
        d = decode(w)
        if d is None:
            prog.append(None)
        else:
            prog.append((OPID[d[0]],) + tuple(d[1:]))
    n = len(prog)
    r = regs
    M = MASK
    MB = MEM_BYTES
    m8 = mem
    mv = memoryview(mem)
    m64 = mv.cast('Q')
    m32 = mv.cast('I')
    m16 = mv.cast('H')
    cycles = 0
    steps = 0
    fb = int.from_bytes

    def fail(c):
        return Result('failure', cycles + c, steps, oracle, mem, r, pc)

    while True:
        if steps >= fuel:
            return Result('unfinished', cycles, steps, oracle, mem, r, pc)
        if pc < 0x1000 or pc & 3:
            return fail(0)
        k = (pc - 0x1000) >> 2
        if k >= n or prog[k] is None:
            return fail(0)
        ins = prog[k]
        o = ins[0]
        steps += 1
        if trace is not None:
            trace.append(k)
        npc = pc + 4
        # --- most frequent first
        if o == 50:    # SD base, data, off
            a = (r[ins[1]] + ins[3]) & M
            if a & 7 or a + 8 > MB:
                return fail(1)
            m64[a >> 3] = r[ins[2]]
        elif o == 18:  # ADDI
            if ins[1]:
                r[ins[1]] = (r[ins[2]] + ins[3]) & M
        elif o == 43:  # LD
            a = (r[ins[2]] + ins[3]) & M
            if a & 7 or a + 8 > MB:
                return fail(1)
            if ins[1]:
                r[ins[1]] = m64[a >> 3]
        elif o == 52:  # ECALL
            t0 = r[5]
            if t0 == 0:
                src, ln, dst = r[10], r[11], r[12]
                if (src % 8 == 0 and ln > 0 and ln % 64 == 0 and src + ln <= MB and
                        dst % 8 == 0 and dst + 8 <= MB and dst + 32 <= MB):
                    ans = oracle(bytes(m8[src:src + ln]))
                    m8[dst:dst + 32] = ans
                    cycles += 8 * (ln // 64)
                    pc = npc
                    continue
            if t0 == 1:
                cycles += 1
                return Result('success' if r[10] == 0 else 'failure', cycles, steps, oracle, mem, r, pc)
            return fail(1)
        elif o == 49:  # SW
            a = (r[ins[1]] + ins[3]) & M
            if a & 3 or a + 4 > MB:
                return fail(1)
            m32[a >> 2] = r[ins[2]] & 0xffffffff
        elif o <= 39 and o >= 34:  # branches
            x, y = r[ins[1]], r[ins[2]]
            if o == 34:
                t = x == y
            elif o == 35:
                t = x != y
            elif o == 38:
                t = x < y
            elif o == 39:
                t = x >= y
            elif o == 36:
                t = _s64(x) < _s64(y)
            else:
                t = _s64(x) >= _s64(y)
            if t:
                npc = (pc + ins[3]) & M
        elif o == 24:  # SLLI
            if ins[1]:
                r[ins[1]] = (r[ins[2]] << ins[3]) & M
        elif o == 25:  # SRLI
            if ins[1]:
                r[ins[1]] = r[ins[2]] >> ins[3]
        elif o == 32:  # JAL
            if ins[1]:
                r[ins[1]] = npc & M
            npc = (pc + ins[2]) & M
        elif o == 0:
            if ins[1]:
                r[ins[1]] = (r[ins[2]] + r[ins[3]]) & M
        elif o == 23:  # ANDI
            if ins[1]:
                r[ins[1]] = r[ins[2]] & (ins[3] & M)
        elif o == 9:
            if ins[1]:
                r[ins[1]] = r[ins[2]] & r[ins[3]]
        elif o == 8:
            if ins[1]:
                r[ins[1]] = r[ins[2]] | r[ins[3]]
        elif o == 1:
            if ins[1]:
                r[ins[1]] = (r[ins[2]] - r[ins[3]]) & M
        elif o == 5:
            if ins[1]:
                r[ins[1]] = r[ins[2]] ^ r[ins[3]]
        elif o == 21:  # XORI
            if ins[1]:
                r[ins[1]] = r[ins[2]] ^ (ins[3] & M)
        elif o == 22:  # ORI
            if ins[1]:
                r[ins[1]] = r[ins[2]] | (ins[3] & M)
        elif o == 46 or o == 42 or o == 44 or o == 40 or o == 41 or o == 45:  # other loads
            width = {46: 4, 42: 4, 44: 1, 40: 1, 41: 2, 45: 2}[o]
            a = (r[ins[2]] + ins[3]) & M
            if a % width or a + width > MB:
                return fail(1)
            if width == 4:
                v = m32[a >> 2]
            elif width == 2:
                v = m16[a >> 1]
            else:
                v = m8[a]
            if o in (42, 40, 41):
                v = sext(v, 8 * width) & M
            if ins[1]:
                r[ins[1]] = v
        elif o == 47 or o == 48:  # SB, SH
            width = 1 if o == 47 else 2
            a = (r[ins[1]] + ins[3]) & M
            if a % width or a + width > MB:
                return fail(1)
            if width == 1:
                m8[a] = r[ins[2]] & 0xff
            else:
                m16[a >> 1] = r[ins[2]] & 0xffff
        elif o == 30:  # LUI
            if ins[1]:
                r[ins[1]] = sext(ins[2] << 12, 32) & M
        elif o == 31:  # AUIPC
            if ins[1]:
                r[ins[1]] = (pc + sext(ins[2] << 12, 32)) & M
        elif o == 33:  # JALR
            tgt = ((r[ins[2]] + ins[3]) & M) & ~1 & M
            if ins[1]:
                r[ins[1]] = npc & M
            npc = tgt
        elif o == 53:  # EBREAK
            return fail(1)
        elif o == 51:  # FENCE
            pass
        else:
            v = _alu_rare(OPS[o], ins, r, pc)
            if ins[1]:
                r[ins[1]] = v
            if OPS[o] in MULDIV:
                cycles += 3
        cycles += 1
        pc = npc


def _alu_rare(name, ins, r, pc):
    M = MASK
    rd, a = ins[1], r[ins[2]]
    if name in ('SLTI', 'SLTIU', 'SRAI', 'ADDIW', 'SLLIW', 'SRLIW', 'SRAIW'):
        imm = ins[3]
        if name == 'SLTI':
            return 1 if _s64(a) < imm else 0
        if name == 'SLTIU':
            return 1 if a < (imm & M) else 0
        if name == 'SRAI':
            return (_s64(a) >> imm) & M
        if name == 'ADDIW':
            return sext(a + imm, 32) & M
        if name == 'SLLIW':
            return sext((a & 0xffffffff) << imm, 32) & M
        if name == 'SRLIW':
            return sext((a & 0xffffffff) >> imm, 32) & M
        if name == 'SRAIW':
            return (sext(a, 32) >> imm) & M
    b = r[ins[3]]
    if name == 'SLL':
        return (a << (b % 64)) & M
    if name == 'SRL':
        return a >> (b % 64)
    if name == 'SRA':
        return (_s64(a) >> (b % 64)) & M
    if name == 'SLT':
        return 1 if _s64(a) < _s64(b) else 0
    if name == 'SLTU':
        return 1 if a < b else 0
    if name == 'MUL':
        return (a * b) & M
    if name == 'MULH':
        return ((_s64(a) * _s64(b)) >> 64) & M
    if name == 'MULHSU':
        return ((_s64(a) * b) >> 64) & M
    if name == 'MULHU':
        return ((a * b) >> 64) & M
    if name == 'DIV':
        return _div(a, b, 64)
    if name == 'DIVU':
        return M if b == 0 else a // b
    if name == 'REM':
        return _rem(a, b, 64)
    if name == 'REMU':
        return a if b == 0 else a % b
    a32, b32 = a & 0xffffffff, b & 0xffffffff
    if name == 'ADDW':
        v = a32 + b32
    elif name == 'SUBW':
        v = a32 - b32
    elif name == 'SLLW':
        v = a32 << (b32 % 32)
    elif name == 'SRLW':
        v = a32 >> (b32 % 32)
    elif name == 'SRAW':
        v = sext(a32, 32) >> (b32 % 32)
    elif name == 'MULW':
        v = a32 * b32
    elif name == 'DIVW':
        v = _div(a32, b32, 32)
    elif name == 'DIVUW':
        v = 0xffffffff if b32 == 0 else a32 // b32
    elif name == 'REMW':
        v = _rem(a32, b32, 32)
    elif name == 'REMUW':
        v = a32 if b32 == 0 else a32 % b32
    else:
        raise AssertionError(name)
    return sext(v, 32) & M


# ---------------------------------------------------------------- loader (Programs.lean)
def data_base(data_len):
    return 16 * ((MEM_BYTES - data_len) // 16)


def write_bytes_as_words(mem, base, data):
    """MachineState.writeBytesAsWords: 8-byte chunks, the last one zero-extended."""
    for off in range(0, len(data), 8):
        chunk = bytes(data[off:off + 8])
        chunk = chunk + bytes(8 - len(chunk))
        a = (base + off) & MASK
        a &= ~7   # setMem at the given (aligned) address; all our bases are 8-aligned
        mem[a:a + 8] = chunk


def layout_valid(layout, sizes, image):
    """layout = dict(message, secretKey, publicKey, cache, signature, witness); sizes=(S, W)."""
    S, W = sizes
    bufs = [(layout['message'], 32), (layout['secretKey'], 32), (layout['publicKey'], 16),
            (layout['cache'], CACHE_BYTES), (layout['signature'], S), (layout['witness'], W)]
    db = data_base(len(image[1]))
    for a, n in bufs:
        if a % 8 or a + n > db:
            return False
    for i in range(len(bufs)):
        for j in range(i + 1, len(bufs)):
            (a, n), (b, m) = bufs[i], bufs[j]
            if not (n == 0 or m == 0 or a + n <= b or b + m <= a):
                return False
    return True


def image_valid(image, sizes, layout):
    code, data = image
    return 4 * len(code) + len(data) < MAX_IMAGE_BYTES and layout_valid(layout, sizes, image)


def input_buffers(phase, layout, inp):
    if phase == 'keygen':
        return [(layout['secretKey'], inp['sk'])]
    if phase == 'sign':
        return [(layout['secretKey'], inp['sk']), (layout['cache'], inp['cache']),
                (layout['message'], inp['msg'])]
    if phase == 'expand':
        return [(layout['message'], inp['msg']), (layout['publicKey'], inp['pk']),
                (layout['signature'], inp['sig'])]
    if phase == 'verify':
        return [(layout['message'], inp['msg']), (layout['publicKey'], inp['pk']),
                (layout['witness'], inp['wit'])]
    raise ValueError(phase)


def run_phase(images, sizes, layout, phase, inp, oracle=None, fuel=CYCLE_LIMIT):
    """Submission.run: returns (value, Result). value is None unless exit == success."""
    image = images[phase]
    if oracle is None:
        oracle = Oracle()
    assert image_valid(image, sizes, layout)
    code, data = image
    mem = bytearray(MEM_BYTES)
    db = data_base(len(data))
    write_bytes_as_words(mem, db, data)
    for base, buf in input_buffers(phase, layout, inp):
        write_bytes_as_words(mem, base, buf)
    regs = [0] * 32
    regs[2] = db
    res = run(code, mem, regs, oracle, fuel=fuel)
    val = None
    if res.exit == 'success':
        S, W = sizes
        if phase == 'keygen':
            val = (res.read(layout['publicKey'], 16), res.read(layout['cache'], CACHE_BYTES))
        elif phase == 'sign':
            val = res.read(layout['signature'], S)
        elif phase == 'expand':
            val = res.read(layout['witness'], W)
        else:
            val = ()
    return val, res
