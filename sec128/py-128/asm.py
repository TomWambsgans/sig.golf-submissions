"""Minimal RV64IM assembler for the sig.golf VM.

Only real RV64I/M encodings are emitted (no pseudo-instructions): every word is
checked against vm.decode (the organizer's decoder, re-implemented) after label
resolution, and the decoded form must equal the intended instruction.
"""

MASK64 = (1 << 64) - 1

# register names
X0, RA, SP, GP, TP, T0, T1, T2, S0, S1, A0, A1, A2, A3, A4, A5, A6, A7 = range(18)
REGNAMES = ['x0', 'ra', 'sp', 'gp', 'tp', 't0', 't1', 't2', 's0', 's1', 'a0', 'a1', 'a2',
            'a3', 'a4', 'a5', 'a6', 'a7', 's2', 's3', 's4', 's5', 's6', 's7', 's8', 's9',
            's10', 's11', 't3', 't4', 't5', 't6']


def fits12(v):
    return -2048 <= v < 2048


class Asm:
    def __init__(self, name='prog'):
        self.name = name
        self.words = []      # encoded (or placeholder) words
        self.ins = []        # intended instruction tuples, e.g. ('ADDI', rd, rs1, imm)
        self.labels = {}     # name -> instruction index
        self.fix = []        # (index, kind, args, label)
        self.serial = 0
        self.comments = {}   # index -> comment (block markers)

    # ------------------------------------------------------------ basics
    def here(self):
        return len(self.words)

    def label(self, name):
        assert name not in self.labels, name
        self.labels[name] = len(self.words)

    def fresh(self, stem):
        self.serial += 1
        return '%s_%d' % (stem, self.serial)

    def note(self, text):
        self.comments.setdefault(len(self.words), []).append(text)

    def _emit(self, word, ins):
        self.words.append(word & 0xffffffff)
        self.ins.append(ins)

    # ------------------------------------------------------------ formats
    def _r(self, name, f7, f3, rd, rs1, rs2, op=0x33):
        self._emit((f7 << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op,
                   (name, rd, rs1, rs2))

    def _i(self, name, f3, rd, rs1, imm, op=0x13):
        assert fits12(imm), (name, imm)
        self._emit(((imm & 0xfff) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op,
                   (name, rd, rs1, imm))

    def _s(self, name, f3, rs2, rs1, imm):
        assert fits12(imm), (name, imm)
        u = imm & 0xfff
        self._emit(((u >> 5) << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | ((u & 31) << 7) | 0x23,
                   (name, rs1, rs2, imm))

    # ------------------------------------------------------------ R-type
    def add(self, rd, a, b): self._r('ADD', 0, 0, rd, a, b)
    def sub(self, rd, a, b): self._r('SUB', 0x20, 0, rd, a, b)
    def sll(self, rd, a, b): self._r('SLL', 0, 1, rd, a, b)
    def sltu(self, rd, a, b): self._r('SLTU', 0, 3, rd, a, b)
    def xor(self, rd, a, b): self._r('XOR', 0, 4, rd, a, b)
    def srl(self, rd, a, b): self._r('SRL', 0, 5, rd, a, b)
    def or_(self, rd, a, b): self._r('OR', 0, 6, rd, a, b)
    def and_(self, rd, a, b): self._r('AND', 0, 7, rd, a, b)

    # ------------------------------------------------------------ I-type ALU
    def addi(self, rd, rs, imm): self._i('ADDI', 0, rd, rs, imm)
    def xori(self, rd, rs, imm): self._i('XORI', 4, rd, rs, imm)
    def ori(self, rd, rs, imm): self._i('ORI', 6, rd, rs, imm)
    def andi(self, rd, rs, imm): self._i('ANDI', 7, rd, rs, imm)

    def nop(self):
        # ADDI x0, x0, 0 -- decodes to ADDI (never to the NOP constructor)
        self.addi(X0, X0, 0)

    def slli(self, rd, rs, sh):
        assert 0 <= sh < 64
        self._emit((sh << 20) | (rs << 15) | (1 << 12) | (rd << 7) | 0x13, ('SLLI', rd, rs, sh))

    def srli(self, rd, rs, sh):
        assert 0 <= sh < 64
        self._emit((sh << 20) | (rs << 15) | (5 << 12) | (rd << 7) | 0x13, ('SRLI', rd, rs, sh))

    # ------------------------------------------------------------ U-type
    def lui(self, rd, imm20):
        assert 0 <= imm20 < (1 << 20)
        self._emit((imm20 << 12) | (rd << 7) | 0x37, ('LUI', rd, imm20))

    # ------------------------------------------------------------ memory
    def ld(self, rd, rs, off=0): self._i('LD', 3, rd, rs, off, op=0x03)
    def lw(self, rd, rs, off=0): self._i('LW', 2, rd, rs, off, op=0x03)
    def lwu(self, rd, rs, off=0): self._i('LWU', 6, rd, rs, off, op=0x03)
    def lbu(self, rd, rs, off=0): self._i('LBU', 4, rd, rs, off, op=0x03)
    def sd(self, src, base, off=0): self._s('SD', 3, src, base, off)
    def sw(self, src, base, off=0): self._s('SW', 2, src, base, off)
    def sb(self, src, base, off=0): self._s('SB', 0, src, base, off)

    # ------------------------------------------------------------ control
    def _branch(self, name, f3, a, b, label):
        self.fix.append((len(self.words), 'B', (name, f3, a, b), label))
        self._emit(0, None)

    def beq(self, a, b, l): self._branch('BEQ', 0, a, b, l)
    def bne(self, a, b, l): self._branch('BNE', 1, a, b, l)
    def blt(self, a, b, l): self._branch('BLT', 4, a, b, l)
    def bge(self, a, b, l): self._branch('BGE', 5, a, b, l)
    def bltu(self, a, b, l): self._branch('BLTU', 6, a, b, l)
    def bgeu(self, a, b, l): self._branch('BGEU', 7, a, b, l)

    def jal(self, rd, label):
        self.fix.append((len(self.words), 'J', rd, label))
        self._emit(0, None)

    def j(self, label): self.jal(X0, label)

    def jalr(self, rd, rs, imm=0): self._i('JALR', 0, rd, rs, imm, op=0x67)

    def ecall(self): self._emit(0x00000073, ('ECALL',))

    # ------------------------------------------------------------ constants
    def li(self, rd, value):
        """Load an arbitrary 64-bit constant with LUI/ADDI/SLLI (checked by evaluation)."""
        value &= MASK64
        seq = _li_seq(value)
        for op in seq:
            if op[0] == 'ADDI':
                self.addi(rd, rd if op[1] else X0, op[2])
            elif op[0] == 'LUI':
                self.lui(rd, op[1])
            elif op[0] == 'SLLI':
                self.slli(rd, rd, op[1])
        assert _li_eval(seq) == value, (hex(value), seq)

    # ------------------------------------------------------------ finish
    def finish(self):
        from vm import decode, describe
        for pos, kind, args, label in self.fix:
            assert label in self.labels, (self.name, label)
            off = 4 * (self.labels[label] - pos)
            if kind == 'B':
                name, f3, a, b = args
                assert -4096 <= off < 4096, (self.name, 'branch out of range', label, off)
                u = off & 0x1fff
                w = ((((u >> 12) & 1) << 31) | (((u >> 5) & 63) << 25) | (b << 20) | (a << 15) |
                     (f3 << 12) | (((u >> 1) & 15) << 8) | (((u >> 11) & 1) << 7) | 0x63)
                self.words[pos] = w
                self.ins[pos] = (name, a, b, off)
            else:
                rd = args
                assert -(1 << 20) <= off < (1 << 20)
                u = off & 0x1fffff
                w = ((((u >> 20) & 1) << 31) | (((u >> 1) & 1023) << 21) | (((u >> 11) & 1) << 20) |
                     (((u >> 12) & 255) << 12) | (rd << 7) | 0x6f)
                self.words[pos] = w
                self.ins[pos] = ('JAL', rd, off)
        # every word must decode to exactly the intended instruction
        for k, (w, ins) in enumerate(zip(self.words, self.ins)):
            d = decode(w)
            assert d is not None, (self.name, k, hex(w))
            assert describe(d) == ins, (self.name, k, hex(w), describe(d), ins)
        return list(self.words)

    def listing(self):
        from vm import decode, describe
        out = []
        inv = {}
        for n, k in self.labels.items():
            inv.setdefault(k, []).append(n)
        for k, w in enumerate(self.words):
            for c in self.comments.get(k, []):
                out.append('        ; ' + c)
            for n in inv.get(k, []):
                out.append('%s:' % n)
            out.append('  %5d %08x  %s' % (k, w, fmt(describe(decode(w)))))
        return '\n'.join(out)


def fmt(ins):
    name = ins[0]
    if name == 'ECALL':
        return 'ecall'
    if name in ('SD', 'SW', 'SB'):
        return '%s %s, %d(%s)' % (name.lower(), REGNAMES[ins[2]], ins[3], REGNAMES[ins[1]])
    if name in ('LD', 'LW', 'LWU', 'LBU'):
        return '%s %s, %d(%s)' % (name.lower(), REGNAMES[ins[1]], ins[3], REGNAMES[ins[2]])
    if name == 'LUI':
        return 'lui %s, 0x%x' % (REGNAMES[ins[1]], ins[2])
    if name == 'JAL':
        return 'jal %s, %+d' % (REGNAMES[ins[1]], ins[2])
    if name in ('BEQ', 'BNE', 'BLT', 'BGE', 'BLTU', 'BGEU'):
        return '%s %s, %s, %+d' % (name.lower(), REGNAMES[ins[1]], REGNAMES[ins[2]], ins[3])
    parts = []
    for i, x in enumerate(ins[1:]):
        if name in ('ADDI', 'XORI', 'ORI', 'ANDI', 'SLLI', 'SRLI', 'JALR') and i == 2:
            parts.append(str(x))
        else:
            parts.append(REGNAMES[x])
    return name.lower() + ' ' + ', '.join(parts)


def _sext(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


def _li_eval(seq):
    r = 0
    for op in seq:
        if op[0] == 'ADDI':
            r = ((r if op[1] else 0) + op[2]) & MASK64
        elif op[0] == 'LUI':
            r = _sext(op[1] << 12, 32) & MASK64
        elif op[0] == 'SLLI':
            r = (r << op[1]) & MASK64
    return r


def _li_seq(value):
    v = _sext(value, 64)
    if fits12(v):
        return [('ADDI', False, v)]
    if -(1 << 31) <= v < (1 << 31):
        lo = _sext(v, 12)
        hi = ((v - lo) >> 12) & 0xfffff
        seq = [('LUI', hi)]
        if lo:
            seq.append(('ADDI', True, lo))
        if _li_eval(seq) == value:
            return seq
    # strip trailing zeros
    tz = (value & -value).bit_length() - 1
    if tz > 0:
        seq = _li_seq(value >> tz)
        return seq + [('SLLI', tz)]
    lo = _sext(v, 12)
    rest = ((v - lo) >> 12) & MASK64
    seq = _li_seq(rest) + [('SLLI', 12)]
    if lo:
        seq.append(('ADDI', True, lo))
    return seq
