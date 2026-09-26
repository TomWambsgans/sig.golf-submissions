"""Generators for the four SPHINCS-golf RV64IM images (keygen, sign, expand, verify).

See PROGRAMS.md for the register conventions, buffers and block structure.
WITNESS_MODE: 'perm' (default; witness = signature with the 7 layer counters moved to the end so
every 16-byte item is 8-aligned) or 'copy' (witness = signature byte copy).
"""
import ref
from asm import Asm, X0

S_BYTES = ref.SIG_BYTES          # 7756
W_BYTES = ref.SIG_BYTES          # 7756

# ------------------------------------------------------------------ memory layout
DB = 0x000        # digest input: tw_msg | P | rho | 0^16 | m | 0^32   (128 bytes)
MSG = 0x040       # message buffer (inside DB)
SK = 0x080
PK = 0x0A0
CB = 0x0C0        # chain / FORS-leaf input: tw | P | value | 0^16
EB = 0x100        # encoding input: tw | P | M | LE32(c) | 0^12
EO = 0x140        # encoding output (32)
DO = 0x160        # digest output (32)
FO = 0x180        # final root (32)
NB = 0x1C0        # node input: tw | P | L | R  (+16 junk bytes at 0x200)
RB2 = 0x220       # FORS roots input: tw | P | 14 roots (256, +16 junk)
LB = 0x340        # OTS leaf input: tw | P | 42 endpoints (704, +16 junk) -> 0x610
RB = 0x620        # sign: randomizer input tw | P | S | m | 0^32 (128)
PB = 0x6A0        # sign/keygen: prf input tw | P | S (64)
DIG = 0x6E0       # sign: 42 digit bytes
US = 0x710        # sign: 14 u_kappa dwords (112) -> 0x780
WIT = 0x800
SIG = 0x2650
CACHE = 0x44A0
FA = 0x30000      # sign: FORS node array, 1025 x 16
TA = 0x34100      # sign/keygen: tree node array, 33 x 16
DIG8 = 0x780      # sign: digits x_0..x_41 of the current layer (one dword each, 336 bytes)
STG = 0x900       # sign: layer staging (8-aligned), layer lay at STG + 760 lay:
                  #   counter dword | 42 chain values | h path nodes; packed into SIG at the end
STG_LAYER = 760

LAYOUT = dict(message=MSG, secretKey=SK, publicKey=PK, cache=CACHE, signature=SIG, witness=WIT)
SIZES = (S_BYTES, W_BYTES)
assert NB % 32 == 0 and ((NB + 32) & 16) == 0
assert LB + 32 + 16 * 42 + 16 <= RB and RB2 + 256 + 16 <= LB and WIT + W_BYTES <= SIG
assert SIG + S_BYTES <= CACHE and CACHE + (1 << 17) <= FA and FA + 1025 * 16 <= TA

LIMIT = 1 << 20
M1 = sum(7 << (6 * k) for k in range(11)) & ((1 << 64) - 1)
M2 = sum(63 << (12 * k) for k in range(6)) & ((1 << 64) - 1)

RT0 = 5
A0, A1, A2 = 10, 11, 12


def halt(a, code):
    a.addi(RT0, X0, 1)
    a.addi(A0, X0, code)
    a.ecall()


def enc_check(a, d0, d1, ra, rb, t, m1, m2, fail):
    """Branch to `fail` unless bits 63/127 are clear and the 42 digits sum to TARGET."""
    a.or_(t, d0, d1)
    a.blt(t, X0, fail)
    a.srli(ra, d0, 3)
    a.and_(ra, ra, m1)
    a.and_(rb, d0, m1)
    a.add(ra, ra, rb)
    a.srli(rb, d1, 3)
    a.and_(rb, rb, m1)
    a.add(ra, ra, rb)
    a.and_(rb, d1, m1)
    a.add(ra, ra, rb)
    a.srli(rb, ra, 6)
    a.add(ra, ra, rb)
    a.and_(ra, ra, m2)
    for sh in (12, 24, 48):
        a.srli(rb, ra, sh)
        a.add(ra, ra, rb)
    a.andi(ra, ra, 0x7ff)
    a.addi(ra, ra, -ref.TARGET)
    a.bne(ra, X0, fail)


def u_extract(a, k, dst, w, tmp):
    """dst = u_k = bits 34+10k .. 34+10k+9 of N; w = (w0, w1, w2) registers."""
    start = 34 + 10 * k
    wi, bit = divmod(start, 64)
    if bit + 10 <= 64:
        if bit == 0:
            a.andi(dst, w[wi], 1023)
        elif bit + 10 == 64:
            a.srli(dst, w[wi], bit)
        else:
            a.srli(dst, w[wi], bit)
            a.andi(dst, dst, 1023)
    else:
        lo = 64 - bit
        a.srli(tmp, w[wi], bit)
        a.andi(dst, w[wi + 1], (1 << (10 - lo)) - 1)
        a.slli(dst, dst, lo)
        a.or_(dst, dst, tmp)


# ================================================================== verify
class VerifyGen:
    V0, V1, T, TP = 1, 2, 3, 4
    TH = {1: 6, 2: 7, 3: 8, 4: 9, 5: 13, 6: 14, 7: 15}
    D0, D1 = 16, 17
    WB = [18, 19, 20, 21]
    IDX, U, U16, X25, M1r, M2r, X28, FW, TAU, X31 = 22, 23, 24, 25, 26, 27, 28, 29, 30, 31

    def __init__(self, mode='perm', pad=True):
        self.mode = mode
        self.pad = pad
        self.a = Asm('verify')

    # witness offsets
    def off_rho(self): return 0
    def off_fs(self, k): return 16 + 176 * k
    def off_fp(self, k, l): return 32 + 176 * k + 16 * l

    def off_chain(self, lay, i):
        if self.mode == 'perm':
            return ref.wit_layer_offset(lay) + 16 * i
        return ref.sig_layer_offset(lay) + 4 + 16 * i

    def off_path(self, lay, l):
        if self.mode == 'perm':
            return ref.wit_layer_offset(lay) + 672 + 16 * l
        return ref.sig_layer_offset(lay) + 676 + 16 * l

    def off_ctr(self, lay):
        if self.mode == 'perm':
            return ref.WIT_COUNTERS + 4 * lay
        return ref.sig_layer_offset(lay)

    def wb(self, off):
        k = off // 2048
        return self.WB[k], off - 2048 * k

    def load16(self, off):
        """Load witness bytes [off, off+16) into registers; returns the store plan."""
        a = self.a
        base, imm = self.wb(off)
        base2, imm2 = self.wb(off + 8)
        if (WIT + off) % 8 == 0:
            a.ld(self.V0, base, imm)
            a.ld(self.V1, base2, imm2)
            return 'd'
        regs = [self.V0, self.V1, self.X25, self.X28]
        for q in range(4):
            b, i = self.wb(off + 4 * q)
            a.lw(regs[q], b, i)
        return 'w'

    def store16(self, plan, base, imm):
        a = self.a
        if plan == 'd':
            a.sd(self.V0, base, imm)
            a.sd(self.V1, base, imm + 8)
        else:
            for q, r in enumerate([self.V0, self.V1, self.X25, self.X28]):
                a.sw(r, base, imm + 4 * q)

    def plan_len(self, off):
        return (2, 2) if (WIT + off) % 8 == 0 else (4, 4)

    # ---------------------------------------------------------- Merkle fold (a0 = NB, a1 = 64)
    def fold_levels(self, h, E, E16, off_fn, last_dst):
        """V is at NB+32+16*bit0(E) and a2 points at it. NB word0 low / tree word already set."""
        a, T, TP = self.a, self.T, self.TP
        for lam in range(h):
            a.note('fold level %d' % (lam + 1))
            a.xori(T, A2, 16)                   # sibling slot
            plan = self.load16(off_fn(lam))
            self.store16(plan, T, 0)
            a.addi(TP, X0, lam + 1)
            a.sw(TP, X0, NB + 4)                # p = level
            if lam < h - 1:
                a.srli(TP, E, lam + 1)
                a.sw(TP, X0, NB + 12)           # j = E >> (level)
                b = lam + 1
                if b == 4:
                    a.andi(T, E, 16)
                else:
                    a.srli(T, E16, b)
                    a.andi(T, T, 16)
                a.addi(A2, T, NB + 32)
            else:
                a.sw(X0, X0, NB + 12)
                a.addi(A2, X0, last_dst)
            a.ecall()

    # ---------------------------------------------------------- one chain
    def chain(self, lay, i, side):
        a, T, TP, TH = self.a, self.T, self.TP, self.TH
        q, r = divmod(i, 21)
        Dq = self.D0 if q == 0 else self.D1
        S = [None] + [a.fresh('c%d_%d_s%d' % (lay, i, mu)) for mu in range(1, 8)]
        NEXT = a.fresh('c%d_%d_next' % (lay, i))
        H7 = a.fresh('c%d_%d_h7' % (lay, i))
        G4 = a.fresh('c%d_%d_g4' % (lay, i))
        ld, st = self.plan_len(self.off_chain(lay, i))
        pre = 1 + ld + st
        h7len = st + 1
        D = {0: 5, 1: 5, 2: 4, 3: 3, 4: 5, 5: 4, 6: 3}
        # cycles(x) = pre + D[x] + pad[x] + 12 (7 - x)   (each step: 4 instructions + 8 for ECALL)
        # cycles(7) = pre + 1 + h7len + pad7
        target = max(pre + 5, pre + 1 + h7len)
        if self.pad:
            pad = {x: target - (pre + D[x]) for x in D}
            pad7 = target - (pre + 1 + h7len)
        else:
            pad = {x: 0 for x in D}
            pad7 = 0
        tgt = {}
        side_blocks = []
        for x in (1, 2, 3, 5, 6):
            if pad[x] == 0:
                tgt[x] = S[x + 1]
            else:
                lab = a.fresh('c%d_%d_p%d' % (lay, i, x))
                tgt[x] = lab
                side_blocks.append((lab, pad[x] - 1, S[x + 1]))
        a.note('chain lay=%d i=%d' % (lay, i))
        a.label(a.fresh('c%d_%d' % (lay, i)))
        a.slli(T, Dq, 61 - 3 * r)                       # digit in bits 61..63
        plan = self.load16(self.off_chain(lay, i))
        self.store16(plan, X0, CB + 32)
        a.bgeu(T, TH[7], H7)
        a.bgeu(T, TH[4], G4)
        a.bgeu(T, TH[3], tgt[3])
        a.bgeu(T, TH[2], tgt[2])
        a.bgeu(T, TH[1], tgt[1])
        for _ in range(pad[0]):
            a.nop()
        for mu in range(1, 8):
            a.label(S[mu])
            a.addi(TP, X0, 8 * i + mu - 1)
            a.sw(TP, A0, 4)
            if mu < 7:
                a.ecall()
                a.sd(X0, A0, 48)
                a.sd(X0, A0, 56)
            else:
                a.addi(A2, X0, LB + 32 + 16 * i)
                a.ecall()
                a.addi(A2, A0, 32)
        a.label(NEXT)

        def emit_side():
            a.label(G4)
            a.bgeu(T, TH[6], tgt[6])
            a.bgeu(T, TH[5], tgt[5])
            for _ in range(pad[4]):
                a.nop()
            a.j(S[5])
            for lab, nops, dst in side_blocks:
                a.label(lab)
                for _ in range(nops):
                    a.nop()
                a.j(dst)
            a.label(H7)
            self.store16(plan, X0, LB + 32 + 16 * i)
            for _ in range(pad7):
                a.nop()
            a.j(NEXT)
        side.append(emit_side)
        return target

    # ---------------------------------------------------------- one hypertree layer
    def layer(self, lay):
        a, T, TP = self.a, self.T, self.TP
        U, U16, TAU, X31, IDX = self.U, self.U16, self.TAU, self.X31, self.IDX
        s = ref.shift_below(lay)
        h = ref.HEIGHTS[lay]
        REJ = a.fresh('rej_l%d' % lay)
        a.note('layer %d: route' % lay)
        a.label('layer_%d' % lay)
        if s:
            a.srli(U, IDX, s)
            a.andi(U, U, (1 << h) - 1)
        else:
            a.andi(U, IDX, (1 << h) - 1)
        a.srli(TAU, IDX, s + h)
        a.slli(T, U, 32)
        a.or_(X31, TAU, T)                               # tau | e << 32
        a.note('layer %d: encoding' % lay)
        a.li(T, 0x401 | (lay << 16))
        a.sd(T, X0, EB)
        a.sd(X31, X0, EB + 8)
        b, i = self.wb(self.off_ctr(lay))
        a.lwu(T, b, i)
        a.sw(T, X0, EB + 48)
        a.sw(X0, X0, EB + 52)
        a.sd(X0, X0, EB + 56)
        a.addi(A0, X0, EB)
        a.addi(A1, X0, 64)
        a.addi(A2, X0, EO)
        a.ecall()
        a.ld(self.D0, X0, EO)
        a.ld(self.D1, X0, EO + 8)
        enc_check(a, self.D0, self.D1, self.X25, self.X28, T, self.M1r, self.M2r, REJ)
        a.note('layer %d: chains' % lay)
        a.li(T, 0x101 | (lay << 16))
        a.sw(T, X0, CB)
        a.sd(X31, X0, CB + 8)
        a.addi(A0, X0, CB)
        a.addi(A2, X0, CB + 32)
        overheads = set()
        for g in range(3):
            side = []
            for i in range(14 * g, 14 * g + 14):
                overheads.add(self.chain(lay, i, side))
            after = a.fresh('l%d_after%d' % (lay, g))
            a.j(after)
            if g == 0:
                a.label(REJ)
                a.j('reject')
            for f in side:
                f()
            a.label(after)
        self.chain_overheads.update(overheads)
        a.note('layer %d: leaf' % lay)
        a.li(T, 0x201 | (lay << 16))
        a.sd(T, X0, LB)
        a.sd(X31, X0, LB + 8)
        a.addi(A0, X0, LB)
        a.addi(A1, X0, 704)
        a.slli(U16, U, 4)
        a.andi(T, U16, 16)
        a.addi(A2, T, NB + 32)
        a.ecall()
        a.note('layer %d: tree fold' % lay)
        a.li(T, 0x301 | (lay << 16))
        a.sw(T, X0, NB)
        a.sw(TAU, X0, NB + 8)
        a.addi(A0, X0, NB)
        a.addi(A1, X0, 64)
        self.fold_levels(h, U, U16, lambda l: self.off_path(lay, l), EB + 32 if lay > 0 else FO)

    # ---------------------------------------------------------- program
    def build(self):
        a, T, TP = self.a, self.T, self.TP
        self.chain_overheads = set()
        V0, V1, IDX, U, U16, FW, X25, X28, X31 = (self.V0, self.V1, self.IDX, self.U, self.U16,
                                                   self.FW, self.X25, self.X28, self.X31)
        a.note('prologue: constants')
        a.label('start')
        for k, r in enumerate(self.WB):
            a.li(r, WIT + 2048 * k)
        for k, r in self.TH.items():
            a.addi(r, X0, k)
            a.slli(r, r, 61)
        a.li(self.M1r, M1)
        a.li(self.M2r, M2)
        a.note('counter range check: every c_lay < 2^20')
        a.label('counters')
        if self.mode == 'perm':
            base, imm = self.wb(ref.WIT_COUNTERS)
            a.ld(T, base, imm)
            a.ld(TP, base, imm + 8)
            a.or_(T, T, TP)
            a.ld(TP, base, imm + 16)
            a.or_(T, T, TP)
            a.lwu(TP, base, imm + 24)
            a.or_(T, T, TP)
            a.li(TP, 0x000FFFFF000FFFFF)
        else:
            a.addi(T, X0, 0)
            for lay in range(7):
                b, i = self.wb(self.off_ctr(lay))
                a.lwu(TP, b, i)
                a.or_(T, T, TP)
            a.li(TP, 0xFFFFF)
        a.or_(T, T, TP)
        a.bne(T, TP, 'reject')
        a.note('message digest')
        a.label('digest')
        a.li(T, 0x0C01)
        a.sd(T, X0, DB)
        plan = self.load16(self.off_rho())
        self.store16(plan, X0, DB + 32)
        a.addi(A0, X0, DB)
        a.addi(A1, X0, 128)
        a.addi(A2, X0, DO)
        a.ecall()
        a.ld(X25, X0, DO + 16)
        a.slli(T, X25, 8)
        a.srli(T, T, 54)
        a.beq(T, X0, 'admissible')
        a.label('reject')
        halt(a, 1)
        a.label('admissible')
        a.ld(self.D0, X0, DO)
        a.ld(self.D1, X0, DO + 8)
        a.slli(IDX, self.D0, 30)
        a.srli(IDX, IDX, 30)
        a.note('FORS setup')
        a.sw(IDX, X0, CB + 8)
        a.sw(IDX, X0, NB + 8)
        a.sw(IDX, X0, RB2 + 8)
        a.srli(T, IDX, 32)
        a.slli(T, T, 24)
        a.li(X28, 0x901)
        a.or_(FW, T, X28)                    # [1, 9, kappa=0, idx>>32]
        a.li(X31, 1 << 16)
        a.addi(A1, X0, 64)
        w = (self.D0, self.D1, X25)
        for k in range(14):
            a.note('FORS tree %d' % k)
            a.label('fors_%d' % k)
            u_extract(a, k, U, w, T)
            a.sw(FW, X0, CB)
            a.sw(U, X0, CB + 12)
            plan = self.load16(self.off_fs(k))
            self.store16(plan, X0, CB + 32)
            a.slli(U16, U, 4)
            a.andi(T, U16, 16)
            a.addi(A2, T, NB + 32)
            a.addi(A0, X0, CB)
            a.ecall()
            a.addi(A0, X0, NB)
            a.addi(T, FW, 0x100)
            a.sw(T, X0, NB)
            self.fold_levels(10, U, U16, lambda l, k=k: self.off_fp(k, l), RB2 + 32 + 16 * k)
            a.add(FW, FW, X31)
        a.note('FORS roots')
        a.label('fors_roots')
        a.srli(T, IDX, 32)
        a.slli(T, T, 24)
        a.li(X28, 0xB01)
        a.or_(T, T, X28)
        a.sw(T, X0, RB2)
        a.addi(A0, X0, RB2)
        a.addi(A1, X0, 256)
        a.addi(A2, X0, EB + 32)
        a.ecall()
        for lay in range(6, -1, -1):
            self.layer(lay)
        a.note('final comparison with the public key')
        a.label('compare')
        a.ld(V0, X0, FO)
        a.ld(V1, X0, PK)
        a.bne(V0, V1, 'reject_final')
        a.ld(V0, X0, FO + 8)
        a.ld(V1, X0, PK + 8)
        a.bne(V0, V1, 'reject_final')
        a.label('accept')
        halt(a, 0)
        a.label('reject_final')
        halt(a, 1)
        return a


# ================================================================== sign / keygen shared
class SignRegs:
    V0, V1, T, TP = 1, 2, 3, 4
    CNT, LIM, KAP, J = 6, 7, 8, 9          # KAP doubles as LAY, J as HH in the layer phase
    U, FW, LAM, JJ, NCNT, SIGL, FAP, EP, I, IDX, MU, P, X, M1r, M2r, TA_, TB_, TAU, W1 = range(13, 32)


R = SignRegs


def tree_build(a, capture):
    """Build tree (LAY=R.KAP, TAU, height R.J) into TA; capture leaf R.U into sig at R.SIGL."""
    T, TP, V0, V1 = R.T, R.TP, R.V0, R.V1
    LAY, HH = R.KAP, R.J
    a.note('tree build: tweak words')
    a.li(R.FAP, TA)
    a.slli(T, LAY, 16)
    a.ori(R.TB_, T, 0x001)
    a.sw(R.TB_, X0, PB)
    a.ori(R.TB_, T, 0x101)
    a.sw(R.TB_, X0, CB)
    a.ori(R.TB_, T, 0x201)
    a.sd(R.TB_, X0, LB)
    a.addi(T, X0, 1)
    a.sll(R.NCNT, T, HH)
    a.addi(R.EP, X0, 0)
    a.label('tb_leaf_loop')
    a.slli(T, R.EP, 32)
    a.or_(T, T, R.TAU)
    a.sd(T, X0, PB + 8)
    a.sd(T, X0, CB + 8)
    a.sd(T, X0, LB + 8)
    a.addi(R.I, X0, 0)
    a.addi(R.P, X0, 0)
    a.label('tb_chain_loop')
    a.sw(R.I, X0, PB + 4)
    a.addi(A0, X0, PB)
    a.addi(A1, X0, 64)
    a.addi(A2, X0, CB + 32)
    a.ecall()
    a.sd(X0, X0, CB + 48)
    a.sd(X0, X0, CB + 56)
    a.addi(R.MU, X0, 0)
    if capture:
        a.slli(T, R.I, 3)
        a.ld(R.X, T, DIG8)
        cap_check(a, 'tb_cap0')
    a.label('tb_step_loop')
    a.addi(R.MU, R.MU, 1)
    a.sw(R.P, X0, CB + 4)
    a.addi(A0, X0, CB)
    a.addi(A2, X0, CB + 32)
    a.ecall()
    a.sd(X0, X0, CB + 48)
    a.sd(X0, X0, CB + 56)
    a.addi(R.P, R.P, 1)
    if capture:
        cap_check(a, 'tb_cap1')
    a.addi(T, X0, 7)
    a.bne(R.MU, T, 'tb_step_loop')
    a.addi(R.P, R.P, 1)
    a.slli(T, R.I, 4)
    a.ld(V0, X0, CB + 32)
    a.ld(V1, X0, CB + 40)
    a.sd(V0, T, LB + 32)
    a.sd(V1, T, LB + 40)
    a.addi(R.I, R.I, 1)
    a.addi(T, X0, 42)
    a.bne(R.I, T, 'tb_chain_loop')
    a.addi(A0, X0, LB)
    a.addi(A1, X0, 704)
    a.slli(T, R.EP, 4)
    a.add(A2, R.FAP, T)
    a.ecall()
    a.addi(R.EP, R.EP, 1)
    a.bne(R.EP, R.NCNT, 'tb_leaf_loop')
    a.note('tree build: levels')
    a.addi(R.LAM, X0, 1)
    a.label('tb_level_loop')
    if capture:
        a.addi(T, R.LAM, -1)
        a.srl(T, R.U, T)
        a.xori(T, T, 1)
        a.slli(T, T, 4)
        a.add(T, T, R.FAP)
        a.ld(V0, T, 0)
        a.ld(V1, T, 8)
        a.slli(R.TB_, R.LAM, 4)
        a.add(R.TB_, R.TB_, R.SIGL)
        a.sd(V0, R.TB_, 664)                   # stage SIGL + 680 + 16 (LAM - 1)
        a.sd(V1, R.TB_, 672)
    a.slli(T, R.LAM, 32)
    a.slli(R.TB_, LAY, 16)
    a.or_(T, T, R.TB_)
    a.ori(T, T, 0x301)
    a.sd(T, X0, NB)
    a.sw(R.TAU, X0, NB + 8)
    a.srli(R.NCNT, R.NCNT, 1)
    a.addi(R.JJ, X0, 0)
    a.label('tb_node_loop')
    node_hash(a)
    a.addi(R.JJ, R.JJ, 1)
    a.bne(R.JJ, R.NCNT, 'tb_node_loop')
    a.addi(R.LAM, R.LAM, 1)
    a.bge(HH, R.LAM, 'tb_level_loop')


def node_hash(a):
    """NB <- array[2JJ], array[2JJ+1]; H(NB) -> array[JJ] (array base R.FAP)."""
    T, V0 = R.T, R.V0
    a.sw(R.JJ, X0, NB + 12)
    a.slli(T, R.JJ, 5)
    a.add(T, T, R.FAP)
    for q in range(4):
        a.ld(V0, T, 8 * q)
        a.sd(V0, X0, NB + 32 + 8 * q)
    a.addi(A0, X0, NB)
    a.addi(A1, X0, 64)
    a.slli(T, R.JJ, 4)
    a.add(A2, R.FAP, T)
    a.ecall()


def cap_check(a, stem):
    skip = a.fresh(stem)
    T, V0 = R.T, R.V0
    a.bne(R.EP, R.U, skip)
    a.bne(R.MU, R.X, skip)
    V1 = R.V1
    a.slli(T, R.I, 4)
    a.add(T, T, R.SIGL)
    a.ld(V0, X0, CB + 32)
    a.ld(V1, X0, CB + 40)
    a.sd(V0, T, 8)                             # stage SIGL + 8 + 16 I
    a.sd(V1, T, 16)
    a.label(skip)


def gen_keygen():
    a = Asm('keygen')
    a.label('start')
    a.note('copy S into the prf buffer')
    for q in range(4):
        a.ld(R.V0, X0, SK + 8 * q)
        a.sd(R.V0, X0, PB + 32 + 8 * q)
    a.addi(R.KAP, X0, 0)       # lay 0
    a.addi(R.TAU, X0, 0)
    a.addi(R.J, X0, ref.HEIGHTS[0])
    tree_build(a, capture=False)
    a.note('root -> public key')
    a.li(R.FAP, TA)
    a.ld(R.V0, R.FAP, 0)
    a.ld(R.V1, R.FAP, 8)
    a.sd(R.V0, X0, PK)
    a.sd(R.V1, X0, PK + 8)
    halt(a, 0)
    return a


def gen_sign():
    a = Asm('sign')
    T, TP, V0, V1 = R.T, R.TP, R.V0, R.V1
    a.label('start')
    a.note('setup: S, m into buffers; constants')
    for q in range(4):
        a.ld(V0, X0, SK + 8 * q)
        a.sd(V0, X0, PB + 32 + 8 * q)
        a.sd(V0, X0, RB + 32 + 8 * q)
        a.ld(V0, X0, MSG + 8 * q)
        a.sd(V0, X0, RB + 64 + 8 * q)
    a.li(T, 0x0701)
    a.sw(T, X0, RB)
    a.li(T, 0x0C01)
    a.sd(T, X0, DB)
    a.li(R.LIM, LIMIT)
    a.note('digest loop')
    a.addi(R.CNT, X0, 0)
    a.label('dig_loop')
    a.sw(R.CNT, X0, RB + 4)
    a.addi(A0, X0, RB)
    a.addi(A1, X0, 128)
    a.addi(A2, X0, DB + 32)
    a.ecall()
    a.sd(X0, X0, DB + 48)
    a.sd(X0, X0, DB + 56)
    a.addi(A0, X0, DB)
    a.addi(A2, X0, DO)
    a.ecall()
    a.ld(T, X0, DO + 16)
    a.slli(T, T, 8)
    a.srli(T, T, 54)
    a.beq(T, X0, 'dig_ok')
    a.addi(R.CNT, R.CNT, 1)
    a.bne(R.CNT, R.LIM, 'dig_loop')
    a.label('fail_digest')
    halt(a, 1)
    a.label('dig_ok')
    a.li(R.SIGL, SIG)
    a.ld(V0, X0, DB + 32)
    a.ld(V1, X0, DB + 40)
    a.sd(V0, R.SIGL, 0)
    a.sd(V1, R.SIGL, 8)
    a.ld(V0, X0, DO)
    a.ld(V1, X0, DO + 8)
    a.ld(R.TA_, X0, DO + 16)
    a.slli(R.IDX, V0, 30)
    a.srli(R.IDX, R.IDX, 30)
    for k in range(14):
        u_extract(a, k, T, (V0, V1, R.TA_), TP)
        a.sd(T, X0, US + 8 * k)
    a.note('FORS')
    a.sw(R.IDX, X0, PB + 8)
    a.sw(R.IDX, X0, CB + 8)
    a.sw(R.IDX, X0, NB + 8)
    a.sw(R.IDX, X0, RB2 + 8)
    a.sw(X0, X0, PB + 4)
    a.sw(X0, X0, CB + 4)
    a.srli(T, R.IDX, 32)
    a.slli(T, T, 24)
    a.li(R.TB_, 0x801)
    a.or_(R.FW, T, R.TB_)
    a.li(R.FAP, FA)
    a.addi(R.KAP, X0, 0)
    a.label('fors_loop')
    a.slli(T, R.KAP, 3)
    a.ld(R.U, T, US)
    a.slli(T, R.KAP, 16)
    a.or_(R.TB_, R.FW, T)
    a.sw(R.TB_, X0, PB)
    a.addi(R.TB_, R.TB_, 0x100)
    a.sw(R.TB_, X0, CB)
    a.addi(R.J, X0, 0)
    a.label('fors_leaf_loop')
    a.sw(R.J, X0, PB + 12)
    a.addi(A0, X0, PB)
    a.addi(A1, X0, 64)
    a.addi(A2, X0, CB + 32)
    a.ecall()
    a.sd(X0, X0, CB + 48)
    a.sd(X0, X0, CB + 56)
    a.bne(R.J, R.U, 'fors_nocap')
    a.ld(V0, X0, CB + 32)
    a.ld(V1, X0, CB + 40)
    a.sd(V0, R.SIGL, 16)
    a.sd(V1, R.SIGL, 24)
    a.label('fors_nocap')
    a.sw(R.J, X0, CB + 12)
    a.addi(A0, X0, CB)
    a.slli(T, R.J, 4)
    a.add(A2, R.FAP, T)
    a.ecall()
    a.addi(R.J, R.J, 1)
    a.addi(T, X0, 1024)
    a.bne(R.J, T, 'fors_leaf_loop')
    a.addi(R.LAM, X0, 1)
    a.addi(R.NCNT, X0, 1024)
    a.label('fors_level_loop')
    a.addi(T, R.LAM, -1)
    a.srl(T, R.U, T)
    a.xori(T, T, 1)
    a.slli(T, T, 4)
    a.add(T, T, R.FAP)
    a.ld(V0, T, 0)
    a.ld(V1, T, 8)
    a.slli(R.TB_, R.LAM, 4)
    a.add(R.TB_, R.TB_, R.SIGL)
    a.sd(V0, R.TB_, 16)                   # SIGL + 32 + 16 (LAM - 1)
    a.sd(V1, R.TB_, 24)
    a.slli(T, R.KAP, 16)
    a.or_(T, T, R.FW)
    a.addi(T, T, 0x200)
    a.slli(R.TB_, R.LAM, 32)
    a.or_(T, T, R.TB_)
    a.sd(T, X0, NB)
    a.srli(R.NCNT, R.NCNT, 1)
    a.addi(R.JJ, X0, 0)
    a.label('fors_node_loop')
    node_hash(a)
    a.addi(R.JJ, R.JJ, 1)
    a.bne(R.JJ, R.NCNT, 'fors_node_loop')
    a.addi(R.LAM, R.LAM, 1)
    a.addi(T, X0, 10)
    a.bge(T, R.LAM, 'fors_level_loop')
    a.ld(V0, R.FAP, 0)
    a.ld(V1, R.FAP, 8)
    a.slli(T, R.KAP, 4)
    a.sd(V0, T, RB2 + 32)
    a.sd(V1, T, RB2 + 40)
    a.addi(R.SIGL, R.SIGL, 176)
    a.addi(R.KAP, R.KAP, 1)
    a.addi(T, X0, 14)
    a.bne(R.KAP, T, 'fors_loop')
    a.note('FORS roots')
    a.srli(T, R.IDX, 32)
    a.slli(T, T, 24)
    a.li(R.TB_, 0xB01)
    a.or_(T, T, R.TB_)
    a.sw(T, X0, RB2)
    a.sw(X0, X0, RB2 + 4)
    a.addi(A0, X0, RB2)
    a.addi(A1, X0, 256)
    a.addi(A2, X0, EB + 32)
    a.ecall()
    a.note('layers 6..0')
    a.addi(R.KAP, X0, 6)
    a.li(R.SIGL, STG + STG_LAYER * 6)
    a.label('layer_loop')
    a.addi(T, X0, 6)
    a.bne(R.KAP, T, 'layer_not6')
    a.addi(R.TA_, X0, 0)
    a.addi(R.J, X0, 4)
    a.j('layer_route')
    a.label('layer_not6')
    a.slli(T, R.KAP, 2)
    a.add(T, T, R.KAP)
    a.addi(R.TA_, X0, 29)
    a.sub(R.TA_, R.TA_, T)
    a.addi(R.J, X0, 5)
    a.label('layer_route')
    a.srl(R.U, R.IDX, R.TA_)
    a.addi(T, X0, 1)
    a.sll(T, T, R.J)
    a.addi(T, T, -1)
    a.and_(R.U, R.U, T)
    a.add(R.TB_, R.TA_, R.J)
    a.srl(R.TAU, R.IDX, R.TB_)
    a.slli(T, R.U, 32)
    a.or_(R.W1, R.TAU, T)
    a.slli(T, R.KAP, 16)
    a.ori(T, T, 0x401)
    a.sd(T, X0, EB)
    a.sd(R.W1, X0, EB + 8)
    a.sd(X0, X0, EB + 56)
    a.addi(R.CNT, X0, 0)
    a.label('enc_loop')
    a.sd(R.CNT, X0, EB + 48)
    a.addi(A0, X0, EB)
    a.addi(A1, X0, 64)
    a.addi(A2, X0, EO)
    a.ecall()
    a.ld(V0, X0, EO)
    a.ld(V1, X0, EO + 8)
    # encoding check (sign: straight-line digit sum, easy to verify; cycles are not scored)
    a.blt(V0, X0, 'enc_next')
    a.blt(V1, X0, 'enc_next')
    for q, d in enumerate((V0, V1)):
        for r in range(21):
            if q == 0 and r == 0:
                a.andi(R.TA_, d, 7)
                continue
            if r:
                a.srli(T, d, 3 * r)
                a.andi(T, T, 7)
            else:
                a.andi(T, d, 7)
            a.add(R.TA_, R.TA_, T)
    a.addi(R.TA_, R.TA_, -ref.TARGET)
    a.bne(R.TA_, X0, 'enc_next')
    a.j('enc_ok')
    a.label('enc_next')
    a.addi(R.CNT, R.CNT, 1)
    a.bne(R.CNT, R.LIM, 'enc_loop')
    a.label('fail_enc')
    halt(a, 1)
    a.label('enc_ok')
    a.sd(R.CNT, R.SIGL, 0)
    a.addi(R.FW, X0, DIG8)
    for i in range(42):
        q, r = divmod(i, 21)
        d = V0 if q == 0 else V1
        if r:
            a.srli(T, d, 3 * r)
            a.andi(T, T, 7)
        else:
            a.andi(T, d, 7)
        a.sd(T, R.FW, 8 * i)
    tree_build(a, capture=True)
    a.ld(V0, R.FAP, 0)
    a.ld(V1, R.FAP, 8)
    a.sd(V0, X0, EB + 32)
    a.sd(V1, X0, EB + 40)
    a.addi(R.SIGL, R.SIGL, -STG_LAYER)
    a.addi(R.KAP, R.KAP, -1)
    a.bge(R.KAP, X0, 'layer_loop')
    pack(a)
    a.label('success')
    halt(a, 0)
    return a


def pack_sources():
    """Signature layer region [2480, 7756) as dwords: for each sig dword offset D (relative to
    SIG, 8-aligned), the stage addresses of its low and high 4-byte chunks (None past the end)."""
    def src(off):       # stage address of the 4-byte chunk at signature offset off
        lay = max(l for l in range(7) if ref.sig_layer_offset(l) <= off)
        r = off - ref.sig_layer_offset(lay)
        base = STG + STG_LAYER * lay
        return base if r == 0 else base + 8 + (r - 4)
    out = []
    for D in range(2480, S_BYTES, 8):
        lo = src(D)
        hi = src(D + 4) if D + 4 < S_BYTES else None
        out.append((D, lo, hi))
    return out


PACK_GROUP = 8


def pack(a):
    """Copy the staged layers into the signature (constant addresses only). Each group of
    PACK_GROUP dwords starts by loading its own base registers (label pack_<g>)."""
    V0, V1 = R.V0, R.V1
    RS, RD = R.TA_, R.TB_
    srcs = pack_sources()
    a.note('pack staged layers into the signature')
    for g in range(0, len(srcs), PACK_GROUP):
        grp = srcs[g:g + PACK_GROUP]
        a.label('pack_%d' % (g // PACK_GROUP))
        bs = min(min(lo, hi if hi is not None else lo) for _, lo, hi in grp)
        bd = SIG + grp[0][0]
        a.li(RS, bs)
        a.li(RD, bd)
        for D, lo, hi in grp:
            if hi == lo + 4 and lo % 8 == 0:
                a.ld(V0, RS, lo - bs)
            else:
                a.lwu(V0, RS, lo - bs)
                if hi is not None:
                    a.lwu(V1, RS, hi - bs)
                    a.slli(V1, V1, 32)
                    a.or_(V0, V0, V1)
            a.sd(V0, RD, SIG + D - bd)


def gen_expand(mode='perm'):
    a = Asm('expand')
    T, SRC, DST, CNT = 3, 6, 7, 8
    a.label('start')

    def copy(src, dst, nwords, tag):
        a.note('copy %d words %s' % (nwords, tag))
        a.li(SRC, src)
        a.li(DST, dst)
        a.li(CNT, nwords)
        lab = a.fresh('copy_' + tag)
        a.label(lab)
        a.lwu(T, SRC, 0)
        a.sw(T, DST, 0)
        a.addi(SRC, SRC, 4)
        a.addi(DST, DST, 4)
        a.addi(CNT, CNT, -1)
        a.bne(CNT, X0, lab)

    if mode == 'copy':
        copy(SIG, WIT, S_BYTES // 4, 'all')
    else:
        head = 16 + 14 * 176
        copy(SIG, WIT, head // 4, 'head')
        for lay in range(7):
            so = ref.sig_layer_offset(lay)
            wo = ref.wit_layer_offset(lay)
            n = 672 + 16 * ref.HEIGHTS[lay]
            copy(SIG + so, WIT + ref.WIT_COUNTERS + 4 * lay, 1, 'ctr%d' % lay)
            copy(SIG + so + 4, WIT + wo, n // 4, 'body%d' % lay)
    halt(a, 0)
    return a


def build_all(mode='perm', pad=True):
    asms = {'keygen': gen_keygen(), 'sign': gen_sign(), 'expand': gen_expand(mode)}
    vg = VerifyGen(mode, pad)
    asms['verify'] = vg.build()
    images = {k: (v.finish(), b'') for k, v in asms.items()}
    return images, asms, vg


if __name__ == '__main__':
    import sys
    mode = sys.argv[1] if len(sys.argv) > 1 else 'perm'
    images, asms, vg = build_all(mode)
    for k, (code, data) in images.items():
        print(k, len(code), 'instructions', 4 * len(code), 'bytes')
    print('chain overheads', vg.chain_overheads)
