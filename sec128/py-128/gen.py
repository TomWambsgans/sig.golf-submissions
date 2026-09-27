"""Generators for the four SPHINCS-golf-128 RV64IM images (keygen, sign, expand, verify).

Scheme: ref.py (129-bit node values, 136-bit chain values, 43 chains, T = ref.TARGET, 11 pinned
digest bits, root salt sigma).  See PROGRAMS.md for the register conventions and block structure.
"""
import ref
from asm import Asm, X0

S_BYTES = ref.SIG_BYTES          # 6720
W_BYTES = ref.W_BYTES            # 6900
NCH = ref.N_CHAINS               # 43

# ------------------------------------------------------------------ memory layout
DG = 0x020        # digest block [0x0C01 | r | rho.lo | m]; m is the message buffer (DG + 32)
MSG = 0x040
SK = 0x080
PK = 0x0A0
CB = 0x0C0        # chain block tw | 0^31 | hi | lo (value lo at CB+48, hi at CB+47; answer junk
                  # CB+64..80 = EB+0..16); FORS leaf block tw | P | s.lo | s.b | 0^15
EB = 0x100        # encoding block tw | P | M.lo | LE64 M.b | LE64 c
EO = 0x140        # encoding output / prf answer (32)
DO = 0x160        # digest output (32)
FO = 0x180        # final root (32)
NB = 0x1C0        # node block tw | L.b R.b 0^14 | L.lo | R.lo (+32 junk to 0x220)
RB2 = 0x220       # FORS roots tw | b_0..b_13 0^2 | lo_0..lo_13 (256, +32 junk to 0x340)
LB = 0x340        # OTS leaf tw | hi_0..hi_42 0^21 | lo_0..lo_42 (768, +16 junk to 0x650)
RB = 0x650        # sign: randomizer tw | P | S | m | 0^32 (128)
PB = 0x6D0        # sign/keygen: prf input tw | P | S (64)
EX = 0x710        # sign: FORS extra-bit answers (4 x 32); layer phase: per-layer staging bases
US = 0x790        # sign: u_0..u_13 (dwords) -> 0x800
WIT = 0x800
SIG = (WIT + W_BYTES + 7) // 8 * 8
CACHE_HDR = SIG + (S_BYTES + 7) // 8 * 8
CACHE = CACHE_HDR + 32
REGION = CACHE + 32                     # lo array; b bytes at REGIONB; sigma at REGION + 69600
REGIONB = REGION + 16 * ref.NODES_CACHED
MAC_LEN = 69696                         # 16 + 16 + 32 + 69608 = 69672 bytes, zero-padded (1089 blocks)
STG = (CACHE + (1 << 17) + 0xff) // 0x100 * 0x100     # sign: witness-format staging (W bytes)
FA = STG + 0x2000                       # sign: FORS node array 1025 x 32
TA = FA + 0x8100                        # sign: tree node array 65 x 32
SBUF = TA + 0x900                       # sign/keygen: prf stream (23 x 32)
DIG8 = SBUF + 0x300                     # sign: digits x_0..x_42 (dwords)
KT = 0x80000                            # keygen: top tree, all levels (4094 x 32)

assert MSG == DG + 32
LAYOUT = dict(message=MSG, secretKey=SK, publicKey=PK, cache=CACHE, signature=SIG, witness=WIT)
SIZES = (S_BYTES, W_BYTES)
assert NB % 32 == 0 and LB + 768 + 16 <= RB and RB2 + 256 + 32 <= LB and US + 112 <= WIT
assert SIG + S_BYTES <= CACHE_HDR and CACHE + (1 << 17) <= STG and DIG8 + 8 * NCH <= KT
assert ref.pad64(bytes(16 + 16 + 32 + ref.REGION_BYTES)).__len__() == MAC_LEN

LIMIT = ref.A_MAX            # digest trials
CLIMIT = ref.C_MAX           # encoding counter trials
M1 = sum(7 << (6 * k) for k in range(11)) & ((1 << 64) - 1)
M2 = sum(63 << (12 * k) for k in range(6)) & ((1 << 64) - 1)
M1ODD = M1 & ((1 << 60) - 1)          # no group at bits 60..62 (keeps bits 63 / 127 out of the sum)
PIN_SHL = 64 - (ref.TOTAL_H + ref.FTS_A * ref.FTS_TREES - 128) - ref.PIN_BITS   # 7
PIN_SHR = 64 - ref.PIN_BITS                                                     # 53

RT0 = 5
A0, A1, A2 = 10, 11, 12


def halt(a, code):
    a.addi(RT0, X0, 1)
    a.addi(A0, X0, code)
    a.ecall()


def enc_check(a, d0, d1, x42, ra, rb, m1, m1odd, m2, fail, k170=None, t=None):
    """Branch to `fail` unless the 43 digits (d0 bits 0..62, d1 bits 0..62, x42 = digit 42 in
    0..7) sum to TARGET.  Bits 63 and 127 are ignored (m1odd has no group at 60..62).
    With k170 (a register holding TARGET << 52) the final test is `slli; bne`."""
    a.srli(ra, d0, 3)
    a.and_(ra, ra, m1odd)
    a.and_(rb, d0, m1)
    a.add(ra, ra, rb)
    a.srli(rb, d1, 3)
    a.and_(rb, rb, m1odd)
    a.add(ra, ra, rb)
    a.and_(rb, d1, m1)
    a.add(ra, ra, rb)
    a.add(ra, ra, x42)                 # lane 0: <= 4 * 7 + 7 = 35, lanes 0 + 1 <= 63
    a.srli(rb, ra, 6)
    a.add(ra, ra, rb)
    a.and_(ra, ra, m2)
    for sh in (12, 24, 48):
        a.srli(rb, ra, sh)
        a.add(ra, ra, rb)
    if k170 is None:
        a.andi(ra, ra, 0x7ff)
        a.addi(ra, ra, -ref.TARGET)
        a.bne(ra, X0, fail)
    else:
        a.slli(ra, ra, 52)
        a.bne(ra, k170, fail)


def u_extract(a, k, dst, w, tmp, combine=None):
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
        (combine or a.or_)(dst, dst, tmp)


# ================================================================== verify
class VerifyGen:
    V0, V1, T, TP = 1, 2, 3, 4
    # P[k] = k: MU[mu] = register holding mu - 1 (chain tweak byte 4); P1 also stores the root
    # heap index 1.  P1..P5 in the prologue, P6 (x26) with the layer constants.
    P = {1: 6, 2: 7, 3: 8, 4: 9, 5: 13, 6: 26}
    R, B = 14, 15                  # layers: dispatch register, dispatch-table window base
    M1r, M2r = 20, 21              # layers: digit-sum masks (set after FORS)
    D0, D1 = 16, 17
    WB = [18, 19]                  # witness bases WIT + 2048, WIT + 6144
    IDX, U, X25, X28, FW, TAU, X31 = 22, 23, 25, 28, 29, 30, 31
    M1ODD = 22                     # layers (after layer 4's route): M1 without its top group
    K16 = 24                       # 1 << 16
    FW10P = 27                     # FORS: node tweak word0 (type 10, p = 0); layers: H
    H = 27                         # layers: 0x101 | lay << 16
    K170 = 29                      # layers: TARGET << 52
    HI = 28                        # chains: the hi byte of the witness value (X28)
    FORS_BLOCKS = (range(0, 5), range(5, 10), range(10, 14))   # tracked regions (branch range)

    # witness offsets
    def off_rho(self): return 0
    def off_fs(self, k): return ref.FORS_OFF + 176 * k
    def off_fp(self, k, l): return ref.FORS_OFF + 176 * k + 16 + 16 * l
    def off_fsb(self, k): return ref.FB_OFF + 11 * k
    def off_fpb(self, k, l): return ref.FB_OFF + 11 * k + 1 + l
    def off_chain(self, lay, i): return ref.LAYER_OFF[lay] + 16 * i
    def off_hi(self, lay, i): return ref.HI_OFF + NCH * lay + i
    def off_path(self, lay, l): return ref.LAYER_OFF[lay] + 16 * NCH + 16 * l
    def off_pathb(self, lay, l): return ref.PB_OFF + ref.PB_LAY[lay] + l
    def off_ctr(self, lay): return ref.CTR_OFF + 4 * lay

    def wb(self, off):
        k = off // 4096
        return self.WB[k], off - 4096 * k - 2048

    def load16(self, off):
        a = self.a
        assert (WIT + off) % 8 == 0
        base, imm = self.wb(off)
        base2, imm2 = self.wb(off + 8)
        a.ld(self.V0, base, imm)
        a.ld(self.V1, base2, imm2)

    def store16(self, base, imm):
        self.a.sd(self.V0, base, imm)
        self.a.sd(self.V1, base, imm + 8)

    def wload(self, op, rd, off):
        base, imm = self.wb(off)
        op(rd, base, imm)

    # ---------------------------------------------------------- Merkle folds: two tracks
    # A "tracked region" is emitted as two code streams; stream t runs while the current node V
    # sits in slot t of NB (lo at NB+32+16t, its answer byte 16 at NB+48+16t).  A branch point on
    # bit b of E stays in the stream when bit b == t and jumps to the same point of the other
    # stream otherwise (both paths cost 2).  Streams end with `jal merge` / nop or with a tail.
    def region(self, E0, b0, items, tail=None):
        a, T = self.a, self.T
        nbr = 1 + sum(1 for it in items if it[0] == 'br')
        X = [[a.fresh('trk%d_x%d' % (t, k)) for k in range(nbr)] for t in range(2)]
        MERGE = a.fresh('trk_merge')
        a.slli(T, E0, 63 - b0)
        a.blt(T, X0, X[1][0])
        for t in range(2):
            a.label(X[t][0])
            k = 1
            for it in items:
                if it[0] == 'code':
                    it[1](t)
                else:
                    _, E, b = it
                    a.slli(T, E, 63 - b)
                    if t == 0:
                        a.blt(T, X0, X[1][k])
                    else:
                        a.bge(T, X0, X[0][k])
                    a.label(X[t][k])
                    k += 1
            if tail is not None:
                tail(t)
            elif t == 0:
                a.j(MERGE)
            else:
                a.nop()
        if tail is None:
            a.label(MERGE)

    def fold_items(self, h, E, off_fn, offb_fn, last_dst, sigma=False, nobits_from=None):
        """h fold levels (a0 = NB, a1 = 64, NB word0 and tree word set; V in slot t).
        Level: V.b -> NB+16+t (lbu, andi, sb: V's answer byte 16 is at NB+48+16t, read before the
        sibling overwrites it for t = 0); sibling lo -> slot 1-t; sibling b byte -> NB+17-t; the
        heap index E >> (lambda+1) -> NB+12 (root: 1; top root also p = sigma)."""
        a, TP, T = self.a, self.TP, self.T
        items = []
        for lam in range(h):
            def lvl(t, lam=lam):
                a.note('fold level %d (track %d)' % (lam + 1, t))
                bits = nobits_from is None or lam < nobits_from
                if bits:
                    a.lbu(T, X0, NB + 48 + 16 * t)
                    a.andi(T, T, 1)
                    a.sb(T, X0, NB + 16 + t)
                elif lam == nobits_from:
                    a.sw(X0, X0, NB + 16)                     # 128-bit inputs: b bytes 0
                self.load16(off_fn(lam))
                self.store16(X0, NB + 48 - 16 * t)
                if bits:
                    self.wload(a.lbu, T, offb_fn(lam))
                    a.sb(T, X0, NB + 17 - t)
                if lam < h - 1:
                    a.srli(TP, E, lam + 1)
                    a.sw(TP, X0, NB + 12)
                else:
                    a.sw(self.P[1], X0, NB + 12)              # root: heap index 1
                    if sigma:
                        self.wload(a.lwu, T, ref.SIGMA_OFF)
                        a.sw(T, X0, NB + 4)                   # top root: p = sigma
                    a.addi(A2, X0, last_dst)
                    a.ecall()
            items.append(('code', lvl))
            if lam < h - 1:
                items.append(('br', E, lam + 1))
                items.append(('code', lambda t: (a.addi(A2, X0, NB + 32 + 16 * t), a.ecall())))
        return items

    # ---------------------------------------------------------- chains: JALR dispatch tables
    # Sites: pairs (i, i+1) of digits in one dword (R = B + 16 x_i + 128 x_{i+1}), the singles
    # 20 / 41 (R = B + 16 (bits 60..63 of D0 / D1): 16-entry tables, entries 8..15 repeat 0..7, so
    # bits 63 / 127 need no mask) and 42 (R = B + 16 x_42, X25 = x_42 from the encoding check).
    def sites(self):
        out = []
        for q in range(2):
            base = 21 * q
            for r in range(0, 20, 2):
                out.append(('pair', q, r, (base + r, base + r + 1)))
            out.append(('single16', q, 20, (base + 20,)))
        out.append(('single8', 2, 0, (42,)))
        return out

    @staticmethod
    def site_tables(kind):
        return {'pair': [1024, 1024], 'single16': [256], 'single8': [128]}[kind]

    def window_plan(self):
        plan = []
        used = None
        for lay in range(ref.LAYERS - 1, -1, -1):
            for kind, q, r, chains in self.sites():
                sizes = self.site_tables(kind)
                new = used is None or used + sum(sizes[:-1]) > 4095
                if new:
                    used = 0
                offs = []
                for s in sizes:
                    offs.append(used)
                    used += s
                plan.append((new, offs))
        return plan

    def dispatch_prep(self, kind, q, r, site_no):
        a, R, B = self.a, self.R, self.B
        new, offs = self.wplan[site_no]
        if new:
            a.lui(B, (self.site_B[site_no] >> 12) & 0xfffff)
        if kind == 'pair':
            Dq = self.D0 if q == 0 else self.D1
            sh = 3 * r - 4
            if sh > 0:
                a.srli(R, Dq, sh)
            else:
                a.slli(R, Dq, -sh)
            a.andi(R, R, 0x3F0)
        elif kind == 'single16':
            Dq = self.D0 if q == 0 else self.D1
            a.srli(R, Dq, 60)
            a.slli(R, R, 4)
        else:
            a.slli(R, self.X25, 4)
        a.add(R, R, B)

    def chain_labels(self, lay, i):
        a = self.a
        S = [None] + [a.fresh('c%d_%d_s%d' % (lay, i, mu)) for mu in range(1, 8)]
        return S, a.fresh('c%d_%d_next' % (lay, i))

    def chain_head(self, lay, i, site_no, slot):
        a = self.a
        a.note('chain lay=%d i=%d' % (lay, i))
        a.label(a.fresh('c%d_%d' % (lay, i)))
        self.load16(self.off_chain(lay, i))
        self.wload(a.lbu, self.HI, self.off_hi(lay, i))
        creg = X0 if i == 0 else self.P.get(i)           # P_i holds i (i = 1..6)
        if creg is not None:
            a.sb(creg, X0, CB + 5)                       # chain tweak byte 5 = i
        else:
            a.addi(self.TP, X0, i)
            a.sb(self.TP, X0, CB + 5)
        a.addi(A2, X0, CB + 48)
        imm = self.site_tab[site_no][slot] - self.site_B[site_no]
        assert -2048 <= imm < 2048
        a.jalr(X0, self.R, imm)

    def chain_body(self, lay, i, site_no, slot, kind, labs, rej=None):
        a, T = self.a, self.T
        S, NEXT = labs
        if rej is not None:
            a.label(rej)
            a.j('reject')
        for mu in range(1, 8):
            a.label(S[mu])
            a.sb(self.P[mu - 1] if mu > 1 else X0, A0, 4)   # byte 4 = mu - 1
            if mu < 7:
                a.ecall()                                   # answer lo in place at CB+48
                a.lbu(T, A0, 64)                            # answer byte 16 -> hi slot CB+47
                a.sb(T, A0, 47)
            else:
                a.addi(A2, X0, LB + 80 + 16 * i)
                a.ecall()                                   # end lo straight into leaf slot i
                a.lbu(T, X0, LB + 96 + 16 * i)
                a.sb(T, X0, LB + 16 + i)                    # end hi byte
        a.label(NEXT)
        if kind == 'pair':
            digit = (lambda e: e & 7) if slot == 0 else (lambda e: e >> 3)
            n = 64
        elif kind == 'single16':
            digit = (lambda e: e & 7)
            n = 16
        else:
            digit = (lambda e: e)
            n = 8
        ents = []
        for e in range(n):
            d = digit(e)
            ents.append((d, i, S[d + 1] if d < 7 else NEXT))
        self.tables.append((self.site_tab[site_no][slot], 'tab_c%d_%d' % (lay, i), ents))

    def emit_tables(self):
        a = self.a
        a.note('dispatch tables (entered only by JALR)')
        for addr, name, ents in sorted(self.tables):
            cur = 0x1000 + 4 * a.here()
            assert addr >= cur and (addr - cur) % 4 == 0, (hex(addr), hex(cur))
            for _ in range((addr - cur) // 4):
                a.nop()
            a.label(name)
            for d, i, tgt in ents:
                if d < 7:
                    a.sd(self.V0, X0, CB + 48)
                    a.sd(self.V1, X0, CB + 56)
                    a.sb(self.HI, X0, CB + 47)
                else:
                    a.sd(self.V0, X0, LB + 80 + 16 * i)
                    a.sd(self.V1, X0, LB + 88 + 16 * i)
                    a.sb(self.HI, X0, LB + 16 + i)
                a.j(tgt)

    # ---------------------------------------------------------- one hypertree layer
    def layer_labels(self, lay):
        self.rej[lay] = self.a.fresh('rej_l%d' % lay)
        self.c0[lay] = self.chain_labels(lay, 0)

    def site_base(self, lay):
        return (ref.LAYERS - 1 - lay) * len(self.sites())

    def precode(self, lay, t):
        a, T, TP = self.a, self.T, self.TP
        U, TAU, X31, IDX = self.U, self.TAU, self.X31, self.IDX
        h = ref.HEIGHTS[lay]
        Hr = self.H
        a.note('layer %d: route (copy %d)' % (lay, t))
        a.label(a.fresh('layer_%d' % lay))
        if lay == ref.LAYERS - 1:
            a.andi(U, IDX, (1 << h) - 1)                 # bottom layer: e = idx mod 2^h, tau = idx >> h
            a.srli(TAU, IDX, h)
            a.slli(self.M1ODD, self.M1r, 4)              # idx is dead from here on
            a.srli(self.M1ODD, self.M1ODD, 4)
        else:
            a.sub(Hr, Hr, self.K16)                      # H = 0x101 | lay << 16
            a.andi(U, TAU, (1 << h) - 1)                 # e_lay = tau_{lay+1} mod 2^h
            a.srli(TAU, TAU, h)
        a.slli(T, U, 32)
        a.add(X31, TAU, T)                               # tau | e << 32
        if h < 11:
            a.ori(U, U, 1 << h)                          # U = e | 2^h (heap-index sentinel)
        else:
            a.addi(U, U, 1024)
            a.addi(U, U, 1024)
        a.note('layer %d: encoding (EB: tw | P | M.lo | LE64 M.b | LE64 c)' % lay)
        a.addi(T, Hr, 0x300)
        a.sd(T, X0, EB)                                  # [1, 4, lay, 0] | p = 0
        a.sd(X31, X0, EB + 8)
        a.lbu(T, X0, EB + 48)                            # M's answer byte 16
        a.andi(T, T, 1)
        a.sd(T, X0, EB + 48)
        self.wload(a.lwu, TP, self.off_ctr(lay))
        a.sd(TP, X0, EB + 56)
        a.addi(A0, X0, EB)
        if lay == ref.LAYERS - 1:
            a.addi(A1, X0, 64)                           # (other layers: a1 = 64 after the fold)
        a.addi(A2, X0, EO)
        a.ecall()
        a.ld(self.D0, X0, EO)
        a.ld(self.D1, X0, EO + 8)
        a.lbu(self.X25, X0, EO + 16)
        a.andi(self.X25, self.X25, 7)                    # x_42
        enc_check(a, self.D0, self.D1, self.X25, self.X28, TP, self.M1r, self.M1ODD, self.M2r,
                  self.rej[lay], k170=self.K170)
        a.note('layer %d: chains' % lay)
        a.sw(Hr, X0, CB)                                 # [1, 1, lay, 0] (p written per step)
        a.sd(X31, X0, CB + 8)                            # tau | e << 32
        if lay == ref.LAYERS - 1:
            a.sd(X0, X0, CB + 32)                        # FORS left s.lo in CB+32..48
            a.sd(X0, X0, CB + 40)
        a.addi(A0, X0, CB)
        kind, q, r, chains = self.sites()[0]
        sn = self.site_base(lay)
        self.dispatch_prep(kind, q, r, sn)
        self.chain_head(lay, 0, sn, 0)

    def layer_body(self, lay):
        a, T = self.a, self.T
        U, TAU, X31 = self.U, self.TAU, self.X31
        h = ref.HEIGHTS[lay]
        Hr = self.H
        sn0 = self.site_base(lay)
        for k, (kind, q, r, chains) in enumerate(self.sites()):
            sn = sn0 + k
            if k:
                a.note('layer %d: dispatch site %s %s' % (lay, kind, chains))
                self.dispatch_prep(kind, q, r, sn)
            for slot, i in enumerate(chains):
                if (k, slot) == (0, 0):
                    labs, rej = self.c0[lay], self.rej[lay]
                else:
                    labs, rej = self.chain_labels(lay, i), None
                    self.chain_head(lay, i, sn, slot)
                self.chain_body(lay, i, sn, slot, kind, labs, rej)
        a.note('layer %d: leaf' % lay)
        a.addi(T, Hr, 0x100)
        a.sd(T, X0, LB)
        a.sd(X31, X0, LB + 8)
        a.addi(T, Hr, 0x200)
        a.sd(T, X0, NB)                                  # [1, 3, lay, 0] | p = 0
        a.sw(TAU, X0, NB + 8)
        a.addi(A0, X0, LB)
        a.addi(A1, X0, 768)

        def leaf_x(t):
            a.addi(A2, X0, NB + 32 + 16 * t)
            a.ecall()
            a.note('layer %d: tree fold' % lay)
            a.addi(A0, X0, NB)
            a.addi(A1, X0, 64)
        items = [('code', leaf_x)]
        items += self.fold_items(h, U, lambda l: self.off_path(lay, l), lambda l: self.off_pathb(lay, l),
                                 EB + 32 if lay > 0 else FO, sigma=(lay == 0))
        if lay > 0:
            self.layer_labels(lay - 1)
            tail = lambda t: self.precode(lay - 1, t)
        else:
            tail = self.compare
        self.region(U, 0, items, tail=tail)

    def compare(self, t):
        a, V0, V1, T = self.a, self.V0, self.V1, self.T
        a.note('final comparison with the public key, root.b == 0 (copy %d)' % t)
        REJ = a.fresh('reject_final')
        a.label(a.fresh('compare'))
        a.ld(V0, X0, FO)
        a.ld(V1, X0, PK)
        a.bne(V0, V1, REJ)
        a.ld(V0, X0, FO + 8)
        a.ld(V1, X0, PK + 8)
        a.bne(V0, V1, REJ)
        a.lbu(T, X0, FO + 16)
        a.andi(T, T, 1)
        a.bne(T, X0, REJ)
        a.label(a.fresh('accept'))
        halt(a, 0)
        a.label(REJ)
        halt(a, 1)

    # ---------------------------------------------------------- program
    def build(self):
        self.wplan = self.window_plan()
        nsites = len(self.wplan)
        self.site_B = [0] * nsites
        self.site_tab = [[0, 0] for _ in range(nsites)]
        self.placed = False
        self._build()
        n_main = self.n_main
        addr = 0x1000 + 4 * n_main
        Bv = None
        for k, (new, offs) in enumerate(self.wplan):
            if new:
                Bv = (addr + 2048 + 4095) // 4096 * 4096
                start = Bv - 2048
            self.site_B[k] = Bv
            self.site_tab[k] = [start + o for o in offs]
            kind = self.sites()[k % len(self.sites())][0]
            addr = max(addr, start + offs[-1] + self.site_tables(kind)[-1])
        self.placed = True
        a = self._build()
        assert self.n_main == n_main
        return a

    def _build(self):
        self.a = Asm('verify')
        self.tables = []
        a, T, TP = self.a, self.T, self.TP
        V0, V1, IDX, U, FW, X25 = self.V0, self.V1, self.IDX, self.U, self.FW, self.X25
        a.note('prologue: constants')
        a.label('start')
        for k, r in enumerate(self.WB):
            a.li(r, WIT + 2048 + 4096 * k)
        for k in range(1, 6):
            a.addi(self.P[k], X0, k)
        cb = ref.C_MAX.bit_length() - 1                 # counters must be < 2^cb
        a.note('counter range check: every c_lay < 2^%d' % cb)
        a.label('counters')
        base, imm = self.wb(ref.CTR_OFF)
        assert (WIT + ref.CTR_OFF) % 8 == 0 and ref.LAYERS == 5
        a.ld(T, base, imm)
        a.ld(TP, base, imm + 8)
        a.or_(T, T, TP)
        a.lwu(TP, base, imm + 16)                        # c_4 (sigma in the high half is skipped)
        a.or_(T, T, TP)
        a.slli(TP, T, 32)
        a.or_(T, T, TP)
        a.srli(T, T, 32 + cb)
        a.bne(T, X0, 'reject')
        a.note('message digest: DG = [0x0C01 | r | rho.lo | m]')
        a.label('digest')
        a.li(T, 0x0C01)
        a.sd(T, X0, DG)
        self.wload(a.ld, T, ref.R_OFF)
        a.sd(T, X0, DG + 8)
        self.load16(self.off_rho())
        self.store16(X0, DG + 16)
        a.addi(A0, X0, DG)
        a.addi(A1, X0, 64)
        a.addi(A2, X0, DO)
        a.ecall()
        a.ld(X25, X0, DO + 16)
        a.slli(T, X25, PIN_SHL)                          # bits 174..184 of N
        a.srli(T, T, PIN_SHR)
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
        a.addi(FW, T, 0x7ff)
        a.addi(FW, FW, 0x901 - 0x7ff)        # [1, 9, kappa=0, idx>>32]
        a.addi(TP, FW, 0x200)
        a.sw(TP, X0, RB2)                    # roots tweak [1, 11, 0, idx>>32]
        a.addi(self.FW10P, FW, 0x100)        # [1, 10, kappa=0, idx>>32] | p = 0
        a.lui(self.K16, 0x10)
        w = (self.D0, self.D1, X25)

        def prefix(k):
            a.note('FORS tree %d' % k)
            a.label(a.fresh('fors_%d' % k))
            u_extract(a, k, U, w, T)
            a.sw(FW, X0, CB)
            a.sw(U, X0, CB + 12)
            a.ori(U, U, 1 << ref.FTS_A)         # U = u | 2^10 (heap-index sentinel)
            self.load16(self.off_fs(k))
            self.store16(X0, CB + 32)
            self.wload(a.lbu, T, self.off_fsb(k))
            a.sb(T, X0, CB + 48)
            a.addi(A0, X0, CB)

        def leaf_x(t):
            a.addi(A2, X0, NB + 32 + 16 * t)
            a.ecall()
            a.addi(A0, X0, NB)
            a.sd(self.FW10P, X0, NB)

        def root_bit(k):
            def f(t):
                if not ref.FORS_INT128:
                    a.lbu(T, X0, RB2 + 48 + 16 * k)      # root answer byte 16
                    a.andi(T, T, 1)
                    a.sb(T, X0, RB2 + 16 + k)
                a.add(FW, FW, self.K16)
                a.add(self.FW10P, self.FW10P, self.K16)
            return f

        def to_layers(t):
            a.note('FORS roots (copy %d)' % t)
            a.addi(A0, X0, RB2)
            a.addi(A1, X0, 256)
            a.addi(A2, X0, EB + 32)
            a.ecall()
            a.note('layer constants')
            m1, m2 = self.M1r, self.M2r
            a.addi(m2, X0, 63)                       # M2 = 63 at 12k (shift-or ladder)
            for sh in (12, 24, 48):
                a.slli(T, m2, sh)
                a.or_(m2, m2, T)
            a.slli(T, m2, 3)
            a.xor(m1, m2, T)                         # M1 = M2 ^ (M2 << 3) = 7 at 6k
            a.li(self.H, 0x101 | ((ref.LAYERS - 1) << 16))
            a.addi(self.P[6], X0, 6)
            a.addi(self.K170, X0, ref.TARGET)
            a.slli(self.K170, self.K170, 52)
            self.precode(ref.LAYERS - 1, t)

        self.rej, self.c0 = {}, {}
        self.layer_labels(ref.LAYERS - 1)
        for blk in self.FORS_BLOCKS:
            items = []
            for k in blk:
                if k != blk[0]:
                    items.append(('code', lambda t, k=k: prefix(k)))
                    items.append(('br', U, 0))
                items.append(('code', leaf_x))
                items += self.fold_items(10, U, lambda l, k=k: self.off_fp(k, l),
                                         lambda l, k=k: self.off_fpb(k, l), RB2 + 32 + 16 * k,
                                         nobits_from=1 if ref.FORS_INT128 else None)
                items.append(('code', root_bit(k)))
            prefix(blk[0])
            self.region(U, 0, items, tail=to_layers if blk[-1] == 13 else None)
        for lay in range(ref.LAYERS - 1, -1, -1):
            self.layer_body(lay)
        self.n_main = a.here()
        if self.placed:
            self.emit_tables()
        return a


# ================================================================== sign / keygen shared
class SignRegs:
    V0, V1, T, TP = 1, 2, 3, 4
    CNT, LIM, KAP, J = 6, 7, 8, 9          # KAP doubles as LAY, J as HH in the layer phase
    U, FW, LAM, JJ, NCNT, SIGL, FAP, EP, I, IDX, MU, P, X, M1r, M2r, TA_, TB_, TAU, W1 = range(13, 32)


R = SignRegs
SEC = EO          # prf answer


def copy_bytes(a, src, soff, dst, doff, n, tmp):
    """Straight-line byte copy (registers src/dst as bases)."""
    for q in range(n):
        a.lbu(tmp, src, soff + q)
        a.sb(tmp, dst, doff + q)


def copy_lo(a, src, soff, dst, doff):
    """16-byte copy, both 8-aligned."""
    for q in range(2):
        a.ld(R.V0, src, soff + 8 * q)
        a.sd(R.V0, dst, doff + 8 * q)


def node_hash(a, dst=None, bmask=None):
    """NB <- entries 2JJ, 2JJ+1 of the 32-byte array at R.FAP (lo = bytes 0..16, b = byte 16 & 1);
    H(NB) -> dst + 32 JJ (default R.FAP)."""
    dst = R.FAP if dst is None else dst
    T, V0 = R.T, R.V0
    a.add(R.V1, R.JJ, R.NCNT)                  # heap index 2^(h - level) + j
    a.sw(R.V1, X0, NB + 12)
    a.slli(T, R.JJ, 6)
    a.add(T, T, R.FAP)
    for q in range(2):
        a.ld(V0, T, 8 * q)
        a.sd(V0, X0, NB + 32 + 8 * q)
        a.ld(V0, T, 32 + 8 * q)
        a.sd(V0, X0, NB + 48 + 8 * q)
    for q in range(2):
        a.lbu(V0, T, 16 + 32 * q)
        if bmask is None:
            a.andi(V0, V0, 1)
        else:
            a.and_(V0, V0, bmask)
        a.sb(V0, X0, NB + 16 + q)
    a.addi(A0, X0, NB)
    a.addi(A1, X0, 64)
    a.slli(T, R.JJ, 5)
    a.add(A2, dst, T)
    a.ecall()


def prf_stream(a):
    """SBUF[32q..] <- H(tw(0, lay, tau, q, e) | P | S) for q = 0..22 (PB word0 low and word1 set;
    the p field PB+4 = q)."""
    T = R.T
    a.li(R.TB_, SBUF)
    a.addi(T, X0, 0)
    lab = a.fresh('stream')
    a.label(lab)
    a.sw(T, X0, PB + 4)
    a.addi(A0, X0, PB)
    a.addi(A1, X0, 64)
    a.slli(A2, T, 5)
    a.add(A2, A2, R.TB_)
    a.ecall()
    a.addi(T, T, 1)
    a.addi(R.TP, X0, ref.STREAM_Q)
    a.bne(T, R.TP, lab)


def chain_secret(a):
    """CB+48..64 <- SBUF[17 I .. 17 I + 16], CB+47 <- SBUF[17 I + 16] (byte copy)."""
    T, TP = R.T, R.TP
    a.slli(TP, R.I, 4)
    a.add(TP, TP, R.I)
    a.li(T, SBUF)
    a.add(TP, TP, T)
    for q in range(16):
        a.lbu(R.V0, TP, q)
        a.sb(R.V0, X0, CB + 48 + q)
    a.lbu(R.V0, TP, 16)
    a.sb(R.V0, X0, CB + 47)


def chain_step(a):
    """CB+4 <- (MU - 1) | I << 8 (MU already incremented), hash CB -> CB+48, hi byte -> CB+47."""
    T = R.T
    a.slli(T, R.I, 8)
    a.add(T, T, R.MU)
    a.addi(T, T, -1)
    a.sw(T, X0, CB + 4)
    a.addi(A0, X0, CB)
    a.addi(A1, X0, 64)
    a.addi(A2, X0, CB + 48)
    a.ecall()
    a.lbu(T, X0, CB + 64)
    a.sb(T, X0, CB + 47)


def stage_value(a, stem):
    """If EP == U and MU == X: copy the chain value (CB+48 lo, CB+47 hi) to the staging area
    (lo base at EX+0, hi base at EX+8 hold STG layer bases)."""
    skip = a.fresh(stem)
    T, TP = R.T, R.TP
    a.bne(R.EP, R.U, skip)
    a.bne(R.MU, R.X, skip)
    a.ld(TP, X0, EX + 0)
    a.slli(T, R.I, 4)
    a.add(TP, TP, T)
    copy_lo(a, X0, CB + 48, TP, 0)
    a.ld(TP, X0, EX + 8)
    a.add(TP, TP, R.I)
    a.lbu(T, X0, CB + 47)
    a.sb(T, TP, 0)
    a.label(skip)


def tree_build(a, capture, base=TA, keep=False, levels=None):
    """Build tree (LAY=R.KAP, TAU, height R.J) into the 32-byte array at `base`; capture leaf R.U
    (chain values at digits DIG8, path).  keep=True (keygen): level l is written right after
    level l-1; `levels` = number of levels to build (default HH)."""
    T, TP, V0, V1 = R.T, R.TP, R.V0, R.V1
    LAY, HH = R.KAP, R.J
    DST = R.X
    a.note('tree build: tweak words')
    a.li(R.FAP, base)
    a.slli(T, LAY, 16)
    a.ori(R.TB_, T, 0x001)
    a.sd(R.TB_, X0, PB)                        # [1, 0, lay, 0] | p (stream index, set per query)
    a.ori(R.TB_, T, 0x101)
    a.sw(R.TB_, X0, CB)
    a.ori(R.TB_, T, 0x201)
    a.sd(R.TB_, X0, LB)
    a.addi(T, X0, 1)
    a.sll(R.NCNT, T, HH)
    a.addi(R.EP, X0, 0)
    for q in range(4):                         # CB+16..47 zero (FORS / previous layers)
        a.sd(X0, X0, CB + 16 + 8 * q)
    a.label('tb_leaf_loop')
    a.slli(T, R.EP, 32)
    a.or_(T, T, R.TAU)
    a.sd(T, X0, PB + 8)
    a.sd(T, X0, CB + 8)
    a.sd(T, X0, LB + 8)
    prf_stream(a)
    a.addi(R.I, X0, 0)
    a.label('tb_chain_loop')
    chain_secret(a)
    a.addi(R.MU, X0, 0)
    if capture:
        a.slli(T, R.I, 3)
        a.li(TP, DIG8)
        a.add(T, T, TP)
        a.ld(R.X, T, 0)
        stage_value(a, 'tb_cap0')
    a.label('tb_step_loop')
    a.addi(R.MU, R.MU, 1)
    chain_step(a)
    if capture:
        stage_value(a, 'tb_cap1')
    a.addi(T, X0, 7)
    a.bne(R.MU, T, 'tb_step_loop')
    a.slli(T, R.I, 4)
    a.ld(V0, X0, CB + 48)
    a.ld(V1, X0, CB + 56)
    a.sd(V0, T, LB + 80)
    a.sd(V1, T, LB + 88)
    a.lbu(V0, X0, CB + 47)
    a.sb(V0, R.I, LB + 16)
    a.addi(R.I, R.I, 1)
    a.addi(T, X0, NCH)
    a.bne(R.I, T, 'tb_chain_loop')
    a.addi(A0, X0, LB)
    a.addi(A1, X0, 768)
    a.slli(T, R.EP, 5)
    a.add(A2, R.FAP, T)
    a.ecall()
    a.addi(R.EP, R.EP, 1)
    a.bne(R.EP, R.NCNT, 'tb_leaf_loop')
    a.note('tree build: levels')
    if levels is not None:
        a.addi(R.TA_, X0, levels)
    else:
        a.addi(R.TA_, HH, 0)
    a.addi(R.LAM, X0, 1)
    a.label('tb_level_loop')
    if capture:
        a.addi(T, R.LAM, -1)
        a.srl(T, R.U, T)
        a.xori(T, T, 1)
        a.slli(T, T, 5)
        a.add(T, T, R.FAP)
        a.ld(TP, X0, EX + 16)                  # path lo base
        a.slli(V1, R.LAM, 4)
        a.add(TP, TP, V1)
        copy_lo(a, T, 0, TP, -16)              # stage path lo (LAM - 1)
        a.lbu(V0, T, 16)
        a.andi(V0, V0, 1)
        a.ld(TP, X0, EX + 24)                  # path b base
        a.add(TP, TP, R.LAM)
        a.sb(V0, TP, -1)
    a.slli(T, LAY, 16)
    a.ori(T, T, 0x301)
    a.sd(T, X0, NB)                            # [1, 3, lay, 0] | p = 0
    a.sw(R.TAU, X0, NB + 8)
    if keep:
        a.slli(T, R.NCNT, 5)
        a.add(DST, R.FAP, T)                   # next level right after the current one
    a.srli(R.NCNT, R.NCNT, 1)
    a.addi(R.JJ, X0, 0)
    a.label('tb_node_loop')
    node_hash(a, DST if keep else R.FAP)
    a.addi(R.JJ, R.JJ, 1)
    a.bne(R.JJ, R.NCNT, 'tb_node_loop')
    if keep:
        a.addi(R.FAP, DST, 0)
    a.addi(R.LAM, R.LAM, 1)
    a.bge(R.TA_, R.LAM, 'tb_level_loop')


def mac_query(a, out):
    """H(tw_mac || P || S || region): tw_mac at CACHE-32 (the P slot CACHE-24..CACHE stays zero),
    S at CACHE..CACHE+32 (the tag slot), the 24 bytes after the region zeroed. Answer -> out."""
    T, V0 = R.T, R.V0
    a.note('MAC query over the cache region (1089 blocks)')
    a.li(R.TB_, CACHE)
    a.li(T, 0x0E01)                            # [1, 14, 0, 0]
    a.sd(T, R.TB_, -32)
    for q in range(4):
        a.ld(V0, X0, SK + 8 * q)
        a.sd(V0, R.TB_, 8 * q)
    a.li(T, REGION + ref.REGION_BYTES)
    for q in range(3):
        a.sd(X0, T, 8 * q)
    a.addi(A0, R.TB_, -32)
    a.li(A1, MAC_LEN)
    if isinstance(out, int):
        a.li(A2, out)
    else:
        a.addi(A2, out, 0)
    a.ecall()


def mask_query(a, lreg, jreg):
    """mask(l, j) = H(tw_mask(l, j) || P || S) -> EO (PB holds P | S)."""
    T = R.T
    a.slli(T, lreg, 32)
    a.addi(T, T, 0x681)
    a.addi(T, T, 0x0D01 - 0x681)               # [1, 13, 0, 0] | l << 32
    a.sd(T, X0, PB)
    a.slli(T, jreg, 32)
    a.sd(T, X0, PB + 8)                        # tau = 0 | j << 32
    a.addi(A0, X0, PB)
    a.addi(A1, X0, 64)
    a.addi(A2, X0, EO)
    a.ecall()


def gen_keygen():
    a = Asm('keygen')
    T, TP, V0, V1 = R.T, R.TP, R.V0, R.V1
    a.label('start')
    a.note('copy S into the prf buffer')
    for q in range(4):
        a.ld(R.V0, X0, SK + 8 * q)
        a.sd(R.V0, X0, PB + 32 + 8 * q)
    a.addi(R.KAP, X0, 0)       # lay 0
    a.addi(R.TAU, X0, 0)
    a.addi(R.J, X0, ref.TOP_H)
    tree_build(a, capture=False, base=KT, keep=True, levels=ref.TOP_H - 1)
    a.note('root search: p = sigma until the root answer bit 128 is 0')
    # after the loop R.FAP = level 10 base (2 entries)
    a.li(T, 0x0301)
    a.sd(T, X0, NB)                            # [1, 3, 0, 0] | p = sigma (written per trial)
    a.addi(T, X0, 1)
    a.slli(T, T, 32)
    a.sd(T, X0, NB + 8)                        # tau = 0 | heap 1
    for q in range(2):                         # L = level-10 entry 0, R = entry 1 (no hash)
        a.ld(V0, R.FAP, 8 * q)
        a.sd(V0, X0, NB + 32 + 8 * q)
        a.ld(V0, R.FAP, 32 + 8 * q)
        a.sd(V0, X0, NB + 48 + 8 * q)
        a.lbu(V0, R.FAP, 16 + 32 * q)
        a.andi(V0, V0, 1)
        a.sb(V0, X0, NB + 16 + q)
    a.addi(R.CNT, X0, 0)
    a.label('root_loop')
    a.sw(R.CNT, X0, NB + 4)
    a.addi(A0, X0, NB)
    a.addi(A1, X0, 64)
    a.addi(A2, X0, EO)
    a.ecall()
    a.lbu(T, X0, EO + 16)
    a.andi(T, T, 1)
    a.beq(T, X0, 'root_ok')
    a.addi(R.CNT, R.CNT, 1)
    a.addi(T, X0, ref.SIGMA_MAX)
    a.bne(R.CNT, T, 'root_loop')
    halt(a, 1)
    a.label('root_ok')
    a.ld(V0, X0, EO)
    a.ld(V1, X0, EO + 8)
    a.sd(V0, X0, PK)
    a.sd(V1, X0, PK + 8)
    a.li(T, REGION + ref.SIGMA_REG)
    a.sd(R.CNT, T, 0)
    a.note('masks: region node n = N_l + j: lo ^= mask.lo, b = (b ^ mask.b) & 1')
    PTR, L, J, NL, SRC = R.EP, R.LAM, R.JJ, R.NCNT, R.FAP
    a.li(PTR, 0)                               # node number n
    a.li(SRC, KT)
    a.addi(L, X0, 0)
    a.label('mask_level_loop')
    a.addi(T, X0, 1)
    a.addi(R.TB_, X0, ref.TOP_H)
    a.sub(R.TB_, R.TB_, L)
    a.sll(NL, T, R.TB_)                        # 2^(11 - l) nodes
    a.addi(J, X0, 0)
    a.label('mask_node_loop')
    mask_query(a, L, J)
    a.slli(T, PTR, 4)
    a.li(TP, REGION)
    a.add(T, T, TP)                            # lo destination
    a.slli(TP, PTR, 5)
    a.add(TP, TP, SRC)                         # KT entry
    for q in range(2):
        a.ld(V0, TP, 8 * q)
        a.ld(V1, X0, EO + 8 * q)
        a.xor(V0, V0, V1)
        a.sd(V0, T, 8 * q)
    a.lbu(V0, TP, 16)
    a.lbu(V1, X0, EO + 16)
    a.xor(V0, V0, V1)
    a.andi(V0, V0, 1)
    a.li(T, REGIONB)
    a.add(T, T, PTR)
    a.sb(V0, T, 0)
    a.addi(PTR, PTR, 1)
    a.addi(J, J, 1)
    a.bne(J, NL, 'mask_node_loop')
    a.addi(L, L, 1)
    a.addi(T, X0, ref.TOP_H)
    a.bne(L, T, 'mask_level_loop')
    mac_query(a, CACHE)                         # tag = full answer -> cache bytes 0..32
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
    a.sd(T, X0, DG)
    a.note('MAC check: tag saved, H(tw_mac | P | S | region) -> DO, compare')
    TAGR = (R.U, R.FW, R.LAM, R.JJ)
    a.li(R.TB_, CACHE)
    for q in range(4):
        a.ld(TAGR[q], R.TB_, 8 * q)
    mac_query(a, DO)
    for q in range(4):
        a.ld(V0, X0, DO + 8 * q)
        a.bne(V0, TAGR[q], 'fail_mac')
    a.note('randomizer (once): rho = H(tw7 | P | S | m); DG = [0x0C01 | rho.b | a | rho.lo | m]')
    a.addi(A0, X0, RB)
    a.addi(A1, X0, 128)
    a.addi(A2, X0, EO)
    a.ecall()
    a.ld(V0, X0, EO)
    a.ld(V1, X0, EO + 8)
    a.sd(V0, X0, DG + 16)
    a.sd(V1, X0, DG + 24)
    a.lbu(T, X0, EO + 16)
    a.andi(T, T, 1)
    a.sd(T, X0, DG + 8)
    a.li(R.LIM, LIMIT)
    a.note('digest loop over a (p field of the tweak word1: DG+12)')
    a.addi(R.CNT, X0, 0)
    a.addi(A1, X0, 64)
    a.label('dig_loop')
    a.sw(R.CNT, X0, DG + 12)
    a.addi(A0, X0, DG)
    a.addi(A2, X0, DO)
    a.ecall()
    a.ld(T, X0, DO + 16)
    a.slli(T, T, PIN_SHL)
    a.srli(T, T, PIN_SHR)
    a.beq(T, X0, 'dig_ok')
    a.addi(R.CNT, R.CNT, 1)
    a.bne(R.CNT, R.LIM, 'dig_loop')
    a.label('fail_digest')
    halt(a, 1)
    a.label('fail_mac')
    halt(a, 1)
    a.label('dig_ok')
    a.li(R.SIGL, STG)
    copy_lo(a, X0, DG + 16, R.SIGL, 0)                 # rho.lo
    a.ld(V0, X0, DG + 8)
    a.li(TP, STG + ref.R_OFF)
    a.sd(V0, TP, 0)                                    # r = rho.b | a << 32
    a.ld(V0, X0, DO)
    a.ld(V1, X0, DO + 8)
    a.ld(R.TA_, X0, DO + 16)
    a.slli(R.IDX, V0, 30)
    a.srli(R.IDX, R.IDX, 30)
    for k in range(14):
        u_extract(a, k, T, (V0, V1, R.TA_), TP, combine=a.add)
        a.sd(T, X0, US + 8 * k)
    a.note('FORS')
    a.sw(R.IDX, X0, PB + 8)
    a.sw(R.IDX, X0, CB + 8)
    a.sw(R.IDX, X0, NB + 8)
    a.sw(R.IDX, X0, RB2 + 8)
    a.sw(X0, X0, CB + 4)
    a.srli(T, R.IDX, 32)
    a.slli(T, T, 24)
    a.li(R.TB_, 0x801)
    a.add(R.FW, T, R.TB_)                              # [1, 8, 0, idx>>32]
    a.li(R.FAP, FA)
    a.addi(R.KAP, X0, 0)
    a.li(R.SIGL, STG + ref.FORS_OFF)                   # FORS tree kappa staging (lo)
    a.li(R.I, STG + ref.FB_OFF)                        # FORS tree kappa staging (b bytes)
    a.label('fors_loop')
    a.slli(T, R.KAP, 3)
    a.ld(R.U, T, US)
    a.slli(T, R.KAP, 16)
    a.add(R.TB_, R.FW, T)
    a.sw(R.TB_, X0, PB)
    a.addi(R.TB_, R.TB_, 0x100)
    a.sw(R.TB_, X0, CB)
    a.note('FORS extras: E_q = H(tw(8, kappa, idx, 1, q) | P | S) -> EX + 32q')
    a.addi(T, X0, 1)
    a.sw(T, X0, PB + 4)
    a.addi(R.J, X0, 0)
    a.label('fors_ex_loop')
    a.sw(R.J, X0, PB + 12)
    a.addi(A0, X0, PB)
    a.addi(A1, X0, 64)
    a.slli(A2, R.J, 5)
    a.addi(A2, A2, EX)
    a.ecall()
    a.addi(R.J, R.J, 1)
    a.addi(T, X0, 4)
    a.bne(R.J, T, 'fors_ex_loop')
    a.sw(X0, X0, PB + 4)
    a.addi(R.J, X0, 0)
    a.label('fors_leaf_loop')
    skip = a.fresh('prf_have')
    a.andi(T, R.J, 1)
    a.bne(T, X0, skip)
    a.srli(T, R.J, 1)
    a.sw(T, X0, PB + 12)
    a.addi(A0, X0, PB)
    a.addi(A1, X0, 64)
    a.addi(A2, X0, SEC)
    a.ecall()
    a.label(skip)
    a.andi(T, R.J, 1)
    a.slli(T, T, 4)
    a.ld(V0, T, SEC)
    a.ld(V1, T, SEC + 8)
    a.sd(V0, X0, CB + 32)
    a.sd(V1, X0, CB + 40)
    a.srli(T, R.J, 3)
    a.lbu(T, T, EX)
    a.andi(TP, R.J, 7)
    a.srl(T, T, TP)
    a.andi(T, T, 1)
    a.sb(T, X0, CB + 48)                               # s.b
    a.bne(R.J, R.U, 'fors_nocap')
    a.sd(V0, R.SIGL, 0)
    a.sd(V1, R.SIGL, 8)
    a.sb(T, R.I, 0)
    a.label('fors_nocap')
    a.sw(R.J, X0, CB + 12)
    a.addi(A0, X0, CB)
    a.addi(A1, X0, 64)
    a.slli(T, R.J, 5)
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
    a.slli(T, T, 5)
    a.add(T, T, R.FAP)
    a.slli(TP, R.LAM, 4)
    a.add(TP, TP, R.SIGL)
    copy_lo(a, T, 0, TP, 0)                            # SIGL + 16 LAM
    a.lbu(V0, T, 16)
    a.andi(V0, V0, 1)
    a.add(TP, R.I, R.LAM)
    a.sb(V0, TP, 0)                                    # b byte at I + LAM
    a.slli(T, R.KAP, 16)
    a.add(T, T, R.FW)
    a.addi(T, T, 0x200)
    a.sd(T, X0, NB)                                    # [1, 10, kappa, idx>>32] | p = 0
    a.srli(R.NCNT, R.NCNT, 1)
    a.addi(R.JJ, X0, 0)
    if ref.FORS_INT128:
        a.addi(R.P, X0, 1)                             # b mask: 1 for leaf inputs, else 0
        a.beq(R.LAM, R.P, 'fors_bm1')
        a.addi(R.P, X0, 0)
        a.label('fors_bm1')
    a.label('fors_node_loop')
    node_hash(a, bmask=R.P if ref.FORS_INT128 else None)
    a.addi(R.JJ, R.JJ, 1)
    a.bne(R.JJ, R.NCNT, 'fors_node_loop')
    a.addi(R.LAM, R.LAM, 1)
    a.addi(T, X0, 10)
    a.bge(T, R.LAM, 'fors_level_loop')
    a.slli(T, R.KAP, 4)
    copy_lo(a, R.FAP, 0, T, RB2 + 32)
    if not ref.FORS_INT128:
        a.lbu(V0, R.FAP, 16)
        a.andi(V0, V0, 1)
        a.sb(V0, R.KAP, RB2 + 16)
    a.addi(R.SIGL, R.SIGL, 176)
    a.addi(R.I, R.I, 11)
    a.addi(R.KAP, R.KAP, 1)
    a.addi(T, X0, 14)
    a.bne(R.KAP, T, 'fors_loop')
    a.note('FORS roots')
    a.srli(T, R.IDX, 32)
    a.slli(T, T, 24)
    a.li(R.TB_, 0xB01)
    a.add(T, T, R.TB_)
    a.sw(T, X0, RB2)
    a.sw(X0, X0, RB2 + 4)
    a.sw(X0, X0, RB2 + 12)
    a.addi(A0, X0, RB2)
    a.addi(A1, X0, 256)
    a.addi(A2, X0, EB + 32)
    a.ecall()
    a.lbu(T, X0, EB + 48)
    a.andi(T, T, 1)
    a.sd(T, X0, EB + 48)                               # M.b
    assert ref.HEIGHTS == [11, 6, 6, 6, 5]
    a.note('layers 4..0 (s = shift below the layer, h = height)')
    a.li(R.LIM, CLIMIT)
    a.li(R.M1r, M1)
    a.li(R.M2r, M2)
    a.addi(R.KAP, X0, ref.LAYERS - 1)
    a.label('layer_loop')
    a.note('staging bases of this layer -> EX+0 (chain lo), +8 (hi), +16 (path lo), +24 (path b)')
    # per-layer constants by a small branch ladder (5 entries)
    for lay in range(ref.LAYERS):
        nxt = a.fresh('lb_next')
        a.addi(T, X0, lay)
        a.bne(R.KAP, T, nxt)
        for q, val in enumerate((STG + ref.LAYER_OFF[lay], STG + ref.HI_OFF + NCH * lay,
                                 STG + ref.LAYER_OFF[lay] + 16 * NCH, STG + ref.PB_OFF + ref.PB_LAY[lay])):
            a.li(TP, val)
            a.sd(TP, X0, EX + 8 * q)
        a.label(nxt)
    a.addi(T, X0, 4)
    a.blt(R.KAP, T, 'layer_h6')
    a.addi(R.TA_, X0, 0)                        # lay 4: h = 5, s = 0
    a.addi(R.J, X0, 5)
    a.j('layer_route')
    a.label('layer_h6')
    a.beq(R.KAP, X0, 'layer_h11')
    a.slli(T, R.KAP, 1)                         # lay 3, 2, 1: h = 6, s = 23 - 6 lay
    a.add(T, T, R.KAP)
    a.slli(T, T, 1)
    a.addi(R.TA_, X0, 23)
    a.sub(R.TA_, R.TA_, T)
    a.addi(R.J, X0, 6)
    a.j('layer_route')
    a.label('layer_h11')
    a.addi(R.TA_, X0, 23)                       # lay 0: h = 11, s = 23
    a.addi(R.J, X0, 11)
    a.label('layer_route')
    a.srl(R.U, R.IDX, R.TA_)
    a.addi(T, X0, 1)
    a.sll(T, T, R.J)
    a.addi(T, T, -1)
    a.and_(R.U, R.U, T)
    a.add(R.TB_, R.TA_, R.J)
    a.srl(R.TAU, R.IDX, R.TB_)
    a.slli(T, R.U, 32)
    a.add(R.W1, R.TAU, T)
    a.slli(T, R.KAP, 16)
    a.addi(T, T, 0x401)
    a.sd(T, X0, EB)
    a.sd(R.W1, X0, EB + 8)
    a.sd(X0, X0, EB + 16)
    a.sd(X0, X0, EB + 24)
    a.li(R.P, M1ODD)
    a.addi(R.CNT, X0, 0)
    a.addi(A1, X0, 64)
    a.label('enc_loop')
    a.sd(R.CNT, X0, EB + 56)
    a.addi(A0, X0, EB)
    a.addi(A2, X0, EO)
    a.ecall()
    a.ld(V0, X0, EO)
    a.ld(V1, X0, EO + 8)
    a.lbu(R.X, X0, EO + 16)
    a.andi(R.X, R.X, 7)
    enc_check(a, V0, V1, R.X, R.TA_, R.TB_, R.M1r, R.P, R.M2r, 'enc_next')
    a.j('enc_ok')
    a.label('enc_next')
    a.addi(R.CNT, R.CNT, 1)
    a.bne(R.CNT, R.LIM, 'enc_loop')
    a.label('fail_enc')
    halt(a, 1)
    a.label('enc_ok')
    a.slli(T, R.KAP, 2)
    a.li(TP, STG + ref.CTR_OFF)
    a.add(T, T, TP)
    a.sw(R.CNT, T, 0)
    a.li(R.FW, DIG8)
    for i in range(NCH):
        if i < 42:
            q, r = divmod(i, 21)
            d = V0 if q == 0 else V1
            if r:
                a.srli(T, d, 3 * r)
                a.andi(T, T, 7)
            else:
                a.andi(T, d, 7)
            a.sd(T, R.FW, 8 * i)
        else:
            a.sd(R.X, R.FW, 8 * i)
    a.beq(R.KAP, X0, 'top_layer')
    tree_build(a, capture=True)
    copy_lo(a, R.FAP, 0, X0, EB + 32)
    a.lbu(V0, R.FAP, 16)
    a.andi(V0, V0, 1)
    a.sd(V0, X0, EB + 48)
    a.addi(R.KAP, R.KAP, -1)
    a.j('layer_loop')
    top_layer(a)
    pack(a)
    a.label('success')
    halt(a, 0)
    return a


def top_layer(a):
    """Layer 0 (tau = 0, e = R.U): the prf stream, chains up to x_i (staged), the path from the
    cache (lo ^ mask.lo, (b ^ mask.b) & 1), sigma."""
    T, TP, V0, V1 = R.T, R.TP, R.V0, R.V1
    a.label('top_layer')
    a.note('layer 0: prf stream, chains up to x_i only')
    a.addi(T, X0, 0x001)
    a.sd(T, X0, PB)                            # [1, 0, 0, 0] | p = q
    a.sd(R.W1, X0, PB + 8)                     # tau = 0 | e << 32
    a.addi(T, X0, 0x101)
    a.sw(T, X0, CB)
    a.sd(R.W1, X0, CB + 8)
    for q in range(4):
        a.sd(X0, X0, CB + 16 + 8 * q)
    prf_stream(a)
    a.addi(R.EP, R.U, 0)                       # stage_value compares EP with U
    a.addi(R.I, X0, 0)
    a.label('top_chain_loop')
    chain_secret(a)
    a.slli(T, R.I, 3)
    a.li(TP, DIG8)
    a.add(T, T, TP)
    a.ld(R.X, T, 0)
    a.addi(R.MU, X0, 0)
    a.label('top_step_loop')
    a.beq(R.MU, R.X, 'top_step_done')
    a.addi(R.MU, R.MU, 1)
    chain_step(a)
    a.j('top_step_loop')
    a.label('top_step_done')
    stage_value(a, 'top_cap')
    a.addi(R.I, R.I, 1)
    a.addi(T, X0, NCH)
    a.bne(R.I, T, 'top_chain_loop')
    a.note('layer 0: path from the cache (masked nodes)')
    L, SIB, NBASE = R.LAM, R.JJ, R.FAP
    a.li(NBASE, 0)                             # node number of (l, 0) = N_l
    a.li(R.NCNT, 1 << ref.TOP_H)               # nodes of level l
    a.addi(L, X0, 0)
    a.label('top_path_loop')
    a.srl(SIB, R.U, L)
    a.xori(SIB, SIB, 1)
    mask_query(a, L, SIB)
    a.add(R.TA_, NBASE, SIB)                   # node number n
    a.slli(T, R.TA_, 4)
    a.li(TP, REGION)
    a.add(T, T, TP)
    a.ld(TP, X0, EX + 16)
    a.slli(V1, L, 4)
    a.add(TP, TP, V1)                          # stage path lo l
    for q in range(2):
        a.ld(V0, T, 8 * q)
        a.ld(V1, X0, EO + 8 * q)
        a.xor(V0, V0, V1)
        a.sd(V0, TP, 8 * q)
    a.li(T, REGIONB)
    a.add(T, T, R.TA_)
    a.lbu(V0, T, 0)
    a.lbu(V1, X0, EO + 16)
    a.xor(V0, V0, V1)
    a.andi(V0, V0, 1)
    a.ld(TP, X0, EX + 24)
    a.add(TP, TP, L)
    a.sb(V0, TP, 0)
    a.add(NBASE, NBASE, R.NCNT)
    a.srli(R.NCNT, R.NCNT, 1)
    a.addi(L, L, 1)
    a.addi(T, X0, ref.TOP_H)
    a.bne(L, T, 'top_path_loop')
    a.li(T, REGION + ref.SIGMA_REG)
    a.lwu(V0, T, 0)
    a.li(T, STG + ref.SIGMA_OFF)
    a.sw(V0, T, 0)


def small_field_code(a, sub, cursor_init):
    """Straight-line calls of `sub` (jal ra) for every small field: TA_ = witness-slot address
    (STG or WIT based, added by the caller through TB_), J = kind (0: byte bit, 1: LE32), NCNT = bits."""
    for kind, off, n in ref.small_fields():
        a.li(R.TA_, off)
        a.add(R.TA_, R.TA_, R.TB_)
        a.addi(R.J, X0, 0 if kind in ('b', 'rb') else 1)
        a.addi(R.NCNT, X0, n)
        a.jal(1, sub)


def pack(a):
    """SIG[0:CORE] = STG[0:CORE] (dwords + tail bytes); bitfield SIG[CORE:] = small fields LSB-first."""
    T, TP = R.T, R.TP
    a.note('pack: copy the core, then the bit field')
    a.li(R.SIGL, SIG)
    a.li(R.FAP, STG)
    a.li(R.CNT, ref.CORE // 8)
    a.label('pack_copy')
    a.ld(T, R.FAP, 0)
    a.sd(T, R.SIGL, 0)
    a.addi(R.FAP, R.FAP, 8)
    a.addi(R.SIGL, R.SIGL, 8)
    a.addi(R.CNT, R.CNT, -1)
    a.bne(R.CNT, X0, 'pack_copy')
    for q in range(ref.CORE % 8):
        a.lbu(T, R.FAP, q)
        a.sb(T, R.SIGL, q)
    a.li(R.EP, 0)                              # bit cursor
    a.li(R.TB_, STG)
    small_field_code(a, 'putbits', None)
    a.j('pack_done')
    # putbits: append NCNT bits of the value at TA_ (byte if J = 0 else LE32) at cursor EP
    a.label('putbits')
    a.beq(R.J, X0, 'pb_byte')
    a.lwu(R.X, R.TA_, 0)
    a.j('pb_go')
    a.label('pb_byte')
    a.lbu(R.X, R.TA_, 0)
    a.label('pb_go')
    a.addi(R.MU, X0, 0)
    a.label('pb_loop')
    a.srl(T, R.X, R.MU)
    a.andi(T, T, 1)
    a.andi(TP, R.EP, 7)
    a.sll(T, T, TP)
    a.srli(TP, R.EP, 3)
    a.li(R.V1, SIG + ref.CORE)
    a.add(TP, TP, R.V1)
    a.lbu(R.V1, TP, 0)
    a.or_(R.V1, R.V1, T)
    a.sb(R.V1, TP, 0)
    a.addi(R.EP, R.EP, 1)
    a.addi(R.MU, R.MU, 1)
    a.bne(R.MU, R.NCNT, 'pb_loop')
    a.jalr(X0, 1, 0)
    a.label('pack_done')


def gen_expand():
    """witness[0:CORE] = sig[0:CORE]; unpack the bit field into the small slots; fail if the
    spare bit is set."""
    a = Asm('expand')
    T, TP = R.T, R.TP
    a.label('start')
    a.li(R.SIGL, WIT)
    a.li(R.FAP, SIG)
    a.li(R.CNT, ref.CORE // 8)
    a.label('copy')
    a.ld(T, R.FAP, 0)
    a.sd(T, R.SIGL, 0)
    a.addi(R.FAP, R.FAP, 8)
    a.addi(R.SIGL, R.SIGL, 8)
    a.addi(R.CNT, R.CNT, -1)
    a.bne(R.CNT, X0, 'copy')
    for q in range(ref.CORE % 8):
        a.lbu(T, R.FAP, q)
        a.sb(T, R.SIGL, q)
    nbf = ref.SIG_BYTES - ref.CORE
    used_last = ref.SMALL_BITS - 8 * (nbf - 1)          # used bits of the last bit-field byte
    assert 1 <= used_last <= 7                            # the spare bits all sit in the last byte
    a.li(T, SIG + ref.SIG_BYTES - 1)
    a.lbu(T, T, 0)
    a.srli(T, T, used_last)
    a.beq(T, X0, 'spare_ok')
    halt(a, 1)
    a.label('spare_ok')
    a.li(R.EP, 0)
    a.li(R.TB_, WIT)
    small_field_code(a, 'getbits', None)
    halt(a, 0)
    # getbits: read NCNT bits at cursor EP into X, store (byte if J = 0 else LE32) at TA_
    a.label('getbits')
    a.addi(R.X, X0, 0)
    a.addi(R.MU, X0, 0)
    a.label('gb_loop')
    a.srli(TP, R.EP, 3)
    a.li(R.V1, SIG + ref.CORE)
    a.add(TP, TP, R.V1)
    a.lbu(T, TP, 0)
    a.andi(TP, R.EP, 7)
    a.srl(T, T, TP)
    a.andi(T, T, 1)
    a.sll(T, T, R.MU)
    a.or_(R.X, R.X, T)
    a.addi(R.EP, R.EP, 1)
    a.addi(R.MU, R.MU, 1)
    a.bne(R.MU, R.NCNT, 'gb_loop')
    a.beq(R.J, X0, 'gb_byte')
    a.sw(R.X, R.TA_, 0)
    a.jalr(X0, 1, 0)
    a.label('gb_byte')
    a.sb(R.X, R.TA_, 0)
    a.jalr(X0, 1, 0)
    return a


def build_all(pad=True):
    asms = {'keygen': gen_keygen(), 'sign': gen_sign(), 'expand': gen_expand()}
    vg = VerifyGen()
    asms['verify'] = vg.build()
    images = {k: (v.finish(), b'') for k, v in asms.items()}
    return images, asms, vg


if __name__ == '__main__':
    images, asms, vg = build_all()
    for k, (code, data) in images.items():
        print(k, len(code), 'instructions', 4 * len(code), 'bytes')
