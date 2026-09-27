"""Byte-exact reference implementation of SPHINCS-golf-128 (work/design/SEC128-STUDY.md).

The 128-bit variant of SPEC-v7: every hash value that the security argument compares or keeps
hidden has at least 129 bits:
  * node values (FORS leaves / nodes / roots, OTS leaves, hypertree nodes, the roots hash, the
    randomizer, masks) are 129 bits: `lo` = answer bytes 0..15, `b` = bit 0 of answer byte 16;
  * WOTS chain values (and chain secrets) are 136 bits: answer bytes 0..16 (the whole byte 16,
    which is what makes the in-place chain step 11 cycles instead of 12);
  * FORS secrets are 129 bits;
  * the WOTS encoding reads 129 answer bits (43 base-8 digits, no pinned bits);
  * the message digest pins 11 bits (u_14 and one more), so the few-time constants of the
    127-bit proof are unchanged in units of 2^-129;
  * the public key (16 bytes) is the root's `lo`; the verifier also requires root.b == 0, which
    keygen arranges by a root salt sigma (tweak p field of the root query, 8 bits).

Values are handled as 17-byte strings (byte 16 is 0/1 for 129-bit values).  The oracle is
queried on the exact 64k-byte blocks the RISC-V programs hash (no relabeling); sha256 is the test
stand-in.  The query ORDER is part of the specification (see PROGRAMS.md).
"""
import hashlib
import os

# Variant switch (SG128_FORSINT=1): FORS nodes of levels 1..10 and the FORS roots are 128-bit
# (b = 0); FORS leaves and secrets stay 129-bit.  Needs an extra proof component (FORS structural
# matches as second-order events, see SEC128-STUDY.md); the default is 129 bits everywhere.
FORS_INT128 = os.environ.get('SG128_FORSINT', '0') == '1'

N_CHAINS = 43
TARGET = 195
HEIGHTS = [11, 6, 6, 6, 5]               # layer 0 = top (cached tree)
LAYERS = 5
TOTAL_H = 34
FTS_A = 10
FTS_TREES = 14                            # k - 1 (u_14 is pinned)
PIN_BITS = 11                             # digest bits 174..184 must be zero
A_MAX = 1 << 20
C_MAX = 1 << 22
SIGMA_MAX = 256
STREAM_Q = 23                             # prf queries per WOTS key: 43 * 17 = 731 <= 23 * 32
P = bytes(16)

CACHE_BYTES = 1 << 17
TOP_H = HEIGHTS[0]
TOP_N = [sum(1 << (TOP_H - k) for k in range(l)) for l in range(TOP_H + 1)]
NODES_CACHED = TOP_N[TOP_H]               # 4094 (levels 0..10)
REGION_BYTES = 16 * NODES_CACHED + NODES_CACHED + 2 + 8     # lo | b bytes | 0^2 | LE64 sigma
SIGMA_REG = 16 * NODES_CACHED + NODES_CACHED + 2           # 69600 (8-aligned)
assert REGION_BYTES == 69608
TAG_MASK, TAG_MAC = 13, 14

# ------------------------------------------------------------------ witness / signature layout
FORS_OFF = 16                              # FORS tree k: s.lo at 16 + 176k, path l at +16+16l
LAYER_OFF = []
_o = FORS_OFF + FTS_TREES * 176            # 2480
for _h in HEIGHTS:
    LAYER_OFF.append(_o)                   # chain i lo at +16i, path l lo at +16*43 + 16l
    _o += 16 * N_CHAINS + 16 * _h
LO_END = _o                                # 6464
HI_OFF = LO_END                            # chain hi bytes: layer lay chain i at HI_OFF + 43 lay + i
CORE = HI_OFF + LAYERS * N_CHAINS          # 6679: witness[0:CORE] == signature[0:CORE]
R_OFF = 6680                               # LE64 r = rho.b | a << 32
CTR_OFF = 6688                             # LE32 c_lay at 6688 + 4 lay
SIGMA_OFF = 6708                           # LE32 sigma
FB_OFF = 6712                              # FORS b bytes: s.b at 6712 + 11k, path l at +1+l
PB_OFF = FB_OFF + 11 * FTS_TREES           # 6866: layer path b bytes: lay's l at 6866 + PB_LAY[lay] + l
PB_LAY = [sum(HEIGHTS[:l]) for l in range(LAYERS)]
W_BYTES = PB_OFF + TOTAL_H                 # 6900
assert CORE == 6679 and W_BYTES == 6900
FB_BITS = 2 if FORS_INT128 else 11        # FORS b bits per tree in the signature (s.b, path b)
SMALL_BITS = 1 + 20 + 8 + 22 * LAYERS + FTS_TREES * FB_BITS + TOTAL_H    # 327 (FORS_INT128: 201)
SIG_BYTES = CORE + (SMALL_BITS + 1 + 7) // 8                             # 6679 + 41 = 6720
assert SIG_BYTES == (6705 if FORS_INT128 else 6720)


def pad64(x):
    return x + bytes((-len(x)) % 64)


class Oracle:
    def __init__(self, log=True, fn=None):
        self.log = [] if log else None
        self.calls = 0
        self.compressions = 0
        self.fn = fn or (lambda y: hashlib.sha256(y).digest())

    def H(self, x):
        y = pad64(x)
        self.calls += 1
        self.compressions += len(y) // 64
        if self.log is not None:
            self.log.append(y)
        return self.fn(y)


def le32(v):
    return v.to_bytes(4, 'little')


def le64(v):
    return v.to_bytes(8, 'little')


def tweak(t, lay, tau, p, j):
    """enc(t, lay, tau, p, j) = 1 || t || lay || tau>>32 || LE32(p) || LE32(tau mod 2^32) || LE32(j)."""
    assert 0 <= tau < (1 << 40) and 0 <= p < (1 << 32) and 0 <= j < (1 << 32)
    return bytes([1, t, lay, tau >> 32]) + le32(p) + le32(tau & 0xffffffff) + le32(j)


def v129(ans):
    return ans[:16] + bytes([ans[16] & 1])


def v136(ans):
    return ans[:17]


def xor129(a, b):
    return bytes(x ^ y for x, y in zip(a[:16], b[:16])) + bytes([(a[16] ^ b[16]) & 1])


# ------------------------------------------------------------------ hash formats
def prf(o, tw, S):
    return o.H(tw + P + S)


def node(o, tw, L, R):
    """Tree / FORS node: tw | L.b | R.b | 0^14 | L.lo | R.lo (64 bytes).  L.b, R.b are whole bytes
    (0/1 for honest values; a verifier copies the sibling's byte from the witness)."""
    return v129(o.H(tw + bytes([L[16], R[16]]) + bytes(14) + L[:16] + R[:16]))


def fors_node(o, tw, L, R):
    v = node(o, tw, L, R)
    return v[:16] + b'\x00' if FORS_INT128 else v


def fors_leaf(o, k, idx, j, s):
    return v129(o.H(tweak(9, k, idx, 0, j) + P + s[:16] + bytes([s[16]]) + bytes(15)))


def chain_step(o, lay, tau, e, i, mu, v):
    """Step mu (1..7) of chain i: word0 = [1, 1, lay, 0, mu-1, i, 0, 0], word1 = tau | e << 32,
    then 0^31 | v.hi | v.lo."""
    tw = tweak(1, lay, tau, (mu - 1) | (i << 8), e)
    return v136(o.H(tw + bytes(31) + v[16:17] + v[:16]))


def ots_leaf(o, lay, tau, e, ends):
    """tw | hi_0..hi_42 | 0^21 | lo_0..lo_42 (768 bytes, 12 blocks)."""
    his = bytes(v[16] for v in ends)
    return v129(o.H(tweak(2, lay, tau, 0, e) + his + bytes(64 - N_CHAINS) + b''.join(v[:16] for v in ends)))


def encoding(o, lay, tau, e, M, c):
    return o.H(tweak(4, lay, tau, 0, e) + P + M[:16] + le64(M[16]) + le64(c))


def randomizer(o, S, m):
    return v129(o.H(tweak(7, 0, 0, 0, 0) + P + S + m))


def digest_block(r, rho, m):
    return tweak(12, 0, 0, 0, 0)[:8] + le64(r) + rho[:16] + m


def roots_hash(o, idx, roots):
    return v129(o.H(tweak(11, 0, idx, 0, 0) + bytes(v[16] for v in roots) + bytes(16 - FTS_TREES)
                    + b''.join(v[:16] for v in roots)))


def mask(o, S, l, j):
    return v129(prf(o, tweak(TAG_MASK, 0, 0, l, j), S))


def mac(o, S, region):
    return o.H(tweak(TAG_MAC, 0, 0, 0, 0) + P + S + region)        # full 32-byte answer


def wots_secrets(o, S, lay, tau, e):
    stream = b''.join(prf(o, tweak(0, lay, tau, q, e), S) for q in range(STREAM_Q))
    return [stream[17 * i:17 * i + 17] for i in range(N_CHAINS)]


# ------------------------------------------------------------------ decoding
def decode_digits(ans):
    d0 = int.from_bytes(ans[0:8], 'little')
    d1 = int.from_bytes(ans[8:16], 'little')
    x = [(d0 >> (3 * r)) & 7 for r in range(21)] + [(d1 >> (3 * r)) & 7 for r in range(21)] + [ans[16] & 7]
    return x if sum(x) == TARGET else None


def split_digest(ans):
    N = int.from_bytes(ans[:24], 'little')
    idx = N & ((1 << TOTAL_H) - 1)
    u = [(N >> (TOTAL_H + FTS_A * k)) & 1023 for k in range(FTS_TREES)]
    ok = (N >> (TOTAL_H + FTS_A * FTS_TREES)) & ((1 << PIN_BITS) - 1) == 0
    return idx, u, ok


def shift_below(lay):
    return sum(HEIGHTS[lay + 1:])


def route(idx, lay):
    s = shift_below(lay)
    h = HEIGHTS[lay]
    return (idx >> s) & ((1 << h) - 1), idx >> (s + h)      # (e, tau)


def node_tw(t, lay, tau, h, lam, j, p=0):
    """Tweak of the node at level lam (1..h), index j: p field p (0; sigma for the top root),
    j field = heap index 2^(h - lam) + j."""
    return tweak(t, lay, tau, p, (1 << (h - lam)) + j)


# ------------------------------------------------------------------ tree building
def build_tree(o, S, lay, tau, h, cap_e=None, x=None, top_levels=None):
    """Leaves in order (per leaf: the 23 prf queries, chains 0..42 steps 1..7, leaf hash), then
    levels 1..top_levels (default h) bottom-up left to right.  Returns (levels, captured values)."""
    leaves = []
    captured = None
    for e in range(1 << h):
        secs = wots_secrets(o, S, lay, tau, e)
        ends = []
        vals_e = []
        for i in range(N_CHAINS):
            v = secs[i]
            vals = [v]
            for mu in range(1, 8):
                v = chain_step(o, lay, tau, e, i, mu, v)
                vals.append(v)
            ends.append(v)
            if e == cap_e:
                vals_e.append(vals[x[i]])
        if e == cap_e:
            captured = vals_e
        leaves.append(ots_leaf(o, lay, tau, e, ends))
    levels = [leaves]
    for lam in range(1, (h if top_levels is None else top_levels) + 1):
        lv = levels[-1]
        levels.append([node(o, node_tw(3, lay, tau, h, lam, j), lv[2 * j], lv[2 * j + 1])
                       for j in range(len(lv) // 2)])
    return levels, captured


def top_root(o, L, R, sigma):
    return node(o, node_tw(3, 0, 0, TOP_H, TOP_H, 0, p=sigma), L, R)


def keygen(o, S):
    """Returns (pk, cache) or None (no root salt found: probability 2^-256)."""
    levels, _ = build_tree(o, S, 0, 0, TOP_H, top_levels=TOP_H - 1)
    for sigma in range(SIGMA_MAX):
        root = top_root(o, levels[TOP_H - 1][0], levels[TOP_H - 1][1], sigma)
        if root[16] == 0:
            break
    else:
        return None
    lo = bytearray(16 * NODES_CACHED)
    bb = bytearray(NODES_CACHED)
    for l in range(TOP_H):
        for j in range(1 << (TOP_H - l)):
            n = TOP_N[l] + j
            mv = xor129(levels[l][j], mask(o, S, l, j))
            lo[16 * n:16 * n + 16] = mv[:16]
            bb[n] = mv[16]
    region = bytes(lo) + bytes(bb) + bytes(2) + le64(sigma)
    tag = mac(o, S, region)
    cache = tag + region + bytes(CACHE_BYTES - 32 - REGION_BYTES)
    return root[:16], cache


# ------------------------------------------------------------------ signing
def sign(o, S, cache, m):
    region = cache[32:32 + REGION_BYTES]
    if mac(o, S, region) != cache[0:32]:
        return None
    # (1) randomizer (once) and digest loop over a
    rho = randomizer(o, S, m)
    for a in range(A_MAX):
        r = rho[16] | (a << 32)
        idx, u, ok = split_digest(o.H(digest_block(r, rho, m)))
        if ok:
            break
    else:
        return None
    w = bytearray(W_BYTES)                     # witness-format staging
    w[0:16] = rho[:16]
    w[R_OFF:R_OFF + 8] = le64(r)
    # (2) FORS
    roots = []
    for k in range(FTS_TREES):
        ex = b''.join(prf(o, tweak(8, k, idx, 1, q), S) for q in range(4))
        level = []
        for jp in range(512):
            A = prf(o, tweak(8, k, idx, 0, jp), S)
            for j in (2 * jp, 2 * jp + 1):
                s = A[16 * (j & 1):16 * (j & 1) + 16] + bytes([(ex[j >> 3] >> (j & 7)) & 1])
                if j == u[k]:
                    w[FORS_OFF + 176 * k:FORS_OFF + 176 * k + 16] = s[:16]
                    w[FB_OFF + 11 * k] = s[16]
                level.append(fors_leaf(o, k, idx, j, s))
        for lam in range(1, FTS_A + 1):
            sib = level[(u[k] >> (lam - 1)) ^ 1]
            off = FORS_OFF + 176 * k + 16 * lam
            w[off:off + 16] = sib[:16]
            w[FB_OFF + 11 * k + lam] = sib[16]
            level = [fors_node(o, node_tw(10, k, idx, FTS_A, lam, j), level[2 * j], level[2 * j + 1])
                     for j in range(len(level) // 2)]
        roots.append(level[0])
    M = roots_hash(o, idx, roots)
    # (3) layers 4..1
    ctrs = [0] * LAYERS
    for lay in range(LAYERS - 1, -1, -1):
        e, tau = route(idx, lay)
        for c in range(C_MAX):
            x = decode_digits(encoding(o, lay, tau, e, M, c))
            if x is not None:
                break
        else:
            return None
        ctrs[lay] = c
        h = HEIGHTS[lay]
        if lay > 0:
            levels, vals = build_tree(o, S, lay, tau, h, e, x)
            path = [levels[l][(e >> l) ^ 1] for l in range(h)]
            M = levels[h][0]
        else:
            assert tau == 0
            secs = wots_secrets(o, S, 0, 0, e)
            vals = []
            for i in range(N_CHAINS):
                v = secs[i]
                for mu in range(1, x[i] + 1):
                    v = chain_step(o, 0, 0, e, i, mu, v)
                vals.append(v)
            path = []
            for l in range(TOP_H):
                sib = (e >> l) ^ 1
                n = TOP_N[l] + sib
                cv = region[16 * n:16 * n + 16] + bytes([region[16 * NODES_CACHED + n]])
                path.append(xor129(cv, mask(o, S, l, sib)))
        base = LAYER_OFF[lay]
        for i, v in enumerate(vals):
            w[base + 16 * i:base + 16 * i + 16] = v[:16]
            w[HI_OFF + N_CHAINS * lay + i] = v[16]
        for l, v in enumerate(path):
            off = base + 16 * N_CHAINS + 16 * l
            w[off:off + 16] = v[:16]
            w[PB_OFF + PB_LAY[lay] + l] = v[16]
    for lay in range(LAYERS):
        w[CTR_OFF + 4 * lay:CTR_OFF + 4 * lay + 4] = le32(ctrs[lay])
    w[SIGMA_OFF:SIGMA_OFF + 4] = region[SIGMA_REG:SIGMA_REG + 4]
    return from_witness(bytes(w))


# ------------------------------------------------------------------ signature <-> witness
def small_fields():
    """(witness offset, width in bytes of the witness slot, bits) of the bit-packed fields, in
    signature bit order."""
    f = [('rb', R_OFF, 1), ('a', R_OFF + 4, 20), ('sigma', SIGMA_OFF, 8)]
    f += [('c', CTR_OFF + 4 * lay, 22) for lay in range(LAYERS)]
    f += [('b', FB_OFF + 11 * k + q, 1) for k in range(FTS_TREES) for q in range(FB_BITS)]
    f += [('b', PB_OFF + q, 1) for q in range(TOTAL_H)]
    return f


def from_witness(w):
    """signature = w[0:CORE] || bitfield(41 bytes): the small fields LSB-first, 1 spare zero bit."""
    acc, pos = 0, 0
    for _, off, n in small_fields():
        val = int.from_bytes(w[off:off + 4], 'little') & ((1 << n) - 1) if n > 1 else w[off] & 1
        acc |= val << pos
        pos += n
    assert pos == SMALL_BITS
    return bytes(w[:CORE]) + acc.to_bytes(SIG_BYTES - CORE, 'little')


def to_witness(sig):
    """expand: None if the signature is not canonical (spare bit set)."""
    assert len(sig) == SIG_BYTES
    acc = int.from_bytes(sig[CORE:], 'little')
    if acc >> SMALL_BITS:
        return None
    w = bytearray(W_BYTES)
    w[:CORE] = sig[:CORE]
    pos = 0
    for kind, off, n in small_fields():
        val = (acc >> pos) & ((1 << n) - 1)
        pos += n
        if kind == 'b' or kind == 'rb':
            w[off] = val
        else:
            w[off:off + 4] = le32(val)
    return bytes(w)


# ------------------------------------------------------------------ verification (witness)
def fold(o, t, lay, tau, h, leaf, value, sibs, p_root=0, nodef=node):
    """value: computed 129-bit node; sibs: witness siblings (lo + whole b byte)."""
    for lam in range(len(sibs)):
        tw = node_tw(t, lay, tau, h, lam + 1, leaf >> (lam + 1), p=p_root if lam == h - 1 else 0)
        if (leaf >> lam) & 1:
            value = nodef(o, tw, sibs[lam], value)
        else:
            value = nodef(o, tw, value, sibs[lam])
    return value


def verify_witness(o, pk, m, w):
    assert len(w) == W_BYTES
    ctr = [int.from_bytes(w[CTR_OFF + 4 * l:CTR_OFF + 4 * l + 4], 'little') for l in range(LAYERS)]
    if any(c >= C_MAX for c in ctr):
        return False
    r = int.from_bytes(w[R_OFF:R_OFF + 8], 'little')
    idx, u, ok = split_digest(o.H(digest_block(r, w[0:16], m)))
    if not ok:
        return False
    roots = []
    for k in range(FTS_TREES):
        b0 = FORS_OFF + 176 * k
        s = w[b0:b0 + 16] + bytes([w[FB_OFF + 11 * k]])
        sibs = [w[b0 + 16 + 16 * l:b0 + 32 + 16 * l] + bytes([w[FB_OFF + 11 * k + 1 + l] if l < FB_BITS - 1 else 0])
                for l in range(FTS_A)]
        v = fors_leaf(o, k, idx, u[k], s)
        roots.append(fold(o, 10, k, idx, FTS_A, u[k], v, sibs, nodef=fors_node))
    M = roots_hash(o, idx, roots)
    sigma = int.from_bytes(w[SIGMA_OFF:SIGMA_OFF + 4], 'little')
    for lay in range(LAYERS - 1, -1, -1):
        e, tau = route(idx, lay)
        x = decode_digits(encoding(o, lay, tau, e, M, ctr[lay]))
        if x is None:
            return False
        base = LAYER_OFF[lay]
        ends = []
        for i in range(N_CHAINS):
            v = w[base + 16 * i:base + 16 * i + 16] + bytes([w[HI_OFF + N_CHAINS * lay + i]])
            for mu in range(x[i] + 1, 8):
                v = chain_step(o, lay, tau, e, i, mu, v)
            ends.append(v)
        leaf = ots_leaf(o, lay, tau, e, ends)
        h = HEIGHTS[lay]
        sibs = [w[base + 16 * N_CHAINS + 16 * l:base + 16 * N_CHAINS + 16 * l + 16]
                + bytes([w[PB_OFF + PB_LAY[lay] + l]]) for l in range(h)]
        M = fold(o, 3, lay, tau, h, e, leaf, sibs, p_root=sigma if lay == 0 else 0)
    return M[:16] == pk and M[16] == 0


def verify(o, pk, m, sig):
    w = to_witness(sig)
    return w is not None and verify_witness(o, pk, m, w)


if __name__ == '__main__':
    import os, time
    S = os.urandom(32)
    m = os.urandom(32)
    o = Oracle(log=False)
    t = time.time()
    pk, cache = keygen(o, S)
    print('keygen', o.calls, o.compressions, time.time() - t)
    o = Oracle(log=False)
    t = time.time()
    sig = sign(o, S, cache, m)
    print('sign', o.calls, o.compressions, time.time() - t, len(sig))
    o = Oracle(log=False)
    print('verify', verify(o, pk, m, sig), o.calls, o.compressions)
