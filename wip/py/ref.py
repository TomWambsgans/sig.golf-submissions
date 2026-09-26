"""Byte-exact reference implementation of SPHINCS-golf (work/design/SPEC.md).

The random oracle H is queried on pad64(x) (x zero-padded to a multiple of 64 bytes); sha256 is the
test stand-in.  Every algorithm takes an Oracle object that records the exact query sequence
(padded inputs) and the compression count.  The query ORDER is part of the specification: it is
exactly what the RISC-V programs do (see PROGRAMS.md, section "Query order").
"""
import hashlib

N_CHAINS = 42
TARGET = 170
HEIGHTS = [5, 5, 5, 5, 5, 5, 4]          # layer 0 = top
LAYERS = 7
TOTAL_H = 34
FTS_A = 10
FTS_TREES = 14                            # k - 1
A_MAX = 1 << 20
C_MAX = 1 << 20
P = bytes(16)                             # public parameter, constant 0^128

SIG_BYTES = 16 + FTS_TREES * (1 + FTS_A) * 16 + LAYERS * (4 + N_CHAINS * 16) + TOTAL_H * 16
assert SIG_BYTES == 7756


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


def tweak(t, lay, tau, p, j):
    """enc(t, lay, tau, p, j) = 1 || t || lay || tau>>32 || LE32(p) || LE32(tau mod 2^32) || LE32(j)."""
    assert 0 <= tau < (1 << 40) and 0 <= p < (1 << 32) and 0 <= j < (1 << 32)
    return bytes([1, t, lay, tau >> 32]) + le32(p) + le32(tau & 0xffffffff) + le32(j)


def Th(o, tw, payload):
    return o.H(tw + P + payload)[:16]


def shift_below(lay):
    """sum_{j > lay} h_j"""
    return sum(HEIGHTS[lay + 1:])


def route(idx, lay):
    s = shift_below(lay)
    h = HEIGHTS[lay]
    return (idx >> s) & ((1 << h) - 1), idx >> (s + h)      # (e, tau)


def decode_digest(d):
    d0 = int.from_bytes(d[0:8], 'little')
    d1 = int.from_bytes(d[8:16], 'little')
    if d0 >> 63 or d1 >> 63:
        return None
    x = [(d0 >> (3 * r)) & 7 for r in range(21)] + [(d1 >> (3 * r)) & 7 for r in range(21)]
    return x if sum(x) == TARGET else None


def split_digest(N):
    idx = N & ((1 << TOTAL_H) - 1)
    u = [(N >> (TOTAL_H + FTS_A * k)) & 1023 for k in range(15)]
    return idx, u


def message_digest(o, rho, m):
    out = o.H(tweak(12, 0, 0, 0, 0) + P + rho + bytes(16) + m)
    return int.from_bytes(out[:23], 'little')        # Truncate_184


# ------------------------------------------------------------------ hypertree tree building
def build_tree(o, S, lay, tau, h, cap_e=None, x=None):
    """Tree (lay, tau) built once: leaves in order (per chain: prf, 7 steps; leaf hash), then
    levels bottom-up left to right. Returns (root, chain values of leaf cap_e at positions x, path)."""
    leaves = []
    captured = None
    for e in range(1 << h):
        ends = []
        vals_e = []
        for i in range(N_CHAINS):
            v = Th(o, tweak(0, lay, tau, i, e), S)
            vals = [v]
            for mu in range(1, 8):
                v = Th(o, tweak(1, lay, tau, 8 * i + mu - 1, e), v)
                vals.append(v)
            ends.append(v)
            if e == cap_e:
                vals_e.append(vals[x[i]])
        if e == cap_e:
            captured = vals_e
        leaves.append(Th(o, tweak(2, lay, tau, 0, e), b''.join(ends)))
    level = leaves
    path = []
    for lam in range(1, h + 1):
        if cap_e is not None:
            path.append(level[(cap_e >> (lam - 1)) ^ 1])
        level = [Th(o, tweak(3, lay, tau, lam, j), level[2 * j] + level[2 * j + 1])
                 for j in range(len(level) // 2)]
    return level[0], captured, path


def keygen(o, S):
    root, _, _ = build_tree(o, S, 0, 0, HEIGHTS[0])
    return root


# ------------------------------------------------------------------ signing
def sign(o, S, m):
    # (1) digest loop
    for a in range(A_MAX):
        rho = Th(o, tweak(7, 0, 0, a, 0), S + m)
        N = message_digest(o, rho, m)
        idx, u = split_digest(N)
        if u[14] == 0:
            break
    else:
        return None
    # (2) FORS
    fors = []
    roots = []
    for k in range(FTS_TREES):
        level = []
        secret = None
        for j in range(1 << FTS_A):
            s = Th(o, tweak(8, k, idx, 0, j), S)
            if j == u[k]:
                secret = s
            level.append(Th(o, tweak(9, k, idx, 0, j), s))
        path = []
        for lam in range(1, FTS_A + 1):
            path.append(level[(u[k] >> (lam - 1)) ^ 1])
            level = [Th(o, tweak(10, k, idx, lam, j), level[2 * j] + level[2 * j + 1])
                     for j in range(len(level) // 2)]
        roots.append(level[0])
        fors.append((secret, path))
    M = Th(o, tweak(11, 0, idx, 0, 0), b''.join(roots))
    # (3) layers bottom-up
    layers = [None] * LAYERS
    for lay in range(LAYERS - 1, -1, -1):
        e, tau = route(idx, lay)
        for c in range(C_MAX):
            x = decode_digest(Th(o, tweak(4, lay, tau, 0, e), M + le32(c)))
            if x is not None:
                break
        else:
            return None
        root, vals, path = build_tree(o, S, lay, tau, HEIGHTS[lay], e, x)
        layers[lay] = (c, vals, path)
        M = root
    # (4) serialize
    out = [rho]
    for secret, path in fors:
        out.append(secret)
        out.extend(path)
    for c, vals, path in layers:
        out.append(le32(c))
        out.extend(vals)
        out.extend(path)
    sig = b''.join(out)
    assert len(sig) == SIG_BYTES
    return sig


# ------------------------------------------------------------------ parsing / witness
def parse(sig):
    assert len(sig) == SIG_BYTES
    rho = sig[0:16]
    pos = 16
    fors = []
    for k in range(FTS_TREES):
        s = sig[pos:pos + 16]
        path = [sig[pos + 16 + 16 * l:pos + 32 + 16 * l] for l in range(FTS_A)]
        fors.append((s, path))
        pos += 16 * (1 + FTS_A)
    layers = []
    for lay in range(LAYERS):
        c = int.from_bytes(sig[pos:pos + 4], 'little')
        pos += 4
        vals = [sig[pos + 16 * i:pos + 16 * i + 16] for i in range(N_CHAINS)]
        pos += 16 * N_CHAINS
        path = [sig[pos + 16 * l:pos + 16 * l + 16] for l in range(HEIGHTS[lay])]
        pos += 16 * HEIGHTS[lay]
        layers.append((c, vals, path))
    assert pos == SIG_BYTES
    return rho, fors, layers


def sig_layer_offset(lay):
    return 16 + FTS_TREES * 176 + sum(4 + 672 + 16 * HEIGHTS[l] for l in range(lay))


def wit_layer_offset(lay):
    return 16 + FTS_TREES * 176 + sum(672 + 16 * HEIGHTS[l] for l in range(lay))


WIT_COUNTERS = wit_layer_offset(LAYERS)       # 7728


def to_witness(sig, mode='perm'):
    """'perm': rho || FORS || (chains, path)_{lay=0..6} || LE32(c_0..c_6)  (all 16-byte items
    8-aligned); 'copy': the signature itself."""
    if mode == 'copy':
        return bytes(sig)
    head = sig[:16 + FTS_TREES * 176]
    body = []
    ctrs = []
    for lay in range(LAYERS):
        o = sig_layer_offset(lay)
        n = 672 + 16 * HEIGHTS[lay]
        ctrs.append(sig[o:o + 4])
        body.append(sig[o + 4:o + 4 + n])
    w = head + b''.join(body) + b''.join(ctrs)
    assert len(w) == SIG_BYTES
    return w


def from_witness(w, mode='perm'):
    if mode == 'copy':
        return bytes(w)
    head = w[:16 + FTS_TREES * 176]
    out = [head]
    for lay in range(LAYERS):
        o = wit_layer_offset(lay)
        n = 672 + 16 * HEIGHTS[lay]
        out.append(w[WIT_COUNTERS + 4 * lay:WIT_COUNTERS + 4 * lay + 4])
        out.append(w[o:o + n])
    s = b''.join(out)
    assert len(s) == SIG_BYTES
    return s


# ------------------------------------------------------------------ verification
def fold(o, t, lay, tau, leaf, value, path):
    """TreeFold / FtsFold: tweak (t, lay, tau, lambda+1, leaf >> (lambda+1)); current value first
    iff bit lambda of leaf is zero."""
    for lam in range(len(path)):
        tw = tweak(t, lay, tau, lam + 1, leaf >> (lam + 1))
        if (leaf >> lam) & 1:
            value = Th(o, tw, path[lam] + value)
        else:
            value = Th(o, tw, value + path[lam])
    return value


def verify(o, pk, m, sig):
    """Concrete.verify (SPEC variant), preceded by the counter range check (no queries)."""
    rho, fors, layers = parse(sig)
    if any(c >= C_MAX for c, _, _ in layers):
        return False
    N = message_digest(o, rho, m)
    idx, u = split_digest(N)
    if u[14] != 0:
        return False
    roots = []
    for k in range(FTS_TREES):
        s, path = fors[k]
        v = Th(o, tweak(9, k, idx, 0, u[k]), s)
        roots.append(fold(o, 10, k, idx, u[k], v, path))
    M = Th(o, tweak(11, 0, idx, 0, 0), b''.join(roots))
    for lay in range(LAYERS - 1, -1, -1):
        e, tau = route(idx, lay)
        c, vals, path = layers[lay]
        x = decode_digest(Th(o, tweak(4, lay, tau, 0, e), M + le32(c)))
        if x is None:
            return False
        ends = []
        for i in range(N_CHAINS):
            v = vals[i]
            for mu in range(x[i] + 1, 8):
                v = Th(o, tweak(1, lay, tau, 8 * i + mu - 1, e), v)
            ends.append(v)
        leaf = Th(o, tweak(2, lay, tau, 0, e), b''.join(ends))
        M = fold(o, 3, lay, tau, e, leaf, path)
    return M == pk


def verify_witness(o, pk, m, w, mode='perm'):
    return verify(o, pk, m, from_witness(w, mode))


if __name__ == '__main__':
    import os, time
    S = os.urandom(32)
    m = os.urandom(32)
    o = Oracle(log=False)
    t = time.time()
    pk = keygen(o, S)
    print('keygen', o.calls, o.compressions, time.time() - t)
    o = Oracle(log=False)
    t = time.time()
    sig = sign(o, S, m)
    print('sign', o.calls, o.compressions, time.time() - t)
    o = Oracle(log=False)
    print('verify', verify(o, pk, m, sig), o.calls, o.compressions)
