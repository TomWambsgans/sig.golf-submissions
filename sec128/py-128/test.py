"""Differential tests: ref.py (SPHINCS-golf-128) vs the four RISC-V images on vm.py.

usage: python3 test.py [--keys N] [--msgs N] [--moment N] [--tables N] [--slow]
"""
import argparse, hashlib, math, os, random, sys, time
import ref, vm, gen

p = argparse.ArgumentParser()
p.add_argument('--keys', type=int, default=2)
p.add_argument('--msgs', type=int, default=3)
p.add_argument('--moment', type=int, default=200)
p.add_argument('--tables', type=int, default=256, help='table-cover runs (256 = every pair-table entry)')
p.add_argument('--slow', action='store_true', help='worst-case / exhaustion runs')
args = p.parse_args()

images, asms, vg = gen.build_all()
SIZES, LAYOUT = gen.SIZES, gen.LAYOUT
FAILS = []
NCH = ref.N_CHAINS


def check(cond, what):
    if not cond:
        FAILS.append(what)
        print('  FAIL:', what, flush=True)


def run(phase, inp, fn=None, fuel=vm.CYCLE_LIMIT):
    o = vm.Oracle(fn=fn)
    return vm.run_phase(images, SIZES, LAYOUT, phase, inp, o, fuel)


def vm_verify(pk, m, w, fn=None):
    val, res = run('verify', {'msg': m, 'pk': pk, 'wit': w}, fn)
    return res.exit == 'success', res


def ref_verify_w(pk, m, w, fn=None):
    o = ref.Oracle(fn=fn)
    return ref.verify_witness(o, pk, m, w), o


def n7_of_witness(pk, m, w, fn=None):
    """digits equal to 7 in the encodings a verification of w computes (ref)."""
    o = ref.Oracle(fn=fn)
    n7 = 0
    orig = o.H

    def H(x):
        ans = orig(x)
        if x[1] == 4 and len(x) == 64:
            d = ref.decode_digits(ans)
            if d is not None:
                nonlocal n7
                n7 += sum(1 for v in d if v == 7)
        return ans
    o.H = H
    ref.verify_witness(o, pk, m, w)
    return n7


print('scheme: 128-bit variant, T=%d, %d chains, S=%d W=%d' % (ref.TARGET, NCH, *SIZES))
for k, (code, data) in images.items():
    print('  %-7s %6d instructions  %7d image bytes' % (k, len(code), 4 * len(code) + len(data)))
print('layout', {k: hex(v) for k, v in LAYOUT.items()})

rng = random.Random(1)
bounds = set()
stats = {}
for kk in range(args.keys):
    S = bytes(rng.getrandbits(8) for _ in range(32))
    o = ref.Oracle()
    pk, rcache = ref.keygen(o, S)
    (vpk, vcache), res = run('keygen', {'sk': S})
    check(res.exit == 'success' and vpk == pk, 'keygen output')
    check(vcache == rcache, 'keygen cache (tag | masked top tree | b bytes | sigma | 0)')
    check(res.oracle.log == o.log, 'keygen query sequence')
    stats['keygen'] = (res.cycles, res.hash_calls, res.compressions, res.steps)
    sigma = rcache[32 + ref.SIGMA_REG]
    print('key %d: sigma = %d' % (kk, sigma))
    # ---------------- tampered caches: sign fails after exactly the MAC query
    for what, off in (('tag', 7), ('region lo', 32 + 16 * 5 + 3), ('region b byte', 32 + 16 * ref.NODES_CACHED + 17),
                      ('pad', 32 + ref.SIGMA_REG - 1), ('sigma', 32 + ref.SIGMA_REG + 1)):
        bad = bytearray(rcache)
        bad[off] ^= 1 << rng.randrange(8)
        o = ref.Oracle()
        r1 = ref.sign(o, S, bytes(bad), bytes(32))
        v2, res2 = run('sign', {'sk': S, 'msg': bytes(32), 'cache': bytes(bad)})
        check(r1 is None and res2.exit == 'failure' and o.calls == 1 and res2.hash_calls == 1
              and res2.oracle.log == o.log, 'tampered cache (%s) fails with exactly the MAC query' % what)
    junk_tail = rcache[:32 + ref.REGION_BYTES] + bytes(rng.getrandbits(8) for _ in range(vm.CACHE_BYTES - 32 - ref.REGION_BYTES))
    for mm in range(args.msgs):
        m = bytes(rng.getrandbits(8) for _ in range(32))
        o = ref.Oracle()
        cache = junk_tail if mm % 2 else rcache
        sig = ref.sign(o, S, cache, m)
        vsig, res = run('sign', {'sk': S, 'msg': m, 'cache': cache})
        check(res.exit == 'success' and vsig == sig, 'sign output')
        check(res.oracle.log == o.log, 'sign query sequence')
        stats.setdefault('sign', []).append((res.cycles, res.hash_calls, res.compressions, res.steps))
        w, res = run('expand', {'msg': m, 'pk': pk, 'sig': sig})
        check(res.exit == 'success' and w == ref.to_witness(sig), 'expand output')
        check(ref.from_witness(w) == sig, 'from_witness inverts expand')
        check(res.hash_calls == 0, 'expand hashes')
        stats['expand'] = (res.cycles, res.hash_calls, res.compressions, res.steps)
        bad = bytearray(sig)
        bad[-1] |= 1 << (7 - rng.randrange(8 * ref.SIG_BYTES - 8 * ref.CORE - ref.SMALL_BITS))
        _, res = run('expand', {'msg': m, 'pk': pk, 'sig': bytes(bad)})
        check(res.exit == 'failure' and ref.to_witness(bytes(bad)) is None, 'non-canonical signature (spare bit) rejected by expand')
        ok_r, o = ref_verify_w(pk, m, w)
        ok_v, res = vm_verify(pk, m, w)
        check(ok_r and ok_v, 'honest verify accepts')
        check(res.oracle.log == o.log, 'verify query sequence')
        n7 = n7_of_witness(pk, m, w)
        bounds.add(res.cycles + n7)
        stats['verify'] = (res.cycles, res.hash_calls, res.compressions, res.steps)
        print('  msg %d: verify cycles %d (+%d digits = 7 -> %d)' % (mm, res.cycles, n7, res.cycles + n7), flush=True)
        honest = res.cycles + n7

        # ---------------- corruptions (witness level, both implementations)
        LO = ref.LAYER_OFF
        spots = {'rho': [0, 15], 'r': [ref.R_OFF, ref.R_OFF + 5],
                 'fors_s': [16 + 176 * k2 for k2 in (0, 7, 13)],
                 'fors_s.b': [ref.FB_OFF + 11 * k2 for k2 in (0, 13)],
                 'fors_path': [32 + 176 * k2 + 16 * l + 5 for k2, l in ((0, 0), (9, 9), (13, 4))],
                 'fors_path.b': [ref.FB_OFF + 11 * k2 + 1 + l for k2, l in ((0, 0), (9, 9), (13, 4))
                                 if l < ref.FB_BITS - 1],
                 'counter': [ref.CTR_OFF + 4 * l for l in range(ref.LAYERS)],
                 'sigma': [ref.SIGMA_OFF],
                 'chain': [LO[l] + 16 * i + 3 for l, i in ((0, 0), (3, 20), (4, 42), (1, 21), (2, 41))],
                 'chain.hi': [ref.HI_OFF + NCH * l + i for l, i in ((0, 0), (3, 20), (4, 42), (1, 21))],
                 'path': [LO[l] + 16 * NCH + 16 * j for l, j in ((0, 0), (0, 10), (4, 3), (2, 5))],
                 'path.b': [ref.PB_OFF + ref.PB_LAY[l] + j for l, j in ((0, 0), (0, 10), (4, 3), (2, 5))]}
        for kind, offs in spots.items():
            for off in offs:
                bad = bytearray(w)
                bad[off] ^= 1 << (rng.randrange(8) if not kind.endswith('.b') else 0)
                bad = bytes(bad)
                r1, o1 = ref_verify_w(pk, m, bad)
                r2, res2 = vm_verify(pk, m, bad)
                check(not r1 and not r2, 'reject corrupted %s @%d' % (kind, off))
                check(o1.log == res2.oracle.log, 'reject query seq %s @%d' % (kind, off))
                check(res2.cycles <= honest, 'reject cycles <= honest bound')
        cb = ref.C_MAX.bit_length() - 1
        for lay in (0, ref.LAYERS - 1, 3):
            bad = bytearray(w)
            off = ref.CTR_OFF + 4 * lay
            c = int.from_bytes(w[off:off + 4], 'little') | (1 << (cb + rng.randrange(32 - cb)))
            bad[off:off + 4] = c.to_bytes(4, 'little')
            r1, o1 = ref_verify_w(pk, m, bytes(bad))
            r2, res2 = vm_verify(pk, m, bytes(bad))
            check(not r1 and not r2 and o1.calls == 0 and res2.hash_calls == 0, 'counter >= C_MAX rejected before hashing')
        m2 = bytes([m[0] ^ 1]) + m[1:]
        r1, o1 = ref_verify_w(pk, m2, w)
        r2, res2 = vm_verify(pk, m2, w)
        check(not r1 and not r2 and o1.log == res2.oracle.log, 'wrong message rejected')
        pk2 = bytes([pk[0] ^ 0x80]) + pk[1:]
        r1, o1 = ref_verify_w(pk2, m, w)
        r2, res2 = vm_verify(pk2, m, w)
        check(not r1 and not r2 and o1.log == res2.oracle.log, 'wrong pk rejected')
        check(res2.cycles <= honest, 'wrong-pk run costs at most the honest bound')
        # non-admissible digest: random r
        for t in range(100):
            rr = rng.getrandbits(64)
            _, _, ok = ref.split_digest(ref.Oracle().H(ref.digest_block(rr, w[0:16], m)))
            if not ok:
                break
        bad = bytearray(w)
        bad[ref.R_OFF:ref.R_OFF + 8] = rr.to_bytes(8, 'little')
        r1, o1 = ref_verify_w(pk, m, bytes(bad))
        r2, res2 = vm_verify(pk, m, bytes(bad))
        check(not r1 and not r2 and o1.calls == 1 and res2.hash_calls == 1, 'non-admissible digest rejected')
        junk = bytes(rng.getrandbits(8) for _ in range(SIZES[1]))
        r1, o1 = ref_verify_w(pk, m, junk)
        r2, res2 = vm_verify(pk, m, junk)
        check(not r1 and not r2 and o1.log == res2.oracle.log, 'random witness rejected')
        bad = bytearray(sig)
        bad[ref.LAYER_OFF[4] + 16 * 9] ^= 4
        w3, _ = run('expand', {'msg': m, 'pk': pk, 'sig': bytes(bad)})
        r2, _ = vm_verify(pk, m, w3)
        check(not ref.verify(ref.Oracle(), pk, m, bytes(bad)) and not r2, 'corrupted signature via expand')
    print('key %d done' % kk, flush=True)

print('\n== honest costs')
print('keygen  cycles=%d hashes=%d compressions=%d steps=%d' % stats['keygen'])
for s in stats['sign']:
    print('sign    cycles=%d hashes=%d compressions=%d steps=%d' % s)
print('expand  cycles=%d hashes=%d compressions=%d steps=%d' % stats['expand'])
print('verify  cycles=%d hashes=%d compressions=%d steps=%d' % stats['verify'])
print('verify cycles + #(digits = 7) over all honest runs:', sorted(bounds), 'constant' if len(bounds) == 1 else 'NOT CONSTANT')
check(len(bounds) == 1, 'verify cycles + n7 constant')
W = SIZES[1]
VB = max(bounds)
C = VB + (W + 255) // 256
print('C = max verify cycles (no digit 7) + ceil(W/256) = %d + %d = %d ; S = %d ; score S*C = %d'
      % (VB, (W + 255) // 256, C, SIZES[0], SIZES[0] * C))


def force_digest(y):
    h = bytearray(hashlib.sha256(y).digest())
    h[21] &= 0x3f; h[22] = 0; h[23] &= 0xfe      # bits 174..184 = 0
    return bytes(h)


def enc_answer(x, y):
    d0 = sum(v << (3 * i) for i, v in enumerate(x[:21]))
    d1 = sum(v << (3 * i) for i, v in enumerate(x[21:42]))
    rest = bytearray(hashlib.sha256(y).digest()[16:])
    rest[0] = (rest[0] & 0xf8) | x[42]
    return d0.to_bytes(8, 'little') + d1.to_bytes(8, 'little') + bytes(rest)


def fix_sum(x, free, r2):
    while True:
        for i in free:
            x[i] = r2.randrange(8)
        s = sum(x)
        while s < ref.TARGET:
            i = r2.choice(free)
            if x[i] < 7:
                x[i] += 1; s += 1
        while s > ref.TARGET:
            i = r2.choice(free)
            if x[i] > 0:
                x[i] -= 1; s -= 1
        if s == ref.TARGET:
            return x


# ---------------- adversarial oracle: forced admissible digest, valid encodings with no digit 7
print('\n== full-length runs on junk witnesses (forced valid encodings)')
def patterned(seed, allow7):
    def fn(y):
        if y[1] == 4 and len(y) == 64:
            r2 = random.Random(hashlib.sha256(bytes([seed]) + y).digest())
            x = [0] * NCH
            while True:
                x = [r2.randrange(8 if allow7 else 7) for _ in range(NCH)]
                s = sum(x)
                while s < ref.TARGET:
                    i = r2.randrange(NCH)
                    if x[i] < (7 if allow7 else 6):
                        x[i] += 1; s += 1
                while s > ref.TARGET:
                    i = r2.randrange(NCH)
                    if x[i] > 0:
                        x[i] -= 1; s -= 1
                break
            return enc_answer(x, y)
        if y[1] == 12:
            return force_digest(y)
        return hashlib.sha256(y).digest()
    return fn


def junk_witness(seed):
    junk = bytearray(random.Random(seed).getrandbits(8) for _ in range(W))
    junk[ref.CTR_OFF:ref.CTR_OFF + 20] = bytes(20)          # counters small
    return bytes(junk)


cyc = set()
for seed in range(6):
    fn = patterned(seed, allow7=(seed % 2 == 1))
    junk = junk_witness(seed)
    r1, o1 = ref_verify_w(bytes(16), bytes(32), junk, fn)
    r2, res2 = vm_verify(bytes(16), bytes(32), junk, fn)
    check(r1 == r2 and o1.log == res2.oracle.log, 'forced-digit run agrees')
    n7 = n7_of_witness(bytes(16), bytes(32), junk, fn)
    cyc.add(res2.cycles + n7)
print('cycles + n7 of full-length runs:', sorted(cyc))
check(max(cyc) <= VB, 'full-length runs <= honest bound')

# ---------------- every entry of every dispatch table
PAIRS = [(q * 21 + r, q * 21 + r + 1) for q in range(2) for r in range(0, 20, 2)]
SINGLES16 = [20, 41]


def table_cover(rn):
    def fn(y):
        if y[1] == 4 and len(y) == 64:
            lay = y[2]
            r2 = random.Random(hashlib.sha256(bytes([rn & 255, rn >> 8]) + y).digest())
            x = [None] * NCH
            for k, (i, j) in enumerate(PAIRS):
                if (k + lay + rn) % 4 == 0:
                    c = ((rn >> 2) + 9 * k + 5 * lay) % 64
                    x[i], x[j] = c & 7, c >> 3
            if (lay + rn) % 3 == 0:
                x[42] = (rn + lay) % 8
            free = [i for i in range(NCH) if x[i] is None]
            x = fix_sum(x, free, r2)
            ans = bytearray(enc_answer(x, y))
            # bits 63 / 127 (entries 8..15 of the single16 tables): random
            if (rn >> 1) & 1:
                ans[7] |= 0x80
            if (rn >> 2) & 1:
                ans[15] |= 0x80
            return bytes(ans)
        if y[1] == 12:
            return force_digest(y)
        return hashlib.sha256(y).digest()
    return fn


cyc = set()
t = time.time()
for rn in range(args.tables):
    fn = table_cover(rn)
    junk = junk_witness(1000 + rn)
    r1, o1 = ref_verify_w(bytes(16), bytes(32), junk, fn)
    r2, res2 = vm_verify(bytes(16), bytes(32), junk, fn)
    check(r1 == r2 and o1.log == res2.oracle.log, 'table-cover run %d agrees' % rn)
    n7 = n7_of_witness(bytes(16), bytes(32), junk, fn)
    cyc.add(res2.cycles + n7)
print('table cover (%d runs, %.0fs): cycles + n7 %s' % (args.tables, time.time() - t, sorted(cyc)))
check(max(cyc) <= VB, 'table-cover runs <= honest bound')

# ---------------- compression moment
print('\n== sign compression moment over %d signings (ref)' % args.moment)
S = os.urandom(32)
_, mcache = ref.keygen(ref.Oracle(log=False), S)
Ks = []
t = time.time()
for i in range(args.moment):
    o = ref.Oracle(log=False)
    assert ref.sign(o, S, mcache, os.urandom(32)) is not None
    Ks.append(o.compressions)
if Ks:
    E = sum(2 ** (k / 2 ** 17) for k in Ks) / len(Ks)
    print('K: min %d mean %.1f max %d ; E[2^(K/2^17)] = %.4f  (%.1fs)' % (min(Ks), sum(Ks) / len(Ks), max(Ks), E, time.time() - t))
prf = ref.STREAM_Q
det = (1089 + 2 + ref.FTS_TREES * (4 + 512 + 1024 + 1023) + 4
       + sum((prf + 7 * NCH + 12) * 2 ** h + 2 ** h - 1 for h in ref.HEIGHTS[1:])
       + prf + ref.TARGET + ref.TOP_H)
cnt = [1]
for _ in range(NCH):
    n = [0] * (len(cnt) + 7)
    for i, c in enumerate(cnt):
        for d in range(8):
            n[i + d] += c
    cnt = n
alpha = cnt[ref.TARGET] / 2 ** (3 * NCH)


def geo_mgf(p, cost):
    z = 2 ** (cost / 2 ** 17)
    return p * z / (1 - (1 - p) * z)


Ean = 2 ** (det / 2 ** 17) * geo_mgf(2 ** -ref.PIN_BITS, 1) * geo_mgf(alpha, 1) ** ref.LAYERS
print('analytic: deterministic %d compressions, alpha = 2^%.3f, E = %.4f' % (det, math.log2(alpha), Ean))
check(Ean <= 2, 'analytic moment <= 2')
kg = stats['keygen'][2]
print('keygen compressions %d: 2^(N/2^20) = %.4f (+ root salt search, E[extra] = 1)' % (kg, 2 ** (kg / 2 ** 20)))

if args.slow:
    print('\n== worst-case sign (digest only at a = A_MAX-1, every enc only at c = C_MAX-1)')
    LASTA, LASTC = ref.A_MAX - 1, ref.C_MAX - 1
    q7, r7 = divmod(ref.TARGET, 7)
    x = [7] * q7 + [r7] + [0] * (NCH - 1 - q7)
    GOOD = enc_answer(x, b'')[:16] + bytes([x[42]]) + bytes(15)

    def worst(y):
        t = y[1]
        if t == 12:
            a_ = int.from_bytes(y[12:16], 'little')
            return bytes(32) if a_ == LASTA else b'\xff' * 32
        if t == 4 and len(y) == 64:
            c = int.from_bytes(y[56:60], 'little')
            return GOOD if c == LASTC else bytes(32)
        if t == 3 and y[2] == 0 and y[12] == 1 and y[13] == 0:   # top root: make sigma = 255 succeed
            return bytes(32) if y[4] == 255 else b'\xff' * 32
        return hashlib.sha256(y).digest()
    S = bytes(32)
    kr = ref.keygen(ref.Oracle(log=False, fn=worst), S)
    (vpk, wcache), res = run('keygen', {'sk': S}, worst)
    check(kr is not None and (vpk, wcache) == kr, 'worst-case keygen (sigma = 255) agrees')
    print('keygen with sigma = 255: cycles %d' % res.cycles)
    t = time.time()
    sigw = ref.sign(ref.Oracle(log=False, fn=worst), S, wcache, bytes(32))
    vs, res = run('sign', {'sk': S, 'msg': bytes(32), 'cache': wcache}, worst)
    check(res.exit == 'success' and vs == sigw, 'worst-case sign agrees with ref')
    print('worst sign: cycles=%d steps=%d compressions=%d (%.0fs)  < 2^32: %s' % (
        res.cycles, res.steps, res.compressions, time.time() - t, res.cycles < 2 ** 32))
    okv, resv = vm_verify(kr[0], bytes(32), ref.to_witness(sigw), worst)
    check(okv, 'worst-case signature verifies')
    nokey = lambda y: b'\xff' * 32 if (y[1] == 3 and y[2] == 0 and y[12] == 1 and y[13] == 0) else hashlib.sha256(y).digest()
    _, res = run('keygen', {'sk': S}, nokey)
    check(res.exit == 'failure' and ref.keygen(ref.Oracle(log=False, fn=nokey), S) is None, 'keygen salt exhaustion fails')
    print('keygen salt search exhausted: exit=%s cycles=%d' % (res.exit, res.cycles))
    never = lambda y: b'\xff' * 32 if y[1] == 12 else hashlib.sha256(y).digest()
    _, ncache = ref.keygen(ref.Oracle(log=False, fn=never), S)
    vs, res = run('sign', {'sk': S, 'msg': bytes(32), 'cache': ncache}, never)
    check(res.exit == 'failure' and ref.sign(ref.Oracle(log=False, fn=never), S, ncache, bytes(32)) is None,
          'digest exhaustion fails')
    print('digest search exhausted: exit=%s cycles=%d' % (res.exit, res.cycles))
    noenc = lambda y: bytes(32) if y[1] == 4 else (force_digest(y) if y[1] == 12 else hashlib.sha256(y).digest())
    _, ecache = ref.keygen(ref.Oracle(log=False, fn=noenc), S)
    vs, res = run('sign', {'sk': S, 'msg': bytes(32), 'cache': ecache}, noenc)
    check(res.exit == 'failure' and ref.sign(ref.Oracle(log=False, fn=noenc), S, ecache, bytes(32)) is None,
          'encoding exhaustion fails')
    print('bottom-layer encoding search exhausted: exit=%s cycles=%d' % (res.exit, res.cycles))

print('\nRESULT:', 'ALL PASSED' if not FAILS else '%d FAILURES' % len(FAILS))
sys.exit(1 if FAILS else 0)
