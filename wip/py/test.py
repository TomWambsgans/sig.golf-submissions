"""Differential tests: ref.py (abstract scheme) vs the four RISC-V images on vm.py.

usage: python3 test.py [--mode perm|copy] [--keys N] [--msgs N] [--moment N] [--slow]
"""
import argparse, hashlib, math, os, random, sys, time
import ref, vm, gen

p = argparse.ArgumentParser()
p.add_argument('--mode', default='perm')
p.add_argument('--keys', type=int, default=3)
p.add_argument('--msgs', type=int, default=3)
p.add_argument('--moment', type=int, default=200)
p.add_argument('--slow', action='store_true', help='worst-case / exhaustion runs (several minutes)')
args = p.parse_args()
MODE = args.mode

images, asms, vg = gen.build_all(MODE)
SIZES, LAYOUT = gen.SIZES, gen.LAYOUT
FAILS = []


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
    return ref.verify_witness(o, pk, m, w, MODE), o


print('mode', MODE)
for k, (code, data) in images.items():
    print('  %-7s %6d instructions  %7d image bytes' % (k, len(code), 4 * len(code) + len(data)))
print('layout', {k: hex(v) for k, v in LAYOUT.items()}, 'S=%d W=%d' % SIZES)

rng = random.Random(1)
verify_cycles = set()
stats = {}
for kk in range(args.keys):
    S = bytes(rng.getrandbits(8) for _ in range(32))
    o = ref.Oracle()
    pk = ref.keygen(o, S)
    (vpk, cache), res = run('keygen', {'sk': S})
    check(res.exit == 'success' and vpk == pk, 'keygen output')
    check(cache == bytes(vm.CACHE_BYTES), 'keygen cache zero')
    check(res.oracle.log == o.log, 'keygen query sequence')
    stats['keygen'] = (res.cycles, res.hash_calls, res.compressions, res.steps)
    for mm in range(args.msgs):
        m = bytes(rng.getrandbits(8) for _ in range(32))
        o = ref.Oracle()
        sig = ref.sign(o, S, m)
        cache = bytes(rng.getrandbits(8) for _ in range(vm.CACHE_BYTES)) if mm % 2 else bytes(vm.CACHE_BYTES)
        vsig, res = run('sign', {'sk': S, 'msg': m, 'cache': cache})
        check(res.exit == 'success' and vsig == sig, 'sign output')
        check(res.oracle.log == o.log, 'sign query sequence')
        stats.setdefault('sign', []).append((res.cycles, res.hash_calls, res.compressions, res.steps))
        w, res = run('expand', {'msg': m, 'pk': pk, 'sig': sig})
        check(res.exit == 'success' and w == ref.to_witness(sig, MODE), 'expand output')
        check(res.hash_calls == 0, 'expand hashes')
        stats['expand'] = (res.cycles, res.hash_calls, res.compressions, res.steps)
        ok_r, o = ref_verify_w(pk, m, w)
        ok_v, res = vm_verify(pk, m, w)
        check(ok_r and ok_v, 'honest verify accepts')
        check(res.oracle.log == o.log, 'verify query sequence')
        verify_cycles.add(res.cycles)
        stats['verify'] = (res.cycles, res.hash_calls, res.compressions, res.steps)

        # ---------------- corruptions (witness level, both implementations)
        wl = lambda lay: ref.wit_layer_offset(lay) if MODE == 'perm' else ref.sig_layer_offset(lay) + 4
        ctr = lambda lay: ref.WIT_COUNTERS + 4 * lay if MODE == 'perm' else ref.sig_layer_offset(lay)
        spots = {'rho': [0, 15], 'fors_s': [16 + 176 * k2 for k2 in (0, 7, 13)],
                 'fors_path': [32 + 176 * k2 + 16 * l + 5 for k2, l in ((0, 0), (9, 9), (13, 4))],
                 'counter': [ctr(l) for l in range(7)],
                 'chain': [wl(l) + 16 * i + 3 for l, i in ((0, 0), (3, 20), (6, 41), (5, 21))],
                 'path': [wl(l) + 672 + 16 * j for l, j in ((0, 0), (0, 4), (6, 3), (2, 2))]}
        for kind, offs in spots.items():
            for off in offs:
                bad = bytearray(w)
                bad[off] ^= 1 << rng.randrange(8)
                bad = bytes(bad)
                r1, o1 = ref_verify_w(pk, m, bad)
                r2, res2 = vm_verify(pk, m, bad)
                check(not r1 and not r2, 'reject corrupted %s @%d' % (kind, off))
                check(o1.log == res2.oracle.log, 'reject query seq %s @%d' % (kind, off))
                check(res2.cycles <= res.cycles, 'reject cycles <= honest')
        # counters >= 2^20 (with the low bits honest)
        for lay in (0, 6, 3):
            bad = bytearray(w)
            c = int.from_bytes(w[ctr(lay):ctr(lay) + 4], 'little') | (1 << (20 + rng.randrange(12)))
            bad[ctr(lay):ctr(lay) + 4] = c.to_bytes(4, 'little')
            r1, o1 = ref_verify_w(pk, m, bytes(bad))
            r2, res2 = vm_verify(pk, m, bytes(bad))
            check(not r1 and not r2 and o1.calls == 0 and res2.hash_calls == 0, 'counter >= 2^20 rejected before hashing')
        # wrong message / wrong key
        m2 = bytes([m[0] ^ 1]) + m[1:]
        r1, o1 = ref_verify_w(pk, m2, w)
        r2, res2 = vm_verify(pk, m2, w)
        check(not r1 and not r2 and o1.log == res2.oracle.log, 'wrong message rejected')
        pk2 = bytes([pk[0] ^ 0x80]) + pk[1:]
        r1, o1 = ref_verify_w(pk2, m, w)
        r2, res2 = vm_verify(pk2, m, w)
        check(not r1 and not r2 and o1.log == res2.oracle.log, 'wrong pk rejected')
        check(res2.cycles <= res.cycles, 'wrong-pk run costs at most the honest cycles')
        # non-admissible randomizer: search rho with u_14 != 0
        for t in range(100):
            rho = bytes(rng.getrandbits(8) for _ in range(16))
            N = ref.message_digest(ref.Oracle(), rho, m)
            if (N >> 174) & 1023:
                break
        bad = rho + w[16:]
        r1, o1 = ref_verify_w(pk, m, bad)
        r2, res2 = vm_verify(pk, m, bad)
        check(not r1 and not r2 and o1.calls == 1 and res2.hash_calls == 1, 'non-admissible rho rejected')
        # random witness
        junk = bytes(rng.getrandbits(8) for _ in range(SIZES[1]))
        r1, o1 = ref_verify_w(pk, m, junk)
        r2, res2 = vm_verify(pk, m, junk)
        check(not r1 and not r2 and o1.log == res2.oracle.log, 'random witness rejected')
        # signature-level corruption through expand
        bad = bytearray(sig)
        bad[ref.sig_layer_offset(4) + 4 + 16 * 9] ^= 4
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
print('verify cycles over all honest runs:', sorted(verify_cycles), 'constant' if len(verify_cycles) == 1 else 'NOT CONSTANT')
check(len(verify_cycles) == 1, 'verify cycles constant')
W = SIZES[1]
C = max(verify_cycles) + (W + 255) // 256
print('C = verify cycles + ceil(W/256) = %d + %d = %d ; score S*C = %d' % (max(verify_cycles), (W + 255) // 256, C, SIZES[0] * C))

# ---------------- adversarial oracle: every enc check passes digit-wise (exercise all x values)
print('\n== dispatch coverage: forced digit patterns')
def patterned(seed):
    def fn(y):
        if y[1] == 4:
            r2 = random.Random(hashlib.sha256(bytes([seed]) + y).digest())
            while True:
                x = [r2.randrange(8) for _ in range(42)]
                s = sum(x)
                if s <= 170:
                    # push digits up to reach 170
                    while s < 170:
                        i = r2.randrange(42)
                        if x[i] < 7:
                            x[i] += 1; s += 1
                    break
            d0 = sum(v << (3 * i) for i, v in enumerate(x[:21]))
            d1 = sum(v << (3 * i) for i, v in enumerate(x[21:]))
            return d0.to_bytes(8, 'little') + d1.to_bytes(8, 'little') + hashlib.sha256(y).digest()[16:]
        if y[1] == 12:
            h = bytearray(hashlib.sha256(y).digest())
            h[21] &= 0x3f; h[22] = 0   # force u_14 = 0 (bits 174..183)
            return bytes(h)
        return hashlib.sha256(y).digest()
    return fn
cyc = set()
for seed in range(6):
    fn = patterned(seed)
    junk = bytes(random.Random(seed).getrandbits(8) for _ in range(W))
    if MODE == 'perm':   # keep counters small
        junk = junk[:ref.WIT_COUNTERS] + bytes(28)
    else:
        jb = bytearray(junk)
        for lay in range(7):
            jb[ref.sig_layer_offset(lay):ref.sig_layer_offset(lay) + 4] = bytes(4)
        junk = bytes(jb)
    pkx = bytes(16)
    r1, o1 = ref_verify_w(pkx, bytes(32), junk, fn)
    r2, res2 = vm_verify(pkx, bytes(32), junk, fn)
    check(r1 == r2 and o1.log == res2.oracle.log, 'forced-digit run agrees')
    cyc.add(res2.cycles)
print('full-length verify runs on junk witnesses (forced valid encodings): cycles', sorted(cyc))
check(len(cyc) == 1 and max(cyc) <= min(verify_cycles), 'full-length runs are constant and <= honest constant')

# ---------------- compression moment
print('\n== sign compression moment over %d signings (ref)' % args.moment)
S = os.urandom(32)
Ks = []
t = time.time()
for i in range(args.moment):
    o = ref.Oracle(log=False)
    assert ref.sign(o, S, os.urandom(32)) is not None
    Ks.append(o.compressions)
E = sum(2 ** (k / 2 ** 17) for k in Ks) / len(Ks)
print('K: min %d mean %.1f max %d ; E[2^(K/2^17)] = %.4f  (%.1fs)' % (min(Ks), sum(Ks) / len(Ks), max(Ks), E, time.time() - t))
# analytic value: deterministic part + geometric grind (4 per trial, p = 2^-10) + 7 enc searches
det = 14 * (3 * 1024 - 1) + 4 + 6 * 32 * 347 + 16 * 347 + 6 * 31 + 15
cnt = [1]
for _ in range(42):
    n = [0] * (len(cnt) + 7)
    for i, c in enumerate(cnt):
        for d in range(8):
            n[i + d] += c
    cnt = n
alpha = cnt[170] / 8 ** 42 / 4
def geo_mgf(p, cost):      # E[2^(cost*G/B)], G ~ Geometric(p) on {1,2,..}
    z = 2 ** (cost / 2 ** 17)
    return p * z / (1 - (1 - p) * z)
Ean = 2 ** (det / 2 ** 17) * geo_mgf(2 ** -10, 4) * geo_mgf(alpha, 1) ** 7
print('analytic: deterministic %d compressions, alpha = 2^%.3f, E = %.4f' % (det, math.log2(alpha), Ean))
check(Ean <= 2, 'analytic moment <= 2')

# ---------------- slow worst-case runs
if args.slow:
    print('\n== worst-case sign (digest succeeds only at a = 2^20-1, every enc only at c = 2^20-1)')
    LAST = (1 << 20) - 1
    x = [7] * 24 + [2] + [0] * 17
    d0 = sum(v << (3 * i) for i, v in enumerate(x[:21]))
    d1 = sum(v << (3 * i) for i, v in enumerate(x[21:]))
    GOOD = d0.to_bytes(8, 'little') + d1.to_bytes(8, 'little') + bytes(16)

    def worst(y):
        t = y[1]
        if t == 7:
            return y[4:8] + bytes(28)
        if t == 12:
            a = int.from_bytes(y[32:36], 'little')
            return bytes(32) if a == LAST else b'\xff' * 32
        if t == 4:
            c = int.from_bytes(y[48:52], 'little')
            return GOOD if c == LAST else bytes(32)   # fails at the final sum test (longest path)
        return hashlib.sha256(y).digest()
    S = bytes(32)
    t = time.time()
    o = ref.Oracle(log=False, fn=worst)
    sigw = ref.sign(o, S, bytes(32))
    vs, res = run('sign', {'sk': S, 'msg': bytes(32), 'cache': bytes(vm.CACHE_BYTES)}, worst)
    check(res.exit == 'success' and vs == sigw, 'worst-case sign agrees with ref')
    print('worst sign: cycles=%d steps=%d compressions=%d (%.0fs)  < 2^32: %s' % (
        res.cycles, res.steps, res.compressions, time.time() - t, res.cycles < 2 ** 32))
    pkw = ref.keygen(ref.Oracle(fn=worst), S)
    okv, resv = vm_verify(pkw, bytes(32), ref.to_witness(sigw, MODE), worst)
    check(okv, 'worst-case signature verifies')
    print('\n== exhausted searches')
    never = lambda y: b'\xff' * 32 if y[1] == 12 else hashlib.sha256(y).digest()
    t = time.time()
    vs, res = run('sign', {'sk': S, 'msg': bytes(32), 'cache': bytes(vm.CACHE_BYTES)}, never)
    check(res.exit == 'failure' and ref.sign(ref.Oracle(log=False, fn=never), S, bytes(32)) is None,
          'digest exhaustion fails')
    print('digest search exhausted: exit=%s cycles=%d (%.0fs)' % (res.exit, res.cycles, time.time() - t))
    noenc = lambda y: bytes(32) if y[1] in (4, 12) else hashlib.sha256(y).digest()
    t = time.time()
    vs, res = run('sign', {'sk': S, 'msg': bytes(32), 'cache': bytes(vm.CACHE_BYTES)}, noenc)
    check(res.exit == 'failure' and ref.sign(ref.Oracle(log=False, fn=noenc), S, bytes(32)) is None,
          'encoding exhaustion fails')
    print('layer-6 encoding search exhausted: exit=%s cycles=%d (%.0fs)' % (res.exit, res.cycles, time.time() - t))

print('\nRESULT:', 'ALL PASSED' if not FAILS else '%d FAILURES' % len(FAILS))
sys.exit(1 if FAILS else 0)
