"""One differential run for the prospective encrypted-cache image."""

import os

from examples.sphincs.build_images import (
    CACHE, CACHE_BYTES, DIGEST, MAC_TAG, PUBLIC_KEY, SECRET_KEY, SIGNATURE,
    TOP_NODES, build_keygen,
)
from examples.sphincs.check_verify import Machine
from examples.sphincs.reference import Oracle, SIG_BYTES, h, keygen, sign
from examples.sphincs.sign_image import DECRYPTED_ROOT, build_sign


def masked_cache(oracle: Oracle, seed: bytes, plain: bytes) -> bytes:
    p = plain[20:40]
    result = bytearray(plain)
    for i in range(TOP_NODES):
        start = 40 + DIGEST * i
        pad = h(oracle, p, 14, seed, position=i)
        result[start:start + DIGEST] = bytes(x ^ y for x, y in zip(plain[start:start + DIGEST], pad))
    result[:DIGEST] = result[40 + DIGEST * (TOP_NODES - 1):40 + DIGEST * TOP_NODES]
    result[-DIGEST:] = h(oracle, p, 15, seed + result[:-DIGEST])
    return bytes(result)


def main() -> None:
    seed = bytes(range(32))
    message = bytes(reversed(range(32)))
    oracle = Oracle()
    pk, plain = keygen(oracle, seed)
    masked = masked_cache(oracle, seed, plain)

    if not os.environ.get("SKIP_KEYGEN"):
        machine = Machine(build_keygen(), bytes(32), bytes(16), bytes(SIG_BYTES))
        machine.mem[SECRET_KEY:SECRET_KEY + 32] = seed
        machine.run(200_000_000)
        assert machine.accepted
        assert machine.mem[PUBLIC_KEY:PUBLIC_KEY + 16] == pk
        assert machine.mem[CACHE:CACHE + CACHE_BYTES] == masked
        print("keygen", machine.instructions, machine.cycles, machine.oracle.compressions, flush=True)

    expected = sign(Oracle(), seed, pk, plain, message)
    code = build_sign()
    signer = Machine(code, message, bytes(16), bytes(SIG_BYTES))
    signer.mem[SECRET_KEY:SECRET_KEY + 32] = seed
    signer.mem[CACHE:CACHE + CACHE_BYTES] = masked
    signer.run(100_000_000)
    labels = build_sign.labels
    position = signer.pc - 0x1000
    nearest = max(((offset, name) for name, offset in labels.items() if offset <= position), default=None)
    print("sign status", signer.accepted, hex(signer.pc), nearest,
          signer.instructions, signer.oracle.compressions, flush=True)
    if not signer.accepted:
        actual = bytes(signer.mem[SIGNATURE:SIGNATURE + SIG_BYTES])
        differences = [i for i, (x, y) in enumerate(zip(actual, expected)) if x != y]
        print("root", bytes(signer.mem[DECRYPTED_ROOT:DECRYPTED_ROOT + 20]).hex(),
              "expected", plain[:20].hex(), "first differences", differences[:20],
              "total", len(differences), flush=True)
    assert signer.accepted
    assert bytes(signer.mem[SIGNATURE:SIGNATURE + SIG_BYTES]) == expected
    assert signer.oracle.compressions < (1 << 17)
    print("sign", signer.instructions, signer.cycles, signer.oracle.compressions, flush=True)

    corrupt = bytearray(masked)
    corrupt[1000] ^= 1
    bad = Machine(build_sign(), message, bytes(16), bytes(SIG_BYTES))
    bad.mem[SECRET_KEY:SECRET_KEY + 32] = seed
    bad.mem[CACHE:CACHE + CACHE_BYTES] = corrupt
    bad.run(1_000_000)
    assert bad.accepted is False
    print("altered cache rejected before signing", bad.oracle.compressions, flush=True)


if __name__ == "__main__":
    main()
