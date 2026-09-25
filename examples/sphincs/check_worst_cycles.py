"""Extrapolate the all-retries-last branch of the sign image."""

import hashlib

from examples.sphincs.build_images import CACHE, CACHE_BYTES, SECRET_KEY
from examples.sphincs.check_mask import masked_cache
from examples.sphincs.check_verify import Machine
from examples.sphincs.reference import Oracle, SIG_BYTES, keygen
from examples.sphincs.sign_image import build_sign


class PatternOracle(Oracle):
    def __init__(self, successful_trial: int) -> None:
        super().__init__()
        self.successful_trial = successful_trial

    def __call__(self, data: bytes) -> bytes:
        self.calls += 1
        self.compressions += max(1, (len(data) + 63) // 64)
        tag = data[1]
        if tag == 7:
            trial = int.from_bytes(data[4:8], "little")
            return trial.to_bytes(4, "little") + bytes(28)
        if tag == 12:
            trial = int.from_bytes(data[40:44], "little")
            result = bytearray(32)
            if trial < self.successful_trial:
                result[28] = 4
            return bytes(result)
        if tag == 4:
            trial = int.from_bytes(data[60:64], "little")
            if trial < self.successful_trial:
                return bytes(32)
            value = (1 << 78) - 1
            value |= 7 << 80
            value |= 5 << 83
            return value.to_bytes(20, "little") + bytes(12)
        return hashlib.sha256(data).digest()


def main() -> None:
    seed = bytes(range(32))
    message = bytes(reversed(range(32)))
    oracle = Oracle()
    pk, plain = keygen(oracle, seed)
    masked = masked_cache(oracle, seed, plain)
    code = build_sign()
    costs = []
    for success in (0, 1):
        machine = Machine(code, message, pk, bytes(SIG_BYTES))
        machine.mem[SECRET_KEY:SECRET_KEY + 32] = seed
        machine.mem[CACHE:CACHE + CACHE_BYTES] = masked
        machine.oracle = PatternOracle(success)
        machine.run(100_000_000)
        assert machine.accepted
        costs.append(machine.cycles)
        print("successful trial", success, "cycles", machine.cycles,
              "compressions", machine.oracle.compressions,
              "instructions", machine.instructions, flush=True)
    worst = costs[0] + ((1 << 20) - 1) * (costs[1] - costs[0])
    print("all retries last extrapolation", worst, "limit", 1 << 32,
          "headroom", (1 << 32) - worst, flush=True)


if __name__ == "__main__":
    main()
