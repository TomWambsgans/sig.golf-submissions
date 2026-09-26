#!/usr/bin/env python3
"""Rebuild and audit the exact beta64 candidate images from proved legacy literals."""
from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path

from translate import Word, parse_code, translate

ROOT = Path(__file__).resolve().parent
LEGACY_NAMESPACE = {
    'SphincsMaskedImages.lean': 'SigGolfCandidate.SphincsMaskedImages',
    'SphincsImages.lean': 'SigGolfCandidate.SphincsImages',
}
SOURCES = {
    'keygen': 'SphincsMaskedImages.lean',
    'sign': 'SphincsMaskedImages.lean',
    'expand': 'SphincsImages.lean',
    'verify': 'SphincsImages.lean',
}
OLD_HASH = {
    'keygen': '36937653dc93c8151e9fa1f79b79ec2c7754c7fe89bf4350ab6ddf0d37541d31',
    'sign': '03e502bada402dd81f6d73c50ab20a79d5e8686159c7883ad918b550e4ca29ef',
    'expand': '5909d95bfeec23509c4fe274e9a9f20ac17b9bec1e764e280839f6b3582bbec6',
    'verify': '6f589d77e27757fc068625c6f44faa8c37edb8c561b3c9796cc0eaf27ac34ea9',
}
BETA_HASH = {
    'keygen': '65fc6d03469bade9c329f6084a7bbc6bff9905c00162b315396cd763319a9adc',
    'sign': '0ad5abeac36f940c21e6525472adfc7b3bd26bd86d4f736e2c862b85daf88fb4',
    'expand': 'a17e2103f72576e4a929ed0d5e69a5a2948f251e87bd9c639991bdf44fda0865',
    'verify': '99addc832d14b5749646e609590c09573e5a2d44c7c5253b686c985b5815a73d',
}
MODULE_HASH = '814e18fb8f306beb25d0c81fa0fe47a63903741f5ad4c138cbdd0e0bbee749e0'
BETA_CONTRACT = 'dbbbfe5e206dc501dbd15c920ff2892e453ec30f'


def digest(words: list[int]) -> str:
    return hashlib.sha256(b''.join(w.to_bytes(4, 'little') for w in words)).hexdigest()


def legacy_source(path: Path) -> str:
    source = path.read_text()
    name = LEGACY_NAMESPACE[path.name]
    begin = 'namespace ' + name + '\n'
    end = '\nend ' + name
    assert source.count(begin) == 1 and source.count(end) == 1
    return source.split(begin, 1)[1].split(end, 1)[0]


def main() -> None:
    repo = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT.parent.parent
    submission = repo / 'submission' / 'SigGolfCandidate'
    report = {'target_beta_commit': BETA_CONTRACT}
    ROOT.joinpath('output').mkdir(exist_ok=True)
    for name, filename in SOURCES.items():
        old = [w.value for w in parse_code(legacy_source(submission / filename), name)]
        assert digest(old) == OLD_HASH[name], (name, 'legacy hash mismatch', digest(old))
        beta, sites = translate([Word(w, 0, 0) for w in old], name)
        assert digest(beta) == BETA_HASH[name], (name, 'beta hash mismatch', digest(beta))
        assert all(s['beta_length_aligned'] for s in sites if s['kind'] == 'HASH')
        ROOT.joinpath(f'pc64-beta-{name}.hex').write_text(
            ''.join(f'{w:08x}\n' for w in beta))
        report[name] = {'old_words': len(old), 'beta_words': len(beta),
                        'old_sha256': digest(old), 'beta_sha256': digest(beta),
                        'sites': sites}
    ROOT.joinpath('pc64-padding-report.json').write_text(json.dumps(report, indent=2) + '\n')
    import emit_lean
    module = ROOT / 'output' / 'SphincsBeta64Images.lean'
    got = hashlib.sha256(module.read_bytes()).hexdigest()
    assert got == MODULE_HASH, ('Lean image-section hash mismatch', got)
    committed = (submission / 'SphincsBeta64Images.lean').read_text()
    assert committed.startswith(module.read_text()), 'committed image section differs'
    print('Reproduced image section', module, got)


if __name__ == '__main__':
    main()
