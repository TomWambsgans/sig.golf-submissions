#!/usr/bin/env python3
"""Assemble the admitted submission root: import closure of Solution.lean, SphincsSecurity moved under
SigGolfCandidate (module prefix rewrite), claim.json. Usage: package.py OUTDIR [SPHINCS_SRC_ROOT]"""
import os, re, sys, shutil, json
W = '/root/siggolf/work'
out = sys.argv[1]
sph = sys.argv[2] if len(sys.argv) > 2 else f'{W}/sec-event'
roots = {  # module prefix -> source root directory containing it
  'SphincsSecurity': sph,
  'SigGolfCandidate': f'{W}/int',   # int/SigGolfCandidate has symlinks to rv, bridge, equiv, final
}
EXTERNAL = ('Mathlib', 'ToMathlib', 'VCVio', 'RiscvZkvm', 'Batteries', 'Lean', 'Init', 'Std', 'SigGolf')
def path_of(mod):
    top = mod.split('.')[0]
    if top not in roots: return None
    return os.path.join(roots[top], *mod.split('.')) + '.lean'
IMP = re.compile(r'^\s*import\s+(\S+)', re.M)
def imports(src):
    # imports only appear in the header; strip comments crudely
    body = re.sub(r'/-.*?-/', '', src, flags=re.S)
    return [m for m in IMP.findall(body.split('\nnamespace')[0].split('\nsection')[0])]
def newname(mod):
    return 'SigGolfCandidate.' + mod if mod.startswith('SphincsSecurity') else mod
seen = {}
stack = []
sol = open(f'{W}/int/Solution.lean').read()
for m in imports(sol): stack.append(m)
while stack:
    m = stack.pop()
    if m in seen or m.split('.')[0] in EXTERNAL and m.split('.')[0] not in roots: continue
    if m == 'SigGolf' or m.startswith('SigGolf.'): continue
    p = path_of(m)
    if p is None: continue
    if not os.path.exists(p): sys.exit(f'missing {m} at {p}')
    src = open(p).read(); seen[m] = src
    stack.extend(imports(src))
if os.path.exists(out): shutil.rmtree(out)
os.makedirs(out)
def rewrite(src):
    return re.sub(r'^(\s*import\s+)(SphincsSecurity)', r'\1SigGolfCandidate.\2', src, flags=re.M)
for m, src in seen.items():
    dst = os.path.join(out, *newname(m).split('.')) + '.lean'
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    open(dst, 'w').write(rewrite(src))
open(os.path.join(out, 'Solution.lean'), 'w').write(rewrite(sol))
json.dump({"S":7756,"W":7756,"C":18388,"layout":{"message":64,"secret_key":128,"public_key":160,"cache":17568,"signature":9808,"witness":2048}},
          open(os.path.join(out, 'claim.json'), 'w'), separators=(',', ':'))
tot = sum(len(s.encode()) for s in seen.values())
print(f'{len(seen)} modules, {tot/2**20:.2f} MiB')
