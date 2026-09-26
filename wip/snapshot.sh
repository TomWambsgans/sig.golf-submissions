#!/bin/bash
# Assemble the fork branch: submission/ (admitted root, via package.py), presentation/, wip/ (sources in progress).
set -e
W=/root/siggolf/work
S=/root/siggolf/submissions
SPH=${1:-$W/sec-event}
cd $S
git checkout -q claude-submission
rm -rf submission wip presentation
python3 $W/tools/package.py $S/submission $SPH
python3 /root/siggolf/dev/verifier/check_submission.py $S/submission | python3 -c 'import json,sys; r=json.load(sys.stdin); print("policy ok:", r["ok"], r["files"], "entries", r["bytes"], "bytes", r["errors"][:3])'
cp -r $W/presentation presentation
mkdir -p wip
for b in sec-scheme sec-event; do mkdir -p wip/$b; cp $W/$b/*.md wip/$b/ 2>/dev/null || true; done
rsync -a --exclude '__pycache__' --exclude '.git' $W/py/ wip/py/
rsync -a --exclude '.lake' --exclude 'Scratch*' $W/rv/SigGolfCandidate/Rv/ wip/rv-framework/
cp $W/tools/package.py $W/tools/snapshot.sh wip/
cp $W/design/SPEC.md wip/SPEC.md
