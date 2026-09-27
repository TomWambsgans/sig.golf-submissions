#!/bin/bash
D=/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice
peak=0
sleep 5
while true; do
  f=$(ls -d $D/sig-verify-* 2>/dev/null | head -1)
  [ -z "$f" ] && break
  c=$(cat $f/memory.peak 2>/dev/null || echo 0)
  [ "$c" -gt "$peak" ] && peak=$c
  sleep 10
done
echo "peak_GB $((peak/1073741824))"
cat /home/sigverify/verify_err.log
head -c 400 /home/sigverify/verify_result.json; echo
tail -3 /home/sigverify/vwork/verify.log
