#!/usr/bin/env bash
# Build the Grosswald/Direct/Run chunks, a few at a time. Concurrency is read from $JOBS_FILE
# (default 48) before each launch, so it can be changed while this runs. Logs to $LOG_DIR.
set -u
cd "$(dirname "$0")/.."
export PATH=$HOME/.elan/bin:$PATH
JOBS_FILE=${JOBS_FILE:-.lake/direct.jobs}
LOG_DIR=${LOG_DIR:-.lake/direct-logs}
mkdir -p "$LOG_DIR"
[ -f "$JOBS_FILE" ] || echo 48 > "$JOBS_FILE"
mods=$(ls Grosswald/Direct/Run/*.lean | sed 's|/|.|g; s|\.lean$||')
for m in $mods; do
  name=${m##*.}
  [ -f "$LOG_DIR/$name.ok" ] && continue
  while [ "$(jobs -rp | wc -l)" -ge "$(cat "$JOBS_FILE")" ]; do sleep 5; done
  ( start=$(date +%s)
    if lake build "$m" > "$LOG_DIR/$name.log" 2>&1; then
      echo "$(( $(date +%s) - start ))" > "$LOG_DIR/$name.ok"
    else
      echo "$(( $(date +%s) - start ))" > "$LOG_DIR/$name.fail"
    fi ) &
done
wait
echo ALL_DONE > "$LOG_DIR/ALL_DONE"
