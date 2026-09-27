#!/bin/sh
# Run bend and show a compact error: the message lines plus the source
# excerpt, with the giant Context dumps stripped.
export PATH="$HOME/.bend/bin:$PATH"
out=$(bend "$@" 2>&1)
status=$?
printf '%s\n' "$out" | awk '
  /^- (t[0-9]|n[0-9]|w[0-9]|c[0-9]|_[a-zA-Z0-9]* *: (Sigma|Unit|main\.))/ { skip=1; next }
  /^- (m|r|g|cl|cr|al|ar|dt|soft|fuel|t2|STEP|DEPTH|SOFT|DT) / { skip=1; next }
  skip && /^[^ -]/ { skip=0 }
  skip { next }
  { print }
' | head -40
exit $status
