#!/usr/bin/env sh
# SPDX-License-Identifier: MIT OR Apache-2.0
# Every module under Oris/ except the gate and the audit command must be imported by Oris.lean:
# Oris/Gate.lean audits exactly what Oris.lean imports, so a module missing there would escape
# the axiom audit.
set -eu
cd "$(dirname "$0")/.."
status=0
for f in $(find Oris -name '*.lean' | sort); do
  m=$(printf '%s' "${f%.lean}" | tr '/' '.')
  case "$m" in
    Oris.Gate | Oris.Audit) continue ;;
  esac
  if ! grep -qx "import $m" Oris.lean; then
    echo "Oris.lean does not import $m (it would escape the axiom audit)"
    status=1
  fi
done
exit "$status"
