#!/usr/bin/env bash
# Trusted setup, before any submitted Lean runs: the pinned Lean toolchain and the formal-conjectures workspace at
# the commit our statements come from (fc/FC_REV), Mathlib from its official cache.
#   setup-workspace.sh fetch   clone + toolchain + Mathlib cache
#   setup-workspace.sh build   build the FC modules statements import (restored from the Actions cache when possible)
set -euo pipefail
NV=${NV:-/opt/nv}
FC_REV=$(tr -d '[:space:]' < "$NV/base/fc/FC_REV")
printf '%s' "$FC_REV" | grep -Eqx '[0-9a-f]{40}'
export ELAN_HOME="$NV/elan"
case "${1:-}" in
  fetch)
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --no-modify-path --default-toolchain none
    git init -q "$NV/fc"
    git -C "$NV/fc" fetch -q --depth 1 https://github.com/google-deepmind/formal-conjectures.git "$FC_REV"
    git -C "$NV/fc" checkout -q --detach FETCH_HEAD
    tc=$(cat "$NV/fc/lean-toolchain")
    "$ELAN_HOME/bin/elan" toolchain install "$tc"
    "$ELAN_HOME/bin/elan" override set "$tc" >/dev/null 2>&1 || true
    cd "$NV/fc"
    TC_BIN=$(dirname "$("$ELAN_HOME/bin/elan" which lake)")
    "$TC_BIN/lake" exe cache get
    ;;
  build)
    cd "$NV/fc"
    TC_BIN=$(dirname "$("$ELAN_HOME/bin/elan" which lake)")
    mods=$(grep -v '^\s*$' "$NV/base/fc/modules.txt" | tr '\n' ' ' || true)
    # shellcheck disable=SC2086
    "$TC_BIN/lake" build FormalConjecturesUtil FormalConjecturesForMathlib $mods
    {
      echo "TC_BIN=$TC_BIN"
      echo "LEAN_PATH_BASE=$("$TC_BIN/lake" env printenv LEAN_PATH)"
      echo "TOOLCHAIN=$(cat lean-toolchain)"
      echo "FC_REV=$FC_REV"
    } > "$NV/workspace.env"
    chmod -R a+rX "$NV/elan" "$NV/fc"
    ;;
  *) echo "usage: setup-workspace.sh fetch|build" >&2; exit 64 ;;
esac
