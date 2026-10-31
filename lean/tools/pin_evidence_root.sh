#!/usr/bin/env bash
# Build the combined root that `check_lean_pin_evidence.py` needs, and run it.
#
# The twin's pins cite two trees that no single checkout holds. A `rocq-twin:`
# name is a declaration of THIS repository's `theories/` at the commit the
# file's `-- Ports rocq-linux-process-semantics <commit>:<path>` header names,
# and a `probe:` line is a CASE of linux-process-semantics'
# `testing/syscall-check/tests/*.c` at the commit the twin was ported from.
# The tool resolves both against one `--root`. This script makes that root out
# of symlinks in a scratch directory; it copies nothing into either repository
# and writes nothing outside the scratch directory.
#
# Usage:
#   lean/tools/pin_evidence_root.sh <upstream-checkout> <kernel-tree> [scratch] [-- extra args]
#
#   <upstream-checkout>  a linux-process-semantics checkout at the commit the
#                        twin ports from (`lean/UPSTREAM` names it), which
#                        supplies `testing/` and `tools/`
#   <kernel-tree>        a Linux v6.18.46 checkout. It is REQUIRED: the twin
#                        carries thousands of `kernel:` annotations and the
#                        tool refuses to run without a tree to read them in.
#   [scratch]            where to build the root; default $TMPDIR/pin-root
#
# Everything after `--` is passed to the tool.
set -euo pipefail

usage() { sed -n '2,24p' "$0"; exit 2; }

[ $# -ge 2 ] || usage
UPSTREAM=$(cd "$1" && pwd); shift
KERNEL=$(cd "$1" && pwd); shift
SCRATCH=${TMPDIR:-/tmp}/pin-root
if [ $# -gt 0 ] && [ "$1" != "--" ]; then SCRATCH=$1; shift; fi
[ "${1:-}" != "--" ] || shift

HERE=$(cd "$(dirname "$0")" && pwd)       # <twin>/lean/tools
TWIN=$(cd "$HERE/../.." && pwd)           # the repository root

[ -d "$UPSTREAM/testing/syscall-check/tests" ] \
  || { echo "$0: $UPSTREAM holds no testing/syscall-check/tests" >&2; exit 2; }
[ -f "$KERNEL/kernel/signal.c" ] \
  || { echo "$0: $KERNEL does not look like a Linux tree" >&2; exit 2; }

rm -rf "$SCRATCH"
mkdir -p "$SCRATCH"
ln -s "$TWIN/theories" "$SCRATCH/theories"          # this repository's Rocq
ln -s "$TWIN/lean" "$SCRATCH/lean"                  # the twin itself
ln -s "$UPSTREAM/testing" "$SCRATCH/testing"        # the recordings and probes
ln -s "$UPSTREAM/tools" "$SCRATCH/tools"            # the checker scripts
ln -s "$UPSTREAM/bugs" "$SCRATCH/bugs" 2>/dev/null || true
# The tool reads the root's AGENTS.md for the kernel version every `kernel:`
# annotation is held to; this repository has no such file, so upstream's serves.
ln -s "$UPSTREAM/AGENTS.md" "$SCRATCH/AGENTS.md"

echo "$0: root at $SCRATCH (theories from $TWIN, testing from $UPSTREAM)"
exec python3 "$UPSTREAM/tools/check_lean_pin_evidence.py" \
  --root "$SCRATCH" --kernel-tree "$KERNEL" "$@"
