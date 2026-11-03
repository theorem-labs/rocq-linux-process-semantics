#!/usr/bin/env bash
# Empties the dune cache when the toolchain changed since the run that filled it.
#
#   .github/dune-cache-toolchain.sh CACHE_DIR before|after
#
# The workflow runs it twice: `before` the dependencies are installed, on the
# switch as the image or setup-ocaml left it, and `after`, before the build.
# dune keys each rule on its inputs, the rocq binary and the .vo files a Rocq
# file loads among them. It does not key on the OCaml plugins (.cmxs) that rocq
# loads: ltac, micromega, and the one of rocq-read-file, which reads the .hex
# bytes of each memory image. A change to a plugin alone leaves every key the
# same, so dune would give back what the old plugin made. This script hashes
# the package list of the opam switch (name and version) and every .cmxs in it,
# and compares the hash with the one the run that filled the cache stored at
# the same stage. When they differ, it deletes the cache entries, CACHE_DIR/db
# (dune 3.24.2 keeps them in $DUNE_CACHE_ROOT/db, src/dune_cache/layout.ml).
#
# `before` catches a new image or compiler, so the dependencies then build cold
# too. `after` catches a dependency that installs another version or plugin,
# so this repository's build is cold. After a `before` emptying, the cache holds
# only what this run built, so `after` keeps it. It reads no binary: dune itself
# is rebuilt on every run, and dune already keys on the rocq binary.
set -euo pipefail

cache=$1
stage=$2
case "$stage" in before|after) ;; *) echo "stage must be before or after: $stage" >&2; exit 2 ;; esac
prefix=$(opam var prefix)
stamp=$(
  {
    opam list --short --columns=package
    cd "$prefix"
    find . -type f -name '*.cmxs' -print0 | LC_ALL=C sort -z | xargs -0 sha256sum
  } | sha256sum | cut -d' ' -f1
)
file="$cache/toolchain-$stage"
fresh="$cache/emptied-this-run"
old=$(cat "$file" 2>/dev/null || true)
mkdir -p "$cache"
if [ "$stage" = after ] && [ -e "$fresh" ]; then
  echo "Toolchain ($stage) $stamp: the cache holds only this run's entries"
elif [ "$stage" = before ] && [ ! -d "$cache/db" ]; then
  echo "Toolchain ($stage) $stamp: no dune cache was restored"
  touch "$fresh"
elif [ -d "$cache/db" ] && [ "$old" != "$stamp" ]; then
  echo "The toolchain ($stage) is not the one that filled the dune cache (${old:-no hash} -> $stamp): emptying the cache."
  rm -rf "$cache/db"
  if [ "$stage" = before ]; then touch "$fresh"; fi
else
  echo "Toolchain ($stage) $stamp"
fi
echo "$stamp" > "$file"
if [ "$stage" = after ]; then rm -f "$fresh" "$cache/toolchain"; fi
exit 0
