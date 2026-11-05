#!/usr/bin/env bash
# Empties the dune cache when the toolchain changed since the run that filled it.
#
#   .github/dune-cache-toolchain.sh CACHE_DIR
#
# The workflow runs it after the dependencies are installed and before the
# build. dune keys each rule on its inputs, the rocq binary and the .vo files a
# Rocq file loads among them. It does not key on the OCaml plugins (.cmxs) that
# rocq loads: ltac, micromega, and the one of rocq-read-file, which reads the
# .hex bytes of each memory image. A change to a plugin alone leaves every key
# the same, so dune would give back what the old plugin made. This script
# hashes the package list of the opam switch (name and version) and every
# .cmxs in it. When the hash differs from the one stored in the cache, it
# deletes the cache entries, CACHE_DIR/db (dune 3.24.2 keeps them in
# $DUNE_CACHE_ROOT/db, src/dune_cache/layout.ml). Then this repository's build
# is cold. The dependencies were built from the cache before the check, and
# the next run builds them cold too. Then the script stores the hash. It reads
# no binary: dune itself is rebuilt on every run, and dune already keys on the
# rocq binary.
set -euo pipefail

cache=$1
prefix=$(opam var prefix)
stamp=$(
  {
    opam list --short --columns=package
    cd "$prefix"
    find . -type f -name '*.cmxs' -print0 | LC_ALL=C sort -z | xargs -0 sha256sum
  } | sha256sum | cut -d' ' -f1
)
file="$cache/toolchain"
old=$(cat "$file" 2>/dev/null || true)
if [ -d "$cache/db" ] && [ "$old" != "$stamp" ]; then
  echo "The toolchain is not the one that filled the dune cache (${old:-no hash} -> $stamp): emptying the cache."
  rm -rf "$cache/db"
else
  echo "Toolchain $stamp"
fi
mkdir -p "$cache"
echo "$stamp" > "$file"
