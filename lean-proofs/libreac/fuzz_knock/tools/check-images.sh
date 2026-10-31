#!/bin/bash
# Check that the generated image modules are the pinned ELFs, and nothing else.
#
#   bash tools/check-images.sh <dir-holding-the-ELFs>
#
# `Image/Plain.lean` and `Image/Ubsan.lean` are the TRUSTED part of this
# project: their records ARE the programs the statements are about, and no
# Lean proof checks them against an ELF. `gen_image.py --check` is the only
# thing that does, and the adversarial review of slice K1 found that nothing
# ran it (its finding 2, 2026-10-31). This script is what runs it. Run it
# whenever an image module changes, and in CI beside `lake build`.
#
# Each ELF must have the SHA-256 that `projects/libreac/fuzz_knock/harness.yaml`
# pins for that build on `origin/ossv/recipes` of
# theorem-labs/oss-verify-proofs-internal; `--sha256` refuses any other file,
# so a wrong binary stops this script rather than being described by it.
set -euo pipefail

bins=${1:?usage: check-images.sh <dir holding fuzz_knock.plain and fuzz_knock.ubsan>}
cd "$(dirname -- "$0")/.."
out=OssFuzzTheorems/libreac/fuzz_knock/Image
mod=OssFuzzTheorems.libreac.fuzz_knock.Image

check() {  # name file sha256
  python3 tools/gen_image.py "$bins/$2" --out-dir "$out" --module "$mod" \
    --name "$1" --sha256 "$3" --check
}

check Plain fuzz_knock.plain \
  ca9a1031223344528f79f898eb4fc23e648bba08ce95d95d9aef8b3c250c96bf
check Ubsan fuzz_knock.ubsan \
  edcc54d2e7ee66e28ccc0cf8fb297b9d0dfaa1486f9d044d586de739892a3738

echo "check-images.sh: both image modules are the ELFs harness.yaml pins"
