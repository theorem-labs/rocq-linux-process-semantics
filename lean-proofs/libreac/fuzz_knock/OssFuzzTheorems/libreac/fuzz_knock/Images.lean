-- Ports oss-verify-proofs-internal ossv/recipes 9b0ac6f0e6:projects/libreac/fuzz_knock/Images.v
-- over rocq-linux-process-semantics f1006fe8's Lean twin.
import OssFuzzTheorems.Core.Images
import OssFuzzTheorems.libreac.fuzz_knock.Image.PlainCode
import OssFuzzTheorems.libreac.fuzz_knock.Image.UbsanCode

/-! # libreac / fuzz_knock: the images

The Lean twin of `projects/libreac/fuzz_knock/Images.v`.

Rocq's `images/<Build>.v` is generated when that library is built, by the
`elf-snapshot` tool of linux-process-semantics, from the ELF file that
`harness.yaml` pins by SHA-256; it is not stored in that repository. Here
`tools/gen_image.py` does the same job from the same ELF, and the generated
module carries, beside the records, the byte certificates the Lean kernel needs
to read them (`LinuxProcessSemantics.Common.ImageBytes`). The pins:

| build | bytes | SHA-256 |
| --- | ---: | --- |
| plain | 43,480 | `ca9a1031223344528f79f898eb4fc23e648bba08ce95d95d9aef8b3c250c96bf` |
| ubsan | 43,592 | `edcc54d2e7ee66e28ccc0cf8fb297b9d0dfaa1486f9d044d586de739892a3738` |

Each is `harness.yaml`'s `builds.<build>.sha256`, and `gen_image.py --sha256`
refuses any other file.

The `_wf` theorems check by computation that each image is well formed
(`OssFuzzTheorems.Core.Images.image_wf`), so that no statement about it holds
only because the image has no valid entry.

NOT PORTED HERE: `asan` and `asan_ubsan`. Their ELFs are 558,152 and 558,224
bytes, thirteen times the plain build, and no statement this slice proves names
them; a Lean ASan statement also waits on the runtime work that
`sdd/ossv-265/task-T-report.md` ("What a Lean ASan runtime would need") sets
out. OSSV-265 gaps row K1-3. -/

namespace OssFuzzTheorems.libreac.fuzz_knock.Images

open LinuxProcessSemantics.LinuxProcessSem.MemImageType (Image)
open OssFuzzTheorems.Core.Images (image_wf image_wf_iff_IMAGE_WF)

/-- The image of `fuzz_knock.plain`: four LOAD segments (read at `0x10000`,
read and execute at `0x124f0`, two read and write at `0x1c1e0` and `0x1d298`),
entry `0x124f0`. -/
def plain : Image := Image.Plain.image

/-- The image of `fuzz_knock.ubsan`. -/
def ubsan : Image := Image.Ubsan.image

theorem plain_wf : image_wf plain := (image_wf_iff_IMAGE_WF plain).2 Image.PlainCode.imageWf

theorem ubsan_wf : image_wf ubsan := (image_wf_iff_IMAGE_WF ubsan).2 Image.UbsanCode.imageWf

end OssFuzzTheorems.libreac.fuzz_knock.Images
