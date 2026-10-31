#!/usr/bin/env bash
# run-kernel.sh — drive the placement conformance probe on a real Linux kernel.
#
# Builds Linux v6.18.46 for riscv64 in three configurations, builds the probe
# (tools/placement_conformance/probe.c) as a static non-PIE rv64g musl program,
# boots the kernel under qemu-system-riscv64 with the probe as init, and writes
# the probe's JSON log.  Everything except the docker calls themselves runs in
# containers; nothing is installed on the host.
#
# Usage:
#   ./run-kernel.sh image              build the build container
#   ./run-kernel.sh source             clone Linux v6.18.46 and check the commit
#   ./run-kernel.sh probe              build probe and probe.cpio
#   ./run-kernel.sh kernel CONFIG      configure and build Image
#   ./run-kernel.sh boot CONFIG        boot the kernel, write the log
#   ./run-kernel.sh startstate CONFIG SEED
#                                      boot with qemu's -seed SEED and run the
#                                      two start-state probes of OSSV-257 A4,
#                                      writing one log per run
#   ./run-kernel.sh qemu-user          run the probe under qemu-riscv64 (user mode)
#   ./run-kernel.sh all CONFIG         image, source, probe, kernel, boot
#
# CONFIG is one of:
#   defconfig    riscv defconfig, CONFIG_LSM_MMAP_MIN_ADDR=4096
#   thp          the same plus CONFIG_TRANSPARENT_HUGEPAGE
#   norandmaps   the defconfig kernel, booted with "norandmaps"
#
# CONFIG_LSM_MMAP_MIN_ADDR is lowered to 4096 because the riscv defconfig turns
# SELinux on, whose default is 65536, and mmap_min_addr is the maximum of that
# and dac_mmap_min_addr (Linux v6.18.46, security/min_addr.c,
# update_mmap_min_addr).  SCOPE.md's assumption is mmap_min_addr = 4096.
#
# The host needs docker, git and the coreutils; every compile and every boot
# runs in a container.
#
# Outputs, under $PC_WORK (default ~/pc):
#   out/<config>.log    the probe's JSON lines, under a '#' header — this is
#                       what log_to_rocq.py reads
#   out/<config>.raw    the whole console, kernel messages included
#   kernels/<config>/   vdso.so, vdso.so.dbg, the two .config lines, the
#                       build identity, and readelf of the vDSO
#
# Every run is pinned: the Debian base image by digest, qemu 10.0.11 by the
# SHA-256 of its four packages (the version the collection's runner image
# uses), the kernel by its commit, and the probe's toolchain by the digest of
# the collection's builder image.
set -euo pipefail

PC_WORK=${PC_WORK:-$HOME/pc}
PC_IMAGE=${PC_IMAGE:-lps-placement-conformance:1}
# The collection's builder image (release.yaml images.builder), by digest.  On
# a machine with GitHub credentials this is
# ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c…
PC_TOOLCHAIN=${PC_TOOLCHAIN:-us-central1-docker.pkg.dev/autoformalization/ossv/oss-fuzz-theorems-toolchain@sha256:6a6b4816865c7ec61801ae0fcab6d9c81a599ffcb20616576a9c668abd8b0a7b}

LINUX_URL=${LINUX_URL:-https://github.com/gregkh/linux.git}
LINUX_TAG=v6.18.46
LINUX_COMMIT=1f99e9ab748fc5c32120de9c4eca31abfe54a4d5

HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
SRC=$PC_WORK/linux
OUT=$PC_WORK/out
mkdir -p "$PC_WORK" "$OUT"

die() { echo "run-kernel.sh: $*" >&2; exit 1; }

# The kernel tree a configuration builds in, and the Image it boots.
build_dir() {
  case $1 in
    defconfig|norandmaps) echo "$PC_WORK/build/defconfig" ;;
    thp)                  echo "$PC_WORK/build/thp" ;;
    *) die "unknown configuration '$1'" ;;
  esac
}

in_image() { docker run --rm -u "$(id -u):$(id -g)" -e HOME=/tmp \
  -v "$PC_WORK":"$PC_WORK" -w "$PC_WORK" "$PC_IMAGE" "$@"; }

# ---------------------------------------------------------------- image ----
cmd_image() {
  mkdir -p "$PC_WORK/img"
  cat > "$PC_WORK/img/Dockerfile" <<'EOF'
# The build container: a riscv64 cross toolchain, the kernel's build
# dependencies, and qemu 10.0.11 in system and user mode.
#
# The archive carries a newer qemu, so the four packages of 10.0.11 are added
# by their own URL and SHA-256 out of the Debian snapshot archive and put over
# the archive's version, which has brought their libraries in.  10.0.11 is the
# version of the collection's runner image (toolchain/runner.Dockerfile of the
# internal repository), and its qemu-user package is the same file: the hash
# below is the hash that file pins.
ARG DEBIAN_BASE=debian:trixie-slim@sha256:a99cfc517144bc59b1978475ec53b46ecabec7e43635402ee5b77cc54cd1b20a

FROM scratch AS qemu-debs
ADD --checksum=sha256:35bbfdca8de3967a3412d1beff4309127de0c330e1430ddc1a458f4f1cc37c78 \
    https://snapshot.debian.org/file/445e1450e0cdbd680fd0f57c6dde005a386dd7c7 /qemu-system-common.deb
ADD --checksum=sha256:5ab6916f8cbda16c9bfee3bc4ebdad917b47c6cceeed9309d920f85c01a73c4e \
    https://snapshot.debian.org/file/5255195eb156694543364510e44f1aa409ae276e /qemu-system-data.deb
ADD --checksum=sha256:22db4d51a97fd69a40cc430f1aef9c76fcb6c07e249e2259eba531edea1c2bb8 \
    https://snapshot.debian.org/file/fd21bebff0e0b462951d337b3f8e605b320b3805 /qemu-system-riscv.deb
ADD --checksum=sha256:6b6fea55551fbcc1eb30e146ad5abdfbb49f8fa8c5998016242126de4d7f80df \
    https://snapshot.debian.org/file/a0eaa62f815efb2361d43b1e3f8011c17ad9123a /qemu-user.deb

FROM ${DEBIAN_BASE}
SHELL ["/bin/bash", "-euo", "pipefail", "-c"]
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      bc bison flex build-essential libssl-dev libelf-dev cpio kmod xz-utils \
      gcc-riscv64-linux-gnu binutils-riscv64-linux-gnu \
      qemu-system-riscv qemu-user python3 file \
    && rm -rf /var/lib/apt/lists/*
RUN --mount=type=bind,from=qemu-debs,target=/debs \
    dpkg -i /debs/qemu-system-data.deb /debs/qemu-system-common.deb \
            /debs/qemu-system-riscv.deb /debs/qemu-user.deb
# The two qemu binaries this harness quotes.
RUN qemu-system-riscv64 --version > /tmp/v.txt && qemu-riscv64 --version >> /tmp/v.txt \
    && grep -q 'QEMU emulator version 10\.0\.11' /tmp/v.txt \
    && grep -q 'qemu-riscv64 version 10\.0\.11' /tmp/v.txt \
    && echo '44076c56382fea0cca26fb4ec1ab688fcc59573d87de1094d664f37915ac8d72  /usr/bin/qemu-riscv64' \
       | sha256sum -c - \
    && rm /tmp/v.txt
EOF
  docker build -t "$PC_IMAGE" "$PC_WORK/img"
}

# --------------------------------------------------------------- source ----
cmd_source() {
  if [ ! -d "$SRC/.git" ]; then
    git clone --depth 1 --branch "$LINUX_TAG" "$LINUX_URL" "$SRC"
  fi
  local got
  got=$(git -C "$SRC" rev-parse HEAD)
  [ "$got" = "$LINUX_COMMIT" ] || die "Linux is $got, expected $LINUX_COMMIT"
  echo "Linux $LINUX_TAG = $got"
}

# ---------------------------------------------------------------- probe ----
# Static, non-PIE, rv64g, musl 1.2.6, in the collection's builder image — the
# way the collection builds every binary it proves about (docs/building.md of
# the internal repository: -march=rv64g -mabi=lp64d, clang 20.1.8, musl, lld).
cmd_probe() {
  cp "$HERE/probe.c" "$PC_WORK/probe.c"
  docker run --rm -u "$(id -u):$(id -g)" -e HOME=/tmp \
    -v "$PC_WORK":"$PC_WORK" -w "$PC_WORK" "$PC_TOOLCHAIN" \
    clang --target=riscv64-alpine-linux-musl --sysroot=/opt/musl-sysroot/usr \
      --gcc-install-dir=/usr/lib/gcc/riscv64-alpine-linux-musl/14.2.0 \
      -march=rv64g -mabi=lp64d -static -no-pie -fno-pie -Os -g \
      -fno-stack-protector -Wall -Wextra -fuse-ld=lld -nostartfiles \
      -o "$PC_WORK/probe" "$PC_WORK/probe.c"
  in_image file probe
  # The initramfs holds the probe, a /proc for it to mount, and
  # /dev/console, which init/main.c console_on_rootfs opens as the standard
  # descriptors: without it the probe's writes go nowhere.  The kernel's own
  # usr/gen_init_cpio makes the device node, so no step here needs to be root.
  [ -f "$SRC/usr/gen_init_cpio.c" ] || die "no kernel source; run 'source'"
  printf '%s\n' \
    'dir /dev 755 0 0' \
    'nod /dev/console 644 0 0 c 5 1' \
    'dir /proc 755 0 0' \
    "file /probe $PC_WORK/probe 755 0 0" \
    "file /a $PC_WORK/probe 755 0 0" > "$PC_WORK/initramfs.list"
  in_image bash -euo pipefail -c "
    cc -O2 -o '$PC_WORK/gen_init_cpio' '$SRC/usr/gen_init_cpio.c'
    '$PC_WORK/gen_init_cpio' '$PC_WORK/initramfs.list' > '$PC_WORK/probe.cpio'
  "
  ls -l "$PC_WORK/probe" "$PC_WORK/probe.cpio"
}

# --------------------------------------------------------------- kernel ----
cmd_kernel() {
  local cfg=$1 b
  b=$(build_dir "$cfg")
  [ "$cfg" != norandmaps ] || die "norandmaps boots the defconfig kernel; build 'defconfig'"
  mkdir -p "$b"
  in_image bash -euo pipefail -c "
    cd '$SRC'
    make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O='$b' defconfig
    ./scripts/config --file '$b/.config' --set-val LSM_MMAP_MIN_ADDR 4096
    $( [ "$cfg" = thp ] && echo "./scripts/config --file '$b/.config' -e TRANSPARENT_HUGEPAGE" )
    make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O='$b' olddefconfig
    make ARCH=riscv CROSS_COMPILE=riscv64-linux-gnu- O='$b' -j\$(nproc) Image
  "
  cmd_vdso "$cfg"
}

# The vDSO image and the build identity, for the lane that needs the text size.
cmd_vdso() {
  local cfg=$1 b d
  b=$(build_dir "$cfg")
  d=$PC_WORK/kernels/$cfg
  mkdir -p "$d"
  cp "$b/arch/riscv/kernel/vdso/vdso.so" "$d/"
  [ ! -f "$b/arch/riscv/kernel/vdso/vdso.so.dbg" ] \
    || cp "$b/arch/riscv/kernel/vdso/vdso.so.dbg" "$d/"
  { echo "kernel_commit: $(git -C "$SRC" rev-parse HEAD)"
    echo "kernel_tag: $LINUX_TAG"
    echo "config: $cfg"
    grep -E '^(CONFIG_LSM_MMAP_MIN_ADDR|CONFIG_TRANSPARENT_HUGEPAGE)[= ]' "$b/.config" || true
    grep -E '^# CONFIG_TRANSPARENT_HUGEPAGE is not set' "$b/.config" || true
    echo "compiler: $(in_image riscv64-linux-gnu-gcc --version | head -1)"
    echo "image: $PC_IMAGE"
  } > "$d/build-identity.txt"
  in_image bash -c "readelf -lW '$d/vdso.so' | sed -n '1,30p'" > "$d/vdso-phdrs.txt"
  cat "$d/build-identity.txt"
}

# ----------------------------------------------------------------- boot ----
# cmd_boot CONFIG [MODE] [SEED]
#
# MODE is "place" (the placement sequence, one log) or "startstate" (the two
# start-state runs of OSSV-257 A4, one log each).  SEED, when given, is
# qemu's -seed: it fixes the devicetree's rng-seed, and so the kernel's
# randomization draws, so two boots of one configuration give two draws that
# the log names.  The log's tag is CONFIG, or CONFIG-seedSEED with a seed.
#
# Every log this function writes carries the three facts the probe cannot
# read for itself -- the kernel's .config lines, the devicetree cache
# properties and the whole command line -- merged into the launch object by
# merge_launch.py.
# DT, when it is "cache", gives the boot CPU a cache hierarchy that qemu's
# devicetree does not carry, so the kernel publishes non-zero AT_L*_CACHE*
# words (patch_dtb.py).  The tag then carries "-cache".
cmd_boot() {
  local cfg=$1 mode=${2:-place} seed=${3:-} dt=${4:-} b append extra= tag
  local machine seedarg= dtbarg=
  b=$(build_dir "$cfg")
  [ -f "$b/arch/riscv/boot/Image" ] || die "no Image in $b; run 'kernel'"
  [ -f "$PC_WORK/probe.cpio" ] || die "no probe.cpio; run 'probe'"
  [ "$cfg" != norandmaps ] || extra=" norandmaps"
  [ "$mode" != startstate ] || extra="$extra pc_mode=startstate"
  append="console=ttyS0 no5lvl rdinit=/probe${extra}"
  machine="-M virt -cpu rv64,sv57=off -m 2G"
  tag=$cfg${dt:+-$dt}${seed:+-seed$seed}
  [ -z "$seed" ] || seedarg="-seed $seed"
  cp "$HERE/merge_launch.py" "$PC_WORK/merge_launch.py"
  cp "$HERE/patch_dtb.py" "$PC_WORK/patch_dtb.py"
  # The devicetree the firmware hands this kernel, for the cache properties
  # that drivers/base/cacheinfo.c reads.  qemu writes it and exits.
  in_image bash -euo pipefail -c "
    cd '$PC_WORK'
    qemu-system-riscv64 -M virt,dumpdtb='$OUT/$tag.dtb' -cpu rv64,sv57=off \
      -m 2G -nographic $seedarg > '$OUT/$tag.dtb.log' 2>&1 || true
  "
  if [ "$dt" = cache ]; then
    in_image bash -euo pipefail -c "
      cd '$PC_WORK'
      python3 patch_dtb.py '$OUT/$tag.dtb' '$OUT/$tag.cache.dtb'
      mv '$OUT/$tag.cache.dtb' '$OUT/$tag.dtb'
    "
    dtbarg="-dtb $OUT/$tag.dtb"
  fi
  in_image bash -euo pipefail -c "
    cd '$PC_WORK'
    timeout 300 qemu-system-riscv64 $machine -nographic $seedarg $dtbarg \
      -kernel '$b/arch/riscv/boot/Image' -initrd probe.cpio \
      -append '$append' > '$OUT/$tag.raw' 2>&1 || true
  "
  grep -q '^{' "$OUT/$tag.raw" || die "no probe output in $OUT/$tag.raw"
  # The log carries its own provenance: log_to_rocq.py reads the lines that
  # start with '{' and nothing else.
  { echo "# placement conformance log: $tag"
    echo "# kernel: Linux $LINUX_TAG, commit $(git -C "$SRC" rev-parse HEAD), riscv64"
    echo "# compiler: $(in_image riscv64-linux-gnu-gcc --version | head -1)"
    grep -E '^(CONFIG_LSM_MMAP_MIN_ADDR|CONFIG_TRANSPARENT_HUGEPAGE)=' "$b/.config" \
      | sed 's/^/# /' || true
    grep -E '^# CONFIG_TRANSPARENT_HUGEPAGE is not set' "$b/.config" || true
    echo "# qemu: $(in_image qemu-system-riscv64 --version | head -1)"
    echo "# machine: $machine $seedarg"
    echo "# cmdline: $append"
    echo "# probe: $(in_image sha256sum probe | cut -c1-64)"
    echo "# mode: $mode"
    echo "# devicetree patch: ${dt:-none}"
    echo "# devicetree: qemu -M virt,dumpdtb, $(in_image sha256sum "$OUT/$tag.dtb" | cut -c1-64)"
    echo "# probe source: $(in_image sha256sum probe.c | cut -c1-64)"
    echo "# written by tools/placement_conformance/run-kernel.sh boot $cfg $mode $seed"
  } > "$OUT/$tag.hdr"
  in_image python3 "$PC_WORK/merge_launch.py" --config "$b/.config" \
    --dtb "$OUT/$tag.dtb" --cmdline "$append" --raw "$OUT/$tag.raw" \
    --header "$OUT/$tag.hdr" --out-dir "$OUT" --name "$tag" --mode "$mode"
  if [ "$mode" = startstate ]; then
    echo "stack ends: $(sed -n 's/.*"stack_end":\([0-9]*\).*/\1/p' "$OUT/$tag.raw")"
  else
    sed -n '1,12p' "$OUT/$tag.log"
    echo "mmu: $(sed -n 's/.*"mmu": *"\([^"]*\)".*/\1/p' "$OUT/$tag.log" | head -1)"
    echo "lines: $(grep -c '^{' "$OUT/$tag.log")"
  fi
}

# ------------------------------------------------------------ qemu-user ----
# The same probe under qemu-user, which places a mapping where QEMU's own
# allocator puts it, not where Linux does.  SCOPE.md's statement that
# qemu-user placement is outside the model is read off this log.
cmd_qemu_user() {
  [ -f "$PC_WORK/probe" ] || die "no probe; run 'probe'"
  in_image bash -euo pipefail -c "
    cd '$PC_WORK'
    qemu-riscv64 ./probe > '$OUT/qemu-user.raw' 2>&1 || true
  "
  grep -q '^{' "$OUT/qemu-user.raw" || die "no probe output"
  { echo "# placement conformance log: qemu-user"
    echo "# qemu: $(in_image qemu-riscv64 --version | head -1)"
    echo "# host: $(uname -srm)"
    echo "# probe: $(in_image sha256sum probe | cut -c1-64)"
    echo "# written by tools/placement_conformance/run-kernel.sh qemu-user"
    echo "# These placements are QEMU's, not Linux's: the replay must refuse them."
    grep '^{' "$OUT/qemu-user.raw"
  } > "$OUT/qemu-user.log"
  sed -n '1,6p' "$OUT/qemu-user.log"
  echo "lines: $(grep -c '^{' "$OUT/qemu-user.log")"
}

cmd=${1:-}
case $cmd in
  image)     cmd_image ;;
  source)    cmd_source ;;
  probe)     cmd_probe ;;
  kernel)    cmd_kernel "${2:?CONFIG}" ;;
  vdso)      cmd_vdso "${2:?CONFIG}" ;;
  boot)      cmd_boot "${2:?CONFIG}" "${3:-place}" "${4:-}" "${5:-}" ;;
  # The boots of OSSV-257 A4: three randomized draws, one norandmaps, and
  # one whose devicetree carries a cache hierarchy.
  startstate) cmd_boot "${2:?CONFIG}" startstate "${3:?SEED}" "${4:-}" ;;
  qemu-user) cmd_qemu_user ;;
  all)       cmd_image; cmd_source; cmd_probe
             [ "${2:?CONFIG}" = norandmaps ] || cmd_kernel "$2"
             cmd_boot "$2" ;;
  *) sed -n '2,40p' "$0"; exit 2 ;;
esac
