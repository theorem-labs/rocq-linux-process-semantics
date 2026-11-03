(** * LinuxProcessSem.Checks.Extraction — extract the verified checker to OCaml

    The page-rounding / grant-top roots are the [Z]-side
    helpers of the bitvector model
    ([page_round_up_Z]/[page_round_down_Z]; [two_pow_64],
    [sp_window_lo] and [mmap_base_max] are [Z] constants).  [bv]
    extracts to its unsigned
    [Z] value (the [BvWf] proof is erased).

    THAT ERASURE IS WHY THE ROOTS BELOW ARE THE CHECKED ONES.  With the
    proof erased, the extracted [word] is zarith's arbitrary-precision
    integer: nothing in the extracted code holds it to [0 <= z < 2^64],
    and a caller that passes an integer no register holds gets a VERDICT
    on a value outside the Rocq type, which no theorem here covers.  So
    the supported surface is [Checks.CheckedInput]: every entry point
    takes the outside world's values as [Z] and refuses, before the
    checker runs, any integer that is not in the type it would inhabit.
    A refusal ([CheckedRefused], and [None] from [init_model_checked])
    is a third answer, distinct from every verdict.  Read that file for
    what it checks, what it builds, and what it cannot enforce.

    Not part of the batch build (it writes a .ml file as a side effect):
    theories/dune excludes it by name in
    [(modules :standard \ Riscv.Extraction LinuxProcessSem.Checks.Extraction)],
    so that list is what must be updated if this file is moved or renamed.
    Compile it by hand to write syscall_model.ml.

    The extracted artifact is [CheckedInput.check_syscall_for_run_checked],
    which is [ExecutableSpecs.check_syscall_for_run] behind that boundary.
    The checker's raw syscall acceptor is verified against the relational
    specs, then its successful post-model is charged for the effect's
    copy-in/copy-out ranges exactly as [Run.sstep_syscall] charges them.  A
    caller assembles a [RawInput] (registers, the captured pre-syscall
    memory as the byte runs it holds, and a predicate saying which
    addresses the kernel may write) and a
    [RawEffect] (observed return value plus the captured output buffers)
    for each real syscall and folds this accounted checker over the run.

    [N]/[Z]/[positive] are realized with zarith's [Big_int_Z] so OCaml
    can build argument/return values from parsed integers cheaply.  They
    carry erased invariants of their own — a [positive] is at least 1 and
    an [N] is not negative — so no root below takes one from a caller;
    every width this surface mentions is fixed inside Rocq. *)

From Stdlib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlZBigInt.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import
  ExecutableSpecs CheckedInput.

Require Extraction.

(* Roots: the checked checker and the checked initial state, the raw
   record constructors a caller fills in ([mkRawInput], [mkRawEffect],
   [mkRawProcInput], [mkRawPeer], and the three the seed's kernel build
   is assembled from, [mkRawKernelBuild], [mkRawCacheView] and
   [mkRawCacheLeaf]), the two scalar checkers a caller needs
   to validate a value it is about to put somewhere else ([word_of_Z],
   [byte_of_Z]), [execfn_shape_b], the exec file name's launch
   condition on its own, so that a caller can tell a name that is not
   a VALUE from one no launch could have presented before it seeds a
   model, [image_shape_b] and [fs_of_raw], which say the same two
   things about the file-system image the run is launched over --
   [fs_of_raw] answers whether the image is a VALUE (a byte of it no
   [byte] holds refuses it) and [image_shape_b] answers, of an image
   [fs_of_raw] converted, whether it describes a file system at all,
   which is [Run.valid_input]'s [Fs.fs_image_real] conjunct that
   revision/linux-only added; the image needs the two roots because
   that test reads the keys as paths and so can only be asked after
   the bytes are bytes, while the exec name's two tests are facts
   about the integers themselves, [wmem_ranges], the writable-address
   predicate a reader
   that holds ranges rather than a per-page test hands in, and
   [raw_of_effect], the way back for an effect the
   caller built with the model's own constructors below -- it is checked
   like any other outside value, so no root hands the checker a word that
   did not pass the boundary.  Then: the
   fd-table lookup (a caller needs it on the write, readv and writev
   paths, to decide which user memory a transfer touched; read's own
   capture is fd-blind and never asks the kind), error-encoding helpers, the iovec layout decoder that
   picks which guest ranges to capture (no spec reaches it,
   so it is not extracted transitively; see [State.read_iovecs] for why
   it is the validation-free one), the mmap argument-shape
   predicates and the mremap flag word,
   the futex predicate deciding whether a call read its word
   (a root rather than a transitively reached name, because the checker
   states that gate in its own order and never reaches this spelling; and
   a shared definition rather than a second copy in OCaml, with
   [Checks.Sys.Kernel.Futex.Syscalls.futex_copyins_exact] proving it
   describes the ledger every answered call carries), the effect components a caller would otherwise re-derive
   in OCaml ([brk_zeros], [brk_unmaps]) together with the two whole mremap
   effect records that hold all three mremap ledgers
   ([mremap_inplace_effect], [mremap_move_effect] -- [mremap_tail] itself is
   reached only through them, so it is not a root), and the model
   projections.

   [check_syscall_for_run], [init_model], [mkInput], [mkEffectU],
   [mkCopy] and [net_silent] are NOT roots any more: each is reached
   through its checked form, and naming one here would publish a way into
   the checker that no boundary guards.  (The generated .mli publishes
   everything the roots reach, these included, so no choice of roots can
   hide them; the roots are what this tree supports, and what a reader
   must use.) *)
Extraction "syscall_model.ml"
  check_syscall_for_run_checked
  init_model_checked
  mkRawInput
  mkRawEffect
  mkRawProcInput
  mkRawPeer
  mkRawKernelBuild
  mkRawCacheView
  mkRawCacheLeaf
  raw_of_effect
  execfn_shape_b
  image_shape_b
  fs_of_raw
  wmem_ranges
  word_of_Z
  byte_of_Z
  fd_lookup
  fs_lookup
  addr_is_error_b
  errno_ret
  read_iovecs
  two_pow_64
  page_round_up_Z
  page_round_down_Z
  map_has
  mmap_modeled_b
  mmap_noaccess_b
  mmap_fixed_noaccess_b
  mmap_fixed_rw_b
  mmap_noreplace_noaccess_b
  mmap_noreplace_rw_b
  madvise_dontneed_b
  madvise_dontneed_ok
  int32
  futex_wait_reads_b
  FUTEX_WORD_SIZE
  MREMAP_MAYMOVE
  sp_window_lo
  mmap_base_min
  State.TASK_SIZE
  mmap_base_max
  brk_zeros
  brk_unmaps
  mremap_inplace_effect
  mremap_move_effect
  brk_aslr_max
  reserved_top
  m_fds
  m_halted
  m_killed
  m_vmmaps
  m_fs
  vm_brk
  vm_maps
  vm_noaccess
  vm_reserved.
