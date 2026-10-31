(** * LinuxProcessSem.Checks.Cases.Drivers.Char.Random — worked examples over getrandom (278)

    Mirrors [Sys/Drivers/Char/Random.v], which answers to Linux
    [drivers/char/random.c]: this file holds the worked examples for
    the syscalls defined there, and no others.

    [Checks/Examples.v] keeps what is not per-syscall and
    re-exports this module. These are worked examples
    over the specs and checkers for the matching [Sys] module, read off
    without running a binary. *)

From Stdlib Require Import ZArith List Bool Lia String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad Specs Run StackLayout MemImageType RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Decode DecodeC.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Cases Require Export
  Prelude.

(** A writable landing zone at 4096, wide enough for a request above
    [Random.getrandom_small_max]. *)

Definition getrandom_dest : word -> option byte :=
  fun a => if bv_leu 4096 a && bv_ltu a 4608 then Some 0 else None.

Definition getrandom_model : Model :=
  init_model [] 0 0 demo_sp demo_limit (demo_input [] IEof).

(** One getrandom(4096, buflen, 0) over that zone. *)

Definition getrandom_call (buflen : Z) : SyscallInput :=
  mkInput 278 [4096; Z_to_bv 64 buflen; 0; 0; 0; 0] getrandom_dest getrandom_dest.

(** [n] environment bytes, all the same. *)

Definition some_bytes (n : nat) : list byte := repeat (Z_to_bv 8 7) n.

(** A SMALL REQUEST IS DELIVERED IN FULL, AND ONLY IN FULL.  ADMISSION
    REASON: the environment cannot be made to produce what this
    REJECTS.  A real kernel never cuts a request of at most
    [Random.getrandom_small_max] bytes short and never interrupts it,
    so no execution can show the short count or the -EINTR being
    refused; this pins them against the checker directly.

    The first conjunct is what makes the rejections say something: the
    full delivery on the same call is ACCEPTED, so the rejections are
    of the count and the errno, not of the call. *)

Example getrandom_small_request_is_delivered_in_full :
  check_syscall (getrandom_call 16)
    (mkEffect 16 [(4096, some_bytes 16)] []) getrandom_model
  = CheckOk getrandom_model []
  (* the short count Linux cannot produce below the bound *)
  /\ check_syscall (getrandom_call 16)
       (mkEffect 5 [(4096, some_bytes 5)] []) getrandom_model
     = CheckReject
  (* nor the interrupted return *)
  /\ check_syscall (getrandom_call 16)
       (mkEffect (errno_ret EINTR) [] []) getrandom_model
     = CheckReject
  (* and over-delivery stays out, as everywhere *)
  /\ check_syscall (getrandom_call 16)
       (mkEffect 17 [(4096, some_bytes 17)] []) getrandom_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** THE BOUND IS INCLUSIVE.  ADMISSION REASON: it pins the exact edge
    of the narrowing, which no execution reaches — a real kernel
    delivers both of these requests in full.
    A request of exactly [Random.getrandom_small_max] bytes is small;
    one byte more is large, and its short count is admitted again. *)

Example getrandom_small_bound_is_inclusive :
  check_syscall (getrandom_call 256)
    (mkEffect 255 [(4096, some_bytes 255)] []) getrandom_model
  = CheckReject
  /\ check_syscall (getrandom_call 256)
       (mkEffect 256 [(4096, some_bytes 256)] []) getrandom_model
     = CheckOk getrandom_model []
  /\ check_syscall (getrandom_call 257)
       (mkEffect 255 [(4096, some_bytes 255)] []) getrandom_model
     = CheckOk getrandom_model [].
Proof. repeat split; check_eq. Qed.

(** A LARGE REQUEST STILL ADMITS THE SHORT COUNT AND -EINTR, and still
    refuses the bare 0.  ADMISSION REASON: the environment cannot be
    made to produce it — with no signal, a real kernel delivers a
    large request in full too, and the admissions below are
    what keep a signal-interrupted large request from being rejected
    as impossible. *)

Example getrandom_large_request_still_admits_the_short_count :
  check_syscall (getrandom_call 300)
    (mkEffect 300 [(4096, some_bytes 300)] []) getrandom_model
  = CheckOk getrandom_model []
  /\ check_syscall (getrandom_call 300)
       (mkEffect 5 [(4096, some_bytes 5)] []) getrandom_model
     = CheckOk getrandom_model []
  /\ check_syscall (getrandom_call 300)
       (mkEffect (errno_ret EINTR) [] []) getrandom_model
     = CheckOk getrandom_model []
  (* a nonzero request never "succeeds" with nothing delivered *)
  /\ check_syscall (getrandom_call 300)
       (mkEffect 0 [] []) getrandom_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(* =========================================================================
   THE DESTINATION THAT WALKED OFF THE TOP OF THE ADDRESS SPACE

   [Random.getrandom_spec] read its destination with [State.read_bytes_map]
   bare, a walk that wraps at 2^64 (see [State.copy_bytes_map]'s note), so
   a [buf] in the last bytes of the address space whose range was backed
   at both ends was ANSWERED: the bytes were delivered and the count
   returned.  Linux refuses the range in [import_ubuf] (lib/iov_iter.c),
   which asks [access_ok] before a byte moves, and the arm now asks the
   same through [State.copy_bytes_map].  The interrupted return stays
   beside the -EFAULT: [SYSCALL_DEFINE3(getrandom, ...)]
   (drivers/char/random.c) runs [wait_for_random_bytes] BEFORE the import.

   Each group is the refusal at a small and a large length, the control
   that the bare walk really would have passed, and a neighbour at the
   top of what [State.access_okb] accepts that is still answered.  The
   memories map exactly their own range: [wmem_open] answers [Some]
   everywhere and could not tell a wrapping pointer from any other.
   ========================================================================= *)

Definition getrandom_wrap_buf : word := Z_to_bv 64 (2 ^ 64 - 8).

(** The last eight bytes and the first [n - 8]: exactly the [n]-byte range
    that starts at [getrandom_wrap_buf] and wraps. *)
Definition getrandom_wrap_mem (n : Z) : word -> option byte :=
  fun a => if ((bv_unsigned a <? n - 8)%Z || (2 ^ 64 - 8 <=? bv_unsigned a)%Z)%bool
           then Some 0 else None.

Definition getrandom_wrap_call (n : Z) : SyscallInput :=
  mkInput 278 [getrandom_wrap_buf; Z_to_bv 64 n; 0; 0; 0; 0]
    (getrandom_wrap_mem n) (getrandom_wrap_mem n).

Example getrandom_wrap_would_pass_the_bare_walk :
  read_bytes_map (getrandom_wrap_mem 16) getrandom_wrap_buf (Z_to_bv 64 16)
    <> None
  /\ read_bytes_map (getrandom_wrap_mem 300) getrandom_wrap_buf (Z_to_bv 64 300)
       <> None.
Proof. split; vm_compute; discriminate. Qed.

Example getrandom_wrap_buffer_is_not_copyable :
  copy_bytes_map (getrandom_wrap_mem 16) getrandom_wrap_buf 16 = None
  /\ copy_bytes_map (getrandom_wrap_mem 300) getrandom_wrap_buf 300 = None.
Proof. split; vm_compute; reflexivity. Qed.

(** A SMALL REQUEST THAT WRAPS IS -EFAULT, and the full delivery the bare
    walk admitted is refused.  -EINTR is admitted beside it, and this is
    the one place a nonzero small request admits it:
    [getrandom_small_request_is_delivered_in_full] refuses it on a
    request that is delivered, and this request never reaches the
    delivery. *)
Example getrandom_wrapping_small_request_is_efault :
  check_syscall (getrandom_wrap_call 16)
    (mkEffect (errno_ret EFAULT) [] []) getrandom_model
  = CheckOk getrandom_model []
  /\ check_syscall (getrandom_wrap_call 16)
       (mkEffect (errno_ret EINTR) [] []) getrandom_model
     = CheckOk getrandom_model []
  (* the delivery the bare walk admitted *)
  /\ check_syscall (getrandom_wrap_call 16)
       (mkEffect 16 [(getrandom_wrap_buf, some_bytes 16)] []) getrandom_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** The same above the small-request bound, where the bare walk admitted
    a short delivery as well. *)
Example getrandom_wrapping_large_request_is_efault :
  check_syscall (getrandom_wrap_call 300)
    (mkEffect (errno_ret EFAULT) [] []) getrandom_model
  = CheckOk getrandom_model []
  /\ check_syscall (getrandom_wrap_call 300)
       (mkEffect (errno_ret EINTR) [] []) getrandom_model
     = CheckOk getrandom_model []
  /\ check_syscall (getrandom_wrap_call 300)
       (mkEffect 5 [(getrandom_wrap_buf, some_bytes 5)] []) getrandom_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** THE NEIGHBOURS, and the half that says the arm still works: the last
    [n] bytes [State.access_okb] accepts, mapped end to end.  The small
    request is still delivered in full and the large one still admits
    its short count, and -EFAULT is refused at both. *)
Definition getrandom_top_buf (n : Z) : word := Z_to_bv 64 (TASK_SIZE - n).

Definition getrandom_top_mem (n : Z) : word -> option byte :=
  fun a => if ((TASK_SIZE - n <=? bv_unsigned a)%Z
               && (bv_unsigned a <? TASK_SIZE)%Z)%bool
           then Some 0 else None.

Definition getrandom_top_call (n : Z) : SyscallInput :=
  mkInput 278 [getrandom_top_buf n; Z_to_bv 64 n; 0; 0; 0; 0]
    (getrandom_top_mem n) (getrandom_top_mem n).

Example getrandom_at_the_top_still_delivers :
  check_syscall (getrandom_top_call 16)
    (mkEffect 16 [(getrandom_top_buf 16, some_bytes 16)] []) getrandom_model
  = CheckOk getrandom_model []
  /\ check_syscall (getrandom_top_call 16)
       (mkEffect (errno_ret EFAULT) [] []) getrandom_model
     = CheckReject
  /\ check_syscall (getrandom_top_call 300)
       (mkEffect 5 [(getrandom_top_buf 300, some_bytes 5)] []) getrandom_model
     = CheckOk getrandom_model []
  /\ check_syscall (getrandom_top_call 300)
       (mkEffect (errno_ret EFAULT) [] []) getrandom_model
     = CheckReject.
Proof. repeat split; check_eq. Qed.

(** A range [State.access_okb] ADMITS with nothing behind it is declined,
    not answered -EFAULT: the house rule [Kernel.Sys.prlimit64_spec]'s
    note states, which keeps -EFAULT for the ranges [access_ok] refuses. *)
Example getrandom_admitted_but_unbacked_declines :
  check_syscall (mkInput 278 [getrandom_top_buf 16; 16; 0; 0; 0; 0]
                   (fun _ => None) (fun _ => None))
    (mkEffect (errno_ret EFAULT) [] []) getrandom_model
  = CheckUnmodeled.
Proof. check_eq. Qed.
