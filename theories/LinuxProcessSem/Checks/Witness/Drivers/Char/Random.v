(** * LinuxProcessSem.Checks.Witness.Drivers.Char.Random — the getrandom (278) witnesses, and their proofs

    Mirrors [Sys/Drivers/Char/Random.v], which answers to Linux
    [drivers/char/random.c]: this file holds the witnesses for the
    syscalls defined there, and no others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude.

(** getrandom's witness.  A nonzero request of at most
    [Random.getrandom_small_max] bytes has ONE admissible shape — full
    delivery — so the witness exhibits it with all-zero bytes (the
    bytes are the environment's; any list of the right length is
    admissible).  Every other answered request answers -EINTR, which
    joins the -EFAULT of a range [access_ok] refuses (at every length),
    the 0 of an admitted zero-byte request and the delivery alternative
    of a large request.  A range [access_ok] admits that the memory does
    not wholly back is [Unmodeled], as in the spec. *)

Definition getrandom_witness (buf buflen flags : word) (i : SyscallInput)
    (m : Model) : outcome SyscallEffect :=
  if negb (Z.eqb (bv_unsigned flags) 0 || Z.eqb (bv_unsigned flags) GRND_NONBLOCK)
  then Unmodeled
  else if negb (modeled_rw_count buflen) then Unmodeled   (* see [rw_bytes_max] *)
  else match copy_bytes_map (in_wmem i) buf (bv_unsigned buflen) with
       | None =>
           if negb (access_okb buf (bv_unsigned buflen))
           then ret_outcome (errno_ret EINTR) m   (* -EINTR joins the -EFAULT *)
           else Unmodeled                        (* admitted, not wholly writable *)
       | Some _ =>
           if negb (w_is0 buflen) && (bv_unsigned buflen <=? getrandom_small_max)%Z
           then (* the small request: delivered in full, and only that *)
             let bs := repeat (Z_to_bv 8 0) (Z.to_nat (bv_unsigned buflen)) in
             Ok (mkEffect (len_word bs) [(buf, bs)] []) m []
           else ret_outcome (errno_ret EINTR) m   (* -EINTR joins every other verdict *)
       end.

Lemma getrandom_witness_ok : forall buf buflen flags i m,
  getrandom_spec buf buflen flags i m (getrandom_witness buf buflen flags i m).
Proof.
  intros. unfold getrandom_spec, getrandom_witness.
  destruct (negb (Z.eqb (bv_unsigned flags) 0
                  || Z.eqb (bv_unsigned flags) GRND_NONBLOCK)) eqn:Hf.
  - apply unmodeled_intro.
  - destruct (negb (modeled_rw_count buflen)) eqn:Hn; [apply unmodeled_intro|].
    destruct (copy_bytes_map (in_wmem i) buf (bv_unsigned buflen)) as [ok|] eqn:Hw.
    + eapply bind_step; [apply input_ok|]. cbv beta iota zeta; srw Hw.
      destruct (w_is0 buflen) eqn:Hz; cbn [negb andb].
      * apply alt_l; (eapply bind_step; [apply errno_head_witness|]); apply pure_ok.
      * destruct (bv_unsigned buflen <=? getrandom_small_max)%Z eqn:Hsm.
        { (* the small request: the chosen list has exactly [buflen] bytes *)
          cbv zeta. eapply bind_step; [|apply pure_ok].
          apply choose_ok. cbv beta. rewrite repeat_length.
          pose proof (bv_unsigned_in_range _ buflen). lia. }
        apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
    + eapply bind_step; [apply input_ok|]. cbv beta iota zeta; srw Hw.
      destruct (negb (access_okb buf (bv_unsigned buflen))); cbv iota.
      * apply alt_l. eapply bind_step; [apply errno_head_witness|]. apply pure_ok.
      * apply unmodeled_intro.
Qed.

(* =========================================================================
   exit (93) / exit_group (94) — deterministic
   ========================================================================= *)
