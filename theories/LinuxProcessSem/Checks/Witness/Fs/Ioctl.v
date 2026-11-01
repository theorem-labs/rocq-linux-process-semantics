(** * LinuxProcessSem.Checks.Witness.Fs.Ioctl — the ioctl (29) witnesses, and their proofs

    Mirrors [Sys/Fs/Ioctl.v], which answers to Linux [fs/ioctl.c]: this
    file holds the witnesses for the syscalls defined there, and no
    others.

    [Checks/Progress.v] keeps the dispatcher and
    re-exports this module. A witness here exhibits one admissible
    outcome for a spec in the matching [Sys] module, which is what
    progress is proved from. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
Import ListNotations.
Open Scope bv_scope.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Witness Require Export
  Prelude Fs.ReadWrite.

(** Mirrors [Ioctl.siocgifindex_spec]: -EFAULT when the 40 bytes cannot
    be read, [Unmodeled] for any name but "lo", then the write-back
    when all of it lands, -EFAULT (with the copy-in recorded) when none
    of it does, and [Unmodeled] for a partial landing. *)
Definition siocgifindex_witness (argp : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match copy_bytes_map (in_mem i) argp IFREQ_SIZE with
  | None => ret_outcome (errno_ret EFAULT) m
  | Some ifr =>
      if negb (ifreq_names_lo ifr) then Unmodeled
      else
        match read_bytes_map (in_wmem i) argp (Z_to_bv 64 IFREQ_SIZE) with
        | Some _ =>
            Ok (with_copyins [(argp, Z.to_nat IFREQ_SIZE)]
                  (mkEffect (Z_to_bv 64 0)
                     [(argp, ifreq_with_index ifr LOOPBACK_IFINDEX)] []))
               m []
        | None =>
            match read_bytes_map (in_wmem i) argp (Z_to_bv 64 1) with
            | None =>
                Ok (with_copyins [(argp, Z.to_nat IFREQ_SIZE)]
                      (mkEffect (errno_ret EFAULT) [] []))
                   m []
            | Some _ => Unmodeled
            end
        end
  end.

Lemma siocgifindex_witness_ok : forall argp i m,
  siocgifindex_spec argp i i m (siocgifindex_witness argp i m).
Proof.
  intros. unfold siocgifindex_spec, siocgifindex_witness.
  destruct (copy_bytes_map (in_mem i) argp IFREQ_SIZE) as [ifr|]; cbv iota;
    [|apply pure_ok].
  destruct (ifreq_names_lo ifr); cbn [negb];
    [|apply record_copyins_unmodeled; apply unmodeled_intro].
  destruct (read_bytes_map (in_wmem i) argp (Z_to_bv 64 IFREQ_SIZE)); cbv iota.
  - apply record_copyins_ok_empty; [reflexivity|]. apply pure_ok.
  - destruct (read_bytes_map (in_wmem i) argp (Z_to_bv 64 1)); cbv iota.
    + apply record_copyins_unmodeled. apply unmodeled_intro.
    + apply record_copyins_ok_empty; [reflexivity|]. apply pure_ok.
Qed.

Definition ioctl_witness (fd req : word) (i : SyscallInput) (m : Model)
    : outcome SyscallEffect :=
  match fd_lookup (m_fds m) fd with
  | None => ret_outcome (errno_ret EBADF) m
  | Some (FdChannel _) | Some (FdFile _ _) | Some (FdFileW _ _) | Some FdDir
  | Some (FdSocket _) | Some (FdStream _ _ _) | Some (FdEventfd _) | Some (FdPipe _ _)
  | Some (FdFileA _ _) | Some (FdFileRW _ _) | Some (FdDevNull _ _) =>
      if tty_only_request req then ret_outcome (errno_ret ENOTTY) m
      else Unmodeled
  | Some FdUrandom => Unmodeled
  | Some (FdDgram _) =>
      if tty_only_request req then ret_outcome (errno_ret ENOTTY) m
      else if bv_eqb req SIOCGIFINDEX then siocgifindex_witness (in_arg i 2) i m
      else Unmodeled
  end.

Lemma ioctl_witness_ok : forall fd req i m, ioctl_spec fd req i m (ioctl_witness fd req i m).
Proof.
  intros. unfold ioctl_spec, ioctl_witness.
  destruct (fd_lookup (m_fds m) fd) as [e|] eqn:Hfd.
  - (* the open-fd arms are enumerated, so [e] must be destructed for the
       match to reduce; every constructor answers the terminal requests
       alike. *)
    destruct e; destruct (tty_only_request req) eqn:Hr;
      (eapply bind_step; [apply get_model_ok|]);
      cbv beta iota; srw Hfd;
      try first [apply pure_ok | apply unmodeled_intro].
    (* what is left is the datagram socket past the terminal requests *)
    destruct (bv_eqb req SIOCGIFINDEX); [|apply unmodeled_intro].
    eapply bind_step; [apply input_ok|]. cbv beta.
    apply siocgifindex_witness_ok.
  - eapply bind_step; [apply get_model_ok|].
    cbv beta iota; srw Hfd. apply pure_ok.
Qed.
