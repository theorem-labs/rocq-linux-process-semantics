(** * Tests: the extracted checker's input boundary refuses out-of-type values

    These are the tests for [Checks.CheckedInput].  Each one feeds the
    boundary an integer that the Rocq type it would have to inhabit does
    not hold, and shows the answer is [CheckedRefused] — the boundary's
    third answer, which is NOT a verdict — rather than [CheckedAnswer _].
    Beside each refusal is the in-range control that shows the same call
    IS judged when the value is one a machine could produce, so the tests
    cannot pass by refusing everything.

    THE WITNESS.  [witness_effect_2_64] is the effect of record [seq 1] of
    theorem-labs/linux-process-semantics at ff0313ba4f,
    testing/syscall-check/traces/set_tid/022.jsonl, case
    [reject --mutate set_tid_address#2:ret=2^64]: a [set_tid_address]
    (riscv64 syscall 96) whose observed return value is
    18446744073709551616.  The extracted checker gave that record the
    verdict [reject]; a0 is 64 bits wide
    (arch/riscv/include/asm/syscall.h, [syscall_set_return_value], Linux
    v6.18.46, commit 1f99e9ab748f), so no kernel produced it and no
    theorem of this tree covers that verdict.  [witness_effect_ok] is the
    same record's unmutated return, 624. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import CheckedInput.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* The primitive                                                       *)
(* ------------------------------------------------------------------ *)

Example word_2_64_refused : word_of_Z 18446744073709551616 = None.
Proof. vm_compute. reflexivity. Qed.

Example word_max64_accepted :
  option_map bv_unsigned (word_of_Z 18446744073709551615)
  = Some 18446744073709551615.
Proof. vm_compute. reflexivity. Qed.

Example word_negative_refused : word_of_Z (-1) = None.
Proof. vm_compute. reflexivity. Qed.

Example byte_256_refused : byte_of_Z 256 = None.
Proof. vm_compute. reflexivity. Qed.

Example byte_255_accepted :
  option_map bv_unsigned (byte_of_Z 255) = Some 255.
Proof. vm_compute. reflexivity. Qed.

Example byte_negative_refused : byte_of_Z (-1) = None.
Proof. vm_compute. reflexivity. Qed.

Example bv32_refused : bv32_of_Z 4294967296 = None.
Proof. vm_compute. reflexivity. Qed.

Example bv16_refused : bv16_of_Z 65536 = None.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The witness: a return value no 64-bit word holds                    *)
(* ------------------------------------------------------------------ *)

(** set_tid_address(2) as the trace records it: syscall 96, one pointer
    argument, no captured memory and no writable range (the call reads
    and writes nothing). *)
Definition witness_input : RawInput :=
  mkRawInput 96 [274877906944; 0; 0; 0; 0; 0] [] [].

Definition witness_effect_2_64 : RawEffect :=
  mkRawEffect 18446744073709551616 [] [] [] [] [].

Definition witness_effect_ok : RawEffect :=
  mkRawEffect 624 [] [] [] [] [].

(** The defect, closed: the boundary refuses, for every model. *)
Example witness_is_refused : forall m,
  check_syscall_for_run_checked witness_input witness_effect_2_64 m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(** And it is refused BEFORE the checker runs: the effect has no
    in-type reading at all. *)
Example witness_effect_has_no_reading :
  effect_of_raw witness_effect_2_64 = None.
Proof. vm_compute. reflexivity. Qed.

(** The control: the same call with the return value the kernel really
    gave is judged, not refused. *)
Example witness_in_range_is_judged : forall m,
  exists a, check_syscall_for_run_checked witness_input witness_effect_ok m
            = CheckedAnswer a.
Proof.
  intro m. unfold check_syscall_for_run_checked.
  destruct (input_of_raw witness_input) as [i|] eqn:Hi;
    [|vm_compute in Hi; discriminate Hi].
  destruct (effect_of_raw witness_effect_ok) as [e|] eqn:He;
    [|vm_compute in He; discriminate He].
  eexists. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* One test per place an out-of-type value can enter a syscall         *)
(* ------------------------------------------------------------------ *)

(* word: the syscall number *)
Example sysno_out_of_range_refused : forall m,
  check_syscall_for_run_checked
    (mkRawInput 18446744073709551616 [] [] []) witness_effect_ok m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word: a register argument *)
Example arg_out_of_range_refused : forall m,
  check_syscall_for_run_checked
    (mkRawInput 96 [0; 18446744073709551616] [] []) witness_effect_ok m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word: the address of a captured readable run *)
Example mem_address_out_of_range_refused : forall m,
  check_syscall_for_run_checked
    (mkRawInput 96 [] [(18446744073709551616, [1])] []) witness_effect_ok m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* byte: a captured readable byte *)
Example mem_byte_out_of_range_refused : forall m,
  check_syscall_for_run_checked
    (mkRawInput 96 [] [(4096, [0; 256])] []) witness_effect_ok m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word: a writable range *)
Example wmem_range_out_of_range_refused : forall m,
  check_syscall_for_run_checked
    (mkRawInput 96 [] [] [(4096, 18446744073709551616)]) witness_effect_ok m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* byte: a byte the kernel is said to have written *)
Example write_byte_out_of_range_refused : forall m,
  check_syscall_for_run_checked witness_input
    (mkRawEffect 0 [(4096, [256])] [] [] [] []) m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word: a zero-filled range *)
Example zeros_out_of_range_refused : forall m,
  check_syscall_for_run_checked witness_input
    (mkRawEffect 0 [] [(18446744073709551616, 4096)] [] [] []) m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word: an unmapped range *)
Example unmaps_out_of_range_refused : forall m,
  check_syscall_for_run_checked witness_input
    (mkRawEffect 0 [] [] [(0, 18446744073709551616)] [] []) m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word: a symbolic copy *)
Example copies_out_of_range_refused : forall m,
  check_syscall_for_run_checked witness_input
    (mkRawEffect 0 [] [] [] [(0, 0, 18446744073709551616)] []) m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* word, and the nat beside it: a copy-in ledger entry *)
Example copyin_address_out_of_range_refused : forall m,
  check_syscall_for_run_checked witness_input
    (mkRawEffect 0 [] [] [] [] [(18446744073709551616, 8)]) m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

Example copyin_negative_length_refused : forall m,
  check_syscall_for_run_checked witness_input
    (mkRawEffect 0 [] [] [] [] [(4096, -1)]) m
  = CheckedRefused.
Proof. intro m. vm_compute. reflexivity. Qed.

(* the in-range controls for the effect components *)
Example effect_components_in_range_are_judged : forall m,
  exists a, check_syscall_for_run_checked witness_input
              (mkRawEffect 0 [(4096, [255])] [(4096, 4096)] [(8192, 4096)]
                 [(0, 4096, 8)] [(4096, 8)]) m
            = CheckedAnswer a.
Proof.
  intro m. unfold check_syscall_for_run_checked.
  destruct (input_of_raw witness_input) as [i|] eqn:Hi;
    [|vm_compute in Hi; discriminate Hi].
  destruct (effect_of_raw _) as [e|] eqn:He;
    [|vm_compute in He; discriminate He].
  eexists. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* One test per place an out-of-type value can enter the model's seed  *)
(* ------------------------------------------------------------------ *)

Definition raw_seed : RawProcInput :=
  mkRawProcInput [] [] [] [] 0 0 [] [] 1024 0 4397 false Sv48 [] [].

Example seed_is_accepted :
  exists m, init_model_checked [] 4096 4096 4096 0 raw_seed = Some m.
Proof.
  unfold init_model_checked.
  destruct (pairs_of_Z []) eqn:E1; [|vm_compute in E1; discriminate E1].
  destruct (word_of_Z 4096) eqn:E2; [|vm_compute in E2; discriminate E2].
  destruct (proc_input_of_raw raw_seed) eqn:E3;
    [|vm_compute in E3; discriminate E3].
  eexists. reflexivity.
Qed.

(* word: the reserved segments, the break, the mmap base, the stack *)
Example seed_reserved_out_of_range_refused :
  init_model_checked [(18446744073709551616, 4096)] 4096 4096 4096 0 raw_seed
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_brk_out_of_range_refused :
  init_model_checked [] 18446744073709551616 4096 4096 0 raw_seed = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_mmap_base_out_of_range_refused :
  init_model_checked [] 4096 18446744073709551616 4096 0 raw_seed = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_sp_out_of_range_refused :
  init_model_checked [] 4096 4096 18446744073709551616 0 raw_seed = None.
Proof. vm_compute. reflexivity. Qed.

(* word: the credentials and the launch limits *)
Example seed_uid_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 18446744073709551616 0 [] [] 1024 0 4397
       false Sv48 [] []) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_group_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 [18446744073709551616] [] 1024 0 4397
       false Sv48 [] []) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_nofile_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 [] [] 18446744073709551616 0 4397
       false Sv48 [] []) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_sigmask_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 [] [] 1024 18446744073709551616 4397
       false Sv48 [] []) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_hwcap_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 [] [] 1024 0 18446744073709551616
       false Sv48 [] []) = None.
Proof. vm_compute. reflexivity. Qed.

(* byte: argv, envp, the file system, standard input, the random device *)
Example seed_argv_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [[256]] [] [] [] 0 0 [] [] 1024 0 4397 false Sv48 [] [])
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_envp_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [[256]] [] [] 0 0 [] [] 1024 0 4397 false Sv48 [] [])
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_fs_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [([97], [256])] [] 0 0 [] [] 1024 0 4397
       false Sv48 [] []) = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_stdin_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [256] 0 0 [] [] 1024 0 4397 false Sv48 [] [])
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_urandom_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 [] [] 1024 0 4397 false Sv48 [256] [])
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_tmp_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 [] [] 1024 0 4397 false Sv48 []
       [([97], [256])]) = None.
Proof. vm_compute. reflexivity. Qed.

(* bv 32 and bv 16: a network peer's address and port *)
Example seed_peer_addr_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 []
       [mkRawPeer 4294967296 80 [] RneFin] 1024 0 4397 false Sv48 [] [])
  = None.
Proof. vm_compute. reflexivity. Qed.

Example seed_peer_port_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 []
       [mkRawPeer 0 65536 [] RneFin] 1024 0 4397 false Sv48 [] [])
  = None.
Proof. vm_compute. reflexivity. Qed.

(* byte: what a peer says *)
Example seed_peer_byte_out_of_range_refused :
  init_model_checked [] 4096 4096 4096 0
    (mkRawProcInput [] [] [] [] 0 0 []
       [mkRawPeer 0 80 [256] RneFin] 1024 0 4397 false Sv48 [] [])
  = None.
Proof. vm_compute. reflexivity. Qed.

(* the in-range control for the seed's structured fields *)
Definition raw_seed_full : RawProcInput :=
  mkRawProcInput [[112; 0]] [[65; 0]] [([97], [1; 255])] [0; 255] 1000 1000
    [1000] [mkRawPeer 2130706433 80 [255] RneRst] 1024 0 4397 false Sv48
    [7] [([98], [2])].

Example seed_structured_fields_in_range_accepted :
  exists m, init_model_checked [(4096, 4096)] 8192 12288 16384 65536
              raw_seed_full = Some m.
Proof.
  unfold init_model_checked.
  destruct (pairs_of_Z [(4096, 4096)]) eqn:E1; [|vm_compute in E1; discriminate E1].
  destruct (word_of_Z 8192) eqn:E2; [|vm_compute in E2; discriminate E2].
  destruct (word_of_Z 12288) eqn:E3; [|vm_compute in E3; discriminate E3].
  destruct (word_of_Z 16384) eqn:E4; [|vm_compute in E4; discriminate E4].
  destruct (proc_input_of_raw raw_seed_full) eqn:E5;
    [|vm_compute in E5; discriminate E5].
  eexists. reflexivity.
Qed.
