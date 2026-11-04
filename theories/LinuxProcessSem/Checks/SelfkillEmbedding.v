(** * LinuxProcessSem.Checks.SelfkillEmbedding — earlier launch statements embed unchanged

    Not part of the trusted specification: a theorem ABOUT it.

    [ProcInput23] has fields 1-23 of commit 604b5c371ed0. [embed]
    supplies false for both the self-kill declaration (field 24) and
    the cgroup-BPF setsockopt launch value (field 25),
    [State.no_clone_refusers] for the host's clone refusers (field 26),
    and [true], SIG_DFL, for the launch's SIGCHLD disposition (field 27).
    The images are exactly the inputs with those four defaults. [CgroupBpfEmbedding]
    separately states the 24-to-25 layer, including inputs whose
    self-kill declaration is true.

    Each [V_pre] body below is copied word for word from 604b5c371ed0;
    [tools/check_pre_copies.py] checks those copies and the table-number
    list against that immutable source. [embeds] composes the four
    layers: V inp iff V_pre inp /\ selfkill=false /\ cgroup_bpf=false
    /\ clone_refusers=no_clone_refusers /\ sigchld_default=true. No
    copied body or mechanical comparison is changed by composition.
    [embeds_excludes], [embeds_excludes_clone_refusers] and
    [embeds_excludes_sigchld_ignored] exclude the inputs fields 24, 26
    and 27 add; [embeds_covers_images] says every admitted input is an
    image.

    [spec_table_pre] removes row 129 from the current table. The run
    lemmas below establish that the self-kill declaration is initialized
    from the input and retained by every successful step, and that 129
    with it off declines just as an absent row did. This table is not
    a snapshot of later socket features: [CgroupBpfEmbedding] gives the
    separate false-field setsockopt table equivalence. Rows 220 and 435
    read field 26 ([Kernel.Fork.clone_refusable]): at its default, the
    value every image carries and no step changes
    ([Checks.CloneRefusersKept.star_clone_refusers_kept],
    [Checks.ProcsCloneRefusers.clone_refusers_reachable]), they answer
    exactly as before ([Kernel.Fork.clone_spec_default_iff],
    [Kernel.Fork.clone3_spec_default_iff]). The step and run relations
    continue to consult the table through [Specs.syscall_spec]. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase Fs State Monad StackLayout RiscvSemantics Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ProcsChildPidsFrame.
From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput.
Import ListNotations.

(* =========================================================================
   (0) The embedding
   ========================================================================= *)

(** Fields 1-23 of [State.ProcInput] at commit 604b5c371ed0
    (theories/LinuxProcessSem/State.v:7094-7384 there). *)
Record ProcInput23 := mkProcInput23 {
  p23_argv : list (list byte);
  p23_envp : list (list byte);
  p23_image_fs : Fs.Fs;
  p23_stdin : InputStream;
  p23_uid : word;
  p23_gid : word;
  p23_groups : list word;
  p23_net : NetQueue;
  p23_nofile : word;
  p23_sigmask : word;
  p23_hwcap : word;
  p23_abort_terminal : bool;
  p23_va_size : VaSize;
  p23_urandom : InputStream;
  p23_tmp : Fs.Fs;
  p23_kernel : KernelBuild;
  p23_execfn : list byte;
  p23_channel_reader : bool;
  p23_sigpipe_default : bool;
  p23_sigpipe_terminal : bool;
  p23_ppid : word;
  p23_cap_inheritable : word;
  p23_inherited_fds : list (word * list byte)
}.

(** An old input as a new one: fields 24 and 25 are [false], field 26
    is [State.no_clone_refusers], field 27 is [true] (SIG_DFL). *)
Definition embed (o : ProcInput23) : ProcInput :=
  {| in_argv := p23_argv o; in_envp := p23_envp o;
     in_image_fs := p23_image_fs o; in_stdin := p23_stdin o;
     in_uid := p23_uid o; in_gid := p23_gid o; in_groups := p23_groups o;
     in_net := p23_net o; in_nofile := p23_nofile o;
     in_sigmask := p23_sigmask o; in_hwcap := p23_hwcap o;
     in_abort_terminal := p23_abort_terminal o;
     in_va_size := p23_va_size o; in_urandom := p23_urandom o;
     in_tmp := p23_tmp o; in_kernel := p23_kernel o;
     in_execfn := p23_execfn o;
     in_channel_reader := p23_channel_reader o;
     in_sigpipe_default := p23_sigpipe_default o;
     in_sigpipe_terminal := p23_sigpipe_terminal o;
     in_ppid := p23_ppid o; in_cap_inheritable := p23_cap_inheritable o;
     in_inherited_fds := p23_inherited_fds o;
     in_selfkill_terminal := false; in_cgroup_bpf_setsockopt := false;
     in_clone_refusers := no_clone_refusers;
     in_sigchld_default := true |}.

(** A new input with fields 24 to 27 dropped. *)
Definition forget (inp : ProcInput) : ProcInput23 :=
  {| p23_argv := in_argv inp; p23_envp := in_envp inp;
     p23_image_fs := in_image_fs inp; p23_stdin := in_stdin inp;
     p23_uid := in_uid inp; p23_gid := in_gid inp;
     p23_groups := in_groups inp; p23_net := in_net inp;
     p23_nofile := in_nofile inp; p23_sigmask := in_sigmask inp;
     p23_hwcap := in_hwcap inp;
     p23_abort_terminal := in_abort_terminal inp;
     p23_va_size := in_va_size inp; p23_urandom := in_urandom inp;
     p23_tmp := in_tmp inp; p23_kernel := in_kernel inp;
     p23_execfn := in_execfn inp;
     p23_channel_reader := in_channel_reader inp;
     p23_sigpipe_default := in_sigpipe_default inp;
     p23_sigpipe_terminal := in_sigpipe_terminal inp;
     p23_ppid := in_ppid inp; p23_cap_inheritable := in_cap_inheritable inp;
     p23_inherited_fds := in_inherited_fds inp |}.

(** [inp] with field 24 set to [b], every other field kept.  Named for
    the input because [State.with_selfkill_terminal] is the MODEL's
    setter. *)
Definition input_with_selfkill_terminal (b : bool) (inp : ProcInput)
    : ProcInput :=
  {| in_argv := in_argv inp; in_envp := in_envp inp;
     in_image_fs := in_image_fs inp; in_stdin := in_stdin inp;
     in_uid := in_uid inp; in_gid := in_gid inp; in_groups := in_groups inp;
     in_net := in_net inp; in_nofile := in_nofile inp;
     in_sigmask := in_sigmask inp; in_hwcap := in_hwcap inp;
     in_abort_terminal := in_abort_terminal inp;
     in_va_size := in_va_size inp; in_urandom := in_urandom inp;
     in_tmp := in_tmp inp; in_kernel := in_kernel inp;
     in_execfn := in_execfn inp;
     in_channel_reader := in_channel_reader inp;
     in_sigpipe_default := in_sigpipe_default inp;
     in_sigpipe_terminal := in_sigpipe_terminal inp;
     in_ppid := in_ppid inp; in_cap_inheritable := in_cap_inheritable inp;
     in_inherited_fds := in_inherited_fds inp;
     in_selfkill_terminal := b;
     in_cgroup_bpf_setsockopt := in_cgroup_bpf_setsockopt inp;
     in_clone_refusers := in_clone_refusers inp;
     in_sigchld_default := in_sigchld_default inp |}.

(** Embedding loses nothing. *)
Lemma forget_embed : forall o, forget (embed o) = o.
Proof. intros []. reflexivity. Qed.

(** Every new input with the four later fields at their defaults is the
    image of exactly one old input ([forget_embed] gives uniqueness). *)
Lemma embed_forget : forall inp,
  in_selfkill_terminal inp = false ->
  in_cgroup_bpf_setsockopt inp = false ->
  in_clone_refusers inp = no_clone_refusers ->
  in_sigchld_default inp = true -> embed (forget inp) = inp.
Proof.
  intros [a e fs s u g gs n nf sm hc ab va r tm kb xf cr sd st pp ci ifd sk bp crf scd]
    Hsk Hbp Hcrf Hscd.
  cbn [in_selfkill_terminal] in Hsk.
  cbn [in_cgroup_bpf_setsockopt] in Hbp.
  cbn [in_clone_refusers] in Hcrf.
  cbn [in_sigchld_default] in Hscd. subst sk bp crf scd. reflexivity.
Qed.

(** Every thirteen-place literal has field 24 off
    ([State.mkProcInput_selfkill_terminal] is the same fact), field 25
    off ([State.mkProcInput_cgroup_bpf_setsockopt]), field 26 at its
    default ([State.mkProcInput_clone_refusers]) and field 27 at SIG_DFL
    ([State.mkProcInput_sigchld_default]), so is an image ([embed_forget]
    needs all four). *)
Lemma mkProcInput_embed :
  forall argv envp image_fs stdin uid gid groups net nofile sigmask hwcap
         abort_terminal va_size,
  in_selfkill_terminal
    (mkProcInput argv envp image_fs stdin uid gid groups net nofile sigmask
       hwcap abort_terminal va_size) = false.
Proof. intros. reflexivity. Qed.

(** Every finite input has field 24 off, field 25 off
    ([Checks.CgroupBpfEmbedding.finite_input_bpf_default]), field 26
    at its default ([FinInput.to_proc_input] builds
    [State.no_clone_refusers]) and field 27 at SIG_DFL ([to_proc_input]
    builds [true]), so is an image. *)
Lemma to_proc_input_embed : forall f, in_selfkill_terminal (to_proc_input f) = false.
Proof. intros f. reflexivity. Qed.

Lemma to_proc_input_clone_refusers : forall f,
  in_clone_refusers (to_proc_input f) = no_clone_refusers.
Proof. intros f. reflexivity. Qed.

Lemma to_proc_input_sigchld_default : forall f,
  in_sigchld_default (to_proc_input f) = true.
Proof. intros f. reflexivity. Qed.

(* =========================================================================
   (i) The input predicates
   ========================================================================= *)

(** The sixteen [Run] predicates as they were, each copied from
    [git show 604b5c3:theories/LinuxProcessSem/Run.v] at the lines its
    comment names, and [FinInput.finite_input] from
    [git show 604b5c3:theories/EquivalenceDefinition/FinInput.v].
    [tools/check_pre_copies.py] holds each copy to its source. *)

(** Run.v:4661-4674. *)
Definition valid_input_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** Run.v:4745-4758. *)
Definition valid_input_abort_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = true
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** Run.v:4769-4781. *)
Definition valid_input_either_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** Run.v:4844-4857. *)
Definition valid_input_sigpipe_ignored_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = false
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** Run.v:4865-4877. *)
Definition valid_input_sigpipe_either_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** Run.v:4959-4972. *)
Definition valid_input_channel_closed_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = false
  /\ in_sigpipe_terminal inp = true
  /\ in_inherited_fds inp = [].

(** Run.v:4976-4988. *)
Definition valid_input_channel_either_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_sigpipe_terminal inp = negb (in_channel_reader inp)
  /\ in_inherited_fds inp = [].

(** Run.v:5069-5082. *)
Definition valid_input_paths_pre (inp : ProcInput) : Prop :=
  valid_argv_paths (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** Run.v:5171-5184. *)
Definition valid_input_sigpipe_kills_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = true
  /\ in_inherited_fds inp = [].

(** Run.v:5212-5225. *)
Definition valid_input_sv39_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv39
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** Run.v:5227-5240. *)
Definition valid_input_sv57_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv57
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** Run.v:5242-5254. *)
Definition valid_input_va_any_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ valid_hwcap (in_hwcap inp)
  /\ in_abort_terminal inp = false
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** Run.v:5537-5550. *)
Definition valid_input_hwcap_rv64gc_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ in_hwcap inp = hwcap_rv64gc
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** Run.v:5552-5565. *)
Definition valid_input_hwcap_rv64gcv_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ in_hwcap inp = hwcap_rv64gcv
  /\ in_abort_terminal inp = false
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** Run.v:5648-5661. *)
Definition valid_input_abort_hwcap_rv64gc_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ in_hwcap inp = hwcap_rv64gc
  /\ in_abort_terminal inp = true
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** Run.v:5663-5676. *)
Definition valid_input_abort_hwcap_rv64gcv_pre (inp : ProcInput) : Prop :=
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ fs_keys_relative (in_image_fs inp)
  /\ fs_image_real (in_image_fs inp) = true
  /\ valid_creds inp /\ valid_nofile (in_nofile inp)
  /\ valid_sigmask inp /\ in_hwcap inp = hwcap_rv64gcv
  /\ in_abort_terminal inp = true
  /\ in_va_size inp = Sv48
  /\ valid_urandom inp
  /\ valid_launch inp
  /\ in_sigpipe_default inp = true
  /\ in_channel_reader inp = true
  /\ in_sigpipe_terminal inp = false
  /\ in_inherited_fds inp = [].

(** FinInput.v:404-406. *)
Definition finite_input_pre (inp : ProcInput) : Prop :=
  finite_stream (in_stdin inp) /\ padded_urandom (in_urandom inp)
  /\ in_inherited_fds inp = [].

(** [V_pre] reads fields 1-23 only. [V] adds the four later default
    pins. *)
Definition embeds (V V_pre : ProcInput -> Prop) : Prop :=
  (forall inp b, V_pre (input_with_selfkill_terminal b inp) <-> V_pre inp)
  /\ (forall inp b, V_pre (input_with_cgroup_bpf_setsockopt b inp) <-> V_pre inp)
  /\ (forall inp r, V_pre (input_with_clone_refusers r inp) <-> V_pre inp)
  /\ (forall inp b, V_pre (input_with_sigchld_default b inp) <-> V_pre inp)
  /\ (forall inp, V inp <-> V_pre inp /\ in_selfkill_terminal inp = false
                                      /\ in_cgroup_bpf_setsockopt inp = false
                                      /\ in_clone_refusers inp = no_clone_refusers
                                      /\ in_sigchld_default inp = true).

(** The second half, once both bodies are unfolded: the same conjuncts,
    the pin last.  Destruct and split GUARDED, as [Run]'s own proofs do:
    a bare [repeat split] would also apply the constructor of
    [Run.valid_urandom], which is coinductive. *)
Ltac embeds_conj :=
  split; intros H;
  repeat match goal with H0 : _ /\ _ |- _ => destruct H0 end;
  repeat match goal with |- _ /\ _ => split end;
  assumption.

(** The first half holds by conversion: [V_pre] reads the input through
    its projections, and those of [input_with_selfkill_terminal b inp]
    reduce to those of [inp] for fields 1-23. *)
Ltac embeds_frame :=
  intros inp b; split; intros H; exact H.

Lemma valid_input_embeds : embeds valid_input valid_input_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input, valid_input_pre. embeds_conj.
Qed.

Lemma valid_input_abort_embeds : embeds valid_input_abort valid_input_abort_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_abort, valid_input_abort_pre. embeds_conj.
Qed.

Lemma valid_input_either_embeds : embeds valid_input_either valid_input_either_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_either, valid_input_either_pre. embeds_conj.
Qed.

Lemma valid_input_sigpipe_ignored_embeds :
  embeds valid_input_sigpipe_ignored valid_input_sigpipe_ignored_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_sigpipe_ignored, valid_input_sigpipe_ignored_pre.
  embeds_conj.
Qed.

Lemma valid_input_sigpipe_either_embeds :
  embeds valid_input_sigpipe_either valid_input_sigpipe_either_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_sigpipe_either, valid_input_sigpipe_either_pre.
  embeds_conj.
Qed.

Lemma valid_input_channel_closed_embeds :
  embeds valid_input_channel_closed valid_input_channel_closed_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_channel_closed, valid_input_channel_closed_pre.
  embeds_conj.
Qed.

Lemma valid_input_channel_either_embeds :
  embeds valid_input_channel_either valid_input_channel_either_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_channel_either, valid_input_channel_either_pre.
  embeds_conj.
Qed.

Lemma valid_input_paths_embeds : embeds valid_input_paths valid_input_paths_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_paths, valid_input_paths_pre. embeds_conj.
Qed.

Lemma valid_input_sigpipe_kills_embeds :
  embeds valid_input_sigpipe_kills valid_input_sigpipe_kills_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_sigpipe_kills, valid_input_sigpipe_kills_pre.
  embeds_conj.
Qed.

Lemma valid_input_sv39_embeds : embeds valid_input_sv39 valid_input_sv39_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_sv39, valid_input_sv39_pre. embeds_conj.
Qed.

Lemma valid_input_sv57_embeds : embeds valid_input_sv57 valid_input_sv57_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_sv57, valid_input_sv57_pre. embeds_conj.
Qed.

Lemma valid_input_va_any_embeds : embeds valid_input_va_any valid_input_va_any_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_va_any, valid_input_va_any_pre. embeds_conj.
Qed.

Lemma valid_input_hwcap_rv64gc_embeds :
  embeds valid_input_hwcap_rv64gc valid_input_hwcap_rv64gc_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_hwcap_rv64gc, valid_input_hwcap_rv64gc_pre.
  embeds_conj.
Qed.

Lemma valid_input_hwcap_rv64gcv_embeds :
  embeds valid_input_hwcap_rv64gcv valid_input_hwcap_rv64gcv_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold valid_input_hwcap_rv64gcv, valid_input_hwcap_rv64gcv_pre.
  embeds_conj.
Qed.

Lemma valid_input_abort_hwcap_rv64gc_embeds :
  embeds valid_input_abort_hwcap_rv64gc valid_input_abort_hwcap_rv64gc_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp.
  unfold valid_input_abort_hwcap_rv64gc, valid_input_abort_hwcap_rv64gc_pre.
  embeds_conj.
Qed.

Lemma valid_input_abort_hwcap_rv64gcv_embeds :
  embeds valid_input_abort_hwcap_rv64gcv valid_input_abort_hwcap_rv64gcv_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp.
  unfold valid_input_abort_hwcap_rv64gcv, valid_input_abort_hwcap_rv64gcv_pre.
  embeds_conj.
Qed.

Lemma finite_input_embeds : embeds finite_input finite_input_pre.
Proof.
  unfold embeds; split; [embeds_frame |]. split; [embeds_frame |].
  split; [embeds_frame |]. split; [embeds_frame |].
  intros inp. unfold finite_input, finite_input_pre. embeds_conj.
Qed.

(** On an old input's image the new predicate holds iff the old one did. *)
Corollary embeds_image : forall V V_pre, embeds V V_pre ->
  forall o, V (embed o) <-> V_pre (embed o).
Proof.
  intros V V_pre [_ [_ [_ [_ HV]]]] o. split.
  - intros H. exact (proj1 (proj1 (HV (embed o)) H)).
  - intros H. apply (proj2 (HV (embed o))).
    split; [exact H | split; [reflexivity | split; [reflexivity | split; reflexivity]]].
Qed.

(** Every input the field adds is excluded. *)
Corollary embeds_excludes : forall V V_pre, embeds V V_pre ->
  forall inp, in_selfkill_terminal inp = true -> ~ V inp.
Proof.
  intros V V_pre [_ [_ [_ [_ HV]]]] inp Ht Hv.
  destruct (proj1 (HV inp) Hv) as [_ [Hf _]]. rewrite Ht in Hf. discriminate Hf.
Qed.

(** Nor any input with a clone refuser present. *)
Corollary embeds_excludes_clone_refusers : forall V V_pre, embeds V V_pre ->
  forall inp, in_clone_refusers inp <> no_clone_refusers -> ~ V inp.
Proof.
  intros V V_pre [_ [_ [_ [_ HV]]]] inp Hc Hv.
  destruct (proj1 (HV inp) Hv) as [_ [_ [_ [Hd _]]]]. exact (Hc Hd).
Qed.

(** Nor any input launched with SIGCHLD at SIG_IGN. *)
Corollary embeds_excludes_sigchld_ignored : forall V V_pre, embeds V V_pre ->
  forall inp, in_sigchld_default inp = false -> ~ V inp.
Proof.
  intros V V_pre [_ [_ [_ [_ HV]]]] inp Hf Hv.
  destruct (proj1 (HV inp) Hv) as [_ [_ [_ [_ Ht]]]]. rewrite Hf in Ht.
  discriminate Ht.
Qed.

(** Every input the new predicate admits is an old input's image. *)
Corollary embeds_covers_images : forall V V_pre, embeds V V_pre ->
  forall inp, V inp -> inp = embed (forget inp).
Proof.
  intros V V_pre [_ [_ [_ [_ HV]]]] inp Hv.
  destruct (proj1 (HV inp) Hv) as [_ [Hsk [Hbp [Hcrf Hscd]]]].
  symmetry. exact (embed_forget inp Hsk Hbp Hcrf Hscd).
Qed.

(* =========================================================================
   (ii) The run relations
   ========================================================================= *)

(** The table without row 129. *)
Definition spec_table_pre : list SpecArm :=
  List.filter (fun a => negb (Z.eqb (sa_no a) 129%Z)) spec_table.

(** It is commit 604b5c371ed0's table, number for number: the list below
    is that commit's [Sys.SyscallTable.spec_table], read off
    [git show 604b5c3:theories/LinuxProcessSem/Sys/SyscallTable.v], and
    [tools/check_pre_copies.py] holds it to that file. *)
Lemma spec_table_pre_numbers : arm_numbers spec_table_pre = [17; 19; 20; 21; 22; 23; 24; 25; 29; 32; 35; 46; 48; 56; 57; 59; 61; 62; 63; 64; 65; 66; 67; 68; 72; 73; 74; 78; 79; 80; 82; 83; 85; 90; 91; 93; 94; 96; 98; 99; 101; 113; 114; 119; 123; 124; 130; 131; 132; 134; 135; 144; 146; 147; 148; 149; 150; 156; 157; 158; 159; 160; 167; 169; 172; 173; 174; 175; 176; 177; 178; 198; 199; 200; 201; 202; 203; 204; 205; 206; 207; 208; 209; 210; 211; 212; 214; 215; 216; 220; 222; 226; 233; 242; 260; 261; 268; 278; 435; 436; 439]%Z.
Proof. reflexivity. Qed.

(** Removing the rows of one number changes no lookup of another. *)
Lemma lookup_arm_filter_other : forall t k n, n <> k ->
  lookup_arm (List.filter (fun a => negb (Z.eqb (sa_no a) k)) t) n = lookup_arm t n.
Proof.
  intros t k n Hn. induction t as [|a r IH]; [reflexivity |].
  cbn [List.filter].
  destruct (Z.eqb (sa_no a) k) eqn:Ek; cbn [negb lookup_arm].
  - apply Z.eqb_eq in Ek. rewrite IH.
    destruct (Z.eqb (sa_no a) n) eqn:En; [| reflexivity].
    apply Z.eqb_eq in En. exfalso. apply Hn. congruence.
  - rewrite IH. reflexivity.
Qed.

(** And leaves that number with no arm. *)
Lemma lookup_arm_filter_self : forall t k,
  lookup_arm (List.filter (fun a => negb (Z.eqb (sa_no a) k)) t) k = None.
Proof.
  intros t k. induction t as [|a r IH]; [reflexivity |].
  cbn [List.filter].
  destruct (Z.eqb (sa_no a) k) eqn:Ek; cbn [negb lookup_arm].
  - exact IH.
  - rewrite Ek. exact IH.
Qed.

Lemma lookup_arm_spec_table_pre_kill : lookup_arm spec_table_pre 129%Z = None.
Proof. exact (lookup_arm_filter_self spec_table 129%Z). Qed.

(** Every number but 129 answers as the pre-change table does, at every
    model. *)
Lemma syscall_spec_other_pre : forall i m o,
  bv_unsigned (in_sysno i) <> 129%Z ->
  (syscall_spec i m o <-> dispatch spec_table_pre i m o).
Proof.
  intros i m o Hn. unfold syscall_spec, dispatch, spec_table_pre.
  rewrite (lookup_arm_filter_other spec_table 129%Z _ Hn). reflexivity.
Qed.

(** At 129 with the declaration off, the one answer is [Unmodeled]
    ([Kernel.Signal.kill_spec_off_unmodeled] and its converse). *)
Lemma syscall_spec_kill_off : forall i m o,
  bv_unsigned (in_sysno i) = 129%Z -> m_selfkill_terminal m = false ->
  (syscall_spec i m o <-> o = Unmodeled).
Proof.
  intros i m o Hn Hoff.
  assert (Ha : exists a, lookup_arm spec_table 129%Z = Some a
                         /\ (sa_spec a i m o <-> o = Unmodeled)).
  { eexists. split; [reflexivity |]. cbn [sa_spec]. split.
    - intros H. exact (kill_spec_off_unmodeled _ _ _ _ _ Hoff H).
    - intros ->. unfold kill_spec. rewrite bind_get_model, Hoff.
      exact (@unmodeled_intro SyscallEffect i m). }
  destruct Ha as (a & Hl & Hs). rewrite <- Hn in Hl.
  pose proof (dispatch_arm spec_table i m o a Hl) as Hd.
  unfold syscall_spec. split.
  - intros H. exact (proj1 Hs (proj1 Hd H)).
  - intros H. exact (proj2 Hd (proj2 Hs H)).
Qed.

(** Keep this reduction over an abstract table.  Unfolding [dispatch]
    after substituting [spec_table_pre] makes the kernel traverse the
    concrete table's specification bodies when it checks the rewrite. *)
Local Lemma dispatch_no_arm : forall t i m o,
  lookup_arm t (bv_unsigned (in_sysno i)) = None ->
  (dispatch t i m o <-> o = Unmodeled).
Proof. intros t i m o H. unfold dispatch. rewrite H. reflexivity. Qed.

(** With the declaration off, every number answers as the pre-change
    table does, 129 included: it has no arm there, and declines here. *)
Lemma syscall_spec_off_pre : forall i m o,
  m_selfkill_terminal m = false ->
  (syscall_spec i m o <-> dispatch spec_table_pre i m o).
Proof.
  intros i m o Hoff.
  destruct (Z.eq_dec (bv_unsigned (in_sysno i)) 129%Z) as [Hn | Hn].
  - assert (Hl : lookup_arm spec_table_pre (bv_unsigned (in_sysno i)) = None)
      by (rewrite Hn; exact lookup_arm_spec_table_pre_kill).
    split.
    + intros H. pose proof (proj1 (syscall_spec_kill_off i m o Hn Hoff) H) as ->.
      exact (dispatch_unmodeled _ _ _ Hl).
    + intros H. apply (proj2 (syscall_spec_kill_off i m o Hn Hoff)).
      exact (proj1 (dispatch_no_arm spec_table_pre i m o Hl) H).
  - exact (syscall_spec_other_pre i m o Hn).
Time Qed.

(** [Run.run] and [Run.run_scfg] start from [Run.init_config], whose model
    carries the declaration the input states. *)
Lemma init_config_selfkill : forall segs pc ph sp brk0 mbase rnd lim inp,
  m_selfkill_terminal (cfg_model (init_config segs pc ph sp brk0 mbase rnd lim inp))
  = in_selfkill_terminal inp.
Proof. intros. reflexivity. Qed.

Lemma selfkill_materialize : forall m acc m'',
  materialize_model_accesses m acc = Some m'' ->
  m_selfkill_terminal m'' = m_selfkill_terminal m.
Proof.
  intros m acc m'' H.
  destruct (materialize_model_accesses_frame _ _ _ H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold m_selfkill_terminal. rewrite Hp. reflexivity.
Qed.

(** No step writes the declaration, under every configuration and every
    launch. *)
Lemma sstep_cfg_selfkill_kept : forall segs cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  m_selfkill_terminal (cfg_model c') = m_selfkill_terminal (cfg_model c).
Proof.
  intros segs cfg c evs c' H.
  inversion H; subst; cbn [cfg_model].
  - (* an instruction: the machine step keeps [State.m_proc] *)
    match goal with
    | Ha : mi_account_step _ _ _ = MachineOk _ |- _ =>
        destruct (mi_account_step_model_frame _ _ _ _ _ Ha)
          as (_ & _ & _ & _ & _ & Hp & _)
    end.
    unfold m_selfkill_terminal. rewrite Hp. reflexivity.
  - (* a vDSO call *)
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ ?m1 _),
      Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
        transitivity (m_selfkill_terminal m2); [reflexivity |];
        rewrite (selfkill_materialize _ _ _ Hm);
        exact (syscall_spec_selfkill_kept _ _ _ _ _ Hsp)
    end.
  - (* a system call that returns *)
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ ?m1 _),
      Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
        transitivity (m_selfkill_terminal m2); [reflexivity |];
        rewrite (selfkill_materialize _ _ _ Hm);
        exact (syscall_spec_selfkill_kept _ _ _ _ _ Hsp)
    end.
  - (* an exit *)
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
        exact (syscall_spec_selfkill_kept _ _ _ _ _ Hsp)
    end.
  - (* a kill *)
    match goal with
    | Hsp : syscall_spec _ _ (Ok _ _ _) |- _ =>
        exact (syscall_spec_selfkill_kept _ _ _ _ _ Hsp)
    end.
Qed.

Lemma sstep_selfkill_kept : forall segs c evs c',
  sstep segs c evs (SNext c') ->
  m_selfkill_terminal (cfg_model c') = m_selfkill_terminal (cfg_model c).
Proof.
  intros segs c evs c' H.
  exact (sstep_cfg_selfkill_kept _ _ _ _ _
           (proj1 (sstep_cfg_may_fail segs c evs (SNext c')) H)).
Qed.

Corollary star_cfg_selfkill_kept : forall segs cfg c tr c',
  star_cfg segs cfg c tr c' ->
  m_selfkill_terminal (cfg_model c') = m_selfkill_terminal (cfg_model c).
Proof.
  intros segs cfg c tr c' H.
  induction H as [c0 | c1 evs1 c2 tr1 c3 Hs _ IH]; [reflexivity |].
  rewrite IH. exact (sstep_cfg_selfkill_kept _ _ _ _ _ Hs).
Qed.

Corollary star_selfkill_kept : forall segs c tr c',
  star segs c tr c' ->
  m_selfkill_terminal (cfg_model c') = m_selfkill_terminal (cfg_model c).
Proof.
  intros segs c tr c' H.
  induction H as [c0 | c1 evs1 c2 tr1 c3 Hs _ IH]; [reflexivity |].
  rewrite IH. exact (sstep_selfkill_kept _ _ _ _ Hs).
Qed.

(** At a 129 call with the declaration off, the one step is the
    fail-closed one, which a number with no arm took before the change. *)
Lemma sstep_kill_off_unmodeled : forall segs ms model x8 evs to,
  m_halted model = None -> m_selfkill_terminal model = false ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 129%Z ->
  (sstep segs (mkCfg ms model) evs to <-> evs = [] /\ to = SError).
Proof.
  intros segs ms model x8 evs to Hh Hoff Hs Hn.
  assert (Hok : forall y eff m' evs',
            ms_svc_pending ms = Some y ->
            ~ syscall_spec (sys_input segs ms y) model (Ok eff m' evs')).
  { intros y eff m' evs' Hy Hsp.
    assert (E : y = x8) by congruence. subst y.
    pose proof (proj1 (syscall_spec_kill_off (sys_input segs ms x8) model
                         (Ok eff m' evs') Hn Hoff) Hsp) as Hu.
    discriminate Hu. }
  split.
  - intros H. inversion H; subst;
      first
      [ congruence
      | (exfalso;
         match goal with
         | Hy : ms_svc_pending ms = Some ?y,
           Hsp : syscall_spec (sys_input _ _ ?y) _ (Ok _ _ _) |- _ =>
             exact (Hok _ _ _ _ Hy Hsp)
         end)
      | (split; reflexivity) ].
  - intros [-> ->]. eapply sstep_syscall_unmodeled; [exact Hh | exact Hs |].
    exact (proj2 (syscall_spec_kill_off (sys_input segs ms x8) model Unmodeled
                    Hn Hoff) eq_refl).
Qed.

Lemma sstep_cfg_kill_off_unmodeled : forall segs cfg ms model x8 evs to,
  m_halted model = None -> m_selfkill_terminal model = false ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 129%Z ->
  (sstep_cfg segs cfg (mkCfg ms model) evs to <-> evs = [] /\ to = SError).
Proof.
  intros segs cfg ms model x8 evs to Hh Hoff Hs Hn. split.
  - intros H.
    exact (proj1 (sstep_kill_off_unmodeled segs ms model x8 evs to Hh Hoff Hs Hn)
             (sstep_cfg_sub _ _ _ _ _ H)).
  - intros [-> ->]. eapply sstep_cfg_syscall_unmodeled; [exact Hh | exact Hs |].
    exact (proj2 (syscall_spec_kill_off (sys_input segs ms x8) model Unmodeled
                    Hn Hoff) eq_refl).
Qed.

Print Assumptions dispatch_no_arm.
Print Assumptions valid_input_embeds.
Print Assumptions finite_input_embeds.
Print Assumptions syscall_spec_off_pre.
Print Assumptions sstep_selfkill_kept.
Print Assumptions star_cfg_selfkill_kept.
Print Assumptions sstep_cfg_kill_off_unmodeled.
