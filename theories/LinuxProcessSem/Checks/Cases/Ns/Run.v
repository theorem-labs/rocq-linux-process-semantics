(** * LinuxProcessSem.Checks.Cases.Ns.Run — generic namespace-step surface

    This case fixes the first public surface of the namespace model: a world
    carried beside a [Run.config], its one-step relation, and the lemma that
    an instruction transition changes the configuration exactly as [Run.sstep]
    does while preserving that world. *)

From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.LinuxProcessSem.Ns Require Import Run.

Check world.
Check ncfg.
Check nstep.
Check nstep_instr_iff.
