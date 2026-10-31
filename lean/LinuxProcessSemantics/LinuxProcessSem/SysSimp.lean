import Lean.Meta.Tactic.Simp.RegisterCommand

/-! # LinuxProcessSem.SysSimp — the `sys_simp` and `arm_unfold` simp sets, registered

Lean-only: no Rocq file mirrors this one.  Its Rocq counterpart is the
`model` rewrite database `theories/LinuxProcessSem/State.v` registers each
setter/getter equation in (`#[export] Hint Rewrite … : model`), which the
checks reach through `autorewrite with model`.

Both sets are EMPTY here.  What goes into `sys_simp`, and how a check
reads a spec with it, is `Checks/Cases/Tactic.lean`'s subject; what goes
into `arm_unfold` is `Checks/Sys/Table.lean`'s.  This module exists only
so that the attributes can be used at all.

WHY ITS OWN MODULE.  `register_simp_attr` expands to an `initialize`,
which runs when the module is IMPORTED and not while it is elaborated, so
the attribute it registers is unknown inside the file that registers it —
`attribute [sys_simp] foo` there is refused as an unknown attribute, and
so is `simp only [sys_simp]`.  The registrations therefore sit alone, in a
module that imports nothing of this development, so that any file above
it may tag: `Checks/Cases/Tactic.lean` tags today, and a `State.lean` or
`Sys/` definition that wants a definition-site `@[sys_simp]` needs only to
import this module.  The check that the set says what `Tactic.lean` claims
of it is in that file, not here: nothing in this module is a proof. -/

/-- The simp set the `Checks/Cases/` files read a syscall spec with.
`Checks/Cases/Tactic.lean` fills it, says what each kind of member is
registered at and why, and checks the register's completeness. -/
register_simp_attr sys_simp

/-- The rewrite set the per-arm lemmas of `Checks/Sys/Table.lean` register
in, so that a proof holding a `CheckedArm` gets back the plain `check_*`,
`*_witness` and `*_spec` application it was written against without naming
the syscall.  Rocq calls it `arm_unfold` too, as a `Hint Rewrite` database
read by `autorewrite with arm_unfold`
(`theories/LinuxProcessSem/Checks/Sys/Dispatch.v`); the Lean reader is
`simp only [arm_unfold]`.

It is declared in this module for the same reason `sys_simp` is: the
registration runs on IMPORT, not on elaboration, so the attribute cannot be
used in the file that declares it.  `Checks/Sys/Table.lean` imports this
module and tags each arm's block into it, and
`Checks/Cases/Checks/Sys/Dispatch.lean` tags its fixture block the same
way.  A `simp only [arm_unfold]` with nothing to rewrite fails with
"`simp` made no progress" rather than passing quietly, so a block whose
lemmas were not tagged is found at the first proof that reaches for
them. -/
register_simp_attr arm_unfold
