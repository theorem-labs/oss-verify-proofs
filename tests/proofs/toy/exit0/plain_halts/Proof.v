(** Proof of OSSVerify.Tests.toy.exit0.Statements.plain_halts.

    Outline.  Fix an entry and an input.  [Exit0Run.exit0_exits_c] says the
    program reaches exit_group(0) after three instructions; lps's
    [Checks.SpuriousCfg.exits_c_must_exit_at_cfg] turns that into the
    inductive statement that EVERY execution under [Env.forced_only] exits
    with status 0 (a straight-line program has no other execution).  Status 0
    is in the allowed set {0, 2}.  The budget premise is not needed: the
    program allocates nothing. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import SpuriousCfg.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit Classifier.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.exit0 Require Statements Images.
From OSSVerify.Tests.proofs.lib Require Exit0Run.
Import ListNotations.

Theorem plain_halts_holds : Statements.plain_halts.
Proof.
  unfold Statements.plain_halts.
  apply (halts_within_budget_mono _ [verdict_accept]).
  { intros code [<- | []]. left. reflexivity. }
  intros [sp brk0 mbase rnd] inp _ _ _.
  unfold Images.plain. cbn [must_exit_in_scfg].
  apply must_exit_in_at_cfg_singleton. unfold init_config.
  apply (exits_c_must_exit_at_cfg _ _ _ 8);
    [reflexivity | reflexivity | apply Exit0Run.exit0_exits_c].
Qed.
