(** Proof of OSSVerify.Tests.toy.exit0.Statements.plain_halts_may_fail.

    Outline.  As for [plain_halts], under [Env.may_fail]: the program makes no
    system call that can fail (exit_group cannot), so refusals change nothing.
    Status 0 is one of the 256 statuses [Exits.any] allows. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import SpuriousCfg.
From LinuxProcessSemantics.EquivalenceDefinition Require Import MustExit HaltsAllowed Classifier.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.exit0 Require Statements Images.
From OSSVerify.Tests.proofs.lib Require Exit0Run.
Import ListNotations.

Theorem plain_halts_may_fail_holds : Statements.plain_halts_may_fail.
Proof.
  unfold Statements.plain_halts_may_fail.
  apply (halts_may_fail_mono [verdict_accept]).
  { intros code [<- | []]. apply status_allowed_In. vm_compute. reflexivity. }
  intros [sp brk0 mbase rnd] inp _ _.
  unfold Images.plain. cbn [must_exit_in_scfg].
  apply must_exit_in_at_cfg_singleton. unfold init_config.
  apply (exits_c_must_exit_at_cfg _ _ _ 8);
    [reflexivity | reflexivity | apply Exit0Run.exit0_exits_c].
Qed.
