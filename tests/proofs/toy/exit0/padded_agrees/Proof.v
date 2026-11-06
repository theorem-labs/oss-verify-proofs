(** Proof of OSSVerify.Tests.toy.exit0.Statements.padded_agrees.

    Outline.  Fix an entry for each program and an input.  Neither program
    can reach an error, and the trace set of each is exactly the prefixes of
    the one event exit_group(0) with the input's file system
    ([Exit0Run.exit0_obs], [Exit0Run.padded_obs]), so the two trace sets are
    equal.  None of the validity premises or the budget premise is needed:
    neither program touches the stack or the heap. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.Tests.toy.exit0 Require Statements Images.
From OSSVerify.Tests.proofs.lib Require Exit0Run.

Theorem padded_agrees_holds : Statements.padded_agrees.
Proof.
  unfold Statements.padded_agrees, agrees.
  intros [sps brks mbs rnds] [spt brkt mbt rndt] inp _ _ _ _.
  split; [| split].
  - apply error_free_iff. unfold Images.plain. cbn [omni_corun].
    apply Exit0Run.exit0_never_errors.
  - apply error_free_iff. unfold Images.padded. cbn [omni_corun].
    apply Exit0Run.padded_never_errors.
  - intros tr. unfold Images.plain, Images.padded. cbn [run bh_traces].
    rewrite Exit0Run.exit0_obs, Exit0Run.padded_obs. reflexivity.
Qed.
