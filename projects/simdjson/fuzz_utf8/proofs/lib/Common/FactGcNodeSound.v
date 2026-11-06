(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import SymStepR AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesAux. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import ExecNodes ExecNodesSound FactGcNode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import FGC.
Open Scope Z_scope.

Module FGCS.
Section Sound.
  Context {fx : FPState}.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.

  (* [comment removed for export] *)
  Theorem xn_soundF : forall args, node1_stmtF SEGS A nx0 LIMIT SINV argH FS0 always (FGC.xn args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn in Hn. injection Hn as <-.
    eapply EXNS.set_kn_sound; [exact HC | | exact Hk].
    unfold gc_kn. apply know_ok_filter. exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC).
  Qed.

  Theorem xn_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (FGC.xn args).
  Proof. intros args. apply node1_stmtF_stmt. apply xn_soundF. Qed.
End Sound.
End FGCS.
