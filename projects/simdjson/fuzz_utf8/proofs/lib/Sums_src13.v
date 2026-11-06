(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare RefMemcpyLib MemsetLib.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import SumsSpecs Img_src13.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require MemsetWalk_src13 MemcpyBase_src13 MemcpyTop_src13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

Lemma src13_segs_wr : APSX.segs_wr_ok SEGS_src13.
Proof. apply segs_wr_of_forallb. vm_compute. reflexivity. Qed.

Section WithFP.
Context {fx : FPState}.

Lemma src13_fill_spec_memset : APSX.fill_spec SEGS_src13 (x_memset AT_src13) AX2.two64.
Proof.
  apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
  exact (MemsetWalk_src13.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.

Lemma src13_copy_spec_memcpy : APSX.copy_spec SEGS_src13 (x_memcpy AT_src13).
Proof.
  apply (copy_spec_of_memcpy SEGS_src13 (0xc4120%bv : word) (x_memcpy AT_src13) MemcpyBase_src13.mcH).
  - apply bv_eq. reflexivity.
  - intros. constructor; assumption.
  - intros mem0 dst src n bs rom HOK regs ret Hret R1 R10 R11 R12.
    exact (MemcpyTop_src13.ref_memcpy mem0 dst src n bs rom HOK regs ret Hret R1 R10 R11 R12).
Qed.

(* [comment removed for export] *)
Section X.
  Variables (nx0 : nat) (LIMIT : Z) (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
  Hypothesis NX0_min : APS.nx0_min_ok nx0.   (* [comment removed for export] *)
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  #[local] Notation XSTMT x := (APS.x_stmt SEGS_src13 AT_src13 nx0 LIMIT SINV argH FS0 x).
  #[local] Ltac pre := try eassumption; try apply src13_segs_wr; try apply src13_wx; try apply src13_in_hull;
                   try apply src13_res_len; try apply src13_hull_ok.
  Theorem src13_x_sound_XMemset : XSTMT XMemset.
  Proof. eapply APSX.node_x_sound_XMemset; pre. intros _. apply src13_fill_spec_memset. Qed.
  Theorem src13_x_sound_XMemcpy : XSTMT XMemcpy.
  Proof. eapply APSX.node_x_sound_XMemcpy; pre. intros _. apply src13_copy_spec_memcpy. Qed.
  (* [comment removed for export] *)
  Theorem src13_xW_sound : forall x args cs ws, AP.x_ws_std x args cs = Some ws ->
    APS.node1_stmtW_at SEGS_src13 AT_src13 nx0 LIMIT SINV argH FS0 APS.always (AP.node_x SEGS_src13 AT_src13 nx0 x args) cs ws.
  Proof.   (* [comment removed for export] *)
    eapply APSX.node_xW_sound_std; pre;
      [intros _; apply src13_fill_spec_memset | intros _; apply src13_copy_spec_memcpy | let H := fresh in intros H; exfalso; apply H; reflexivity | let H := fresh in intros H; exfalso; apply H; reflexivity].
  Qed.
  Theorem src13_x_sound_XIMemset : XSTMT XIMemset.
  Proof. eapply APSX.node_x_sound_XIMemset; pre. intros H. exfalso. apply H. reflexivity. Qed.
  Theorem src13_x_sound_XIMemcpy : XSTMT XIMemcpy.
  Proof. eapply APSX.node_x_sound_XIMemcpy; pre. intros H. exfalso. apply H. reflexivity. Qed.
  Theorem src13_x_sound_XMemIsZero : XSTMT XMemIsZero.
  Proof. eapply APSX.node_x_sound_XMemIsZero; pre. intros H. exfalso. apply H. reflexivity. Qed.
  Theorem src13_x_sound_XIStrncpy : XSTMT XIStrncpy.
  Proof. eapply APSX.node_x_sound_XIStrncpy; pre. intros H. exfalso. apply H. reflexivity. Qed.
  Theorem src13_x_sound_XPopFree : XSTMT XPopFree.
  Proof. eapply APSX.node_x_sound_XPopFree; pre. intros H. exfalso. apply H. reflexivity. Qed.
  Theorem src13_x_sound_XSniff : XSTMT XSniff.
  Proof. eapply APSX.node_x_sound_XSniff; pre. Qed.
End X.
End WithFP.
