(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import L5Defs L5Core FrmInv FpBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6FrmInv_u5 Pm6FpSites_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import CutVF .
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAuto CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_extendsftf2_xsrc_u5.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Leaf_extendsftf2_xsrc.
Definition ENTRY : Z := 765876.
Definition SCR : Z := 0.
Definition ENDS : list Z := [765940; 766148; 766192; 766216].
Definition INL : list (Z * (Z * list nat * option Z)) := [].
Definition IMG : option (Z * Z) := None.
Definition CALLEES : list (Z * (Z * option (Z * Z))) := [].
Lemma chk : CVF.vf_chk CPS TAGS ENTRY SCR ENDS RETS INL CALLEES IMG = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rets : forall pc, In pc ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc H. cbn [ENDS In] in H. destruct H as [<-|H]; [CL.solve_is_ret|]. destruct H as [<-|H]; [CL.solve_is_ret|]. destruct H as [<-|H]; [CL.solve_is_ret|]. destruct H as [<-|H]; [CL.solve_is_ret|]. destruct H. Qed.
Lemma inl : forall e, In e INL -> CVF.inl_sem RSEGS e.
Proof. intros e H. cbn [INL In] in H.  destruct H. Qed.
Section Final.
Context {SCFG_P : ScfgP}.
Lemma callees : forall pc SCRc IMGc, In (pc, (SCRc, IMGc)) CALLEES -> CVF.vf_contract RSEGS pc SCRc IMGc.
Proof. intros pc SCRc IMGc H. cbn [CALLEES In] in H.  destruct H. Qed.
(* [comment removed for export] *)
Definition ok := CVF.vf_leaf_sound_pre RSEGS CPS TAGS ENTRY SCR ENDS RETS INL CALLEES IMG Pm6FrmInv.text_safe (plans ltac:(constructor)) tags_ok chk rets inl callees 765872 [11%nat] eq_refl Pm6FpSites.site_b7588 ltac:(intros x Hx; cbn in Hx; unfold CVF.CSAVED; cbn; intuition lia).
End Final.
End Leaf_extendsftf2_xsrc.
