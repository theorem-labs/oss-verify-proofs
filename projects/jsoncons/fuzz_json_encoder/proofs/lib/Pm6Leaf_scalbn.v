(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit L5Defs L5Core FrmInv FpBridge Pm6FrmInv Pm6FpSites CutVF .
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAuto CutAutoD CutLib Pm6CutKitD.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutGen Require Import Cut_scalbn_xsrc.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Leaf_scalbn_xsrc.
Definition ENTRY : Z := 712512.
Definition SCR : Z := 0.
Definition ENDS : list Z := [712660].
Definition INL : list (Z * (Z * list nat * option Z)) := [(712532, (4, [], None)); (712556, (4, [], None)); (712588, (4, [], None)); (712612, (4, [], None)); (712652, (4, [], None)); (712656, (4, [], None))].
Definition IMG : option (Z * Z) := Some (65536, 813152).
Definition CALLEES : list (Z * (Z * option (Z * Z))) := [].
Lemma chk : CVF.vf_chk CPS TAGS ENTRY SCR ENDS RETS INL CALLEES IMG = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rets : forall pc, In pc ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc H. cbn [ENDS In] in H. destruct H as [<-|H]; [CL.solve_is_ret|]. destruct H. Qed.
Lemma inl : forall e, In e INL -> CVF.inl_sem RSEGS e.
Proof. intros e H. cbn [INL In] in H. destruct H as [<-|H]; [cbn; exact Pm6FpSites.site_adf18|]. destruct H as [<-|H]; [cbn; exact Pm6FpSites.site_adf30|]. destruct H as [<-|H]; [cbn; exact Pm6FpSites.site_adf50|]. destruct H as [<-|H]; [cbn; exact Pm6FpSites.site_adf68|]. destruct H as [<-|H]; [cbn; exact Pm6FpSites.site_adf90|]. destruct H as [<-|H]; [cbn; exact Pm6FpSites.site_adf94|]. destruct H. Qed.
Section Final.
Context {SCFG_P : ScfgP}.
Lemma callees : forall pc SCRc IMGc, In (pc, (SCRc, IMGc)) CALLEES -> CVF.vf_contract RSEGS pc SCRc IMGc.
Proof. intros pc SCRc IMGc H. cbn [CALLEES In] in H.  destruct H. Qed.
(* [comment removed for export] *)
Definition ok := CVF.vf_leaf_sound RSEGS CPS TAGS ENTRY SCR ENDS RETS INL CALLEES IMG Pm6FrmInv.text_safe (plans ltac:(constructor)) tags_ok chk rets inl callees.
End Final.
End Leaf_scalbn_xsrc.
