(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit L5Defs L5Core FrmInv FpBridge Pm6FrmInv FmodlLems Pm6FpSites CutVF Pm6Leaf_divtf3 Pm6Leaf_extendsftf2 Pm6Leaf_floatsitf Pm6Leaf_fpclassifyl Pm6Leaf_letf2 Pm6Leaf_multf3.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAuto CutAutoD CutLib Pm6CutKitD.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutGen Require Import Cut_fmodl_xsrc.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Leaf_fmodl_xsrc.
Definition ENTRY : Z := 751432.
Definition SCR : Z := 192.
Definition ENDS : list Z := [751600].
Definition INL : list (Z * (Z * list nat * option Z)) := [(751736, (4, [], None)); (751888, (4, [], None)); (752132, (4, [], None))].
Definition IMG : option (Z * Z) := None.
Definition CALLEES : list (Z * (Z * option (Z * Z))) := [(733592, (16, None)); (731412, (16, None)); (731800, (80, None)); (736480, (112, None)); (731128, (16, None)); (751044, (16, None))].
Lemma chk : CVF.vf_chk CPS TAGS ENTRY SCR ENDS RETS INL CALLEES IMG = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rets : forall pc, In pc ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc H. cbn [ENDS In] in H. destruct H as [<-|H]; [CL.solve_is_ret|]. destruct H. Qed.
Lemma inl : forall e, In e INL -> CVF.inl_sem RSEGS e.
Proof. intros e H. cbn [INL In] in H. destruct H as [<-|H]; [cbn; exact Pm6FpSites.site_b783c|]. destruct H as [<-|H]; [cbn; exact Pm6FpSites.site_b78d4|]. destruct H as [<-|H]; [cbn; exact Pm6FpSites.site_b79c8|]. destruct H. Qed.
Section Final.
Context {SCFG_P : ScfgP}.
Lemma callees : forall pc SCRc IMGc, In (pc, (SCRc, IMGc)) CALLEES -> CVF.vf_contract RSEGS pc SCRc IMGc.
Proof. intros pc SCRc IMGc H. cbn [CALLEES In] in H. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 733592 0 16 None None ltac:(lia) ltac:(auto) Leaf_floatsitf_xsrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 731412 0 16 None None ltac:(lia) ltac:(auto) Leaf_letf2_xsrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 731800 80 80 None None ltac:(lia) ltac:(auto) Leaf_multf3_xsrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 736480 112 112 None None ltac:(lia) ltac:(auto) Leaf_divtf3_xsrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 731128 0 16 None None ltac:(lia) ltac:(auto) Leaf_fpclassifyl_xsrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 751044 0 16 None None ltac:(lia) ltac:(auto) Leaf_extendsftf2_xsrc.ok)|]. destruct H. Qed.
(* [comment removed for export] *)
Definition ok := CVF.vf_leaf_sound RSEGS CPS TAGS ENTRY SCR ENDS RETS INL CALLEES IMG Pm6FrmInv.text_safe FmodlLems.plans_ok tags_ok chk rets inl callees.
End Final.
End Leaf_fmodl_xsrc.
