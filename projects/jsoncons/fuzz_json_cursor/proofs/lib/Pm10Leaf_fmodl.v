(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto Pm10PlanKit L5Defs L5Core FrmInv FpBridge Pm10FrmInv FmodlLems Pm10FpSites CutVF Pm10Leaf_divtf3 Pm10Leaf_extendsftf2 Pm10Leaf_floatsitf Pm10Leaf_fpclassifyl Pm10Leaf_letf2 Pm10Leaf_multf3.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAuto CutAutoD CutLib Pm10CutKitD.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutGen Require Import Cut_fmodl_csrc.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module Leaf_fmodl_csrc.
Definition ENTRY : Z := 731948.
Definition SCR : Z := 192.
Definition ENDS : list Z := [732116].
Definition INL : list (Z * (Z * list nat * option Z)) := [(732252, (4, [], None)); (732404, (4, [], None)); (732648, (4, [], None))].
Definition IMG : option (Z * Z) := None.
Definition CALLEES : list (Z * (Z * option (Z * Z))) := [(714108, (16, None)); (711928, (16, None)); (712316, (80, None)); (716996, (112, None)); (711644, (16, None)); (731560, (16, None))].
Lemma chk : CVF.vf_chk CPS TAGS ENTRY SCR ENDS RETS INL CALLEES IMG = true.
Proof. vmc_refl. Qed.
Lemma rets : forall pc, In pc ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc H. cbn [ENDS In] in H. destruct H as [<-|H]; [CL.solve_is_ret|]. destruct H. Qed.
Lemma inl : forall e, In e INL -> CVF.inl_sem RSEGS e.
Proof. intros e H. cbn [INL In] in H. destruct H as [<-|H]; [cbn; exact Pm10FpSites.site_b2c20|]. destruct H as [<-|H]; [cbn; exact Pm10FpSites.site_b2cb8|]. destruct H as [<-|H]; [cbn; exact Pm10FpSites.site_b2dac|]. destruct H. Qed.
Section Final.
Context {SCFG_P : ScfgP}.
Lemma callees : forall pc SCRc IMGc, In (pc, (SCRc, IMGc)) CALLEES -> CVF.vf_contract RSEGS pc SCRc IMGc.
Proof. intros pc SCRc IMGc H. cbn [CALLEES In] in H. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 714108 0 16 None None ltac:(lia) ltac:(auto) Leaf_floatsitf_csrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 711928 0 16 None None ltac:(lia) ltac:(auto) Leaf_letf2_csrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 712316 80 80 None None ltac:(lia) ltac:(auto) Leaf_multf3_csrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 716996 112 112 None None ltac:(lia) ltac:(auto) Leaf_divtf3_csrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 711644 0 16 None None ltac:(lia) ltac:(auto) Leaf_fpclassifyl_csrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 731560 0 16 None None ltac:(lia) ltac:(auto) Leaf_extendsftf2_csrc.ok)|]. destruct H. Qed.

Definition ok := CVF.vf_leaf_sound RSEGS CPS TAGS ENTRY SCR ENDS RETS INL CALLEES IMG Pm10FrmInv.text_safe FmodlLems.plans_ok tags_ok chk rets inl callees.
End Final.
End Leaf_fmodl_csrc.
