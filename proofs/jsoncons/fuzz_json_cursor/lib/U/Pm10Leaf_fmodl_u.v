(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs L5Core FrmInv FpBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10FrmInv_u FmodlLems_u Pm10FpSites_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import CutVF. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10Leaf_divtf3_u Pm10Leaf_extendsftf2_u Pm10Leaf_floatsitf_u Pm10Leaf_fpclassifyl_u Pm10Leaf_letf2_u Pm10Leaf_multf3_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAuto CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutCert Require Import Pm10CutKitD_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_fmodl_csrc_u.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Module Leaf_fmodl_csrc.
Definition ENTRY : Z := 739712.
Definition SCR : Z := 192.
Definition ENDS : list Z := [739880].
Definition INL : list (Z * (Z * list nat * option Z)) := [(740016, (4, [], None)); (740168, (4, [], None)); (740412, (4, [], None))].
Definition IMG : option (Z * Z) := None.
Definition CALLEES : list (Z * (Z * option (Z * Z))) := [(721872, (16, None)); (719692, (16, None)); (720080, (80, None)); (724760, (112, None)); (719408, (16, None)); (739324, (16, None))].
Lemma chk : CVF.vf_chk CPS TAGS ENTRY SCR ENDS RETS INL CALLEES IMG = true.
Proof. vmc_refl. Qed.
Lemma rets : forall pc, In pc ENDS -> CL.is_ret_at RSEGS pc.
Proof. intros pc H. cbn [ENDS In] in H. destruct H as [<-|H]; [CL.solve_is_ret|]. destruct H. Qed.
Lemma inl : forall e, In e INL -> CVF.inl_sem RSEGS e.
Proof. intros e H. cbn [INL In] in H. destruct H as [<-|H]; [cbn; exact Pm10FpSites.site_b2c20|]. destruct H as [<-|H]; [cbn; exact Pm10FpSites.site_b2cb8|]. destruct H as [<-|H]; [cbn; exact Pm10FpSites.site_b2dac|]. destruct H. Qed.
Section Final.
Context {SCFG_P : ScfgP}.
Lemma callees : forall pc SCRc IMGc, In (pc, (SCRc, IMGc)) CALLEES -> CVF.vf_contract RSEGS pc SCRc IMGc.
Proof. intros pc SCRc IMGc H. cbn [CALLEES In] in H. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 721872 0 16 None None ltac:(lia) ltac:(auto) Leaf_floatsitf_csrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 719692 0 16 None None ltac:(lia) ltac:(auto) Leaf_letf2_csrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 720080 80 80 None None ltac:(lia) ltac:(auto) Leaf_multf3_csrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 724760 112 112 None None ltac:(lia) ltac:(auto) Leaf_divtf3_csrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 719408 0 16 None None ltac:(lia) ltac:(auto) Leaf_fpclassifyl_csrc.ok)|]. destruct H as [H|H]; [injection H as <- <- <-; exact (CVF.vf_contract_weaken RSEGS 739324 0 16 None None ltac:(lia) ltac:(auto) Leaf_extendsftf2_csrc.ok)|]. destruct H. Qed.

Definition ok := CVF.vf_leaf_sound RSEGS CPS TAGS ENTRY SCR ENDS RETS INL CALLEES IMG Pm10FrmInv.text_safe FmodlLems_u.plans_ok tags_ok chk rets inl callees.
End Final.
End Leaf_fmodl_csrc.
