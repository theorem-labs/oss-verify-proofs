(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import L5Defs L5Core
  FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6FrmInv_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import FpBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6FpSites_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import CutVF CutVFX. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecIface_u5 DecScanPure_u5 DecOkDefs_u5 DecOkSem_u5 DecKinds5_u5 DecfloatLems5_u5
  Pm6Leaf_floatsitf_u5 Pm6Leaf_floatunsitf_u5 Pm6Leaf_extenddftf2_u5 Pm6Leaf_multf3_u5 Pm6Leaf_addtf3_u5 Pm6Leaf_subtf3_u5 Pm6Leaf_divtf3_u5 Pm6Leaf_letf2_u5 Pm6Leaf_getf2_u5 Pm6Leaf_scalbn_u5
  Pm6Leaf_copysignl_u5 Pm6Leaf_fabsl_u5 Pm6Leaf_scalbnl_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import DecAssume.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_decfloat5_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DFO.
(* [comment removed for export] *)
Definition SCANEXP : Z := 0xbad40.   Definition RET_PC : Z := 0xb9ac8.   Definition SCALBNL : Z := 0xbb41c.
Definition TPV : Z := 0xdd010.       Definition ERRNO : Z := 0xdd010 - 164.
Definition IMG_LO : Z := 0x10000.    Definition IMG_HI : Z := 0xca250.
Definition IMGc : option (Z * Z) := Some (IMG_LO, IMG_HI).
Definition INL : list (Z * (Z * list nat * option Z)) :=
  map (fun pc => (pc, (4, [], None))) [0xb9a20; 0xb9a28; 0xb9a2c; 0xb97d8; 0xba298; 0xba2a4; 0xba2cc; 0xba3bc; 0xba3c0; 0xba390; 0xba3d0; 0xb98bc; 0xb98c0; 0xb98c4].
Definition CALLEES : list (Z * (Z * option (Z * Z))) :=
  map (fun ps : Z * Z => (fst ps, (snd ps, IMGc)))
    [(0xb6b84, 16); (0xb7538, 16); (0xb604c, 16); (0xb6484, 80); (0xb6c9c, 48); (0xb6c8c, 48); (0xb76cc, 112); (0xb6300, 16); (0xb63c8, 16); (0xb192c, 16); (0xbb10c, 16);
     (0xbb410, 16); (0xbb134, 192)].

Definition cutc := DOS.cut_chk CPS RETS DK5.DKINDS SCANEXP ERRNO.
Definition gchk (i : nat) (c : CC.cutpoint) (k : nat) (ps : SR.post_spec) (t : CC.tag) : bool :=
  match t with
  | CC.TGoto j s => match nth_error CPS j with Some cj => DOS.goto_chk2 CPS RETS DK5.DKINDS SCANEXP i c ps j cj s | None => false end
  | CC.TOther _ => true
  end.
Definition ochk := DOS.other_chk CPS RETS DK5.DKINDS SCANEXP RET_PC SCALBNL TPV INL CALLEES IMG_LO IMG_HI.

Lemma cuts_ok : CC.cps_all CPS cutc = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma gotos_ok : CH2.leaves_all CPS TAGS gchk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma others_ok : CC.others_all CPS TAGS ochk = true.      (* [comment removed for export] *)
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma ret_pc_ok : CL.is_ret_at RSEGS RET_PC.
Proof. CL.solve_is_ret. Qed.

Lemma inl_ok : forall pc len hv a0, In (pc, (len, hv, a0)) INL -> a0 = None /\ FPB.inl_step RSEGS pc len hv.
Proof.
  intros pc len hv a0 H. unfold INL in H. cbn [map In] in H.
  repeat (destruct H as [H|H]; [injection H as <- <- <- <-; split; [reflexivity|] |]); try contradiction.
  - exact Pm6FpSites.site_b5ff8. - exact Pm6FpSites.site_b6000. - exact Pm6FpSites.site_b6004. - exact Pm6FpSites.site_b5db0.
  - exact Pm6FpSites.site_b6870. - exact Pm6FpSites.site_b687c. - exact Pm6FpSites.site_b68a4. - exact Pm6FpSites.site_b6994.
  - exact Pm6FpSites.site_b6998. - exact Pm6FpSites.site_b6968. - exact Pm6FpSites.site_b69a8. - exact Pm6FpSites.site_b5e94.
  - exact Pm6FpSites.site_b5e98. - exact Pm6FpSites.site_b5e9c.
Qed.

Section Final.
Context {SCFG_P : ScfgP}.
(* [comment removed for export] *)
Hypothesis FMODL : CVF.vf_contract RSEGS 0xbb134 192 IMGc.
Hypothesis SCX : PDC.scanexp_contract RSEGS PDC.src11.

Lemma callees_ok : forall pc SCRc IMG, In (pc, (SCRc, IMG)) CALLEES -> CVF.vf_contract RSEGS pc SCRc IMG.
Proof.
  intros pc SCRc IMG H. unfold CALLEES in H. cbn [map In fst snd] in H.
  repeat (destruct H as [H|H]; [injection H as <- <- <- |]); try contradiction.
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_floatsitf_xsrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_floatunsitf_xsrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_extenddftf2_xsrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 80 80 None IMGc ltac:(lia) ltac:(auto) Leaf_multf3_xsrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 48 48 None IMGc ltac:(lia) ltac:(auto) Leaf_addtf3_xsrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 48 48 None IMGc ltac:(lia) ltac:(auto) Leaf_subtf3_xsrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 112 112 None IMGc ltac:(lia) ltac:(auto) Leaf_divtf3_xsrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_letf2_xsrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_getf2_xsrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 IMGc IMGc ltac:(lia) ltac:(auto) Leaf_scalbn_xsrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_copysignl_xsrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_fabsl_xsrc.ok).
  - exact FMODL.
Qed.
End Final.
End DFO.
