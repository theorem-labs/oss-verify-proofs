(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs L5Core
  FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10FrmInv_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import FpBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10FpSites_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import CutVF CutVFX DecIface DecIfaceU DecScanPure DecOkDefs DecOkSem DecKinds5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import DecfloatLems5_u
  Pm10Leaf_floatsitf_u Pm10Leaf_floatunsitf_u Pm10Leaf_extenddftf2_u Pm10Leaf_multf3_u Pm10Leaf_addtf3_u Pm10Leaf_subtf3_u Pm10Leaf_divtf3_u Pm10Leaf_letf2_u Pm10Leaf_getf2_u Pm10Leaf_scalbn_u
  Pm10Leaf_copysignl_u Pm10Leaf_fabsl_u Pm10Leaf_scalbnl_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutCert Require Import Pm10CutKitD_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import DecAssume.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_decfloat5_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DFO.

Definition SCANEXP : Z := 0xb458c.   Definition RET_PC : Z := 0xb3314.   Definition SCALBNL : Z := 0xb4c68.
Definition TPV : Z := 0xd6800.       Definition ERRNO : Z := 0xd6800 - 164.
Definition IMG_LO : Z := 0x10000.    Definition IMG_HI : Z := 0xc3a78.
Definition IMGc : option (Z * Z) := Some (IMG_LO, IMG_HI).
Definition INL : list (Z * (Z * list nat * option Z)) :=
  map (fun pc => (pc, (4, [], None))) [0xb326c; 0xb3274; 0xb3278; 0xb3024; 0xb3ae4; 0xb3af0; 0xb3b18; 0xb3c08; 0xb3c0c; 0xb3bdc; 0xb3c1c; 0xb3108; 0xb310c; 0xb3110].
Definition CALLEES : list (Z * (Z * option (Z * Z))) :=
  map (fun ps : Z * Z => (fst ps, (snd ps, IMGc)))
    [(0xb03d0, 16); (0xb0d84, 16); (0xaf898, 16); (0xafcd0, 80); (0xb04e8, 48); (0xb04d8, 48); (0xb0f18, 112); (0xafb4c, 16); (0xafc14, 16); (0xab178, 16); (0xb4958, 16);
     (0xb4c5c, 16); (0xb4980, 192)].

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
Lemma others_ok : CC.others_all CPS TAGS ochk = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma ret_pc_ok : CL.is_ret_at RSEGS RET_PC.
Proof. CL.solve_is_ret. Qed.

Lemma inl_ok : forall pc len hv a0, In (pc, (len, hv, a0)) INL -> a0 = None /\ FPB.inl_step RSEGS pc len hv.
Proof.
  intros pc len hv a0 H. unfold INL in H. cbn [map In] in H.
  repeat (destruct H as [H|H]; [injection H as <- <- <- <-; split; [reflexivity|] |]); try contradiction.
  - exact Pm10FpSites.site_b13dc. - exact Pm10FpSites.site_b13e4. - exact Pm10FpSites.site_b13e8. - exact Pm10FpSites.site_b1194.
  - exact Pm10FpSites.site_b1c54. - exact Pm10FpSites.site_b1c60. - exact Pm10FpSites.site_b1c88. - exact Pm10FpSites.site_b1d78.
  - exact Pm10FpSites.site_b1d7c. - exact Pm10FpSites.site_b1d4c. - exact Pm10FpSites.site_b1d8c. - exact Pm10FpSites.site_b1278.
  - exact Pm10FpSites.site_b127c. - exact Pm10FpSites.site_b1280.
Qed.

Section Final.
Context {SCFG_P : ScfgP}.

Hypothesis FMODL : CVF.vf_contract RSEGS 0xb4980 192 IMGc.
Hypothesis SCX : PDC.scanexp_contract RSEGS PDCU.ubsan11.

Lemma callees_ok : forall pc SCRc IMG, In (pc, (SCRc, IMG)) CALLEES -> CVF.vf_contract RSEGS pc SCRc IMG.
Proof.
  intros pc SCRc IMG H. unfold CALLEES in H. cbn [map In fst snd] in H.
  repeat (destruct H as [H|H]; [injection H as <- <- <- |]); try contradiction.
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_floatsitf_csrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_floatunsitf_csrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_extenddftf2_csrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 80 80 None IMGc ltac:(lia) ltac:(auto) Leaf_multf3_csrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 48 48 None IMGc ltac:(lia) ltac:(auto) Leaf_addtf3_csrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 48 48 None IMGc ltac:(lia) ltac:(auto) Leaf_subtf3_csrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 112 112 None IMGc ltac:(lia) ltac:(auto) Leaf_divtf3_csrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_letf2_csrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_getf2_csrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 IMGc IMGc ltac:(lia) ltac:(auto) Leaf_scalbn_csrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_copysignl_csrc.ok).
  - exact (CVF.vf_contract_weaken RSEGS _ 0 16 None IMGc ltac:(lia) ltac:(auto) Leaf_fabsl_csrc.ok).
  - exact FMODL.
Qed.
End Final.
End DFO.
