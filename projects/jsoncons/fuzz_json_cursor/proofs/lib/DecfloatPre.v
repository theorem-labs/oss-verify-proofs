(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto Pm10PlanKit L5Defs L5Core
  FrmInv Pm10FrmInv FpBridge Pm10FpSites CutVF CutVFX DecIface DecScanPure DecOkDefs DecOkSem DecKinds5 DecfloatLems5
  Pm10Leaf_floatsitf Pm10Leaf_floatunsitf Pm10Leaf_extenddftf2 Pm10Leaf_multf3 Pm10Leaf_addtf3 Pm10Leaf_subtf3 Pm10Leaf_divtf3 Pm10Leaf_letf2 Pm10Leaf_getf2 Pm10Leaf_scalbn
  Pm10Leaf_copysignl Pm10Leaf_fabsl Pm10Leaf_scalbnl.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD Pm10CutKitD DecAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.FCutGen Require Import Cut_decfloat5_csrc.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DFO.

Definition SCANEXP : Z := 0xb2738.   Definition RET_PC : Z := 0xb14c0.   Definition SCALBNL : Z := 0xb2e14.
Definition TPV : Z := 0xd49b0.       Definition ERRNO : Z := 0xd49b0 - 164.
Definition IMG_LO : Z := 0x10000.    Definition IMG_HI : Z := 0xc1c28.
Definition IMGc : option (Z * Z) := Some (IMG_LO, IMG_HI).
Definition INL : list (Z * (Z * list nat * option Z)) :=
  map (fun pc => (pc, (4, [], None))) [0xb1418; 0xb1420; 0xb1424; 0xb11d0; 0xb1c90; 0xb1c9c; 0xb1cc4; 0xb1db4; 0xb1db8; 0xb1d88; 0xb1dc8; 0xb12b4; 0xb12b8; 0xb12bc].
Definition CALLEES : list (Z * (Z * option (Z * Z))) :=
  map (fun ps : Z * Z => (fst ps, (snd ps, IMGc)))
    [(0xae57c, 16); (0xaef30, 16); (0xada44, 16); (0xade7c, 80); (0xae694, 48); (0xae684, 48); (0xaf0c4, 112); (0xadcf8, 16); (0xaddc0, 16); (0xa9324, 16); (0xb2b04, 16);
     (0xb2e08, 16); (0xb2b2c, 192)].

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

Hypothesis FMODL : CVF.vf_contract RSEGS 0xb2b2c 192 IMGc.
Hypothesis SCX : PDC.scanexp_contract RSEGS PDC.src11.

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
