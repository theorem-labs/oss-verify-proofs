(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto Pm6PlanKit L5Defs L5Core
  FrmInv Pm6FrmInv FpBridge Pm6FpSites CutVF CutVFX DecIface DecScanPure DecOkDefs DecOkSem DecKinds5 DecfloatLems5
  Pm6Leaf_floatsitf Pm6Leaf_floatunsitf Pm6Leaf_extenddftf2 Pm6Leaf_multf3 Pm6Leaf_addtf3 Pm6Leaf_subtf3 Pm6Leaf_divtf3 Pm6Leaf_letf2 Pm6Leaf_getf2 Pm6Leaf_scalbn
  Pm6Leaf_copysignl Pm6Leaf_fabsl Pm6Leaf_scalbnl.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD Pm6CutKitD DecAssume.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutGen Require Import Cut_decfloat5_xsrc.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DFO.
(* [comment removed for export] *)
Definition SCANEXP : Z := 0xb7354.   Definition RET_PC : Z := 0xb60dc.   Definition SCALBNL : Z := 0xb7a30.
Definition TPV : Z := 0xd9620.       Definition ERRNO : Z := 0xd9620 - 164.
Definition IMG_LO : Z := 0x10000.    Definition IMG_HI : Z := 0xc6860.
Definition IMGc : option (Z * Z) := Some (IMG_LO, IMG_HI).
Definition INL : list (Z * (Z * list nat * option Z)) :=
  map (fun pc => (pc, (4, [], None))) [0xb6034; 0xb603c; 0xb6040; 0xb5dec; 0xb68ac; 0xb68b8; 0xb68e0; 0xb69d0; 0xb69d4; 0xb69a4; 0xb69e4; 0xb5ed0; 0xb5ed4; 0xb5ed8].
Definition CALLEES : list (Z * (Z * option (Z * Z))) :=
  map (fun ps : Z * Z => (fst ps, (snd ps, IMGc)))
    [(0xb3198, 16); (0xb3b4c, 16); (0xb2660, 16); (0xb2a98, 80); (0xb32b0, 48); (0xb32a0, 48); (0xb3ce0, 112); (0xb2914, 16); (0xb29dc, 16); (0xadf40, 16); (0xb7720, 16);
     (0xb7a24, 16); (0xb7748, 192)].

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
Hypothesis FMODL : CVF.vf_contract RSEGS 0xb7748 192 IMGc.
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
