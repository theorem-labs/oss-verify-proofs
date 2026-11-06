(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx ArtBridge EbrInv EbrFsInv EbrFsInvLaws
     HeapIfaceAEx EbrIfaceInst EbrWrapSfree5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Lemma lit_5f444 : Z_to_bv 64 0x5f494 = (0x5f494%bv : word). Proof. apply bv_eq. reflexivity. Qed.

Section Inst.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Htp : rn_tp rn = 0x67a180.
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

#[using="Hwx Htp"] Theorem art_inst_sfree5 : HAJ.astack_free_spec art_L (rn_ar rn) scfg HI 0x5f494 16 5.
Proof.
  intros fx R M model LB FF LK cr A K F rs sp INV Hh HMI Hin H10 H4 Hret AST K0 POST.
  cbn [art_L hl_segs hl_tp] in *. rewrite lit_5f444. rewrite <- Htp in H4.
  apply (art_wrap_sfree5 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl (fx := fx)
           R M model LB FF LK cr A K F rs INV Hh HMI Hin H10 H4 Hret AST K0).
  intros R' M' model' RP SH FR SD RT MI' RI'. exact (POST R' M' model' RP SH FR SD RT MI' RI').
Qed.
End Inst.
