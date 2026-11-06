(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx ArtBridge EarInv EarFsInv EarFsInvLaws
     HeapIfaceAEx EarIfaceInst EarWrapAnn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Lemma lit_7c3b0 : Z_to_bv 64 0x7c400 = (0x7c400%bv : word). Proof. apply bv_eq. reflexivity. Qed.

Section Inst.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Htp : rn_tp rn = 0x675a80.
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

#[using="Hwx Htp"] Theorem art_inst_annotate : HAJ.annotate_spec art_L (rn_ar rn) scfg HI 0x7c400 2304.
Proof.
  intros fx R M model LB FF LK cr A K b c u u' sp INV Hh HMI H10 H11 H12 H13 Hin Hb16 Hu Hu' ANN H4 Hret AST K0 POST.
  cbn [art_L hl_segs hl_tp] in *. rewrite lit_7c3b0. rewrite <- Htp in H4.
  apply (art_wrap_annotate MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl (fx := fx)
           R M model LB FF LK cr A K b c u u' INV Hh HMI H10 H11 H12 H13 Hin Hb16 Hu Hu' ANN H4 Hret AST K0).
  intros R' M' model' A' RP AN FR SD SC RT INC MI' RI'. exact (POST fx R' M' model' A' RP AN FR SD SC RT INC MI' RI').
Qed.
End Inst.
