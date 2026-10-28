(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatFsInv_b BatFsInvLaws_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatIfaceInst_b BatWrapSfree5_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Lemma lit_5ded0 : Z_to_bv 64 0x5e2e8 = (0x5e2e8%bv : word). Proof. apply bv_eq. reflexivity. Qed.

Section Inst.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Htp : rn_tp rn = 0x673d00.
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

#[using="Hwx Htp"] Theorem art_inst_sfree5 : HAJ.astack_free_spec art_L (rn_ar rn) scfg HI 0x5e2e8 16 5.
Proof.
  intros fx R M model LB FF LK cr A K F rs sp INV Hh HMI Hin H10 H4 Hret AST K0 POST.
  cbn [art_L hl_segs hl_tp] in *. rewrite lit_5ded0. rewrite <- Htp in H4.
  apply (art_wrap_sfree5 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl (fx := fx)
           R M model LB FF LK cr A K F rs INV Hh HMI Hin H10 H4 Hret AST K0).
  intros R' M' model' RP SH FR SD RT MI' RI'. exact (POST R' M' model' RP SH FR SD RT MI' RI').
Qed.
End Inst.
