(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA ArtBridge JbtInv JbtFsInv JbtFsInvLaws
HeapIfaceAJx JbtIfaceInst JbtWrapAnn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Lemma lit_7b3f4 : Z_to_bv 64 0x7b3f4 = (0x7b3f4%bv : word). Proof. apply bv_eq. reflexivity. Qed.
Section Inst.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Htp : rn_tp rn = 0x670ac0.
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
#[using="Hwx Htp"] Theorem art_inst_annotate : HAJ.annotate_spec art_L (rn_ar rn) scfg HI 0x7b3f4 2304.
Proof.
intros fx R M model LB FF LK cr A K b c u u' sp INV Hh HMI H10 H11 H12 H13 Hin Hb16 Hc8 Hu8 Hu8' Hu Hu' ANN H4 Hret AST K0 POST.
cbn [art_L hl_segs hl_tp] in *. rewrite lit_7b3f4. rewrite <- Htp in H4.
apply (art_wrap_annotate MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl (fx := fx)
R M model LB FF LK cr A K b c u u' INV Hh HMI H10 H11 H12 H13 Hin Hb16 Hc8 Hu8 Hu8' Hu Hu' ANN H4 Hret AST K0).
intros R' M' model' A' RP AN FR SD SC RT INC MI' RI'. exact (POST fx R' M' model' A' RP AN FR SD SC RT INC MI' RI').
Qed.
End Inst.
