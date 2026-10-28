(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b BatInv_b BatFsInv_b BatIfaceInst_b
     BatWrapStrlen_b BatIcptLaws_b BatWrapMemI_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Theorem art_icpt_ok : forall (scfg : SpuriousCfg) (IL : icpt_layout) (BUDGET : Z), wx_segs_nowrap ASEGS -> as0_icpt_layout IL ->
  forall MAPS0 RESV0 NOACC0 BASE rn, rn_tp rn = 0x673d00 -> rn_key rn = 0 -> rn_tsd rn = 0x6951b8 -> rn_loff rn = 0x10 ->
  aicpt_ok art_L (rn_ar rn) IL scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Proof.
  intros scfg IL BUDGET Hwx ILY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey0 Htsd Hloff.
  destruct ILY as [E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14].
  constructor.
  - exact (art_astrlen MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L IL eq_refl eq_refl eq_refl E1 E2 E3 E4).
  - exact (art_law_globals MAPS0 RESV0 NOACC0 BASE BUDGET rn IL E5).
  - exact (art_law_img_shadow MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L IL eq_refl eq_refl E6).
  - exact (art_law_shadow_defined MAPS0 RESV0 NOACC0 BASE BUDGET rn).
  - exact (art_law_tls MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L IL eq_refl eq_refl eq_refl (eq_sym Htp) E9 Htsd Hkey0 art_L_ro_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro).
  - exact (art_amemcpy_libc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L IL eq_refl eq_refl eq_refl eq_refl E7 art_L_ro_img0 art_L_static_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs rn Htp)).
  - exact (art_amemmove_libc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L IL eq_refl eq_refl eq_refl eq_refl E8 art_L_ro_img0 art_L_static_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs rn Htp)).
Qed.
