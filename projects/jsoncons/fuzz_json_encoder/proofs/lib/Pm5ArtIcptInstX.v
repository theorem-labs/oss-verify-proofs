(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA Pm5IcptLayout Pm5ArtInv Pm5ArtFsInv Pm5ArtIfaceInst
     Pm5ArtWrapStrlen Pm5ArtIcptLaws Pm5ArtWrapMemI Pm5ArtWrapCxa Pm5ArtWrapAnnot Pm5ArtWrapMemcmp Pm5ArtWrapMemsetIR Pm5ArtWrapSetShadow.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Theorem art_pm_icpt_ok : forall (scfg : SpuriousCfg) (IL : icpt_layout) (ILX : icpt_layout_x) (BUDGET : Z) (ANNOTATE : Prop), wx_segs_nowrap ASEGS -> as0_icpt_layout IL -> pm_icpt_layout_x ILX ->
  forall MAPS0 RESV0 NOACC0 BASE rn, rn_tp rn = 0x6a1890 -> rn_key rn = 0 -> rn_tsd rn = 0x6c2d48 -> rn_loff rn = 0x10 ->
  let HI := art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn in
  pm_icptx_open art_L (rn_ar rn) ILX scfg HI -> ANNOTATE ->
  pm_aicpt_ok art_L (rn_ar rn) IL ILX scfg HI ANNOTATE.
Proof.
  intros scfg IL ILX BUDGET ANNOTATE Hwx ILY ILXY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey0 Htsd Hloff HI OPEN ANN.
  destruct OPEN as (MEMCMP & MEMCMP2 & MEMSETL & SH00 & SHF5 & SHF8).
  destruct ILY as [E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14].
  constructor.
  - exact (art_astrlen MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L IL eq_refl eq_refl eq_refl E1 E2 E3 E4).
  - exact (art_law_globals MAPS0 RESV0 NOACC0 BASE BUDGET rn IL E5).
  - exact (art_law_img_shadow MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L IL eq_refl eq_refl E6).
  - exact (art_law_shadow_defined MAPS0 RESV0 NOACC0 BASE BUDGET rn).
  - exact (art_law_tls MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L IL eq_refl eq_refl eq_refl (eq_sym Htp) E9 Htsd Hkey0 art_L_ro_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro).
  - exact (art_amemcpy_libc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L IL eq_refl eq_refl eq_refl eq_refl E7 art_L_ro_img0 art_L_static_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs rn Htp)).
  - exact (art_amemmove_libc MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L IL eq_refl eq_refl eq_refl eq_refl E8 art_L_ro_img0 art_L_static_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs rn Htp)).
  - exact MEMCMP.
  - (* [comment removed for export] *)
    destruct ILXY as [X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15].
    intros fx R M model LB FF LK cr A f arg dso hs Kt sp AX INV Hh HMI H10 H11 H12 Hf Harg H4 Hret AST TAB HLEN HNE CNL TABW KT0 CONT.
    subst sp AX. rewrite X3. rewrite X4 in AST, CONT. rewrite X5 in TAB, TABW, CONT. rewrite X6 in CONT. rewrite X9 in CNL.
    assert (LSANST : forall a, 0x6a18a0 <= a < 0x6a18a0 + 4 -> hl_rt_static art_L a) by (intros a Ha; apply (art_L_tls rn Htp Hkey0 Htsd Hloff); rewrite Htp, Hloff; lia).
    change (hl_tp art_L) with 0x6a1890 in H4. rewrite <- Htp in H4.
    exact (art_wrap_cxa_atexit MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl Htp Hloff Hkey0 Htsd LSANST R M model LB FF LK cr A f arg hs Kt
             INV Hh HMI H10 H11 Hf Harg H4 Hret AST TAB HLEN HNE CNL TABW KT0 CONT).
  - exact ANN.
  - (* [comment removed for export] *)
    destruct ILXY as [X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15].
    intros fx R M model LB FF LK cr A Kt sp INV Hh HMI H10 H4 Hret AST KT0 CONT. subst sp. rewrite X6. rewrite X7 in AST, CONT.
    exact (art_wrap_atcxa MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl R M model LB FF LK cr A Kt INV Hh HMI Hret AST KT0 CONT).
  - exact MEMCMP2.
  - exact MEMSETL.
  - exact SH00.
  - exact SHF5.
  - exact SHF8.
Qed.

(* [comment removed for export] *)
Theorem art_aannotate : forall (scfg : SpuriousCfg) (BUDGET : Z), wx_segs_nowrap ASEGS -> forall MAPS0 RESV0 NOACC0 BASE rn,
  aannotate_spec art_L (rn_ar rn) scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn) 0x848f8 4096.
Proof.
  intros scfg BUDGET Hwx MAPS0 RESV0 NOACC0 BASE rn fx R M model LB FF LK cr A u n om nm Kt sp INV Hh HMI HB H10 H11 H12 H13 Hom Hnm Hn SC Hret AST KT0 CONT.
  exact (art_wrap_annotate MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl R M model LB FF LK cr A u n om nm Kt INV Hh HMI HB H10 H11 H12 H13 Hom Hnm Hn SC Hret AST KT0 CONT).
Qed.

Theorem art_pm_icpt_ok_annot : forall (scfg : SpuriousCfg) (IL : icpt_layout) (ILX : icpt_layout_x) (BUDGET : Z), wx_segs_nowrap ASEGS -> as0_icpt_layout IL -> pm_icpt_layout_x ILX ->
  forall MAPS0 RESV0 NOACC0 BASE rn, rn_tp rn = 0x6a1890 -> rn_key rn = 0 -> rn_tsd rn = 0x6c2d48 -> rn_loff rn = 0x10 ->
  let HI := art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn in
  pm_icptx_open art_L (rn_ar rn) ILX scfg HI ->
  pm_aicpt_ok art_L (rn_ar rn) IL ILX scfg HI (aannotate_spec art_L (rn_ar rn) scfg HI (iclx_annotate ILX) 4096).
Proof.
  intros scfg IL ILX BUDGET Hwx ILY ILXY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey0 Htsd Hloff HI OPEN.
  apply (art_pm_icpt_ok scfg IL ILX BUDGET _ Hwx ILY ILXY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey0 Htsd Hloff OPEN).
  destruct ILXY as [X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15]. rewrite X8. exact (art_aannotate scfg BUDGET Hwx MAPS0 RESV0 NOACC0 BASE rn).
Qed.

(* [comment removed for export] *)
Theorem art_pm_icptx : forall (scfg : SpuriousCfg) (ILX : icpt_layout_x) (BUDGET : Z), wx_segs_nowrap ASEGS -> pm_icpt_layout_x ILX ->
  forall MAPS0 RESV0 NOACC0 BASE rn, rn_tp rn = 0x6a1890 -> rn_key rn = 0 -> rn_tsd rn = 0x6c2d48 -> rn_loff rn = 0x10 ->
  pm_icptx_open art_L (rn_ar rn) ILX scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Proof.
  intros scfg ILX BUDGET Hwx ILXY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey0 Htsd Hloff.
  destruct ILXY as [X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15].
  unfold pm_icptx_open, amemcmp_spec, amemset_libc_spec. rewrite X1, X2, X10, X11, X12, X13, X14, X15.
  split; [| split; [| split; [| split; [| split]]]].
  - exact (art_abcmp_at MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl).
  - exact (art_amemcmp_at MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl).
  - exact (art_amemset_libc_at MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs rn Htp)).
  - exact (art_asetsh_00 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs rn Htp)).
  - exact (art_asetsh_f5 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs rn Htp)).
  - exact (art_asetsh_f8 MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs rn Htp)).
Qed.

(* [comment removed for export] *)
Theorem art_pm_icpt_ok_closed : forall (scfg : SpuriousCfg) (IL : icpt_layout) (ILX : icpt_layout_x) (BUDGET : Z), wx_segs_nowrap ASEGS -> as0_icpt_layout IL -> pm_icpt_layout_x ILX ->
  forall MAPS0 RESV0 NOACC0 BASE rn, rn_tp rn = 0x6a1890 -> rn_key rn = 0 -> rn_tsd rn = 0x6c2d48 -> rn_loff rn = 0x10 ->
  let HI := art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn in
  pm_aicpt_ok art_L (rn_ar rn) IL ILX scfg HI (aannotate_spec art_L (rn_ar rn) scfg HI (iclx_annotate ILX) 4096).
Proof.
  intros scfg IL ILX BUDGET Hwx ILY ILXY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey0 Htsd Hloff HI.
  apply (art_pm_icpt_ok_annot scfg IL ILX BUDGET Hwx ILY ILXY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey0 Htsd Hloff).
  exact (art_pm_icptx scfg ILX BUDGET Hwx ILXY MAPS0 RESV0 NOACC0 BASE rn Htp Hkey0 Htsd Hloff).
Qed.
