(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA PmHeapIfaceA IcptIfaceA PmIcptIfaceA HeapIfaceN Pm5IcptLayout ArtBridge
     Pm5ArtInv Pm5ArtFsInv Pm5ArtFsInvLaws Pm5ArtIfaceInst Pm5ArtWrapMallocAll Pm5ArtWrapMemI.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Lemma art_NB_eq : HeapIfaceN.NB = Pm5ArtInv.NB.  Proof. reflexivity. Qed.

Record pm_instN (L : asan_layout) (ar : asan_run) (IL : icpt_layout) (scfg : SpuriousCfg) (HI : asan_iface) : Prop := PINN {
  pin_mallocN : HeapIfaceN.amalloc_specN L ar scfg HI;
  pin_memcpy_libcN : HeapIfaceN.amemcpy_libc_specN L ar IL scfg HI;
  pin_memmove_libcN : HeapIfaceN.amemmove_libc_specN L ar IL scfg HI
}.

Theorem art_pm_instN : forall MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg (IL : icpt_layout), sc_alloc scfg = false -> wx_segs_nowrap ASEGS ->
  bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX -> as0_icpt_layout IL ->
  rn_tp rn = 0x6a1890 -> rn_key rn = 0 -> rn_tsd rn = 0x6c2d48 -> rn_loff rn = 0x10 ->
  pm_instN art_L (rn_ar rn) IL scfg (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).
Proof.
  intros MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg IL Halloc Hwx STATIC ILY Htp Hkey0 Htsd Hloff.
  destruct ILY as [E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14].
  constructor.
  - apply (art_wrap_mallocN art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg art_L Halloc Hwx STATIC); try reflexivity.
    + symmetry. exact Htp.
    + exact art_L_statics.
    + cbn. lia.
    + cbn. lia.
    + cbn. lia.
    + exact art_fsinv_frame_law_proved.
    + intros gfs FF LK M FS. exact (art_fsinv_in_proved rn gfs FF LK M FS).
  - exact (art_amemcpy_libcN MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L IL eq_refl eq_refl eq_refl eq_refl E7 art_L_ro_img0 art_L_static_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs rn Htp)).
  - exact (art_amemmove_libcN MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L IL eq_refl eq_refl eq_refl eq_refl E8 art_L_ro_img0 art_L_static_img0 art_L_statics (art_L_tls rn Htp Hkey0 Htsd Hloff) art_L_ro (art_L_cs rn Htp)).
Qed.
