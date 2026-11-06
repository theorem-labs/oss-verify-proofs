(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA PmHeapIfaceA ArtMem ArtRuns ArtBridge Pm9ArtInv Pm9ArtFsInv Pm9ArtFsInvLaws
     Pm9ArtWrapMallocAll Pm9ArtWrapAligned16 Pm9ArtIfaceLaws Pm9ArtInvFrame Pm9ArtIfaceFrame Pm9ArtIfaceRelease Pm9ArtHandoffRi Pm9ArtWrapMemI Pm9ArtWrapHnr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Definition art_static (a : Z) : Prop :=
  0x156000 <= a < 0x158c38 \/ 0x15a640 <= a < 0x680350 \/ 0x691d38 <= a < 0x691d40 \/ 0x691d88 <= a < 0x691da0 \/ 0x691da0 <= a < 0x691da4
  \/ 0x691db8 <= a < 0x691dc0 \/ 0x6b3248 <= a < 0x6b3250.
Definition art_ro (a : Z) : Prop := 0x10000 <= a < 0x156000.
Definition art_L : asan_layout :=
  AL ASEGS 0x80db8 0x80db4 0x80dc0 (fun k => if k =? 0 then 0x64e64 else if k =? 1 then 0x64fd8 else if k =? 2 then 0x65168 else if k =? 3 then 0x65304 else if k =? 4 then 0x654b0 else 0x6567c) 0x88788 0x7f6d0 0x7f234 0x7f910
     0x691d90 0x10000 0x6b4000 art_static art_ro 4096 4096 4096 512 4160 2560 8 3 (2 ^ 21) 8192 (2 ^ 34).
Definition art_C : asan_statics_cells := art_statics_cells.

Lemma art_L_statics : forall a, art_zone_statics a -> hl_rt_static art_L a.
Proof. intros a Z. cbn [art_L hl_rt_static]. unfold art_static, art_zone_statics in *. lia. Qed.
Lemma art_L_ro : forall a, 0x10000 <= a < 0x156000 -> hl_rt_ro art_L a.
Proof. intros a Z. exact Z. Qed.

Section Inst.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis Htp : rn_tp rn = 0x691d90.
Hypothesis Hkey0 : rn_key rn = 0.
Hypothesis Htsd : rn_tsd rn = 0x6b3248.
Hypothesis Hloff : rn_loff rn = 0x10.

#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

Lemma art_L_tls : forall a, (rn_tp rn - 88 <= a < rn_tp rn - 80 \/ rn_tsd rn + 8 * rn_key rn <= a < rn_tsd rn + 8 * rn_key rn + 8
                              \/ 0x691d88 <= a < 0x691d90 \/ 0x691db8 <= a < 0x691dc0 \/ rn_tp rn <= a < rn_tp rn + 8
                              \/ rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4) -> hl_rt_static art_L a.
Proof. intros a Z. rewrite Htp, Hkey0, Htsd, Hloff in Z. cbn [art_L hl_rt_static]. unfold art_static. lia. Qed.

Lemma art_L_cs : forall a, (0x156330 <= a < 0x156338 \/ 0x1563f8 <= a < 0x156410 \/ rn_tp rn + 8 <= a < rn_tp rn + 16) -> hl_rt_static art_L a.
Proof. intros a Z. rewrite Htp in Z. cbn [art_L hl_rt_static]. unfold art_static. lia. Qed.

Hypothesis FREE : afree_spec art_L (rn_ar rn) scfg HI.
Hypothesis SMALLOC : forall k, In k PM_FS_CLASSES -> astack_malloc_spec art_L (rn_ar rn) scfg HI k.

Lemma art_L_static_img0 : forall a, hl_rt_static art_L a -> 0x10000 <= a < 0x6b4000.
Proof. intros a S. cbn [art_L hl_rt_static] in S. unfold art_static in S. lia. Qed.
Lemma art_L_ro_img0 : forall a, hl_rt_ro art_L a -> 0x10000 <= a < 0x6b4000.
Proof. intros a S. cbn [art_L hl_rt_ro] in S. unfold art_ro in S. lia. Qed.
Theorem art_inst_no_return : ahandle_no_return_spec art_L (rn_ar rn) scfg HI.
Proof. apply (art_ahnr MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L); try reflexivity. symmetry. exact Htp. Qed.
Theorem art_inst_memset : amemset_spec art_L (rn_ar rn) scfg HI.
Proof. exact (art_amemset MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics art_L_tls art_L_ro art_L_cs). Qed.
Theorem art_inst_memcpy : amemcpy_spec art_L (rn_ar rn) scfg HI.
Proof. exact (art_amemcpy MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics art_L_tls art_L_ro art_L_cs). Qed.
Theorem art_inst_memmove : amemmove_spec art_L (rn_ar rn) scfg HI.
Proof. exact (art_amemmove MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics art_L_tls art_L_ro art_L_cs). Qed.

Theorem art_inst_malloc : amalloc_spec art_L (rn_ar rn) scfg HI.
Proof.
  apply (art_wrap_malloc art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg art_L Halloc Hwx STATIC); try reflexivity.
  - symmetry. exact Htp.
  - exact art_L_statics.
  - cbn. lia.
  - cbn. lia.
  - cbn. lia.
  - exact art_fsinv_frame_law_proved.
  - intros gfs FF LK M FS. exact (art_fsinv_in_proved rn gfs FF LK M FS).
Qed.

Lemma art_r1_1046 : forall G LB M, art_alloc_rep art_fsg rn G LB M -> cell AsanUbsan.M.loaded_segments M 0x104f8 1 4.
Proof. intros G LB M (_ & ST & _). unfold art_rt_statics in ST. decompose [and] ST. assumption. Qed.
Theorem art_inst_aligned : aaligned16_spec art_L (rn_ar rn) scfg HI.
Proof.
  apply (art_wrap_aligned16 art_fsg art_fsinv MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg art_L Halloc Hwx STATIC); try reflexivity.
  - exact art_r1_1046.
  - symmetry. exact Htp.
  - exact art_L_statics.
  - cbn. lia.
  - cbn. lia.
  - cbn. lia.
  - exact art_fsinv_frame_law_proved.
  - intros gfs FF LK M FS. exact (art_fsinv_in_proved rn gfs FF LK M FS).
Qed.

Theorem art_inst_release : rt_release_frame art_L (rn_ar rn) HI.
Proof. exact (art_law_release_frame MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl eq_refl eq_refl art_L_statics art_L_tls art_L_ro art_L_cs ltac:(intros a Z; cbn in Z; unfold art_ro in Z; lia)). Qed.

Theorem art_inst_ok : asan_iface_ok art_L (rn_ar rn) art_C scfg HI.
Proof.
  constructor.
  - exact art_inst_malloc.
  - exact art_inst_aligned.
  - exact FREE.
  - exact SMALLOC.
  - exact art_inst_release.
  - exact (art_law_leak_frames MAPS0 RESV0 NOACC0 BASE BUDGET rn).
  - exact art_inst_no_return.
  - exact art_inst_memset.
  - exact art_inst_memcpy.
  - exact art_inst_memmove.
  - exact (art_law_frame MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl eq_refl art_L_statics art_L_tls art_L_ro art_L_cs).
  - exact (art_law_wf MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl eq_refl).
  - exact (art_law_lazy MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl).
  - exact (art_law_perm MAPS0 RESV0 NOACC0 BASE BUDGET rn).
  - exact (art_law_statics MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl Htp Hkey0 Htsd).
  - exact (art_law_flagptr MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl).
  - exact (art_law_small_high MAPS0 RESV0 NOACC0 BASE BUDGET rn).
Qed.
End Inst.
