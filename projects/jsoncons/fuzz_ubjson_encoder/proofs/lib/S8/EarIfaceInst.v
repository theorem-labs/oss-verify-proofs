(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx ArtMem ArtRuns ArtBridge EarInv EarFsInv EarFsInvLaws
     EarWrapMallocAll EarWrapAligned16 EarIfaceLaws EarInvFrame EarIfaceFrame EarIfaceRelease EarHandoffRi EarWrapMemI EarWrapHnr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import HeapIfaceAEx ShadowRLawsB StrictOfB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Definition art_static (a : Z) : Prop :=
  0x13a000 <= a < 0x13d8d8 \/ 0x13e340 <= a < 0x664050 \/ 0x675a28 <= a < 0x675a30 \/ 0x675a78 <= a < 0x675a90 \/ 0x675a90 <= a < 0x675a94
  \/ 0x675aa8 <= a < 0x675ab0 \/ 0x696f38 <= a < 0x696f40.
Definition art_ro (a : Z) : Prop := 0x10000 <= a < 0x13a000.
Definition art_L : asan_layout :=
  AL ASEGS 0x7a19c 0x7a198 0x7a1a4 (fun k => if k =? 0 then 0x5e414 else if k =? 1 then 0x5e588 else if k =? 2 then 0x5e718 else if k =? 3 then 0x5e8b4 else if k =? 4 then 0x5ea60 else 0x5ea60) 0x81b6c 0x78ab4 0x78618 0x78cf4
     0x675a80 0x10000 0x698000 art_static art_ro 4096 4096 4096 512 4160 2560 8 3 (2 ^ 21) 8192 (2 ^ 34).
Definition art_C : asan_statics_cells := art_statics_cells.

Lemma art_L_statics : forall a, art_zone_statics a -> hl_rt_static art_L a.
Proof. intros a Z. cbn [art_L hl_rt_static]. unfold art_static, art_zone_statics in *. lia. Qed.
Lemma art_L_ro : forall a, 0x10000 <= a < 0x13a000 -> hl_rt_ro art_L a.
Proof. intros a Z. exact Z. Qed.

Section Inst.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis Htp : rn_tp rn = 0x675a80.
Hypothesis Hkey0 : rn_key rn = 0.
Hypothesis Htsd : rn_tsd rn = 0x696f38.
Hypothesis Hloff : rn_loff rn = 0x10.

#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

#[using="Htp Hkey0 Htsd Hloff"] Lemma art_L_tls : forall a, (rn_tp rn - 88 <= a < rn_tp rn - 80 \/ rn_tsd rn + 8 * rn_key rn <= a < rn_tsd rn + 8 * rn_key rn + 8
                              \/ 0x675a78 <= a < 0x675a80 \/ 0x675aa8 <= a < 0x675ab0 \/ rn_tp rn <= a < rn_tp rn + 8
                              \/ rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4) -> hl_rt_static art_L a.
Proof. intros a Z. rewrite Htp, Hkey0, Htsd, Hloff in Z. cbn [art_L hl_rt_static]. unfold art_static. lia. Qed.

#[using="Htp"] Lemma art_L_cs : forall a, (0x13afd0 <= a < 0x13afd8 \/ 0x13b098 <= a < 0x13b0b0 \/ rn_tp rn + 8 <= a < rn_tp rn + 16) -> hl_rt_static art_L a.
Proof. intros a Z. rewrite Htp in Z. cbn [art_L hl_rt_static]. unfold art_static. lia. Qed.

Hypothesis FREE : afree_spec art_L (rn_ar rn) scfg HI.
Hypothesis SMALLOC : forall k, In k [0; 1; 2; 3; 5] -> astack_malloc_spec art_L (rn_ar rn) scfg HI k.

#[using="Type"] Lemma art_L_static_img0 : forall a, hl_rt_static art_L a -> 0x10000 <= a < 0x698000.
Proof. intros a S. cbn [art_L hl_rt_static] in S. unfold art_static in S. lia. Qed.
#[using="Type"] Lemma art_L_ro_img0 : forall a, hl_rt_ro art_L a -> 0x10000 <= a < 0x698000.
Proof. intros a S. cbn [art_L hl_rt_ro] in S. unfold art_ro in S. lia. Qed.
#[using="Hwx Htp"] Theorem art_inst_no_return : ahandle_no_return_spec art_L (rn_ar rn) scfg HI.
Proof. apply (art_ahnr MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L); try reflexivity. symmetry. exact Htp. Qed.
#[using="Hwx Htp Hkey0 Htsd Hloff"] Theorem art_inst_memset : amemset_spec art_L (rn_ar rn) scfg HI.
Proof. exact (art_amemset MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics art_L_tls art_L_ro art_L_cs). Qed.
#[using="Hwx Htp Hkey0 Htsd Hloff"] Theorem art_inst_memcpy : amemcpy_spec art_L (rn_ar rn) scfg HI.
Proof. exact (art_amemcpy MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics art_L_tls art_L_ro art_L_cs). Qed.
#[using="Hwx Htp Hkey0 Htsd Hloff"] Theorem art_inst_memmove : amemmove_spec art_L (rn_ar rn) scfg HI.
Proof. exact (art_amemmove MAPS0 RESV0 NOACC0 BASE BUDGET rn scfg Hwx art_L eq_refl eq_refl eq_refl eq_refl eq_refl art_L_ro_img0 art_L_static_img0 art_L_statics art_L_tls art_L_ro art_L_cs). Qed.

#[using="Halloc Hwx STATIC Htp"] Theorem art_inst_malloc : amalloc_spec art_L (rn_ar rn) scfg HI.
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

#[using="Type"] Lemma art_r1_1046 : forall G LB M, art_alloc_rep art_fsg rn G LB M -> cell Asan.M.loaded_segments M 0x104c8 1 4.
Proof. intros G LB M (_ & ST & _). unfold art_rt_statics in ST. decompose [and] ST. assumption. Qed.
#[using="Halloc Hwx STATIC Htp"] Theorem art_inst_aligned : aaligned16_spec art_L (rn_ar rn) scfg HI.
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

#[using="Htp Hkey0 Htsd Hloff"] Theorem art_inst_release : rt_release_frame art_L (rn_ar rn) HI.
Proof. exact (art_law_release_frame MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl eq_refl eq_refl art_L_statics art_L_tls art_L_ro art_L_cs ltac:(intros a Z; cbn in Z; unfold art_ro in Z; lia)). Qed.

#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff FREE SMALLOC"] Theorem art_inst_ok : HAJ.asan_iface_okR art_L (rn_ar rn) art_C scfg HI.
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
  - exact (art_law_statics MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl Htp Hkey0 Htsd Hloff).
  - exact (art_law_flagptr MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl).
  - exact (art_law_small_high MAPS0 RESV0 NOACC0 BASE BUDGET rn).
Qed.

#[using="Type"] Lemma art_L_img_low : hl_img_hi art_L <= BIGSHADOW_LO.
Proof. cbn [art_L hl_img_hi]. unfold BIGSHADOW_LO. lia. Qed.

#[using="Type"] Lemma art_inst_flag_in_fs : rt_flag_in_fs art_L (rn_ar rn) HI.
Proof.
  intros LB FF LK cr A M V F k rs fl (G & _ & FS & _) Hin CF Hfl.
  destruct FS as (GEO & _ & _ & _ & _ & _ & _ & _ & FR & _).
  destruct (FR (F, k, rs) ltac:(apply in_or_app; left; exact Hin)) as (K1 & (i & (Hi & A1) & C1) & _).
  unfold ff_class, ff_addr in *. cbn [fst snd] in *.
  pose proof (fs_flag_below_frames (ar_fs (rn_ar rn)) k i ltac:(lia) Hi) as B.
  destruct GEO as (G1 & G2 & G3 & _ & (AM0 & _ & AM2) & _).
  assert (W : word_to_le_bytes 8 (Z_to_bv 64 fl) = word_to_le_bytes 8 (Z_to_bv 64 (fs_flag (ar_fs (rn_ar rn)) k i))).
  { unfold cell_is in CF. unfold cell in C1. cbn [art_L hl_segs] in CF. rewrite CF in C1. congruence. }
  assert (E : bv_unsigned (Z_to_bv 64 fl) mod 2 ^ (8 * Z.of_nat 8) = bv_unsigned (Z_to_bv 64 (fs_flag (ar_fs (rn_ar rn)) k i)) mod 2 ^ (8 * Z.of_nat 8)).
  { rewrite <- !bytes_le_N. rewrite W. reflexivity. }
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in E.
  rewrite !art_u_lit in E by (unfold FS_BYTES in *; lia). rewrite !Z.mod_small in E by (unfold FS_BYTES in *; lia).
  unfold FS_BYTES in *. lia.
Qed.

#[using="Htp Hkey0 Htsd Hloff"] Theorem art_inst_frame_ctr : HAJ.rt_frame_ctr art_L (rn_ar rn) HI.
Proof. exact (art_law_frame_ctr MAPS0 RESV0 NOACC0 BASE BUDGET rn art_L eq_refl eq_refl eq_refl art_L_statics art_L_tls art_L_ro art_L_cs Htp Hloff Htsd Hkey0 eq_refl). Qed.

#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff FREE SMALLOC"] Theorem art_inst_strict_ok : asan_iface_okB art_L (rn_ar rn) art_C scfg (HAJ.strict_of HI).
Proof. exact (strict_ok art_L (rn_ar rn) art_C scfg HI art_L_img_low art_inst_flag_in_fs art_inst_ok). Qed.
End Inst.
