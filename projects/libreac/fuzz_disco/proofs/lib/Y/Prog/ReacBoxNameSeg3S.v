(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-148, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_cuts.v, with its module paths, module names, addresses and numbers changed; 169 of its 287 lines of code are new or changed and 517 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/ReacBoxNameLoops.v, with its module paths and module names changed; 335 of its 374 lines of code are new or changed and 248 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
SbCh SbDec ReacBoxName ReacBoxNameCut ReacBoxNameSeg3D.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma rbn3s_ge : forall a l, a + l + 1 <= a + l - (a + l) mod 8 + 8 /\ a + l - (a + l) mod 8 + 8 <= a + l + 8.
Proof. intros a l. pose proof (Z.mod_pos_bound (a + l) 8 ltac:(lia)). lia. Qed.
Lemma rbn3s_ge64 : forall f bs a l, f mod 64 = 0 -> bs mod 64 = 0 -> a + l + 1 <= f + bs ->
  a + l - (a + l) mod 8 + 8 <= f + bs.
Proof. intros f bs a l H1 H2 H3. lia. Qed.
Lemma rbn3s_ge16 : forall s a l, s mod 16 = 0 -> a + l + 1 <= s -> a + l - (a + l) mod 8 + 8 <= s.
Proof. intros s a l H1 H2. lia. Qed.
Lemma rbn3s_frame_ar : forall f bs y, f mod 64 = 0 -> bs mod 64 = 0 -> f <= y < f + bs ->
  in_zr (shadow_of_addr SHADOW_OFF y) (shadow_addr f, bs / 8).
Proof. intros f bs y H1 H2 H3. unfold in_zr, shadow_of_addr, shadow_addr. cbn [fst snd]. lia. Qed.
Lemma rbn3s_stk_ar2 : forall lo hi y, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= y < hi ->
  shadow_of_addr SHADOW_OFF y = shadow_of_addr SHADOW_OFF lo + (y / 8 - lo / 8) /\
  0 <= y / 8 - lo / 8 < (hi - lo) / 8.
Proof. intros lo hi y H1 H2 H3. unfold shadow_of_addr. split; [lia|]. lia. Qed.
Lemma rbn3s_stk_ar : forall lo hi a n s, lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= a -> a + n <= hi -> 0 < n ->
  shadow_addr a / 8 * 8 <= s < shadow_addr (a + n - 1) / 8 * 8 + 8 ->
  s = shadow_of_addr SHADOW_OFF lo + (s - shadow_of_addr SHADOW_OFF lo) /\
  0 <= s - shadow_of_addr SHADOW_OFF lo < (hi - lo) / 8.
Proof.
intros lo hi a n s H1 H2 H3 H4 H5 H6. unfold shadow_of_addr, shadow_addr, SHADOW_OFF in *. split; [lia|]. lia.
Qed.
Lemma rbn3s_globs : forall q sz, rbn_ro q sz -> 0x20f80 <= q /\ q + sz <= 0xa0700.
Proof.
intros q sz H. unfold rbn_ro, tfib_globs in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as E1 E2; subst; lia|]). destruct H.
Qed.
Lemma rbn3s_lb : forall v k, 0 <= YO0f.le_byte v 8 k < bv_modulus 8.
Proof. intros v k. change (bv_modulus 8) with 256. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.
Lemma rbn3s_vm8 : forall segs (m : word -> option byte) a v w, val_mem segs m a 8 v -> val_mem segs m a 8 w ->
  0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 -> v = w.
Proof.
intros segs m a v w Hv Hw Rv Rw.
assert (E : forall k, (k < 8)%nat -> YG0f.le_byte v 8 k = YG0f.le_byte w 8 k).
{ intros k Hk. pose proof (Hv k Hk) as A. rewrite (Hw k Hk) in A.
  assert (A2 : bv_unsigned (Z_to_bv 8 (YO0f.le_byte w 8 k)) = bv_unsigned (Z_to_bv 8 (YO0f.le_byte v 8 k)))
    by congruence.
  rewrite !Z_to_bv_unsigned in A2.
  rewrite !bv_wrap_small in A2 by apply rbn3s_lb. exact (eq_sym A2). }
rewrite <- (le_bytes8 v Rv), <- (le_bytes8 w Rw).
rewrite (E 0%nat), (E 1%nat), (E 2%nat), (E 3%nat), (E 4%nat), (E 5%nat), (E 6%nat), (E 7%nat) by lia.
reflexivity.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma rbn3s_str_mv : forall (W W' : world SEGS) (m m' : word -> option byte) a s,
  rbn_str W m a s ->
  (forall x, a <= x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  range_addressable (aview SEGS (w_H W') m') SHADOW_OFF a (Z.of_nat (length s) + 1) ->
  shadow_hull_vis (aview SEGS (w_H W') m') a (Z.of_nat (length s) + 1) ->
  rbn_str W' m' a s.
Proof.
intros W W' m m' a s (Hf & Hg & Ha0 & Ha1 & Hl & Ham & _ & _ & Htl) HE Hra Hhv.
destruct (rbn3s_ge a (Z.of_nat (length s))) as [G1 G2].
split; [exact Hf|]. split.
{ apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact Hg|]. intros x Hx.
  rewrite length_app in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HE. lia. }
split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Hl|]. split; [exact Ham|].
split; [exact Hra|]. split; [exact Hhv|].
intros x Hx. rewrite (HE x); [exact (Htl x Hx) | lia].
Qed.
Lemma rbn3s_str_mv2 : forall (W W' : world SEGS) (m m' : word -> option byte) a s,
  rbn_str W m a s ->
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  (forall x, a + Z.of_nat (length s) + 1 <= x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     seg_rom SEGS (Z_to_bv 64 x) <> None) ->
  range_addressable (aview SEGS (w_H W') m') SHADOW_OFF a (Z.of_nat (length s) + 1) ->
  shadow_hull_vis (aview SEGS (w_H W') m') a (Z.of_nat (length s) + 1) ->
  rbn_str W' m' a s.
Proof.
intros W W' m m' a s (Hf & Hg & Ha0 & Ha1 & Hl & Ham & _ & _ & Htl) HE HT Hra Hhv.
destruct (rbn3s_ge a (Z.of_nat (length s))) as [G1 G2].
split; [exact Hf|]. split.
{ apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact Hg|]. intros x Hx.
  rewrite length_app in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HE. lia. }
split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Hl|]. split; [exact Ham|].
split; [exact Hra|]. split; [exact Hhv|].
intros x Hx. pose proof (HT x ltac:(lia)) as P.
unfold aview, YP09.mbyte, YK04.mrestrict. destruct (w_H W' (Z_to_bv 64 x)).
- destruct (seg_rom SEGS (Z_to_bv 64 x)); [discriminate|contradiction].
- destruct (m' (Z_to_bv 64 x)); [discriminate|].
  destruct (seg_rom SEGS (Z_to_bv 64 x)); [discriminate|contradiction].
Qed.
Lemma rbn3s_str_rng : forall (W : world SEGS) m a s, rbn_str W m a s ->
  0 < a /\ a + Z.of_nat (length s) + 1 <= 2 ^ 63.
Proof. intros W m a s (_ & _ & H0 & H1 & _). split; [exact H0 | exact H1]. Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Lemma rbn3s_cx_img : forall X, rbn_cx B X -> rbn_img B (ri_W X) (ri_memc X).
Proof. intros X HX. unfold rbn_cx in HX. do 32 (destruct HX as [_ HX]). exact (proj1 HX). Qed.
Lemma rbn3s_cx_said : forall X, rbn_cx B X -> rbm_args X ->
  rbn_said B (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (rbn_SP X) (ri_sp0 X) (ri_said X) (ri_sd X).
Proof. intros X HX HA. unfold rbn_cx in HX. do 33 (destruct HX as [_ HX]). exact (proj1 (HX HA)). Qed.
Lemma rbn3s_env : forall X pos lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X -> rbn3_rel B X pos lyc1 Sc1 W1 memc1 mdc1 ->
  AR SEGS B (ri_lyc X) (ri_Sc X) (ri_W X) (ri_memc X) (ri_mdc X) /\
  AR SEGS B lyc1 Sc1 W1 memc1 mdc1 /\
  (forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p) /\
  ly_stk_lo lyc1 = ly_stk_lo (ri_ly X) /\ ly_stk_hi lyc1 = ly_stk_hi (ri_ly X) /\
  alloc_ceiling + REAC_BOX_NAME_STK <= rbn_SP X /\ rbn_SP X + 16 <= ri_sp0 X /\ ri_sp0 X mod 16 = 0 /\
  ly_stk_lo (ri_ly X) <= rbn_SP X - REAC_BOX_NAME_STK /\ ri_sp0 X <= ly_stk_hi (ri_ly X) /\
  ly_stk_hi (ri_ly X) <= 2 ^ 47 /\
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> ~ in_img SEGS a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 HX (HJ1 & Hfr1 & _ & _).
destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp & _).
destruct HJ as (HAR & L0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (H16 & _ & Hceil & Hslo & Hshi & H47 & _) & _).
destruct HJ1 as (HAR1 & L1 & _).
destruct L0 as (_ & _ & _ & _ & _ & F0 & _).
destruct L1 as (_ & _ & _ & _ & _ & F1 & _ & _ & _ & Elo & Ehi & _).
assert (FA : forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p)
  by (intros c p; unfold frame_addr; rewrite F0, F1; reflexivity).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfr1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4 & HFc & _).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
rewrite FA in HF4. rewrite FA, Hfb3 in HFc.
unfold rbn_F, rbn_SP.
split; [exact HAR|]. split; [exact HAR1|]. split; [exact FA|]. split; [exact Elo|]. split; [exact Ehi|].
split; [lia|]. split; [lia|]. split; [exact H16|]. split; [lia|]. split; [exact Hshi|]. split; [exact H47|].
split; [exact HF4|]. split; [exact HFc|].
intros a Ha. refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
split; [exact Hin3|]. rewrite FA, Hfb3. exact Ha.
Qed.
Lemma rbn3s_stk_sh : forall lyc Sc W mem md a n,
  AR SEGS B lyc Sc W mem md -> ly_stk_lo lyc <= a -> a + n <= ly_stk_hi lyc -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros lyc Sc W mem md a n HAR H1 H2 Hn.
pose proof (al_zshadow _ _ LAWS lyc Sc W mem md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR
  (or_introl eq_refl)) as HZ.
cbn [fst snd] in HZ. unfold zero_shadow in HZ.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & HPlo & HPhi & _).
unfold page_aligned in HPlo, HPhi.
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  destruct (rbn3s_stk_ar2 (ly_stk_lo lyc) (ly_stk_hi lyc) x HPlo HPhi ltac:(lia)) as (Ex & Rx).
  rewrite Ex. apply HZ. exact Rx.
- intros s Hs.
  destruct (rbn3s_stk_ar (ly_stk_lo lyc) (ly_stk_hi lyc) a n s HPlo HPhi H1 H2 Hn Hs) as (Es & Rs).
  rewrite Es. rewrite HZ by exact Rs. discriminate.
Qed.
Lemma rbn3s_sd_img : forall X pos lyc1 Sc1 W1 memc1 mdc1 a s q sz,
  rbn_cx B X -> rbn3_rel B X pos lyc1 Sc1 W1 memc1 mdc1 -> rbn_str (ri_W X) (ri_memc X) a s ->
  (forall x, a <= x < a + Z.of_nat (length s) + 1 ->
     in_img SEGS x /\ ~ Exists (in_zr x) (as_owned_static B) /\ ~ (as_errno B <= x < as_errno B + 4)) ->
  (forall x, a + Z.of_nat (length s) + 1 <= x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     seg_rom SEGS (Z_to_bv 64 x) <> None) ->
  rbn_ro q sz -> q <= a -> a + Z.of_nat (length s) + 1 <= q + sz ->
  rbn_str W1 memc1 a s /\
  (forall x, a <= x < a + Z.of_nat (length s) + 1 ->
     ~ (rbn_SP X - REAC_BOX_NAME_STK <= x < rbn_SP X) /\ ~ (rbn_F X pos <= x < rbn_F X pos + 512)).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 a s q sz HX HR Hs Hi Ht Hq H1 H2.
destruct (rbn3s_env X pos lyc1 Sc1 W1 memc1 mdc1 HX HR)
  as (_ & HAR1 & _ & _ & _ & Hc & _ & _ & _ & _ & _ & _ & _ & HFi).
destruct HR as (_ & _ & _ & (_ & _ & K3 & _)).
destruct (rbn3s_ge a (Z.of_nat (length s))) as [G1 G2].
destruct (rbn3s_globs q sz Hq) as [Q1 Q2].
pose proof asan_consts as (C1 & _).
split.
- apply (rbn3s_str_mv2 (ri_W X) W1 (ri_memc X) memc1 a s Hs).
  + intros x Hx. destruct (Hi x Hx) as (I1 & I2 & I3). exact (K3 x I1 I2 I3).
  + exact Ht.
  + exact (ro_usable_glob SEGS B tfib_globs lyc1 Sc1 W1 memc1 mdc1 q sz a (Z.of_nat (length s) + 1) GM Hq HAR1 H1
      ltac:(lia)).
  + apply (ro_hull SEGS B lyc1 Sc1 W1 memc1 mdc1 a _ HV HAR1); unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; lia.
- intros x Hx. destruct (Hi x ltac:(lia)) as (I1 & _ & _). split.
  + pose proof (pa_img_range x I1) as R. unfold YImgTop.IMG_TOP in R. lia.
  + intros HF. exact (HFi x HF I1).
Qed.
Lemma rbn3s_sd_blk : forall X pos lyc1 Sc1 W1 memc1 mdc1 a s b m,
  rbn_cx B X -> rbn3_rel B X pos lyc1 Sc1 W1 memc1 mdc1 -> rbn_str (ri_W X) (ri_memc X) a s ->
  In (b, m) (ablocks B (ri_lyc X) (ri_Sc X)) -> b <= a ->
  a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 <= b + req_size m ->
  rbn_str W1 memc1 a s /\
  (forall x, a <= x < a + Z.of_nat (length s) + 1 ->
     ~ (rbn_SP X - REAC_BOX_NAME_STK <= x < rbn_SP X) /\ ~ (rbn_F X pos <= x < rbn_F X pos + 512)).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 a s b m HX HR Hs Hb H1 H2.
destruct (rbn3s_env X pos lyc1 Sc1 W1 memc1 mdc1 HX HR)
  as (HAR & HAR1 & FA & _ & _ & Hc & _ & _ & _ & _ & _ & _ & _ & _).
destruct HR as (_ & Hfr1 & Hperm & (_ & K2 & _)).
assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1))
  by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & _ & Hbc & _).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfr1; left; reflexivity).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 3 pos HAR1 Hb1 Hin3) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite FA in Hd.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity. rewrite Hfb3 in Hd.
destruct (rbn3s_ge a (Z.of_nat (length s))) as [G1 G2].
split.
- apply (rbn3s_str_mv (ri_W X) W1 (ri_memc X) memc1 a s Hs).
  + intros x Hx. replace x with (b + (x - b)) by lia. apply (K2 b m (x - b) Hb); [lia | intros []].
  + exact (range_addressable_of_block SEGS B LAWS lyc1 Sc1 W1 memc1 mdc1 b m a (Z.of_nat (length s) + 1) HAR1 Hb1 H1
      ltac:(lia)).
  + exact (shadow_hull_vis_of_block SEGS B LAWS lyc1 Sc1 W1 memc1 mdc1 b m a (Z.of_nat (length s) + 1) HAR1 Hb1 H1
      ltac:(lia) ltac:(lia)).
- intros x Hx. unfold rbn_F. split; lia.
Qed.
Lemma rbn3s_sd_frm : forall X pos lyc1 Sc1 W1 memc1 mdc1 a s cid p,
  rbn_cx B X -> rbn3_rel B X pos lyc1 Sc1 W1 memc1 mdc1 -> rbn_str (ri_W X) (ri_memc X) a s ->
  In (cid, p) (frames (ri_Sc X)) -> frame_addr (ri_lyc X) cid p <= a ->
  a + Z.of_nat (length s) + 1 <= frame_addr (ri_lyc X) cid p + fs_frame_bytes cid ->
  rbn_str W1 memc1 a s /\
  (forall x, a <= x < a + Z.of_nat (length s) + 1 ->
     ~ (rbn_SP X - REAC_BOX_NAME_STK <= x < rbn_SP X) /\ ~ (rbn_F X pos <= x < rbn_F X pos + 512)).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 a s cid p HX HR Hs Hc H1 H2.
destruct (rbn3s_env X pos lyc1 Sc1 W1 memc1 mdc1 HX HR)
  as (HAR & HAR1 & FA & _ & _ & Hcl & _ & _ & _ & _ & _ & _ & _ & _).
destruct HR as (_ & Hfr1 & _ & (_ & _ & _ & K4 & _)).
destruct (frame_al64 SEGS B _ _ _ _ _ cid p HAR Hc) as (Hfal & Hbal & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR Hc) as (_ & Hfc & _).
assert (Hc1 : In (cid, p) (frames Sc1)) by (rewrite Hfr1; right; exact Hc).
assert (Hd : zdisjoint (frame_rng lyc1 (3, pos)) (frame_rng lyc1 (cid, p))).
{ pose proof Hc as Hc'. apply in_split in Hc' as (l2 & l3 & E).
  apply (sep_frames_pos SEGS B LAWS lyc1 Sc1 W1 memc1 mdc1 (3, pos) (cid, p) [] l2 l3 HAR1).
  rewrite Hfr1, E. reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !FA in Hd.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity. rewrite Hfb3 in Hd.
destruct (rbn3s_ge a (Z.of_nat (length s))) as [G1 G2].
pose proof (rbn3s_ge64 _ _ a (Z.of_nat (length s)) Hfal Hbal H2) as Hge.
pose proof Hs as (_ & _ & _ & _ & _ & _ & Hra & _).
split.
- apply (rbn3s_str_mv (ri_W X) W1 (ri_memc X) memc1 a s Hs).
  + intros x Hx. apply (K4 cid p x Hc); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | intros []].
  + apply (range_addressable_agree (aview SEGS (w_H (ri_W X)) (ri_memc X)) (aview SEGS (w_H W1) memc1)
      SHADOW_OFF a _); [|exact Hra].
    intros y Hy. apply (K4 cid p _ Hc); [right; apply rbn3s_frame_ar; [exact Hfal | exact Hbal | lia] | intros []].
  + apply (shadow_hull_vis_of_frame SEGS B LAWS lyc1 Sc1 W1 memc1 mdc1 cid p a _ HAR1 Hc1); rewrite ?FA; lia.
- intros x Hx. unfold rbn_F. split; lia.
Qed.
Lemma rbn3s_sd_stk : forall X pos lyc1 Sc1 W1 memc1 mdc1 a s,
  rbn_cx B X -> rbn3_rel B X pos lyc1 Sc1 W1 memc1 mdc1 -> rbn_str (ri_W X) (ri_memc X) a s ->
  rbn_SP X + 16 <= a -> a + Z.of_nat (length s) + 1 <= ri_sp0 X ->
  rbn_str W1 memc1 a s /\
  (forall x, a <= x < a + Z.of_nat (length s) + 1 ->
     ~ (rbn_SP X - REAC_BOX_NAME_STK <= x < rbn_SP X) /\ ~ (rbn_F X pos <= x < rbn_F X pos + 512)).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 a s HX HR Hs H1 H2.
destruct (rbn3s_env X pos lyc1 Sc1 W1 memc1 mdc1 HX HR)
  as (_ & HAR1 & _ & Elo & Ehi & Hc & Hsp & H16 & Hslo & Hshi & H47 & _ & HFc & _).
destruct HR as (_ & _ & _ & (K1 & _)).
destruct (rbn3s_ge a (Z.of_nat (length s))) as [G1 G2].
pose proof (rbn3s_ge16 _ a (Z.of_nat (length s)) H16 H2) as Hge.
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
destruct (rbn3s_stk_sh lyc1 Sc1 W1 memc1 mdc1 a (Z.of_nat (length s) + 1) HAR1 ltac:(lia) ltac:(lia) ltac:(lia))
  as [Sra Shv].
split.
- apply (rbn3s_str_mv (ri_W X) W1 (ri_memc X) memc1 a s Hs); [|exact Sra | exact Shv].
  intros x Hx. apply K1; [lia | lia | intros []].
- intros x Hx. split; lia.
Qed.
Lemma rbn3s_sd_stem : forall X pos lyc1 Sc1 W1 memc1 mdc1 t s sz,
  rbn_cx B X -> rbn3_rel B X pos lyc1 Sc1 W1 memc1 mdc1 -> rbn_stem B (ri_W X) (ri_memc X) t s ->
  rbn_ro t sz -> Z.of_nat (length s) + 1 <= sz ->
  rbn_str W1 memc1 t s /\
  (forall x, t <= x < t + Z.of_nat (length s) + 1 ->
     ~ (rbn_SP X - REAC_BOX_NAME_STK <= x < rbn_SP X) /\ ~ (rbn_F X pos <= x < rbn_F X pos + 512)).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 t s sz HX HR (Hs & Hi & Ht) Hq Hl.
exact (rbn3s_sd_img X pos lyc1 Sc1 W1 memc1 mdc1 t s t sz HX HR Hs Hi Ht Hq (Z.le_refl t) ltac:(lia)).
Qed.
Theorem rbn3s_said : rbn3_said_stmt B.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 HX HA Hne HR.
destruct (rbn3s_cx_said X HX HA) as [[E _] | (_ & Hs & Hloc)]; [exfalso; exact (Hne E)|].
destruct Hloc as [(b & m & Hb & H1 & H2) | [(cid & p & Hc & H1 & H2) | [(H1 & H2) | (q & sz & Hq & H1 & H2 & Hi & Ht)]]].
- exact (rbn3s_sd_blk X pos lyc1 Sc1 W1 memc1 mdc1 _ _ b m HX HR Hs Hb H1 H2).
- exact (rbn3s_sd_frm X pos lyc1 Sc1 W1 memc1 mdc1 _ _ cid p HX HR Hs Hc H1 H2).
- exact (rbn3s_sd_stk X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HR Hs H1 H2).
- exact (rbn3s_sd_img X pos lyc1 Sc1 W1 memc1 mdc1 _ _ q sz HX HR Hs Hi Ht Hq H1 H2).
Qed.
Theorem rbn3s_tab : rbn3_tab_stmt B.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 HX HA HR.
destruct (rbn3s_env X pos lyc1 Sc1 W1 memc1 mdc1 HX HR) as (_ & HAR1 & _).
destruct HR as (_ & _ & _ & (_ & _ & K3 & _)).
destruct (rbn3s_cx_img X HX) as (t1 & t2 & t3 & _ & Hii & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R26 & _).
assert (Hin : In (VAL (A_OBJ 26), 24) tfib_ro_ranges)
  by (unfold tfib_ro_ranges; apply in_or_app; left; exact R26).
pose proof (tfib_ro_unowned_at B _ _ DRO Hin) as HU.
split.
- exact (ro_usable_glob SEGS B tfib_globs lyc1 Sc1 W1 memc1 mdc1 (VAL (A_OBJ 26)) 24 (VAL (A_OBJ 26)) 24 GM R26 HAR1
    (Z.le_refl _) (Z.le_refl _)).
- intros j v Hj Hv. apply (val_mem_kept SEGS (w_H (ri_W X)) (w_H W1) (ri_memc X) memc1); [|exact Hv].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  destruct (HU (VAL (A_OBJ 26) + 8 * j + k) ltac:(lia)) as [U1 U2].
  apply K3; [apply Hii; lia | exact U1 | exact U2].
Qed.
Theorem rbn3s_stp : rbn3_stp_stmt B.
Proof.
intros X pos P lyc1 Sc1 W1 memc1 mdc1 HX HA HP HR.
unfold rbn_stp.
destruct HP as [(Hne & Hsd & ->) | (Hz & HT)].
- assert (E : rbm_stem X = ri_sd X).
  { unfold rbm_stem, bn_stem. destruct (ri_sd X) as [|c l] eqn:Ed; [congruence | reflexivity]. }
  rewrite E. exact (rbn3s_said X pos lyc1 Sc1 W1 memc1 mdc1 HX HA Hne HR).
- assert (Esd : ri_sd X = []).
  { destruct Hz as [Hz | Hz]; [|exact Hz].
    destruct (rbn3s_cx_said X HX HA) as [[_ E] | (Hne & _)]; [exact E | contradiction]. }
  assert (E : rbm_stem X = bn_STEM (ri_f X)) by (unfold rbm_stem, bn_stem; rewrite Esd; reflexivity).
  rewrite E.
  destruct (rbn3s_cx_img X HX)
    as (t1 & t2 & t3 & _ & _ & _ & V1 & V2 & V3 & S1 & S2 & S3 & S0 & _ & _ & _ & _ & R1 & R2 & R3 & R0 & _).
  destruct HT as [(Hf & HPr & HV1) | [(Hf & HPr & HV1) | [(Hf & HPr & HV1) | (Hf1 & Hf2 & Hf3 & ->)]]].
  + rewrite Hf.
    assert (Et : P = t1).
    { destruct (rbn3s_str_rng _ _ _ _ (proj1 S1)) as [Ra Rb].
      apply (rbn3s_vm8 SEGS (rbn3_mem0 X) (VAL (A_OBJ 26)) P t1 HV1 V1 HPr). lia. }
    subst P. exact (rbn3s_sd_stem X pos lyc1 Sc1 W1 memc1 mdc1 t1 _ 7 HX HR S1 R1 ltac:(cbn; lia)).
  + rewrite Hf.
    assert (Et : P = t2).
    { destruct (rbn3s_str_rng _ _ _ _ (proj1 S2)) as [Ra Rb].
      apply (rbn3s_vm8 SEGS (rbn3_mem0 X) (VAL (A_OBJ 26) + 8) P t2 HV1 V2 HPr). lia. }
    subst P. exact (rbn3s_sd_stem X pos lyc1 Sc1 W1 memc1 mdc1 t2 _ 7 HX HR S2 R2 ltac:(cbn; lia)).
  + rewrite Hf.
    assert (Et : P = t3).
    { destruct (rbn3s_str_rng _ _ _ _ (proj1 S3)) as [Ra Rb].
      apply (rbn3s_vm8 SEGS (rbn3_mem0 X) (VAL (A_OBJ 26) + 16) P t3 HV1 V3 HPr). lia. }
    subst P. exact (rbn3s_sd_stem X pos lyc1 Sc1 W1 memc1 mdc1 t3 _ 8 HX HR S3 R3 ltac:(cbn; lia)).
  + assert (E0 : bn_STEM (ri_f X) = bn_STEM 0).
    { unfold bn_STEM. rewrite (proj2 (Z.eqb_neq _ _) Hf1), (proj2 (Z.eqb_neq _ _) Hf2),
        (proj2 (Z.eqb_neq _ _) Hf3). reflexivity. }
    rewrite E0. exact (rbn3s_sd_stem X pos lyc1 Sc1 W1 memc1 mdc1 _ _ 5 HX HR S0 R0 ltac:(cbn; lia)).
Qed.
End h.
End f.
End d.
