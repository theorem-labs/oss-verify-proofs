(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg7.v, with its module paths, module names and numbers changed; 414 of its 541 lines of code are new or changed and 964 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
SbCh SbDec ReacBoxName ReacBoxNameCut ReacBoxNameLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma rbn_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma rbn_keep_get : forall (regs regs2 : bvmap 5 word) cl (r : bv 5),
  rbn_keep_regs regs regs2 cl -> existsb (Z.eqb (bv_unsigned r)) cl = false -> getr regs2 r = getr regs r.
Proof.
intros regs regs2 cl r HK Hb.
pose proof (u5_range r) as Hr.
assert (Hn : ~ In (bv_unsigned r) cl).
{ intros Hin. assert (E : existsb (Z.eqb (bv_unsigned r)) cl = true)
    by (apply existsb_exists; exists (bv_unsigned r); split; [exact Hin | apply Z.eqb_refl]).
  rewrite E in Hb. discriminate. }
pose proof (HK _ Hr Hn) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma rbn_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
  kLowShadowBeg <= shadow_addr x + j < kHighMemBeg.
Proof.
intros x n j H1 H2 H3 H4.
pose proof (shadow_range_end x n H2) as E1.
pose proof (shadow_mono (x + n) alloc_ceiling H3) as E2.
pose proof (shadow_mono 4096 x H1) as E3.
pose proof asan_consts as (C1 & _).
assert (E4 : alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia).
assert (E5 : shadow_addr 4096 = SHADOW_OFF + 512) by reflexivity.
assert (E6 : shadow_addr alloc_ceiling = SHADOW_OFF + alloc_ceiling / 8) by reflexivity.
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma rbn_amem_shadow : forall x a n, amem_range a n -> 0 <= a -> a <= x < a + n ->
  SHADOW_OFF <= shadow_addr x /\ shadow_addr x + 1 <= kHighMemBeg.
Proof.
intros x a n Ham Ha Hx. unfold shadow_addr.
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.
Lemma rbn_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
Lemma rbn_cells_app : forall (m : word -> option byte) l1 l2,
  rbn_cells m (l1 ++ l2) <-> rbn_cells m l1 /\ rbn_cells m l2.
Proof.
intros m l1 l2. induction l1 as [|[[a n] v] t IH]; cbn [app rbn_cells]; [tauto|]. rewrite IH. tauto.
Qed.
Lemma rbn_argc_rng : forall X a n v, In (a, n, v) (rbn_argc X) ->
  rbn_A X <= a /\ a + Z.of_nat n <= rbn_A X + 64.
Proof.
intros X a n v H. unfold rbn_argc in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn_rw_rng : forall X pos n0 ov0 a n v, In (a, n, v) (rbn_rw X pos n0 ov0) ->
  rbn_A X + 184 <= a /\ a + Z.of_nat n <= rbn_A X + 212.
Proof.
intros X pos n0 ov0 a n v H. unfold rbn_rw in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn_w4_len : forall X, rbm_args X -> length (rbm_w4 X) = 4%nat.
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
exact (bn_w4_length _ _ Hi Ho).
Qed.
Lemma rbn_stem_ne : forall X, rbm_stem X <> [].
Proof.
intros X. unfold rbm_stem, bn_stem. destruct (ri_sd X) as [|c l]; [|discriminate].
unfold bn_STEM. destruct (ri_f X =? 1); [discriminate|]. destruct (ri_f X =? 2); [discriminate|].
destruct (ri_f X =? 3); discriminate.
Qed.
Lemma rbn_P_sep : forall X pos P,
  (forall a, P <= a < P + Z.of_nat (length (rbm_stem X)) + 1 ->
     ~ (rbn_SP X - REAC_BOX_NAME_STK <= a < rbn_SP X) /\ ~ (rbn_F X pos <= a < rbn_F X pos + 512)) ->
  (P + Z.of_nat (length (rbm_stem X)) + 1 <= rbn_F X pos \/ rbn_F X pos + 512 <= P) /\
  (P + Z.of_nat (length (rbm_stem X)) + 1 <= rbn_SP X - 8816 \/ rbn_SP X <= P).
Proof.
intros X pos P Hdis.
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
split.
- destruct (Z_lt_le_dec P (rbn_F X pos)) as [Hlt | Hge].
  + left. destruct (Z_lt_le_dec (P + Z.of_nat (length (rbm_stem X))) (rbn_F X pos)) as [Hl | Hl]; [lia|].
    exfalso. apply (proj2 (Hdis (rbn_F X pos) ltac:(lia))). lia.
  + right. destruct (Z_lt_le_dec P (rbn_F X pos + 512)) as [Hl | Hl]; [|lia].
    exfalso. apply (proj2 (Hdis P ltac:(lia))). lia.
- destruct (Z_lt_le_dec P (rbn_SP X - 8816)) as [Hlt | Hge].
  + left. destruct (Z_lt_le_dec (P + Z.of_nat (length (rbm_stem X))) (rbn_SP X - 8816)) as [Hl | Hl]; [lia|].
    exfalso. apply (proj1 (Hdis (rbn_SP X - 8816) ltac:(lia))). lia.
  + right. destruct (Z_lt_le_dec P (rbn_SP X)) as [Hl | Hl]; [|lia].
    exfalso. apply (proj1 (Hdis P ltac:(lia))). lia.
Qed.
Lemma rbn_str_kept : forall (W W' : world SEGS) (m m' : word -> option byte) a s,
  rbn_str W m a s ->
  (forall x, 0 <= x < 2 ^ 64 ->
     a <= x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 \/ kLowShadowBeg <= x < kHighMemBeg ->
     aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  rbn_str W' m' a s.
Proof.
intros W W' m m' a s (Hf & Hg & Ha0 & Ha1 & Hl & Ham & Hra & Hhv & Htl) HE.
pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)) as M1.
assert (Hsb : forall x, a <= x < a + Z.of_nat (length s) + 1 ->
  SHADOW_OFF <= shadow_addr x /\ shadow_addr x + 1 <= kHighMemBeg)
  by (intros x Hx; exact (rbn_amem_shadow x a _ Ham ltac:(lia) ltac:(lia))).
assert (Hband : forall y, SHADOW_OFF <= y < kHighMemBeg -> aview SEGS (w_H W') m' y = aview SEGS (w_H W) m y).
{ intros y Hy. apply HE; [unfold SHADOW_OFF, kHighMemBeg in Hy; lia|].
  right. unfold kLowShadowBeg, SHADOW_OFF in *. lia. }
split; [exact Hf|]. split.
{ apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact Hg|]. intros x Hx.
  rewrite length_app in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HE; [lia|]. left. lia. }
split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Hl|]. split; [exact Ham|]. split.
{ intros x Hx. destruct (Hra x Hx) as (sv & Hs & Hok). exists sv. split; [|exact Hok].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hs |- *.
  destruct (Hsb x ltac:(lia)) as [S1 S2]. rewrite (Hband (shadow_addr x) ltac:(lia)). exact Hs. }
split.
{ intros sx Hsx. destruct (Hsb a ltac:(lia)) as [S1 _].
  destruct (Hsb (a + Z.of_nat (length s)) ltac:(lia)) as [_ S2].
  replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) in Hsx by lia.
  rewrite (Hband sx).
  - apply Hhv. replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) by lia. exact Hsx.
  - unfold SHADOW_OFF, kHighMemBeg in *. lia. }
intros x Hx. rewrite (HE x); [exact (Htl x Hx) | lia | left; lia].
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma rbn_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM c p.
destruct HX as ((_ & L0 & _) & _). destruct HM as ((_ & L1 & _) & _).
destruct L0 as (_ & _ & _ & _ & _ & F0 & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F0, F1. reflexivity.
Qed.
Lemma rbn_stk_eq : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  ly_stk_lo lyc1 = ly_stk_lo (ri_ly X) /\ ly_stk_hi lyc1 = ly_stk_hi (ri_ly X).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM.
destruct HM as ((_ & L1 & _) & _).
destruct L1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _). split; assumption.
Qed.
Lemma rbn_A_rng : forall X, rbn_cx B X ->
  alloc_ceiling + 8816 <= rbn_SP X /\ rbn_SP X - 351 <= rbn_A X /\ rbn_A X + 320 <= rbn_SP X /\
  rbn_A X mod 32 = 0 /\ rbn_SP X + 16 <= 2 ^ 47 /\
  ri_sp0 X - ri_STK X <= rbn_SP X - 8816 /\ rbn_SP X + 16 <= ri_sp0 X /\
  ly_stk_lo (ri_ly X) + ri_STK X <= ri_sp0 X /\ ri_sp0 X <= ly_stk_hi (ri_ly X) /\ rbn_SP X mod 16 = 0.
Proof.
intros X HX. destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & Hal & Hstk & Hsp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
rewrite WS in Hstk. unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 320) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 320) 32 ltac:(lia)) as M1.
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
repeat split; lia.
Qed.
Lemma rbn_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) memc1 a /\ ~ in_img SEGS a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
pose proof (rbn_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM 3 pos) as FA.
destruct HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (Hal & Happ & Hpr & _).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
unfold rbn_F. rewrite <- FA. rewrite Hfb3 in *.
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact Hal|]. split; [exact Happ|].
intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
split; [exact Hin3|]. rewrite Hfb3. exact Ha.
Qed.
Lemma rbn_F_img : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh a,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  rbn_F X pos <= a < rbn_F X pos + 512 -> a < YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh a HX HM Ha.
pose proof (rbn_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM 3 pos) as FA.
destruct HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
pose proof HAR1 as (_ & LG & _). destruct (pa_img_cover lyc1 Sc1 mdc1 LG) as [C1 C2].
assert (Hz : ~ in_zr a (ly_img lyc1)).
{ refine (proj1 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
  split; [exact Hin3|]. rewrite FA. change (fs_frame_bytes 3) with 512. exact Ha. }
unfold in_zr in Hz. lia.
Qed.
Lemma rbn_stk_shadow : forall lyc Sc W mem md a n,
  AR SEGS B lyc Sc W mem md ->
  ly_stk_lo lyc + 64 <= a -> a + n + 64 <= ly_stk_hi lyc -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros lyc Sc W mem md a n HAR H1 H2 Hn.
pose proof (al_zshadow _ _ LAWS lyc Sc W mem md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR
  (or_introl eq_refl)) as HZ.
cbn [fst snd] in HZ.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & HPlo & HPhi & _).
unfold page_aligned in HPlo, HPhi.
assert (Hz : forall x, ly_stk_lo lyc <= x < ly_stk_hi lyc -> aview SEGS (w_H W) mem (shadow_addr x) = Some 0).
{ intros x Hx.
  pose proof (HZ (x / 8 - ly_stk_lo lyc / 8) ltac:(lia)) as E.
  unfold shadow_of_addr in E. unfold shadow_addr.
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + ly_stk_lo lyc / 8 + (x / 8 - ly_stk_lo lyc / 8)) by lia.
  exact E. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). apply Hz. lia.
- intros s Hs.
  assert (Hx : shadow_addr (8 * (s - SHADOW_OFF)) = s) by (unfold shadow_addr; lia).
  rewrite <- Hx. rewrite Hz; [discriminate|]. unfold shadow_addr in Hs. lia.
Qed.
Lemma rbn_mid_fw : forall X pos lyc1 Sc1 W1 memc1 mdc1 lyc2 Sc2 W2 mem2 md2 sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 mem2 md2 (ri_k X) ->
  frames Sc2 = frames Sc1 -> ablocks B lyc2 Sc2 = ablocks B lyc1 Sc1 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2) ->
  Z.of_nat (length sh) <= 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - TSB_CH_STK <= a < rbn_A X) -> ~ (rbn_A X + 168 <= a < rbn_A X + 180) ->
     ~ (rbn_F X pos + 64 <= a < rbn_F X pos + 88) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_A X - TSB_CH_STK <= a < rbn_A X) ->
     apresent (w_H W1) memc1 a -> apresent (w_H W2) mem2 a) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  rbn_mid B X pos lyc2 Sc2 W2 mem2 md2 (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 lyc2 Sc2 W2 mem2 md2 sh HX HM HJ2 Hfr2 Hab2 Hro2 Hsh HEQ HPR HIMG.
pose proof (rbn_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HX HM) as FA.
destruct (rbn_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (HE : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_SP X - 8816 <= a < rbn_SP X) ->
  ~ (rbn_F X pos <= a < rbn_F X pos + 512) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc1 a)
  by (intros a Ha H1 H2; apply HEQ; lia).
assert (Happ : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> a < kLowShadowBeg \/ kHighMemBeg <= a).
{ intros a Ha. unfold in_app in HFapp. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & HK & Hfr & Hfl & Hsh0).
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
unfold rbn_mid. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|].
split; [rewrite Hab2; exact Hperm|]. split; [exact Hro2|].
split.
{ destruct HK as (K1 & K2 & K3 & K4 & K5 & K6). unfold rbn_kept.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn' He. rewrite (HE a) by lia. exact (K1 a Ha Hn' He).
  - intros b m j Hb Hj He.
    assert (Hb1 : In (b, m) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb1) as (_ & Hb4 & Hbc & _).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b m 3 pos HAR1 Hb1 Hin3) as Hd.
    rewrite FA3, Hfb3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    rewrite (HE (b + j)) by lia. exact (K2 b m j Hb Hj He).
  - intros a Hia Ho He. rewrite (HIMG a Hia Ho He). exact (K3 a Hia Ho He).
  - intros cid p a Hcp Ha He.
    assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hc4096 & Hcceil & _).
    rewrite FA in Hc4096, Hcceil.
    pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
    destruct Ha as [Ha | Ha].
    + destruct (in_split _ _ Hcp) as (l2 & l3 & El).
      pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
        ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite FA3, Hfb3, FA in Hd.
      unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha.
      rewrite (HE a) by lia. exact (K4 cid p a Hcp (or_introl Ha) He).
    + unfold in_zr in Ha. cbn [fst snd] in Ha.
      pose proof (rbn_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
        (a - shadow_addr (frame_addr (ri_lyc X) cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
      rewrite (HE a) by (unfold kLowShadowBeg, kHighMemBeg in *; first [lia | intros Hf; destruct (Happ a Hf); lia]).
      exact (K4 cid p a Hcp (or_intror Ha) He).
  - intros a Ha Hn' Hp. apply HPR; [lia | lia | exact (K5 a Ha Hn' Hp)].
  - intros a Ha. apply Hpres2. lia. }
split.
{ unfold rbn_frame. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W2) memc1 mem2); [|exact (Hfr j r Hj)].
  intros k Hk. apply HEQ; lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) memc1 mem2); [|exact Hfl].
  intros k Hk. apply HEQ; lia. }
unfold rbn_shadow_at. intros j Hj.
pose proof (rbn_sh_band (rbn_F X pos) 512 j HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as Hb.
unfold rbn_SH.
rewrite (HE (shadow_addr (rbn_F X pos) + j))
  by (unfold kLowShadowBeg, kHighMemBeg in *; first [lia | intros Hf; destruct (Happ _ Hf); lia]).
exact (Hsh0 j Hj).
Qed.
Lemma rbn_lbuf_name : forall X pos lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true false false) ->
  rbn_lbuf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1
    (rbn_A X) (rbn_A X + 152) (rbn_F X pos + 64) 24.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 HX HM.
pose proof (rbn_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM 3 pos) as FA.
destruct (rbn_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh0).
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HFal, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
pose proof (rbn_F_img X pos lyc1 Sc1 W1 memc1 mdc1 _ _ (rbn_F X pos + 64) HX HM ltac:(lia)) as I1.
pose proof (rbn_F_img X pos lyc1 Sc1 W1 memc1 mdc1 _ _ (rbn_F X pos + 87) HX HM ltac:(lia)) as I2.
unfold rbn_lbuf.
split; [lia|]. split; [lia|]. split; [apply (in_app_sub _ _ _ _ HFapp); lia|].
split; [unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia|].
split; [unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia|].
split; [right; lia|]. split; [left; lia|].
split.
{ apply zero_shadow_range; [lia | reflexivity |].
  intros i Hi. change (24 / 8) with 3 in Hi.
  replace (shadow_of_addr SHADOW_OFF (rbn_F X pos + 64) + i) with (rbn_SH X pos + (8 + i))
    by (unfold rbn_SH, shadow_addr, shadow_of_addr; lia).
  rewrite (Hsh0 (8 + i)) by (rewrite rbn_sh_len; lia).
  assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia; reflexivity. }
split.
{ intros sx Hsx.
  assert (Hj : 0 <= sx - rbn_SH X pos < 64) by (unfold rbn_SH, shadow_addr in *; lia).
  pose proof (Hsh0 (sx - rbn_SH X pos) ltac:(rewrite rbn_sh_len; lia)) as E.
  replace (rbn_SH X pos + (sx - rbn_SH X pos)) with sx in E by lia. rewrite E. discriminate. }
intros a Ha. split; [|exact (proj1 (HFpr a ltac:(lia)))].
right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
unfold in_zr. cbn [fst snd]. rewrite FA. change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos).
change (fs_frame_bytes 3) with 512. lia.
Qed.
Lemma rbn4_post : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P lyc2 Sc2 W2 regs2 mem2 md2,
  rbn_cx B X -> rbn_st4 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 mem2 md2 (ri_k X) ->
  frames Sc2 = frames Sc1 -> ablocks B lyc2 Sc2 = ablocks B lyc1 Sc1 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2) ->
  rbn_keep_regs regs1 regs2 rbn_cl1 ->
  val_mem SEGS (mrestrict (w_H W2) mem2) (rbn_A X + 152 + 16) 8 (Z.of_nat (length (firstn 23 (rbm_stem X)))) ->
  val_mem SEGS (mrestrict (w_H W2) mem2) (rbn_A X + 152 + 24) 4 (rbm_ovf 23 (rbm_stem X)) ->
  garr8 SEGS (mrestrict (w_H W2) mem2) (rbn_F X pos + 64) (firstn 23 (rbm_stem X)) ->
  tsb_ch_kept B lyc1 Sc1 W1 memc1 W2 mem2 (rbn_A X)
    (fun a => rbn_A X + 152 + 16 <= a < rbn_A X + 152 + 28 \/
       rbn_F X pos + 64 <= a < rbn_F X pos + 64 + Z.of_nat (length (firstn 23 (rbm_stem X)))) ->
  rbn_st5 B X pos regs2 lyc2 Sc2 W2 mem2 md2 P.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P lyc2 Sc2 W2 regs2 mem2 md2 HX H4 HJ2 Hfr2 Hab2 Hro2 HK O24 O30 HG HT.
destruct H4 as (HM & HRB & R18 & R20 & R27 & R25 & R21 & R26 & R24 & R10 & HC & HW4 & HSTP & HA).
destruct (rbn_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (Hl23 : Z.of_nat (length (firstn 23 (rbm_stem X))) <= 23)
  by (pose proof (firstn_le_length 23 (rbm_stem X)); lia).
destruct HT as (T1 & T2 & T3 & T4 & T5 & T6).
assert (HEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - TSB_CH_STK <= a < rbn_A X) ->
  ~ (rbn_A X + 168 <= a < rbn_A X + 180) -> ~ (rbn_F X pos + 64 <= a < rbn_F X pos + 88) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha H1 H2 H3. apply T1; [exact Ha | exact H1 |]. cbv beta. intros [E | E]; lia. }
assert (HE : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_SP X - 8816 <= a < rbn_SP X) ->
  ~ (rbn_F X pos <= a < rbn_F X pos + 512) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc1 a)
  by (intros a Ha H1 H2; apply HEQ; lia).
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HFal, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
assert (Happ : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> a < kLowShadowBeg \/ kHighMemBeg <= a).
{ intros a Ha. unfold in_app in HFapp. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
pose proof (rbn_w4_len X HA) as Hw4.
assert (KG : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) rbn_cl1 = false -> getr regs2 r = getr regs1 r)
  by (intros r Hr; exact (rbn_keep_get regs1 regs2 _ r HK Hr)).
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
unfold rbn_st5. split.
{ apply (rbn_mid_fw X pos lyc1 Sc1 W1 memc1 mdc1 lyc2 Sc2 W2 mem2 md2 _ HX HM HJ2 Hfr2 Hab2 Hro2);
  [rewrite rbn_sh_len; lia | exact HEQ | exact T5 | exact T3]. }
split.
{ unfold rbn_rbase.
  split; [rewrite KG by reflexivity; exact B2|]. split; [rewrite KG by reflexivity; exact B3|].
  split; [rewrite KG by reflexivity; exact B4|]. split; [rewrite KG by reflexivity; exact B8|].
  split; [rewrite KG by reflexivity; exact B9|]. split; [rewrite KG by reflexivity; exact B19|].
  split; [rewrite KG by reflexivity; exact B22|]. rewrite KG by reflexivity; exact B23. }
split; [rewrite KG by reflexivity; exact R18|]. split; [rewrite KG by reflexivity; exact R20|].
split; [rewrite KG by reflexivity; exact R27|]. split; [rewrite KG by reflexivity; exact R25|].
split.
{ apply rbn_cells_app in HC as [HCa HCr]. apply rbn_cells_app in HCr as [HCw HCn].
  apply rbn_cells_app. split.
  { apply (rbn_cells_kept (w_H W1) (w_H W2) memc1 mem2); [|exact HCa].
    intros a n v k Hin Hk. pose proof (rbn_argc_rng X a n v Hin). apply HEQ; lia. }
  apply rbn_cells_app. split.
  { apply (rbn_cells_kept (w_H W1) (w_H W2) memc1 mem2); [|exact HCw].
    intros a n v k Hin Hk. pose proof (rbn_rw_rng X pos 4 0 a n v Hin). apply HEQ; lia. }
  unfold rbn_rn in HCn |- *. cbn [rbn_cells] in HCn |- *.
  destruct HCn as (N0 & N8 & _ & _ & _).
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memc1 mem2); [intros k Hk; apply HEQ; lia | exact N0]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) memc1 mem2); [intros k Hk; apply HEQ; lia | exact N8]|].
  split; [replace (rbn_A X + 168) with (rbn_A X + 152 + 16) by lia; exact O24|].
  split; [replace (rbn_A X + 176) with (rbn_A X + 152 + 24) by lia; exact O30|].
  exact I. }
split.
{ apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HW4|]. intros x Hx.
  rewrite length_app, Hw4 in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HEQ; lia. }
split; [exact HG|].
split; [|exact HA].
unfold rbn_stp in HSTP |- *. destruct HSTP as [Hstr Hdis]. split; [|exact Hdis].
destruct (rbn_P_sep X pos P Hdis) as [HsepF HsepS].
apply (rbn_str_kept W1 W2 memc1 mem2 P (rbm_stem X) Hstr).
intros x Hx Hr. apply HE; [exact Hx | |].
- destruct Hr as [Hr | Hr]; [lia|]. unfold kLowShadowBeg, kHighMemBeg in *. lia.
- destruct Hr as [Hr | Hr]; [lia|]. intros Hf. destruct (Happ x Hf); lia.
Qed.
Hypothesis L1F : rbn_L1_fits B.
Hypothesis L1O : rbn_L1_ovf B.
Theorem rbn_seg4 : rbn_seg4_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX H4.
pose proof H4 as (HM & HRB & R18 & R20 & R27 & R25 & R21 & R26 & R24 & R10 & HC & HW4 & HSTP & HA).
destruct (rbn_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
destruct (rbn_stk_eq X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as [Elo Ehi].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
pose proof HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
assert (Hsp : spZ regs1 = rbn_A X) by (unfold spZ; rewrite B2; unfold w64; apply unsigned_lit_small; lia).
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & _).
pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPst & _).
unfold rbn_stp in HSTP. destruct HSTP as [Hstr Hdis].
destruct (rbn_P_sep X pos P Hdis) as [HsepF HsepS].
unfold rbn_str in Hstr. destruct Hstr as (Hfs & Hgs & HP0 & HP1 & HPl & Ham & HPra & HPhv & HPtl).
apply rbn_cells_app in HC as [_ HCr]. apply rbn_cells_app in HCr as [_ HCn].
unfold rbn_rn in HCn. cbn [rbn_cells] in HCn. destruct HCn as (N0 & N8 & N16 & N24 & _).
pose proof (rbn_stem_ne X) as Hne.
pose proof (rbn_lbuf_name X pos lyc1 Sc1 W1 memc1 mdc1 HX HM) as Hbuf. rewrite <- Hsp in Hbuf.
set (s := rbm_stem X) in *.
assert (Hsrc : rbn_lsrc W1 memc1 P (s ++ [0])).
{ split; [exact Hgs|]. split; [lia|]. rewrite length_app. cbn [length].
  replace (Z.of_nat (length s + 1)) with (Z.of_nat (length s) + 1) by lia. split; [lia|].
  split; [unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in Ham; lia|]. exact HPra. }
assert (Hrec : rbn_lrec B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1
  memc1 (spZ regs1) (spZ regs1 + 152) (rbn_F X pos + 64) 24 0 0).
{ rewrite Hsp. unfold rbn_lrec.
  destruct (rbn_stk_shadow lyc1 Sc1 W1 memc1 mdc1 (rbn_A X + 152) 28 HAR1 ltac:(lia) ltac:(lia) ltac:(lia))
    as [Hra Hhv].
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold amem_range, kHighMemBeg, kHighMemEnd; lia|].
  split; [unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP; lia|].
  split; [left; lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact N0|].
  split; [replace (rbn_A X + 152 + 8) with (rbn_A X + 160) by lia; exact N8|].
  split; [replace (rbn_A X + 152 + 16) with (rbn_A X + 168) by lia; exact N16|].
  split; [replace (rbn_A X + 152 + 24) with (rbn_A X + 176) by lia; exact N24|].
  split; [exact Hra|]. split; [exact Hhv|].
  intros a Ha. split; [left; lia | apply HPst; lia]. }
assert (Hsep : rbn_lsep (spZ regs1) (spZ regs1 + 152) (rbn_F X pos + 64) 24 P (Z.of_nat (length s) + 1)).
{ rewrite Hsp. unfold rbn_lsep. rewrite HTS. lia. }
assert (Hlcx : rbn_lcx B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
  ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 mdc1 (ri_k X) regs1).
{ unfold rbn_lcx. split; [exact HJ1|]. split; [exact Hro|]. split; [exact B3|]. split; [exact B4|].
  split; [rewrite B9, B2; reflexivity|]. split; [exact B22|]. rewrite Hsp, HTS.
  split; [lia|]. split; lia. }
unfold rbn_cfg. change RBN_P4 with RBN_L1.
assert (POST : forall nF ovF wr W2 c2,
  rbn_lpost B (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 (ri_k X) regs1 RBN_L1X rbn_cl1
    (spZ regs1 + 152) (rbn_F X pos + 64) 0 nF ovF wr W2 c2 ->
  nF = Z.of_nat (length (firstn 23 s)) -> ovF = rbm_ovf 23 s -> wr = firstn 23 s -> rbn_at5 B X W2 c2).
{ intros nF ovF wr W2 c2 (lyc2 & Sc2 & regs2 & mem2 & md2 & -> & HJ2 & Hfr2 & Hab2 & Hro2 & HK & O24 & O30 & HG & HT)
    -> -> ->.
  rewrite Hsp in O24, O30, HT. rewrite Z.add_0_r in HG, HT.
  exists pos, regs2, lyc2, Sc2, mem2, md2, P. split; [reflexivity|].
  exact (rbn4_post X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P lyc2 Sc2 W2 regs2 mem2 md2 HX H4 HJ2 Hfr2 Hab2 Hro2 HK
    O24 O30 HG HT). }
destruct (Z_le_gt_dec (Z.of_nat (length s)) 23) as [Hf | Ho].
- pose proof (L1F (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 mdc1 (ri_k X) regs1 P (rbn_F X pos + 64) 0 0 s ltac:(lia)) as RUN.
  unfold rbn_L1_run in RUN.
  eapply SRr_mono; [apply RUN; first [exact Hlcx | exact Hrec | exact Hbuf | exact Hne | exact Hfs | exact Hsrc
    | exact Hsep | lia | left; reflexivity | assumption] |].
  intros W2 c2 _ Hp. apply (POST _ _ _ _ _ Hp).
  + rewrite firstn_all2 by lia. lia.
  + unfold rbm_ovf. replace (23 <? Z.of_nat (length s)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  + rewrite firstn_all2 by lia. reflexivity.
- pose proof (L1O (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1 mdc1 (ri_k X) regs1 P (rbn_F X pos + 64) 0 0 s ltac:(lia)) as RUN.
  unfold rbn_L1_run in RUN.
  eapply SRr_mono; [apply RUN; first [exact Hlcx | exact Hrec | exact Hbuf | exact Hne | exact Hfs | exact Hsrc
    | exact Hsep | lia | left; reflexivity | assumption] |].
  intros W2 c2 _ Hp. apply (POST _ _ _ _ _ Hp).
  + rewrite firstn_length_le by lia. lia.
  + unfold rbm_ovf. replace (23 <? Z.of_nat (length s)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  + reflexivity.
Qed.
End h.
End f.
End d.
