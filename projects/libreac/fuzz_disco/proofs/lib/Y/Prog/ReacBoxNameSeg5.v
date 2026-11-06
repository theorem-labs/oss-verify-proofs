(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg7.v, with its module paths, module names and numbers changed; 2457 of its 2624 lines of code are new or changed and 924 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q YG0s YC1g YC4b YC44 YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YXcalls YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef StrlenDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import SbCh SbDec ReacBoxName ReacBoxNameCut ReacBoxNameLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma rbn5_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma rbn5_sh_nb : forall a c d j, 8 <= j < 11 -> nth (Z.to_nat j) (rbn_sh a true c d) 0 = 0.
Proof.
intros a c d j Hj. assert (j = 8 \/ j = 9 \/ j = 10) as [-> | [-> | ->]] by lia; destruct a, c, d; reflexivity.
Qed.
Lemma rbn5_sh_w4 : forall b c d, nth 4 (rbn_sh true b c d) 0 = 5.
Proof. intros b c d. destruct b, c, d; reflexivity. Qed.
Lemma rbn5_sh_tb : forall j, 0 <= j < 64 -> ~ (16 <= j < 19) ->
  nth (Z.to_nat j) (rbn_sh true true true false) 0 = nth (Z.to_nat j) (rbn_sh true true false false) 0.
Proof.
intros j Hj Hn.
assert (E : forall k, (k < 64)%nat -> ~ (16 <= k < 19)%nat ->
  nth k (rbn_sh true true true false) 0 = nth k (rbn_sh true true false false) 0).
{ intros k Hk Hk2. do 64 (destruct k as [|k]; [first [reflexivity | lia]|]). lia. }
apply E; lia.
Qed.
Lemma rbn5_sh_tb3 : forall j, 16 <= j < 19 -> nth (Z.to_nat j) (rbn_sh true true true false) 0 = 0.
Proof. intros j Hj. assert (j = 16 \/ j = 17 \/ j = 18) as [-> | [-> | ->]] by lia; reflexivity. Qed.
Lemma rbn5_le1 : forall v, 0 <= v < 256 -> YO0f.le_byte v 1 0 = v.
Proof.
intros v Hv. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma rbn5_d64 : forall x, x mod 64 = 0 -> x / 8 = 8 * (x / 64) /\ x = 64 * (x / 64).
Proof.
intros x Hx. pose proof (Z.div_mod x 64 ltac:(lia)) as D. rewrite Hx, Z.add_0_r in D.
split; [|exact D]. rewrite D at 1. replace (64 * (x / 64)) with (8 * (x / 64) * 8) by lia.
rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma rbn5_keep_get : forall (regs regs2 : bvmap 5 word) cl (r : bv 5),
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
Lemma rbn5_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
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
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma rbn5_w4_len : forall X, rbm_args X -> length (rbm_w4 X) = 4%nat.
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
exact (bn_w4_length _ _ Hi Ho).
Qed.
Lemma rbn5_w4_digits : forall X, rbm_args X -> Forall (fun c => 0 < c < 256) (rbm_w4 X).
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
apply bn_ok_in in Hi. apply bn_ok_in in Ho. unfold rbm_w4.
assert (A : forallb (fun i => forallb (fun o => forallb (fun c => (0 <? c) && (c <? 256)) (bn_w4 i o)) bn_oks) bn_oks = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A _ Hi). rewrite forallb_forall in A. specialize (A _ Ho).
rewrite forallb_forall in A. apply Forall_forall. intros c Hc. specialize (A c Hc).
apply andb_prop in A as [A1 A2]. apply Z.ltb_lt in A1. apply Z.ltb_lt in A2. lia.
Qed.
Lemma rbn5_stem_ne : forall X, rbm_stem X <> [].
Proof.
intros X. unfold rbm_stem, bn_stem. destruct (ri_sd X) as [|c l]; [|discriminate].
unfold bn_STEM. destruct (ri_f X =? 1); [discriminate|]. destruct (ri_f X =? 2); [discriminate|].
destruct (ri_f X =? 3); discriminate.
Qed.
Lemma rbn5_NM_cases : forall X,
  (4 <= Z.of_nat (length (rbm_stem X)) /\ skipn (length (rbm_stem X) - 4) (rbm_stem X) = rbm_w4 X /\
   rbm_NM X = rbm_stem X) \/
  (~ (4 <= Z.of_nat (length (rbm_stem X)) /\ skipn (length (rbm_stem X) - 4) (rbm_stem X) = rbm_w4 X) /\
   rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X).
Proof.
intros X. unfold rbm_NM, bn_NM, rbm_stem, rbm_w4. cbv zeta.
set (s := bn_stem (ri_f X) (ri_sd X)). set (w := bn_w4 (ri_i X) (ri_o X)).
assert (Hleq : forall a b, bn_leq a b = true <-> a = b).
{ induction a as [|x a IH]; intros [|y b]; cbn [bn_leq]; split; intros H; try discriminate; try reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst. reflexivity.
  - injection H as <- <-. rewrite Z.eqb_refl. cbn. apply IH. reflexivity. }
destruct (4 <=? Z.of_nat (length s)) eqn:H4; destruct (bn_leq (skipn (length s - 4) s) w) eqn:Hl; cbn [andb].
- left. apply Z.leb_le in H4. apply Hleq in Hl. auto.
- right. split; [|reflexivity]. intros [_ He]. apply Hleq in He. congruence.
- right. split; [|reflexivity]. intros [He _]. apply Z.leb_gt in H4. lia.
- right. split; [|reflexivity]. intros [He _]. apply Z.leb_gt in H4. lia.
Qed.
Lemma rbn5_NB_ne : forall X, (1 <= length (rbm_NB X))%nat.
Proof.
intros X. assert (H : rbm_NM X <> []).
{ destruct (rbn5_NM_cases X) as [(_ & _ & ->) | (_ & ->)]; [exact (rbn5_stem_ne X)|].
  destruct (rbm_stem X); discriminate. }
unfold rbm_NB. destruct (rbm_NM X) as [|c l]; [exfalso; exact (H eq_refl)|]. cbn [firstn length]. lia.
Qed.
Lemma rbn5_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
Lemma rbn5_cells_app : forall (m : word -> option byte) l1 l2,
  rbn_cells m (l1 ++ l2) <-> rbn_cells m l1 /\ rbn_cells m l2.
Proof.
intros m l1 l2. induction l1 as [|[[a n] v] t IH]; cbn [rbn_cells app]; [tauto|]. rewrite IH. tauto.
Qed.
Lemma rbn5_cells_in : forall (m : word -> option byte) l a n v,
  rbn_cells m l -> In (a, n, v) l -> val_mem SEGS m a n v.
Proof.
intros m l. induction l as [|[[a0 n0] v0] t IH]; cbn [rbn_cells In]; intros a n v HC Hin; [destruct Hin|].
destruct HC as [H1 H2]. destruct Hin as [E | Hin]; [injection E as <- <- <-; exact H1 | exact (IH a n v H2 Hin)].
Qed.
Lemma rbn5_vm1 : forall H (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv. destruct (aview_byte SEGS H m a v Hv) as (b & Hb & -> & Hr).
intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r, Hb. f_equal.
rewrite (rbn5_le1 _ Hr). symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma rbn5_aview_vm1 : forall H (m : word -> option byte) a v,
  val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview SEGS H m a = Some v.
Proof.
intros H m a v Hv Hr. specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal. rewrite (rbn5_le1 _ Hr).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.
Lemma rbn5_VB : forall E k v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some k) = v.
Proof. intros E k v Hk Hv. cbn [base_val]. rewrite Hk. apply unsigned_lit_small. exact Hv. Qed.
Lemma rbn5_kept_frame : forall E rs H (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn5_env_agree : forall regs extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma rbn5_amem_shadow : forall x a n, amem_range a n -> 0 <= a -> a <= x < a + n ->
  SHADOW_OFF <= shadow_addr x /\ shadow_addr x + 1 <= kHighMemBeg.
Proof.
intros x a n Ham Ha Hx. unfold shadow_addr.
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M1.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.
Lemma rbn5_argc_rng : forall X a n v, In (a, n, v) (rbn_argc X) ->
  rbn_A X <= a /\ a + Z.of_nat n <= rbn_A X + 64.
Proof.
intros X a n v H. unfold rbn_argc in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn5_rw_rng : forall X pos n0 ov0 a n v, In (a, n, v) (rbn_rw X pos n0 ov0) ->
  rbn_A X + 184 <= a /\ a + Z.of_nat n <= rbn_A X + 212.
Proof.
intros X pos n0 ov0 a n v H. unfold rbn_rw in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn5_P_sep : forall X pos P,
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
Lemma rbn5_str_kept : forall (W W' : world SEGS) (m m' : word -> option byte) a s,
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
  by (intros x Hx; exact (rbn5_amem_shadow x a _ Ham ltac:(lia) ltac:(lia))).
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
Hypothesis mc_consts_unowned : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis mc_consts_img : forall a, MC_CONSTS_LO <= a < MC_CONSTS_HI -> in_img SEGS a.
Lemma rbn5_fa : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM c p.
destruct HX as ((_ & L0 & _) & _). destruct HM as ((_ & L1 & _) & _).
destruct L0 as (_ & _ & _ & _ & _ & F0 & _). destruct L1 as (_ & _ & _ & _ & _ & F1 & _).
unfold frame_addr. rewrite F0, F1. reflexivity.
Qed.
Lemma rbn5_A_rng : forall X, rbn_cx B X ->
  alloc_ceiling + 8816 <= rbn_SP X /\ rbn_SP X - 351 <= rbn_A X /\ rbn_A X + 320 <= rbn_SP X /\
  rbn_SP X + 16 <= 2 ^ 47 /\ ri_sp0 X - ri_STK X <= rbn_SP X - 8816 /\ rbn_SP X + 16 <= ri_sp0 X /\
  rbn_A X mod 32 = 0 /\ ri_sp0 X mod 16 = 0.
Proof.
intros X HX. destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & Hsp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hal & _ & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 320) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 320) 32 ltac:(lia)) as M1.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [|exact Hal]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Lemma rbn5_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 64 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) memc1 a /\ ~ in_img SEGS a) /\
  (forall j, 0 <= j < 64 -> apresent (w_H W1) memc1 (rbn_SH X pos + j)) /\
  rbn_SH X pos = SHADOW_OFF + rbn_F X pos / 8 /\ rbn_SH X pos mod 8 = 0 /\
  kLowMemEnd <= rbn_SH X pos /\ rbn_SH X pos + 64 <= kHighShadowEnd.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM 3 pos) as FA.
destruct HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (_ & Happ & Hpr & Hsh).
destruct (frame_al64 SEGS B _ _ _ _ _ 3 pos HAR1 Hin3) as (H64 & _).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold rbn_SH, rbn_F. rewrite <- FA. rewrite Hfb3 in *.
set (F := frame_addr lyc1 3 pos) in *.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite H64, Z.add_0_r in DF.
assert (E8 : F / 8 = 8 * (F / 64)) by (rewrite DF at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia;
  rewrite Z.div_mul by lia; reflexivity).
split; [exact HF4096|]. split; [exact HFceil|]. split; [exact H64|]. split; [exact Happ|].
split.
{ intros a Ha. split; [exact (proj1 (Hpr a Ha))|].
  refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
  split; [exact Hin3|]. rewrite Hfb3. exact Ha. }
split.
{ intros j Hj. exact (proj1 (Hsh j ltac:(change (512 / 8) with 64; lia))). }
split; [reflexivity|].
split; [unfold shadow_addr; rewrite E8; replace (SHADOW_OFF + 8 * (F / 64)) with ((268431360 + F / 64) * 8)
  by (unfold SHADOW_OFF; lia); apply Z_mod_mult|].
unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd. split; [lia|].
pose proof (Z.div_mod alloc_ceiling 8 ltac:(lia)). pose proof (Z.mod_pos_bound alloc_ceiling 8 ltac:(lia)).
pose proof (Z.div_mod F 8 ltac:(lia)). pose proof (Z.mod_pos_bound F 8 ltac:(lia)). lia.
Qed.
Lemma rbn5_oframe : forall X pos lyc1 Sc1 W1 m md Er sh cid p a,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m md Er sh -> In (cid, p) (frames (ri_Sc X)) ->
  (in_zr a (frame_rng (ri_lyc X) (cid, p)) \/
   in_zr a (shadow_addr (frame_addr (ri_lyc X) cid p), fs_frame_bytes cid / 8)) ->
  0 <= a < alloc_ceiling /\ ~ (rbn_F X pos <= a < rbn_F X pos + 512) /\ ~ (rbn_SH X pos <= a < rbn_SH X pos + 64).
Proof.
intros X pos lyc1 Sc1 W1 m md Er sh cid p a HX HM Hcp Ha.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 m md Er sh HX HM) as FA.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md Er sh HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & _ & _ & ESH & _ & _ & SHhi).
destruct HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp1) as (Hc4096 & Hcceil & Hcapp).
destruct (frame_al64 SEGS B _ _ _ _ _ cid p HAR1 Hcp1) as (Hc64 & Hb64 & Hb64').
destruct (in_split _ _ Hcp) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (3, pos) (cid, p) [] l2 l3 HAR1
  ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !FA in Hd. rewrite FA in Hc4096, Hcceil, Hcapp, Hc64.
change (fs_frame_bytes 3) with 512 in Hd.
fold (rbn_F X pos) in Hd. rewrite ESH. clear ESH.
destruct (rbn5_d64 _ HF64) as (EF8 & EF). destruct (rbn5_d64 _ Hc64) as (Ec8 & Ec).
destruct (rbn5_d64 _ Hb64) as (Eb8 & Eb).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, Hcapp. unfold kHighShadowEnd in SHhi.
unfold in_zr, frame_rng, shadow_addr in Ha. cbn [fst snd] in Ha. unfold SHADOW_OFF in *.
rewrite EF8, Ec8, Eb8 in *. destruct Ha as [Ha | Ha]; lia.
Qed.
Definition rbn5_step (X : rbn_in) (lyc1 : alayout) (Sc1 : astate) (W W' : world SEGS)
  (m m' : word -> option byte) (Er : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X + 212) -> ~ Er a ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) /\
  (forall b mm j, In (b, mm) (ablocks B lyc1 Sc1) -> 0 <= j < req_size mm -> ~ Er (b + j) ->
     aview SEGS (w_H W') m' (b + j) = aview SEGS (w_H W) m (b + j)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) /\
  (forall cid p a, In (cid, p) (frames Sc1) ->
     (in_zr a (frame_rng lyc1 (cid, p)) \/ in_zr a (shadow_addr (frame_addr lyc1 cid p), fs_frame_bytes cid / 8)) ->
     ~ Er a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a).
Lemma rbn5_step_glob : forall X pos lyc1 Sc1 W1 mdc1 sh W' (m m' : word -> option byte) (Er : Z -> Prop),
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m mdc1 (fun _ => False) sh ->
  (forall a, Er a -> ~ in_img SEGS a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X + 212) -> ~ Er a ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W1) m a) ->
  rbn5_step X lyc1 Sc1 W1 W' m m' Er.
Proof.
intros X pos lyc1 Sc1 W1 mdc1 sh W' m m' Er HX HM Hni HEQ.
pose proof HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & _).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
split; [|split; [|split]].
- intros a Ha Hw He. apply HEQ; [lia | exact Hw | exact He].
- intros b mm j Hb Hj He.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR1 Hb) as (_ & Hb4 & Hbc & _).
  apply HEQ; [lia | lia | exact He].
- intros a Hia Ho He. pose proof (pa_segs_low a Hia) as Hlow. unfold kLowMemEnd in Hlow.
  apply HEQ; [lia | lia |]. intros Hc. exact (Hni a Hc Hia).
- intros cid p a Hcp Ha He.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid p HAR1 Hcp) as (Hc4096 & Hcceil & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hcnn.
  assert (Hrng : 0 <= a < alloc_ceiling).
  { destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha; [lia|].
    pose proof (rbn5_sh_band (frame_addr lyc1 cid p) (fs_frame_bytes cid)
      (a - shadow_addr (frame_addr lyc1 cid p)) Hc4096 Hcnn Hcceil ltac:(lia)) as Hb.
    unfold kLowShadowBeg, kHighMemBeg in Hb. lia. }
  apply HEQ; [lia | lia | exact He].
Qed.
Lemma rbn5_mid_step : forall X pos lyc1 Sc1 lyc2 Sc2 (W1 W2 : world SEGS) m mdc1 m' md' sh sh' Er,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m mdc1 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 m' md' (ri_k X) ->
  frames Sc2 = frames Sc1 -> Permutation (ablocks B lyc2 Sc2) (ablocks B lyc1 Sc1) ->
  rbn5_step X lyc1 Sc1 W1 W2 m m' Er ->
  (forall a, Er a -> rbn_F X pos <= a < rbn_F X pos + 504 \/ rbn_SH X pos <= a < rbn_SH X pos + 64) ->
  rbn_shadow_at W2 m' (rbn_SH X pos) sh' ->
  rbn_mid B X pos lyc2 Sc2 W2 m' md' (fun _ => False) sh'.
Proof.
intros X pos lyc1 Sc1 lyc2 Sc2 W1 W2 m mdc1 m' md' sh sh' Er HX HM HJ2 Hfr2 Hperm2 HST HEr Hsh'.
destruct HST as (C1 & C2 & C3 & C4).
pose proof (rbn5_fa X pos lyc1 Sc1 W1 m mdc1 _ sh HX HM) as FA.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m mdc1 _ sh HX HM)
  as (HF4096 & HFceil & HFal & HFapp & HFpr & _ & ESH & SH8 & SHlo & SHhi).
destruct (rbn5_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & _).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
assert (FR : forall c p, frame_rng lyc1 (c, p) = frame_rng (ri_lyc X) (c, p))
  by (intros c p0; unfold frame_rng; cbn [fst snd]; rewrite FA; reflexivity).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (Happ : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> a < kLowShadowBeg \/ kHighMemBeg <= a).
{ intros a Ha. unfold in_app in HFapp. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
assert (HnErH : forall a, alloc_ceiling <= a -> ~ Er a).
{ intros a Ha He. destruct (HEr a He) as [Hq | Hq]; [lia|]. unfold kHighShadowEnd in SHhi. lia. }
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & HK & Hfr & Hfl & Hsh0).
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (HnErS : forall a, Er a -> rbn_F X pos <= a < rbn_F X pos + 504 \/ rbn_SH X pos <= a < rbn_SH X pos + 64) by exact HEr.
unfold rbn_mid. split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfrs|].
split; [exact (Permutation_trans Hperm2 Hperm)|].
split.
{ intros a Hro0 Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  rewrite (C3 a Hia Ho He). exact (Hro a Hro0 Ho He). }
split.
{ unfold rbn_kept. split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn' He. rewrite (C1 a Ha ltac:(unfold rbn_SP in *; lia) (HnErH a ltac:(lia))).
    exact (K1 a Ha Hn' He).
  - intros b mm j Hb Hj He.
    assert (Hb1 : In (b, mm) (ablocks B lyc1 Sc1)) by exact (Permutation_in _ (Permutation_sym Hperm) Hb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR1 Hb1) as (_ & Hb4 & Hbc & [Hh1 Hh2] & _).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b mm 3 pos HAR1 Hb1 Hin3) as Hd.
    rewrite FA3, Hfb3 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    unfold in_app, zone2, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hh1, Hh2, HFapp.
    unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
    rewrite (C2 b mm j Hb1 Hj ltac:(intros He2; destruct (HEr _ He2); lia)).
    exact (K2 b mm j Hb Hj He).
  - intros a Hia Ho He. rewrite (C3 a Hia Ho He). exact (K3 a Hia Ho He).
  - intros cid p a Hcp Ha He.
    destruct (rbn5_oframe X pos lyc1 Sc1 W1 m mdc1 _ sh cid p a HX HM Hcp Ha) as (O1 & O2 & O3).
    assert (Hcp1 : In (cid, p) (frames Sc1)) by (rewrite Hfrs; right; exact Hcp).
    assert (HnE : ~ Er a) by (intros He2; destruct (HEr a He2); lia).
    rewrite (C4 cid p a Hcp1 ltac:(rewrite FR, FA; exact Ha) HnE). exact (K4 cid p a Hcp Ha He).
  - intros a Ha Hn' Hp.
    apply (apresent_transfer SEGS (w_H W1) (w_H W2) m m' a);
      [lia | intros Hi; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia
       | apply C1; [lia | unfold rbn_SP in *; lia | exact (HnErH a ltac:(lia))]
       | exact (K5 a Ha Hn' Hp)].
  - intros a Ha. apply Hpres2. unfold rbn_SP in *. lia. }
split.
{ unfold rbn_frame. intros j r Hj.
  assert (Hj13 : (j < length rbn_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  change (length rbn_saved_regs) with 13%nat in Hj13.
  apply (val_mem_kept SEGS (w_H W1) (w_H W2) m m'); [|exact (Hfr j r Hj)].
  intros kk Hk. apply C1; [unfold rbn_SP in *; lia | unfold rbn_SP in *; lia |].
  apply HnErH. unfold rbn_SP in *. lia. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W2) m m'); [|exact Hfl].
  intros kk Hk. apply (C4 3 pos); [exact Hin3 | left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite FA3, Hfb3; lia|].
  intros He2. destruct (HEr _ He2) as [Hq | Hq]; [lia|].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi. lia. }
exact Hsh'.
Qed.
Lemma rbn5_sh_kept : forall X pos lyc1 Sc1 (W1 W2 : world SEGS) m mdc1 m' sh Er (sh' : list Z),
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m mdc1 (fun _ => False) sh ->
  rbn5_step X lyc1 Sc1 W1 W2 m m' Er ->
  length sh' = length sh -> Z.of_nat (length sh) <= 64 ->
  (forall j, 0 <= j < Z.of_nat (length sh) ->
     aview SEGS (w_H W2) m' (rbn_SH X pos + j) = Some (nth (Z.to_nat j) sh' 0) \/
     (~ Er (rbn_SH X pos + j) /\ nth (Z.to_nat j) sh' 0 = nth (Z.to_nat j) sh 0)) ->
  rbn_shadow_at W2 m' (rbn_SH X pos) sh'.
Proof.
intros X pos lyc1 Sc1 W1 W2 m mdc1 m' sh Er sh' HX HM HST Hlen Hsh Hj0.
destruct HST as (_ & _ & _ & C4).
pose proof (rbn5_fa X pos lyc1 Sc1 W1 m mdc1 _ sh HX HM) as FA.
pose proof HM as (HJ1 & Hfrs & _ & _ & _ & _ & _ & Hsh0).
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
assert (FA3 : frame_addr lyc1 3 pos = rbn_F X pos) by (rewrite FA; reflexivity).
intros j Hj. rewrite Hlen in Hj.
destruct (Hj0 j Hj) as [Hn | (He & Hs)]; [exact Hn|].
rewrite Hs. unfold rbn_SH in *.
rewrite (C4 3 pos (shadow_addr (rbn_F X pos) + j) Hin3
  ltac:(right; unfold in_zr; cbn [fst snd]; rewrite FA3; change (fs_frame_bytes 3 / 8) with 64; lia) He).
exact (Hsh0 j Hj).
Qed.
Lemma rbn5_consts : forall X pos lyc1 Sc1 W1 m md Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m md Er sh ->
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W1 m.
Proof.
intros X pos lyc1 Sc1 W1 m md Er sh HX HM a Ha.
pose proof HX as (_ & _ & HCV & _). pose proof HM as (_ & _ & _ & _ & (_ & _ & K3 & _) & _).
destruct (mc_consts_unowned a Ha) as [Ho He].
rewrite (K3 a (mc_consts_img a Ha) Ho He). exact (HCV a Ha).
Qed.
Lemma rbn5_stk_eq : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  ly_stk_lo lyc1 = ly_stk_lo (ri_ly X) /\ ly_stk_hi lyc1 = ly_stk_hi (ri_ly X).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM.
destruct HM as ((_ & L1 & _) & _).
destruct L1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _). split; assumption.
Qed.
Lemma rbn5_A_rngS : forall X, rbn_cx B X ->
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
Lemma rbn5_F_factsS : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\ rbn_F X pos mod 32 = 0 /\
  in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) memc1 a /\ ~ in_img SEGS a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM 3 pos) as FA.
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
Lemma rbn5_F_img : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh a,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  rbn_F X pos <= a < rbn_F X pos + 512 -> a < YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= a.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh a HX HM Ha.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM 3 pos) as FA.
destruct HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
pose proof HAR1 as (_ & LG & _). destruct (pa_img_cover lyc1 Sc1 mdc1 LG) as [C1 C2].
assert (Hz : ~ in_zr a (ly_img lyc1)).
{ refine (proj1 (al_client_img _ _ LAWS _ _ _ _ _ a HAR1 _)). right; left. exists 3, pos.
  split; [exact Hin3|]. rewrite FA. change (fs_frame_bytes 3) with 512. exact Ha. }
unfold in_zr in Hz. lia.
Qed.
Lemma rbn5_stk_shadow : forall lyc Sc W mem md a n,
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
Lemma rbn5_mid_fw : forall X pos lyc1 Sc1 W1 memc1 mdc1 lyc2 Sc2 W2 mem2 md2 sh,
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
pose proof (rbn5_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HX HM) as FA.
destruct (rbn5_F_factsS X pos lyc1 Sc1 W1 memc1 mdc1 _ sh HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
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
      pose proof (rbn5_sh_band (frame_addr (ri_lyc X) cid p) (fs_frame_bytes cid)
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
pose proof (rbn5_sh_band (rbn_F X pos) 512 j HF4096 ltac:(lia) HFceil ltac:(change (512 / 8) with 64; lia)) as Hb.
unfold rbn_SH.
rewrite (HE (shadow_addr (rbn_F X pos) + j))
  by (unfold kLowShadowBeg, kHighMemBeg in *; first [lia | intros Hf; destruct (Happ _ Hf); lia]).
exact (Hsh0 j Hj).
Qed.
Lemma rbn5_lbuf_name : forall X pos lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true false false) ->
  rbn_lbuf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc1
    (rbn_A X) (rbn_A X + 152) (rbn_F X pos + 64) 24.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 HX HM.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM 3 pos) as FA.
destruct (rbn5_F_factsS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh0).
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HFal, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
pose proof (rbn5_F_img X pos lyc1 Sc1 W1 memc1 mdc1 _ _ (rbn_F X pos + 64) HX HM ltac:(lia)) as I1.
pose proof (rbn5_F_img X pos lyc1 Sc1 W1 memc1 mdc1 _ _ (rbn_F X pos + 87) HX HM ltac:(lia)) as I2.
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
  rewrite (Hsh0 (8 + i)) by (rewrite rbn5_sh_len; lia).
  assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia; reflexivity. }
split.
{ intros sx Hsx.
  assert (Hj : 0 <= sx - rbn_SH X pos < 64) by (unfold rbn_SH, shadow_addr in *; lia).
  pose proof (Hsh0 (sx - rbn_SH X pos) ltac:(rewrite rbn5_sh_len; lia)) as E.
  replace (rbn_SH X pos + (sx - rbn_SH X pos)) with sx in E by lia. rewrite E. discriminate. }
intros a Ha. split; [|exact (proj1 (HFpr a ltac:(lia)))].
right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
unfold in_zr. cbn [fst snd]. rewrite FA. change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos).
change (fs_frame_bytes 3) with 512. lia.
Qed.
Definition rbn5_cT (X : rbn_in) (pos : Z) (regs : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (m : word -> option byte) (md : Model) : Prop :=
  rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) (rbn_sh true true false false) /\
  rbn_rbase B X pos regs /\ getr regs 18 = w64 (rbn_SH X pos) /\ getr regs 27 = w64 (rbn_F X pos + 64) /\
  rbn_cells (mrestrict (w_H W1) m)
    (rbn_argc X ++ rbn_rw X pos 4 0 ++ rbn_rn X pos (Z.of_nat (length (rbm_NB X))) (rbm_ovf 23 (rbm_NM X))) /\
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) (rbm_NB X) /\ rbm_args X.
Definition rbn5_cD (X : rbn_in) (pos : Z) (regs : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (m : word -> option byte) (md : Model) : Prop :=
  rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) (rbn_sh true true false false) /\
  rbn_rbase B X pos regs /\ getr regs 18 = w64 (rbn_SH X pos) /\
  getr regs 20 = w64 (rbn_F X pos + 32) /\ getr regs 27 = w64 (rbn_F X pos + 64) /\
  rbn_cells (mrestrict (w_H W1) m)
    (rbn_argc X ++ rbn_rw X pos 4 0 ++
     rbn_rn X pos (Z.of_nat (length (firstn 23 (rbm_stem X)))) (rbm_ovf 23 (rbm_stem X))) /\
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 32) (rbm_w4 X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) (firstn 23 (rbm_stem X)) /\
  rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X /\ rbm_args X.
Definition RBN5_D : Z := 0x398.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (SIGMA AS___interceptor_trampoline_bcmp).
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (SIGMA AS___interceptor_trampoline_strlen).
Hypothesis TLF : PALibF B.
Hypothesis TSB : tsb_ch_spec B.
Hypothesis DRO : tfib_ro_unowned B.
Hypothesis GM : globs_marked SEGS B tfib_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis L2F : rbn_L2_fits B.
Hypothesis L2O : rbn_L2_ovf B.
Definition rbn5t_ss : sstate :=
  mkSS (AF_both3_reac_box_name + RBN_L2X) sr_atoms
    [YP09.mkRegion (Some 9%nat) 120 176 120 136 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))];
     YP09.mkRegion (Some 33%nat) 0 1 0 1 [];
     YP09.mkRegion (Some 18%nat) 16 19 16 19 []] None
    (mkFacts [] [] [(SAlu ALU_ADD (SOff 27 0) (SOff 32 0), SOff 33 0)]).
Definition rbn5t_W (A D SH a : Z) : Prop := A + 120 <= a < A + 136 \/ a = D \/ SH + 16 <= a < SH + 19.
Lemma rbn5t_W_rng : forall A F SH n a, rbn5t_W A (F + 64 + n) SH a -> 0 <= n <= 23 ->
  A + 120 <= a < A + 152 \/ F <= a < F + 512 \/ SH <= a < SH + 64.
Proof. intros A F SH n a Hw Hn. unfold rbn5t_W in Hw. lia. Qed.
Lemma rbn5t_rn_rng : forall X pos n0 ov0 a k v, In (a, k, v) (rbn_rn X pos n0 ov0) ->
  rbn_A X + 152 <= a /\ a + Z.of_nat k <= rbn_A X + 180.
Proof.
intros X pos n0 ov0 a k v H. unfold rbn_rn in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn5t_lxor : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. change (2 ^ 64 - 1) with (Z.ones 64).
assert (Hd : Z.ldiff x (Z.ones 64) = 0).
{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. }
rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x Hd).
apply Z.bits_inj'. intros k Hk. rewrite Z.lxor_spec, Z.ldiff_spec.
pose proof (f_equal (fun z => Z.testbit z k) Hd) as Hb. cbv beta in Hb. rewrite Z.ldiff_spec, Z.bits_0 in Hb.
destruct (Z.testbit x k), (Z.testbit (Z.ones 64) k); cbn in *; congruence.
Qed.
Lemma rbn5t_br1 : forall E n, ew E 32 = Z_to_bv 64 n -> 0 <= n <= 23 ->
  branch_taken BC_LTU (sv_denot E (SLit 23)) (sv_denot E (SOff 32 0)) = false.
Proof.
intros E n H Hn. rewrite branch_ltu_U, (U_lit E 23), (U_atom E 32 n H) by lia. apply Z.ltb_ge. lia.
Qed.
Lemma rbn5t_br2 : forall E x n, ew E 27 = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 n -> 0 <= x -> 0 <= n ->
  x + n < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 27 0) (SLit (-1)))) (sv_denot E (SOff 32 0)) = false.
Proof.
intros E x n H27 H32 Hx Hn Hxn.
rewrite branch_ltu_U, U_SAlu, (U_atom E 32 n H32), (U_atom E 27 x H27), U_SLit by lia. cbn [zalu_raw].
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite rbn5t_lxor by lia.
rewrite zcanon_id by (unfold M64; lia). apply Z.ltb_ge. lia.
Qed.
Lemma rbn5t_vm0 : forall H (m : word -> option byte) a (k : nat),
  (forall i, 0 <= i < Z.of_nat k -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a k 0.
Proof.
intros H m a k Hz j Hj.
destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & E0 & _).
rewrite Hb. f_equal. unfold YO0f.le_byte. rewrite Zmod_0_l, Z.shiftr_0_l, Zmod_0_l.
rewrite E0. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma rbn5t_pres : forall (regsT regs2 : bvmap 5 word) (r : bv 5), aregs_preserved regsT regs2 ->
  existsb (Z.eqb (bv_unsigned r)) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true ->
  getr regs2 r = getr regsT r.
Proof.
intros regsT regs2 r HP Hr. apply existsb_exists in Hr as (x & Hx & Hq). apply Z.eqb_eq in Hq.
assert (Hc : acallee_saved (bv_unsigned r)) by (unfold acallee_saved; cbn [In] in Hx; lia).
pose proof (HP _ Hc) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Lemma rbn5t_c8 {fq : YK11.FPState} : forall E ss (H : word -> bool) (ms0 : machine_state) i r k b off e v,
  st_ok SEGS E ss (restrict H ms0) -> nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some k ->
  bv_unsigned (ew E k) = b -> In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> val_mem SEGS (mrestrict H (ms_mem ms0)) (b + off) 8 v.
Proof.
intros E ss H ms0 i r k b off e v HS Hi Hb Hk Hc He Hv.
pose proof (st_ok_region_nth E ss (restrict H ms0) i r HS Hi) as HR. cbn [ms_mem restrict] in HR.
pose proof (region_ok_chunk SEGS E _ r _ HR Hc) as C. rewrite Hb in C. cbn [base_val] in C. rewrite Hk in C.
change 8%nat with (N.to_nat 8). exact (val_of_chunk_ok SEGS E _ b off 8%N e v C He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma rbn5t_c1z {fq : YK11.FPState} : forall E ss (H : word -> bool) (ms0 : machine_state) i r k b off,
  st_ok SEGS E ss (restrict H ms0) -> nth_error (ss_mem ss) i = Some r -> YP09.r_base r = Some k ->
  bv_unsigned (ew E k) = b -> In (YP09.mkChunk off (CVal 1 (SLit 0))) (YP09.r_chunks r) ->
  aview SEGS H (ms_mem ms0) (b + off) = Some 0.
Proof.
intros E ss H ms0 i r k b off HS Hi Hb Hk Hc.
pose proof (st_ok_region_nth E ss (restrict H ms0) i r HS Hi) as HR. cbn [ms_mem restrict] in HR.
pose proof (region_ok_chunk SEGS E _ r _ HR Hc) as C. rewrite Hb in C. cbn [base_val] in C. rewrite Hk in C.
apply rbn5_aview_vm1; [|lia].
change 1%nat with (N.to_nat 1).
exact (val_of_chunk_ok SEGS E _ b off 1%N (SLit 0) 0 C eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Lemma rbn5t_bnd : forall X pos regs lyc1 Sc1 W1 m md, rbn_cx B X -> rbn5_cT X pos regs lyc1 Sc1 W1 m md ->
  1 <= Z.of_nat (length (rbm_NB X)) <= 23 /\ 0 <= rbn_A X /\ rbn_A X + 320 <= 2 ^ 47 /\
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= 2 ^ 47 /\ 0 <= rbn_SH X pos /\ rbn_SH X pos + 64 <= 2 ^ 47 /\
  rbn_F X pos + 512 <= rbn_A X - 4096 /\ rbn_SH X pos + 64 <= rbn_A X - 4096.
Proof.
intros X pos regs lyc1 Sc1 W1 m md HX HT. destruct HT as (HM & _).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM) as (HF4096 & HFceil & _ & _ & _ & _ & _ & _ & SHlo & SHhi).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rbn5_NB_ne X) as Hn1. assert (Hn23 : (length (rbm_NB X) <= 23)%nat) by apply firstn_le_length.
unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
repeat split; lia.
Qed.
Lemma rbn5t_entry : forall (fq : YK11.FPState) X pos regs lyc1 Sc1 W1 m md,
  rbn_cx B X -> rbn5_cT X pos regs lyc1 Sc1 W1 m md ->
  st_ok_pi SEGS VAL
    (Eimg (Ereg regs (map (Z_to_bv 64)
      [Z.of_nat (length (rbm_NB X)); rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))])))
    rbn5t_ss
    (restrict (w_H W1) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_L2X))) m (seg_rom SEGS))).
Proof.
intros fq X pos regs lyc1 Sc1 W1 m md HX HT.
pose proof HT as (HM & HR & R18 & R27 & HC & HG & HA).
pose proof HR as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
pose proof HM as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & K6) & _).
pose proof (rbn5_NB_ne X) as Hn1. assert (Hn23 : (length (rbm_NB X) <= 23)%nat) by apply firstn_le_length.
assert (V168 : val_mem SEGS (mrestrict (w_H W1) m) (rbn_A X + 168) 8 (Z.of_nat (length (rbm_NB X)))).
{ apply (rbn5_cells_in _ _ _ _ _ HC). apply in_or_app. right. apply in_or_app. right.
  unfold rbn_rn. right. right. left. reflexivity. }
remember (Z.of_nat (length (rbm_NB X))) as n eqn:Hn0.
assert (Hn : 1 <= n <= 23) by (subst n; lia).
clear Hn0 Hn1 Hn23.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
rewrite restrict_mkst_fx.
remember (Eimg (Ereg regs (map (Z_to_bv 64) [n; rbn_F X pos + 64 + n]))) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 n)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (rbn_F X pos + 64 + n))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E9 : ew E 9 = Z_to_bv 64 (rbn_A X)) by (rewrite (EE 9%nat 9%bv eq_refl); exact B9).
assert (E18 : ew E 18 = Z_to_bv 64 (rbn_SH X pos)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E27 : ew E 27 = Z_to_bv 64 (rbn_F X pos + 64)) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (HER : regs_ok E sr_atoms regs) by (subst E; apply regs_ok_Eimg_Ereg).
clear HE.
unfold rbn5t_ss. apply pa_entry_st_ok_full.
- exact HER.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (rbn5_VB E 9%nat _ E9) by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply K6; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 168 8 (SOff 32 0) n);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V168].
  + rewrite (rbn5_VB E 33%nat _ E33) by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS);
            exact (proj1 (HFpr (rbn_F X pos + 64 + n + o) ltac:(lia)))|]. apply Forall_nil.
  + rewrite (rbn5_VB E 18%nat _ E18) by lia. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply HSHp; lia|]. apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (rbn5_VB E 9%nat _ E9), (rbn5_VB E 33%nat _ E33), (rbn5_VB E 18%nat _ E18) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [exact I|]. split; [exact I|]. cbn [f_alias alias_ok]. split; [|exact I].
  apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 27 _ E27), (U_atom E 32 n E32), (U_atom E 33 _ E33) by lia.
  apply zcanon_id. unfold M64. lia.
Qed.
Lemma rbn5t_awr : forall X pos lyc1 Sc1 W1 m md sh FP bl0 blc a,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) sh ->
  rbn_A X + 120 <= a < rbn_A X + 152 \/ rbn_F X pos <= a < rbn_F X pos + 512 \/
    rbn_SH X pos <= a < rbn_SH X pos + 64 ->
  awr_byte (ri_STK X) (ri_sp0 X) FP bl0 blc lyc1 ((3, pos) :: ri_own X) a.
Proof.
intros X pos lyc1 Sc1 W1 m md sh FP bl0 blc a HX HM Ha.
pose proof (rbn5_fa X pos lyc1 Sc1 W1 m md _ sh HX HM 3 pos) as FA.
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & _).
destruct Ha as [Ha | [Ha | Ha]].
- left. lia.
- right; right; right. exists 3, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite FA. change (frame_addr (ri_lyc X) 3 pos) with (rbn_F X pos).
  change (fs_frame_bytes 3) with 512. lia.
- right; right; right. exists 3, pos. split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite FA. change (shadow_addr (frame_addr (ri_lyc X) 3 pos)) with (rbn_SH X pos).
  change (fs_frame_bytes 3) with 512. change (512 / 8) with 64. lia.
Qed.
Lemma rbn5t_memset : forall X pos lyc1 Sc1 W1 m md sh regsT memT mdT raw,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memT mdT (ri_k X) ->
  getr regsT 10 = Z_to_bv 64 (rbn_A X + 136) -> getr regsT 11 = Z_to_bv 64 0 -> getr regsT 12 = Z_to_bv 64 16 ->
  getr regsT 2 = w64 (rbn_A X) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W1 (mkCfg (mkst (fx := ri_fq X) regsT (Z_to_bv 64 (SIGMA AS___asan_memset)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W1 /\ exists regs2 mem2 md2,
      c2 = mkCfg (mkst (fx := ri_fq X) regs2 raw mem2 (seg_rom SEGS)) md2 /\
      ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
        ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem2 md2 (ri_k X) /\
      aregs_preserved regsT regs2 /\
      (forall i, 0 <= i < 16 -> aview SEGS (w_H W1) mem2 (rbn_A X + 136 + i) = Some 0) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 136 <= a < rbn_A X + 152) -> ~ (rbn_A X - 4096 <= a < rbn_A X) ->
         aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memT a)).
Proof.
intros X pos lyc1 Sc1 W1 m md sh regsT memT mdT raw HX HM HJ R10 R11 R12 R2 R3 R4 R1 Hraw.
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
destruct (rbn5_A_rng X HX) as (_ & _ & _ & _ & _ & _ & _ & H16).
destruct (rbn5_stk_eq X pos lyc1 Sc1 W1 m md _ sh HM) as (Elo & Ehi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HO : (rbn_A X - ri_sp0 X) mod 16 = 0).
{ pose proof (Z.div_mod (rbn_A X) 32 ltac:(lia)) as D1. pose proof (Z.div_mod (ri_sp0 X) 16 ltac:(lia)) as D2.
  rewrite AR4, Z.add_0_r in D1. rewrite H16, Z.add_0_r in D2.
  replace (rbn_A X - ri_sp0 X) with ((2 * (rbn_A X / 32) - ri_sp0 X / 16) * 16) by lia. apply Z.mod_mul. lia. }
destruct (rbn5_stk_shadow lyc1 Sc1 W1 memT mdT (rbn_A X + 136) 16 (proj1 HJ)
  ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia) ltac:(lia)) as (Hrad & Hhv).
eapply SRr_mono.
{ eapply (aj_intrin_at SEGS B LAWS pa_segs_low OSet (SIGMA AS___asan_memset) (AMEMSET (ri_fq X)) W1 regsT memT
    (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X) ((3, pos) :: ri_own X)
    lyc1 Sc1 mdT (ri_k X) (rbn_A X + 136) 0 16 (rbn_A X - ri_sp0 X) raw HJ R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - exact HO.
  - lia.
  - rewrite Hes. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - exact Hraw.
  - intros a Ha. split; [|rewrite Hes; lia].
    apply (rbn5t_awr X pos lyc1 Sc1 W1 m md sh); [exact HX | exact HM | left; lia].
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - exact Hrad.
  - intros _. exact Hhv.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & Heff & Hfr & _).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
split; [intros i Hi; rewrite (Heff i Hi); reflexivity|].
intros a Ha H1 H2. apply Hfr; [exact Ha | lia | rewrite Hes; lia].
Qed.
Lemma rbn5t_Fsh : forall F SH n j, 4096 <= F -> (F + 512 <= 2147446784 \/ 17594333495296 <= F) ->
  SH = SHADOW_OFF + F / 8 -> 1 <= n <= 23 -> 0 <= j < 64 -> SH + j <> F + 64 + n.
Proof.
intros F SH n j H1 H2 ESH Hn Hj. pose proof (Z.div_mod F 8 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as M. unfold SHADOW_OFF in ESH. lia.
Qed.
Lemma rbn5t_post : forall X pos regs lyc1 Sc1 W1 m md regs2 m2 md2,
  rbn_cx B X -> rbn5_cT X pos regs lyc1 Sc1 W1 m md ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m2 md2 (ri_k X) ->
  rbn_rbase B X pos regs2 -> getr regs2 18 = w64 (rbn_SH X pos) -> getr regs2 20 = w64 24 ->
  getr regs2 25 = w64 (rbn_F X pos + 128) -> getr regs2 27 = w64 (rbn_F X pos + 64) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 120 <= a < rbn_A X + 152) -> ~ (rbn_A X - 4096 <= a < rbn_A X) ->
     ~ (a = rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) -> ~ (rbn_SH X pos + 16 <= a < rbn_SH X pos + 19) ->
     aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a) ->
  aview SEGS (w_H W1) m2 (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) = Some 0 ->
  (forall j, 16 <= j < 19 -> aview SEGS (w_H W1) m2 (rbn_SH X pos + j) = Some 0) ->
  val_mem SEGS (mrestrict (w_H W1) m2) (rbn_A X + 120) 8 (rbn_F X pos + 128) ->
  val_mem SEGS (mrestrict (w_H W1) m2) (rbn_A X + 128) 8 24 ->
  (forall i, 0 <= i < 16 -> aview SEGS (w_H W1) m2 (rbn_A X + 136 + i) = Some 0) ->
  rbn_st6 B X pos regs2 lyc1 Sc1 W1 m2 md2.
Proof.
intros X pos regs lyc1 Sc1 W1 m md regs2 m2 md2 HX HT HJ2 Hrbase2 R18v R20v R25v R27v HEQ Zcell Zsh T120 T128 Zrec.
pose proof HT as (HM & HR & R18 & R27 & HC & HG & HA).
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 m md _ _ HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & HSHp & ESH & SH8 & SHlo & SHhi).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rbn5_NB_ne X) as Hn1. assert (Hn23 : (length (rbm_NB X) <= 23)%nat) by apply firstn_le_length.
assert (Hn : 1 <= Z.of_nat (length (rbm_NB X)) <= 23) by lia.
assert (HFd : rbn_F X pos + 512 <= 2147446784 \/ 17594333495296 <= rbn_F X pos)
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
      destruct HFapp as [_ [Hlo | [Hhi _]]]; [left; exact Hlo | right; exact Hhi]).
unfold kLowMemEnd, kHighShadowEnd in SHlo, SHhi.
clear HFapp.
assert (KEEP : forall a, rbn_A X <= a < rbn_A X + 212 -> ~ (rbn_A X + 120 <= a < rbn_A X + 152) ->
  aview SEGS (w_H W1) m2 a = aview SEGS (w_H W1) m a).
{ intros a Ha Hn'. apply HEQ; [lia | exact Hn' | lia | lia | lia]. }
assert (Hmid : rbn_mid B X pos lyc1 Sc1 W1 m2 md2 (fun _ => False) (rbn_sh true true true false)).
{ assert (HST : rbn5_step X lyc1 Sc1 W1 W1 m m2
    (fun a => a = rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X)) \/ rbn_SH X pos + 16 <= a < rbn_SH X pos + 19)).
  { apply (rbn5_step_glob X pos lyc1 Sc1 W1 md (rbn_sh true true false false) W1 m m2
      (fun a => a = rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X)) \/ rbn_SH X pos + 16 <= a < rbn_SH X pos + 19)
      HX HM).
    - intros a [-> | Hc].
      + exact (proj2 (HFpr (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) ltac:(lia))).
      + intros Hi. pose proof (pa_segs_low a Hi). unfold kLowMemEnd in *. lia.
    - intros a Ha Hw He. apply HEQ;
      [exact Ha | lia | lia | intros E4; apply He; left; exact E4 | intros Hc; apply He; right; exact Hc]. }
  assert (Hsh2 : rbn_shadow_at W1 m2 (rbn_SH X pos) (rbn_sh true true true false)).
  { apply (rbn5_sh_kept X pos lyc1 Sc1 W1 W1 m md m2 (rbn_sh true true false false)
      (fun a => a = rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X)) \/ rbn_SH X pos + 16 <= a < rbn_SH X pos + 19)
      (rbn_sh true true true false) HX HM HST).
    - rewrite !rbn5_sh_len. reflexivity.
    - rewrite rbn5_sh_len. lia.
    - intros j Hj. rewrite rbn5_sh_len in Hj.
      destruct (Z_lt_le_dec j 16) as [Hj1 | Hj1]; [|destruct (Z_lt_le_dec j 19) as [Hj2 | Hj2]].
      + right. split; [intros [Hc | Hc];
          [exact (rbn5t_Fsh (rbn_F X pos) (rbn_SH X pos) (Z.of_nat (length (rbm_NB X))) j HF4096 HFd ESH Hn ltac:(lia) Hc) | lia]
          | rewrite (rbn5_sh_tb j) by lia; reflexivity].
      + left. rewrite (Zsh j ltac:(lia)). rewrite rbn5_sh_tb3 by lia. reflexivity.
      + right. split; [intros [Hc | Hc];
          [exact (rbn5t_Fsh (rbn_F X pos) (rbn_SH X pos) (Z.of_nat (length (rbm_NB X))) j HF4096 HFd ESH Hn ltac:(lia) Hc) | lia]
          | rewrite (rbn5_sh_tb j) by lia; reflexivity]. }
  apply (rbn5_mid_step X pos lyc1 Sc1 lyc1 Sc1 W1 W1 m md m2 md2 (rbn_sh true true false false)
    (rbn_sh true true true false)
    (fun a => a = rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X)) \/ rbn_SH X pos + 16 <= a < rbn_SH X pos + 19)
    HX HM HJ2 eq_refl (Permutation_refl _) HST); [| exact Hsh2].
  intros a [-> | Hc]; [left; lia | right; lia]. }
apply rbn5_cells_app in HC. destruct HC as [HCa HCrest].
apply rbn5_cells_app in HCrest. destruct HCrest as [HCrw HCrn].
unfold rbn_st6. split; [exact Hmid|]. split; [exact Hrbase2|]. split; [exact R18v|]. split; [exact R20v|].
split; [exact R25v|]. split; [exact R27v|]. split.
{ apply rbn5_cells_app. split.
  { apply (rbn5_cells_kept (w_H W1) (w_H W1) m m2); [|exact HCa].
    intros a nn v k Hin Hk. pose proof (rbn5_argc_rng X a nn v Hin) as Hr. apply KEEP; lia. }
  apply rbn5_cells_app. split.
  { apply (rbn5_cells_kept (w_H W1) (w_H W1) m m2); [|exact HCrw].
    intros a nn v k Hin Hk. pose proof (rbn5_rw_rng X pos 4 0 a nn v Hin) as Hr. apply KEEP; lia. }
  apply rbn5_cells_app. split.
  { apply (rbn5_cells_kept (w_H W1) (w_H W1) m m2); [|exact HCrn].
    intros a nn v k Hin Hk.
    pose proof (rbn5t_rn_rng X pos (Z.of_nat (length (rbm_NB X))) (rbm_ovf 23 (rbm_NM X)) a nn v Hin) as Hr.
    apply KEEP; lia. }
  unfold rbn_rt. cbn [rbn_cells]. split; [exact T120|]. split; [exact T128|]. split.
  { apply (rbn5t_vm0 (w_H W1) m2 (rbn_A X + 136) 8). intros i Hi. apply Zrec. lia. }
  split; [|exact I].
  apply (rbn5t_vm0 (w_H W1) m2 (rbn_A X + 144) 4). intros i Hi.
  replace (rbn_A X + 144 + i) with (rbn_A X + 136 + (8 + i)) by lia. apply Zrec. lia. }
split; [|exact HA].
apply (garr8_app1 SEGS (mrestrict (w_H W1) m) (mrestrict (w_H W1) m2) (rbn_F X pos + 64) (rbm_NB X) 0 HG).
- apply rbn5_vm1. exact Zcell.
- lia.
- intros a Ha. apply (mbyte_of_aview SEGS). apply HEQ; [lia | lia | lia | lia|].
  intros Hc. pose proof (Z.div_mod (rbn_F X pos) 8 ltac:(lia)) as Dd.
  pose proof (Z.mod_pos_bound (rbn_F X pos) 8 ltac:(lia)) as Md.
  unfold SHADOW_OFF in ESH. destruct HFd as [HFlo | HFhi]; lia.
Qed.
Ltac rbn5t_inlist := solve [ repeat (first [ left; reflexivity | right ]) ].
Ltac rbn5t_awrok HXa HMa U9 U33 U18 :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  let aa := fresh "aa" in let Hin := fresh "Hin" in let rr := fresh "rr" in
  let Hrr := fresh "Hrr" in let Hww := fresh "Hww" in
  intros aa Hin; destruct Hin as (rr & Hrr & Hww); cbn [In] in Hrr;
  repeat destruct Hrr as [<- | Hrr]; try destruct Hrr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hww;
  (eapply rbn5t_awr; [ exact HXa | exact HMa | rewrite ?U9, ?U33, ?U18 in Hww; lia ]).
Ltac rbn5t_hw U9 U33 U18 :=
  let aa := fresh "aa" in let Hin := fresh "Hin" in let rr := fresh "rr" in
  let Hrr := fresh "Hrr" in let Hww := fresh "Hww" in
  intros aa Hin; destruct Hin as (rr & Hrr & Hww);
  lazymatch type of Hrr with In _ ?L => let L' := eval vm_compute in L in change (In rr L') in Hrr end;
  cbn [In] in Hrr; repeat destruct Hrr as [<- | Hrr]; try destruct Hrr;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hww;
  rewrite ?U9, ?U33, ?U18 in Hww; unfold rbn5t_W; lia.
Lemma rbn5_tail : forall X pos regs lyc1 Sc1 W1 m md,
  rbn_cx B X -> rbn5_cT X pos regs lyc1 Sc1 W1 m md ->
  SRr SEGS W1 (rbn_cfg X RBN_L2X regs m md) (rbn_at6 B X).
Proof.
intros X pos regs lyc1 Sc1 W1 m md HX HT.
pose proof HT as (HM & HR & R18 & R27 & HC & HG & HA).
pose proof HR as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
destruct (rbn5t_bnd X pos regs lyc1 Sc1 W1 m md HX HT)
  as (Hn & HA0 & HA47 & HF4096 & HF47 & HSH0 & HSH47 & HAFsep & HSHsep).
pose proof (proj1 HM) as HJ.
pose proof (@SRr_run_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call (ri_fq X) _ _ _ _ _ B LAWS) as RUNC.
pose proof (paj_branch (fx := ri_fq X) (L := lib_both3_0_listing) (PI := PI)) as BR.
pose proof (rbn5t_entry (ri_fq X) X pos regs lyc1 Sc1 W1 m md HX HT) as HS.
remember (Eimg (Ereg regs (map (Z_to_bv 64)
  [Z.of_nat (length (rbm_NB X)); rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))]))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64)
  [Z.of_nat (length (rbm_NB X)); rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))])) E) by (rewrite HE; apply rbn5_env_agree).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros kk r Hk; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat (length (rbm_NB X))))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E9 : ew E 9 = w64 (rbn_A X)) by (rewrite (EE 9%nat 9%bv eq_refl); exact B9).
assert (E18 : ew E 18 = w64 (rbn_SH X pos)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 (rbn_F X pos)) by (rewrite (EE 19%nat 19%bv eq_refl); exact B19).
assert (E27 : ew E 27 = w64 (rbn_F X pos + 64)) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (EU9 : bv_unsigned (ew E 9) = rbn_A X) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (EU18 : bv_unsigned (ew E 18) = rbn_SH X pos) by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
assert (EU33 : bv_unsigned (ew E 33) = rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X)))
  by (rewrite E33; apply unsigned_lit_small; lia).
assert (D19 : sv_denot E (SOff 19 128) = Z_to_bv 64 (rbn_F X pos + 128)).
{ cbn [sv_denot]. rewrite E19. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
clear HE.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_both3_reac_box_name + RBN_L2X) with (BASE + (AF_both3_reac_box_name + RBN_L2X)) by lia.
paj_run_sh RUNP HS HJ.
{ rbn5t_awrok HX HM EU9 EU33 EU18. }
cbn [ms_mem mkst] in HFr. rename HFr into HFr1. rename ms into msa.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite (rbn5t_br1 E (Z.of_nat (length (rbm_NB X))) E32 ltac:(lia)) in Hc. discriminate. }
clear Hc.
paj_run_sh RUNP HS HJ.
{ rbn5t_awrok HX HM EU9 EU33 EU18. }
rename HFr into HFr2. rename ms into msb.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite (rbn5t_br2 E (rbn_F X pos + 64) (Z.of_nat (length (rbm_NB X))) E27 E32
    ltac:(lia) ltac:(lia) ltac:(lia)) in Hc. discriminate. }
paj_run_shc RUNP RUNC HS HJ.
{ rbn5t_awrok HX HM EU9 EU33 EU18. }
rename HFr into HFr3. rename ms into msc. rename HJ into HJ3.
pose proof (rbn5_kept_frame E _ (w_H W1) m (ms_mem msa)
  (rbn5t_W (rbn_A X) (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) (rbn_SH X pos))
  HFr1 ltac:(rbn5t_hw EU9 EU33 EU18)) as K1.
pose proof (rbn5_kept_frame E _ (w_H W1) (ms_mem msa) (ms_mem msb)
  (rbn5t_W (rbn_A X) (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) (rbn_SH X pos))
  HFr2 ltac:(rbn5t_hw EU9 EU33 EU18)) as K2.
pose proof (rbn5_kept_frame E _ (w_H W1) (ms_mem msb) (ms_mem msc)
  (rbn5t_W (rbn_A X) (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) (rbn_SH X pos))
  HFr3 ltac:(rbn5t_hw EU9 EU33 EU18)) as K3.
assert (KM : forall a, 0 <= a < 2 ^ 64 ->
  ~ rbn5t_W (rbn_A X) (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) (rbn_SH X pos) a ->
  aview SEGS (w_H W1) (ms_mem msc) a = aview SEGS (w_H W1) m a).
{ intros a Ha HP. rewrite (K3 a Ha HP), (K2 a Ha HP), (K1 a Ha HP). reflexivity. }
assert (KR : forall r, In r [2;3;4;8;9;18;19;22;23;27]%bv -> getr (ms_regs msc) r = getr regs r)
  by (apply (regs_kept_of_st_ok SEGS E _ (restrict (w_H W1) msc) regs
       (map (Z_to_bv 64) [Z.of_nat (length (rbm_NB X)); rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))])
       [2;3;4;8;9;18;19;22;23;27]%bv HS HAE ltac:(vm_compute; reflexivity))).
assert (V120 : val_mem SEGS (mrestrict (w_H W1) (ms_mem msc)) (rbn_A X + 120) 8 (rbn_F X pos + 128)).
{ eapply (rbn5t_c8 (fq:=ri_fq X) E _ (w_H W1) msc 0 _ 9 (rbn_A X) 120 (SOff 19 128) (rbn_F X pos + 128));
  [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact EU9
  | cbn [YP09.r_chunks]; right; left; reflexivity | exact D19 | lia ]. }
assert (V128 : val_mem SEGS (mrestrict (w_H W1) (ms_mem msc)) (rbn_A X + 128) 8 24).
{ eapply (rbn5t_c8 (fq:=ri_fq X) E _ (w_H W1) msc 0 _ 9 (rbn_A X) 128 (SLit 24) 24);
  [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity | exact EU9
  | cbn [YP09.r_chunks]; left; reflexivity | cbn [sv_denot]; reflexivity | lia ]. }
assert (Z0c : aview SEGS (w_H W1) (ms_mem msc) (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) = Some 0).
{ pose proof (rbn5t_c1z (fq:=ri_fq X) E _ (w_H W1) msc 1 _ 33
    (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) 0 HS ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) EU33 ltac:(cbn [YP09.r_chunks]; left; reflexivity)) as Z0.
  rewrite Z.add_0_r in Z0. exact Z0. }
assert (Z16 : aview SEGS (w_H W1) (ms_mem msc) (rbn_SH X pos + 16) = Some 0)
  by (apply (rbn5t_c1z (fq:=ri_fq X) E _ (w_H W1) msc 2 _ 18 (rbn_SH X pos) 16 HS ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) EU18 ltac:(cbn [YP09.r_chunks]; right; right; left; reflexivity))).
assert (Z17 : aview SEGS (w_H W1) (ms_mem msc) (rbn_SH X pos + 17) = Some 0)
  by (apply (rbn5t_c1z (fq:=ri_fq X) E _ (w_H W1) msc 2 _ 18 (rbn_SH X pos) 17 HS ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) EU18 ltac:(cbn [YP09.r_chunks]; right; left; reflexivity))).
assert (Z18c : aview SEGS (w_H W1) (ms_mem msc) (rbn_SH X pos + 18) = Some 0)
  by (apply (rbn5t_c1z (fq:=ri_fq X) E _ (w_H W1) msc 2 _ 18 (rbn_SH X pos) 18 HS ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) EU18 ltac:(cbn [YP09.r_chunks]; left; reflexivity))).
assert (D10 : getr (ms_regs msc) 10 = Z_to_bv 64 (rbn_A X + 136)).
{ pose proof (st_ok_restrict_reg SEGS (w_H W1) E _ msc (10%bv) HS) as Q.
  lazymatch type of Q with _ = sv_denot _ ?s => let s' := eval vm_compute in s in change s with s' in Q end.
  cbn [sv_denot] in Q. rewrite E9 in Q. unfold w64 in Q. rewrite unsigned_lit_small in Q by lia. exact Q. }
assert (D11 : getr (ms_regs msc) 11 = Z_to_bv 64 0).
{ pose proof (st_ok_restrict_reg SEGS (w_H W1) E _ msc (11%bv) HS) as Q.
  lazymatch type of Q with _ = sv_denot _ ?s => let s' := eval vm_compute in s in change s with s' in Q end.
  cbn [sv_denot] in Q. exact Q. }
assert (D12 : getr (ms_regs msc) 12 = Z_to_bv 64 16).
{ pose proof (st_ok_restrict_reg SEGS (w_H W1) E _ msc (12%bv) HS) as Q.
  lazymatch type of Q with _ = sv_denot _ ?s => let s' := eval vm_compute in s in change s with s' in Q end.
  cbn [sv_denot] in Q. exact Q. }
assert (D1 : getr (ms_regs msc) 1 = Z_to_bv 64 (BASE + 15104)).
{ pose proof (st_ok_restrict_reg SEGS (w_H W1) E _ msc (1%bv) HS) as Q.
  lazymatch type of Q with _ = sv_denot _ ?s => let s' := eval vm_compute in s in change s with s' in Q end.
  cbn [sv_denot] in Q. rewrite (img_env_codeptr E HEI 15104) in Q. exact Q. }
assert (R2 : getr (ms_regs msc) 2 = w64 (rbn_A X)) by (rewrite (KR (2%bv) ltac:(rbn5t_inlist)); exact B2).
assert (R3 : getr (ms_regs msc) 3 = w64 (as_gp B)) by (rewrite (KR (3%bv) ltac:(rbn5t_inlist)); exact B3).
assert (R4 : getr (ms_regs msc) 4 = w64 (as_tp B)) by (rewrite (KR (4%bv) ltac:(rbn5t_inlist)); exact B4).
assert (D20 : getr (ms_regs msc) 20 = w64 24).
{ pose proof (st_ok_restrict_reg SEGS (w_H W1) E _ msc (20%bv) HS) as Q.
  lazymatch type of Q with _ = sv_denot _ ?s => let s' := eval vm_compute in s in change s with s' in Q end.
  cbn [sv_denot] in Q. exact Q. }
assert (D25 : getr (ms_regs msc) 25 = w64 (rbn_F X pos + 128)).
{ pose proof (st_ok_restrict_reg SEGS (w_H W1) E _ msc (25%bv) HS) as Q.
  lazymatch type of Q with _ = sv_denot _ ?s => let s' := eval vm_compute in s in change s with s' in Q end.
  cbn [sv_denot] in Q. rewrite E19 in Q. unfold w64 in Q. rewrite unsigned_lit_small in Q by lia. exact Q. }
pmkst HS.
eapply SRr_bind.
{ eapply (rbn5t_memset X pos lyc1 Sc1 W1 m md (rbn_sh true true false false) (ms_regs msc) (ms_mem msc) _ _
    HX HM HJ3 D10 D11 D12 R2 R3 R4 D1 (ret_ok_codeptr_v 15104 ltac:(lia) ltac:(reflexivity))). }
cbv beta. intros W2 c2 Hle (-> & regs2 & mem2 & md2 & -> & HJ4 & HPRm & Zrec & Hfrm).
assert (HEQmain : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X + 120 <= a < rbn_A X + 152) ->
  ~ (rbn_A X - 4096 <= a < rbn_A X) -> ~ (a = rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) ->
  ~ (rbn_SH X pos + 16 <= a < rbn_SH X pos + 19) -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) m a).
{ intros a Ha H1 H2 H3 H4. rewrite (Hfrm a Ha ltac:(lia) H2). apply KM; [exact Ha | unfold rbn5t_W; lia]. }
assert (Zcell : aview SEGS (w_H W1) mem2 (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) = Some 0)
  by (rewrite (Hfrm (rbn_F X pos + 64 + Z.of_nat (length (rbm_NB X))) ltac:(lia) ltac:(lia) ltac:(lia)); exact Z0c).
assert (Zsh : forall j, 16 <= j < 19 -> aview SEGS (w_H W1) mem2 (rbn_SH X pos + j) = Some 0).
{ intros j Hj. assert (j = 16 \/ j = 17 \/ j = 18) as [-> | [-> | ->]] by lia;
  [ rewrite (Hfrm (rbn_SH X pos + 16) ltac:(lia) ltac:(lia) ltac:(lia)); exact Z16
  | rewrite (Hfrm (rbn_SH X pos + 17) ltac:(lia) ltac:(lia) ltac:(lia)); exact Z17
  | rewrite (Hfrm (rbn_SH X pos + 18) ltac:(lia) ltac:(lia) ltac:(lia)); exact Z18c ]. }
assert (T120 : val_mem SEGS (mrestrict (w_H W1) mem2) (rbn_A X + 120) 8 (rbn_F X pos + 128)).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem msc) mem2 (rbn_A X + 120) 8 (rbn_F X pos + 128));
  [ intros k Hk; apply (Hfrm (rbn_A X + 120 + k) ltac:(lia) ltac:(lia) ltac:(lia)) | exact V120 ]. }
assert (T128 : val_mem SEGS (mrestrict (w_H W1) mem2) (rbn_A X + 128) 8 24).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem msc) mem2 (rbn_A X + 128) 8 24);
  [ intros k Hk; apply (Hfrm (rbn_A X + 128 + k) ltac:(lia) ltac:(lia) ltac:(lia)) | exact V128 ]. }
assert (KR2 : forall r, In r [2;3;4;8;9;18;19;22;23;27]%bv -> getr regs2 r = getr regs r).
{ intros r Hr.
  assert (Hex : existsb (Z.eqb (bv_unsigned r)) [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27] = true)
    by (destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; vm_compute; reflexivity).
  rewrite (rbn5t_pres (ms_regs msc) regs2 r HPRm Hex). exact (KR r Hr). }
assert (R18v : getr regs2 18 = w64 (rbn_SH X pos)) by (rewrite (KR2 (18%bv) ltac:(rbn5t_inlist)); exact R18).
assert (R27v : getr regs2 27 = w64 (rbn_F X pos + 64)) by (rewrite (KR2 (27%bv) ltac:(rbn5t_inlist)); exact R27).
assert (R20v : getr regs2 20 = w64 24)
  by (rewrite (rbn5t_pres (ms_regs msc) regs2 (20%bv) HPRm ltac:(vm_compute; reflexivity)); exact D20).
assert (R25v : getr regs2 25 = w64 (rbn_F X pos + 128))
  by (rewrite (rbn5t_pres (ms_regs msc) regs2 (25%bv) HPRm ltac:(vm_compute; reflexivity)); exact D25).
assert (Hrbase2 : rbn_rbase B X pos regs2).
{ unfold rbn_rbase.
  rewrite (KR2 (2%bv) ltac:(rbn5t_inlist)), (KR2 (3%bv) ltac:(rbn5t_inlist)), (KR2 (4%bv) ltac:(rbn5t_inlist)),
          (KR2 (8%bv) ltac:(rbn5t_inlist)), (KR2 (9%bv) ltac:(rbn5t_inlist)), (KR2 (19%bv) ltac:(rbn5t_inlist)),
          (KR2 (22%bv) ltac:(rbn5t_inlist)), (KR2 (23%bv) ltac:(rbn5t_inlist)). exact HR. }
apply SRr_ret. unfold rbn_at6. exists pos, regs2, lyc1, Sc1, mem2, md2. split.
{ unfold rbn_cfg, cfg_at, w64.
  replace (BASE + AF_both3_reac_box_name + RBN_P6) with (BASE + 15104)
    by (unfold AF_both3_reac_box_name, RBN_P6; lia). reflexivity. }
apply (rbn5t_post X pos regs lyc1 Sc1 W1 m md regs2 mem2 md2 HX HT HJ4 Hrbase2 R18v R20v R25v R27v
  HEQmain Zcell Zsh T120 T128 Zrec).
Qed.
Lemma rbn5d_ch_ovf : forall (M : list Z) c, 24 <= Z.of_nat (length (firstn 23 M)) + 1 ->
  firstn 23 (M ++ [c]) = firstn 23 M /\ rbm_ovf 23 (M ++ [c]) = 1.
Proof.
intros M c H. rewrite length_firstn in H.
assert (Hl : (23 <= length M)%nat) by lia.
split.
- rewrite firstn_app. replace (23 - length M)%nat with 0%nat by lia. rewrite firstn_O, app_nil_r. reflexivity.
- unfold rbm_ovf. rewrite length_app. cbn [length].
  destruct (Z.ltb_spec 23 (Z.of_nat (length M + 1))); [reflexivity | lia].
Qed.
Lemma rbn5d_ch_fit : forall (M : list Z) c, Z.of_nat (length (firstn 23 M)) + 1 < 24 ->
  firstn 23 M = M /\ firstn 23 (M ++ [c]) = M ++ [c] /\ rbm_ovf 23 (M ++ [c]) = rbm_ovf 23 M /\
  Z.of_nat (length (M ++ [c])) = Z.of_nat (length M) + 1.
Proof.
intros M c H. rewrite length_firstn in H.
assert (Hl : (length M <= 22)%nat) by lia.
split; [apply firstn_all2; lia|].
split; [apply firstn_all2; rewrite length_app; cbn [length]; lia|].
split; [|rewrite length_app; cbn [length]; lia].
unfold rbm_ovf. rewrite length_app. cbn [length].
destruct (Z.ltb_spec 23 (Z.of_nat (length M + 1))); [lia|].
destruct (Z.ltb_spec 23 (Z.of_nat (length M))); [lia|]. reflexivity.
Qed.
Lemma rbn5d_l2_fit : forall (M s : list Z), (1 <= length s)%nat ->
  Z.of_nat (length (firstn 23 M)) + Z.of_nat (length s) <= 23 ->
  firstn 23 M ++ s = firstn 23 (M ++ s) /\
  Z.of_nat (length (firstn 23 M)) + Z.of_nat (length s) = Z.of_nat (length (firstn 23 (M ++ s))) /\
  rbm_ovf 23 M = rbm_ovf 23 (M ++ s).
Proof.
intros M s Hs H. rewrite length_firstn in H.
assert (Hl : (length M <= 22)%nat) by lia.
assert (E1 : firstn 23 M = M) by (apply firstn_all2; lia).
assert (E2 : firstn 23 (M ++ s) = M ++ s) by (apply firstn_all2; rewrite length_app; lia).
rewrite E1, E2. split; [reflexivity|]. split; [rewrite length_app; lia|].
unfold rbm_ovf. rewrite length_app.
destruct (Z.ltb_spec 23 (Z.of_nat (length M))); [lia|].
destruct (Z.ltb_spec 23 (Z.of_nat (length M + length s))); [lia|]. reflexivity.
Qed.
Lemma rbn5d_l2_ovf : forall (M s : list Z),
  23 < Z.of_nat (length (firstn 23 M)) + Z.of_nat (length s) ->
  firstn 23 M ++ firstn (Z.to_nat (23 - Z.of_nat (length (firstn 23 M)))) s = firstn 23 (M ++ s) /\
  23 = Z.of_nat (length (firstn 23 (M ++ s))) /\ 1 = rbm_ovf 23 (M ++ s).
Proof.
intros M s H.
assert (Ek : Z.to_nat (23 - Z.of_nat (length (firstn 23 M))) = (23 - length M)%nat)
  by (rewrite length_firstn; lia).
rewrite Ek. rewrite length_firstn in H.
split; [symmetry; apply firstn_app|].
split.
- rewrite length_firstn, length_app. lia.
- unfold rbm_ovf. rewrite length_app.
  destruct (Z.ltb_spec 23 (Z.of_nat (length M + length s))); [reflexivity | lia].
Qed.
Definition rbn5d_rl : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 27]%bv.
Definition rbn5d_KR (regs regs' : bvmap 5 word) : Prop :=
  forall r, In r rbn5d_rl -> getr regs' r = getr regs r.
Lemma rbn5d_KR_pres : forall regs regs', aregs_preserved regs regs' -> rbn5d_KR regs regs'.
Proof.
intros regs regs' HP r Hin.
apply (in_map bv_unsigned) in Hin.
change (map bv_unsigned rbn5d_rl) with [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 27] in Hin.
assert (Hc : acallee_saved (bv_unsigned r)) by (unfold acallee_saved; cbn [In] in Hin; lia).
pose proof (HP _ Hc) as E. rewrite !Z_to_bv_bv_unsigned in E. exact E.
Qed.
Lemma rbn5d_KR_regs : forall X pos (regs regs' : bvmap 5 word), rbn5d_KR regs regs' ->
  rbn_rbase B X pos regs -> getr regs 18 = w64 (rbn_SH X pos) ->
  getr regs 20 = w64 (rbn_F X pos + 32) -> getr regs 27 = w64 (rbn_F X pos + 64) ->
  rbn_rbase B X pos regs' /\ getr regs' 18 = w64 (rbn_SH X pos) /\
  getr regs' 20 = w64 (rbn_F X pos + 32) /\ getr regs' 27 = w64 (rbn_F X pos + 64).
Proof.
intros X pos regs regs' K HRB R18 R20 R27.
destruct HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
unfold rbn_rbase.
rewrite !K by (unfold rbn5d_rl; cbn [In]; repeat (first [left; reflexivity | right])).
repeat split; assumption.
Qed.
Lemma rbn5d_pres_same : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m' x = mrestrict H m x) -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hm (Ha & b & Hb). split; [exact Ha|]. exists b.
pose proof (Hm (Z_to_bv 64 a)) as E. unfold mrestrict in E. rewrite Ha in E. cbv beta iota in E.
rewrite E. exact Hb.
Qed.
Lemma rbn5d_ro_kept : forall (W W' : world SEGS) (m m' : word -> option byte),
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m').
Proof.
intros W W' m m' Hro HE a Hro0 Ho He.
assert (Hia : in_img SEGS a)
  by (destruct Hro0 as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
rewrite (HE a Hia Ho He). exact (Hro a Hro0 Ho He).
Qed.
Lemma rbn5d_hull_sub : forall (rd : reader) D cap x k, shadow_hull_vis rd D cap -> D <= x -> x + k <= D + cap ->
  0 < k -> shadow_hull_vis rd x k.
Proof.
intros rd D cap x k H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
assert (M1 : D / 8 <= x / 8) by (apply Z.div_le_mono; lia).
assert (M2 : (x + k - 1) / 8 <= (D + cap - 1) / 8) by (apply Z.div_le_mono; lia).
assert (M3 : (SHADOW_OFF + D / 8) / 8 * 8 <= (SHADOW_OFF + x / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
assert (M4 : (SHADOW_OFF + (x + k - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (D + cap - 1) / 8) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
lia.
Qed.
Lemma rbn5d_w4_hd : forall X (W : world SEGS) (m : word -> option byte) pos, rbm_args X ->
  garr8 SEGS (mrestrict (w_H W) m) (rbn_F X pos + 32) (rbm_w4 X ++ [0]) ->
  val_mem SEGS (mrestrict (w_H W) m) (rbn_F X pos + 32) 1 (hd 0 (rbm_w4 X)) /\ 1 <= hd 0 (rbm_w4 X) <= 255.
Proof.
intros X W m pos HA HG.
pose proof (rbn5_w4_len X HA) as Hl. pose proof (rbn5_w4_digits X HA) as Hd.
revert Hl Hd HG. destruct (rbm_w4 X) as [|c w]; intros Hl Hd HG; [cbn [length] in Hl; discriminate Hl|].
cbn [hd]. split.
- destruct (HG 0%nat ltac:(cbn; lia)) as [Hv _]. cbn [nth app Z.of_nat] in Hv. rewrite Z.add_0_r in Hv. exact Hv.
- apply Forall_inv in Hd. lia.
Qed.
Definition rbn5d_cM (X : rbn_in) (pos : Z) (regs : bvmap 5 word) (lyc1 : alayout) (Sc1 : astate)
  (W1 : world SEGS) (m : word -> option byte) (md : Model) (M : list Z) : Prop :=
  rbn_mid B X pos lyc1 Sc1 W1 m md (fun _ => False) (rbn_sh true true false false) /\
  rbn_rbase B X pos regs /\ getr regs 18 = w64 (rbn_SH X pos) /\
  getr regs 20 = w64 (rbn_F X pos + 32) /\ getr regs 27 = w64 (rbn_F X pos + 64) /\
  rbn_cells (mrestrict (w_H W1) m)
    (rbn_argc X ++ rbn_rw X pos 4 0 ++ rbn_rn X pos (Z.of_nat (length (firstn 23 M))) (rbm_ovf 23 M)) /\
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 32) (rbm_w4 X ++ [0]) /\
  garr8 SEGS (mrestrict (w_H W1) m) (rbn_F X pos + 64) (firstn 23 M) /\
  rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X /\ rbm_args X.
Lemma rbn5d_cM_same : forall X pos regs regs' lyc1 Sc1 W1 m m' md md' M,
  rbn_cx B X -> rbn5d_cM X pos regs lyc1 Sc1 W1 m md M ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m' md' (ri_k X) ->
  (forall x, mrestrict (w_H W1) m' x = mrestrict (w_H W1) m x) ->
  rbn5d_KR regs regs' ->
  rbn5d_cM X pos regs' lyc1 Sc1 W1 m' md' M.
Proof.
intros X pos regs regs' lyc1 Sc1 W1 m m' md md' M HX HC HJ' Hm K.
destruct HC as (HM & HRB & R18 & R20 & R27 & HCL & HW4 & HG & HNM & HA).
assert (HVq : forall a, aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) by (intros a; apply aview_eq_of; apply Hm).
assert (HB : forall a, mbyte SEGS (mrestrict (w_H W1) m') a = mbyte SEGS (mrestrict (w_H W1) m) a)
  by (intros a; apply (mbyte_of_aview SEGS); apply HVq).
destruct (rbn5d_KR_regs X pos regs regs' K HRB R18 R20 R27) as (HRB' & R18' & R20' & R27').
pose proof HM as (_ & _ & _ & Hro & _).
unfold rbn5d_cM. split.
{ apply (rbn5_mid_fw X pos lyc1 Sc1 W1 m md lyc1 Sc1 W1 m' md' _ HX HM HJ' eq_refl eq_refl).
  - apply (rbn5d_ro_kept W1 W1 m m' Hro). intros a _ _ _. apply HVq.
  - rewrite rbn5_sh_len. lia.
  - intros a _ _ _ _. apply HVq.
  - intros a _ _ Hp. exact (rbn5d_pres_same _ _ _ a Hm Hp).
  - intros a _ _ _. apply HVq. }
split; [exact HRB'|]. split; [exact R18'|]. split; [exact R20'|]. split; [exact R27'|].
split; [apply (rbn5_cells_kept (w_H W1) (w_H W1) m m'); [intros; apply HVq | exact HCL]|].
split; [apply (garr8_frame SEGS _ _ _ _ HW4); intros a _; apply HB|].
split; [apply (garr8_frame SEGS _ _ _ _ HG); intros a _; apply HB|].
split; [exact HNM | exact HA].
Qed.
Lemma rbn5d_chpost : forall X pos regs1 lyc1 Sc1 W1 m1 md1 M regs2 ly2 S2 W2 m2 md2,
  rbn_cx B X -> rbn5d_cM X pos regs1 lyc1 Sc1 W1 m1 md1 M ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) ly2 S2 W2 m2 md2 (ri_k X) ->
  aregs_preserved regs1 regs2 -> frames S2 = frames Sc1 -> ablocks B ly2 S2 = ablocks B lyc1 Sc1 ->
  ((24 <= Z.of_nat (length (firstn 23 M)) + 1 /\
    val_mem SEGS (mrestrict (w_H W2) m2) (rbn_A X + 152 + 24) 4 1 /\
    tsb_ch_kept B lyc1 Sc1 W1 m1 W2 m2 (rbn_A X) (fun a => rbn_A X + 152 + 24 <= a < rbn_A X + 152 + 28)) \/
   (Z.of_nat (length (firstn 23 M)) + 1 < 24 /\
    val_mem SEGS (mrestrict (w_H W2) m2) (rbn_A X + 152 + 16) 8 (Z.of_nat (length (firstn 23 M)) + 1) /\
    val_mem SEGS (mrestrict (w_H W2) m2) (rbn_F X pos + 64 + Z.of_nat (length (firstn 23 M))) 1 (45 mod 256) /\
    tsb_ch_kept B lyc1 Sc1 W1 m1 W2 m2 (rbn_A X)
      (fun a => rbn_A X + 152 + 16 <= a < rbn_A X + 152 + 24 \/
         a = rbn_F X pos + 64 + Z.of_nat (length (firstn 23 M))))) ->
  rbn5d_cM X pos regs2 ly2 S2 W2 m2 md2 (M ++ [45]).
Proof.
intros X pos regs1 lyc1 Sc1 W1 m1 md1 M regs2 ly2 S2 W2 m2 md2 HX HC HJ2 HP Hfr2 Hab2 HCASE.
destruct HC as (HM & HRB & R18 & R20 & R27 & HCL & HW4 & HG & HNM & HA).
destruct (rbn5_F_factsS X pos lyc1 Sc1 W1 m1 md1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
pose proof (firstn_le_length 23 M) as Hn23.
assert (TK : (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - TSB_CH_STK <= a < rbn_A X) ->
     ~ (rbn_A X + 168 <= a < rbn_A X + 180) -> ~ (rbn_F X pos + 64 <= a < rbn_F X pos + 88) ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (rbn_A X - TSB_CH_STK <= a < rbn_A X) ->
     apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a)).
{ destruct HCASE as [(_ & _ & (T1 & _ & T3 & _ & T5 & _)) | (_ & _ & _ & (T1 & _ & T3 & _ & T5 & _))].
  - split; [|split; [exact T3|]].
    + intros a Ha H1 H2 H3. apply T1; [exact Ha | exact H1 | cbv beta; lia].
    + intros a Ha H1 Hp. apply T5; [lia | exact H1 | exact Hp].
  - split; [|split; [exact T3|]].
    + intros a Ha H1 H2 H3. apply T1; [exact Ha | exact H1 | cbv beta; lia].
    + intros a Ha H1 Hp. apply T5; [lia | exact H1 | exact Hp]. }
destruct TK as (HEQ & HIMG & HPR).
pose proof HM as (_ & _ & _ & Hro & _).
assert (Hro2 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) m2))
  by exact (rbn5d_ro_kept W1 W2 m1 m2 Hro HIMG).
assert (HM2 : rbn_mid B X pos ly2 S2 W2 m2 md2 (fun _ => False) (rbn_sh true true false false)).
{ apply (rbn5_mid_fw X pos lyc1 Sc1 W1 m1 md1 ly2 S2 W2 m2 md2 _ HX HM HJ2 Hfr2 Hab2 Hro2);
  [rewrite rbn5_sh_len; lia | exact HEQ | exact HPR | exact HIMG]. }
destruct (rbn5d_KR_regs X pos regs1 regs2 (rbn5d_KR_pres _ _ HP) HRB R18 R20 R27) as (HRB2 & R18' & R20' & R27').
assert (HEQs : forall a, rbn_A X <= a < rbn_A X + 168 \/ rbn_A X + 180 <= a < rbn_A X + 320 ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) by (intros a Ha; apply HEQ; lia).
assert (HEQf : forall a, rbn_F X pos <= a < rbn_F X pos + 64 ->
  aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) by (intros a Ha; apply HEQ; lia).
apply rbn5_cells_app in HCL as [HCa HCr]. apply rbn5_cells_app in HCr as [HCw HCn].
unfold rbn_rn in HCn. cbn [rbn_cells] in HCn. destruct HCn as (N0 & N8 & N16 & N24 & _).
unfold rbn5d_cM.
split; [exact HM2|]. split; [exact HRB2|]. split; [exact R18'|]. split; [exact R20'|]. split; [exact R27'|].
split.
{ apply rbn5_cells_app. split.
  { apply (rbn5_cells_kept (w_H W1) (w_H W2) m1 m2); [|exact HCa].
    intros a n v k Hin Hk. pose proof (rbn5_argc_rng X a n v Hin). apply HEQs; lia. }
  apply rbn5_cells_app. split.
  { apply (rbn5_cells_kept (w_H W1) (w_H W2) m1 m2); [|exact HCw].
    intros a n v k Hin Hk. pose proof (rbn5_rw_rng X pos 4 0 a n v Hin). apply HEQs; lia. }
  unfold rbn_rn. cbn [rbn_cells].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [intros k Hk; apply HEQs; lia | exact N0]|].
  split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [intros k Hk; apply HEQs; lia | exact N8]|].
  destruct HCASE as [(Hc & O24 & (T1 & _)) | (Hc & O16 & OB & (T1 & _))].
  - destruct (rbn5d_ch_ovf M 45 Hc) as (EF & EO). rewrite EF, EO.
    split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [|exact N16]|].
    { intros k Hk. apply T1; [lia | lia | cbv beta; lia]. }
    split; [replace (rbn_A X + 176) with (rbn_A X + 152 + 24) by lia; exact O24 | exact I].
  - destruct (rbn5d_ch_fit M 45 Hc) as (EF0 & EF & EO & EL).
    rewrite EF, EO, EL.
    assert (En : Z.of_nat (length (firstn 23 M)) = Z.of_nat (length M)) by (rewrite EF0; reflexivity).
    split; [replace (rbn_A X + 168) with (rbn_A X + 152 + 16) by lia; rewrite <- En; exact O16|].
    split; [apply (val_mem_kept SEGS (w_H W1) (w_H W2) m1 m2); [|exact N24] | exact I].
    intros k Hk. apply T1; [lia | lia | cbv beta; lia]. }
split.
{ apply (garr8_frame SEGS (mrestrict (w_H W1) m1)); [exact HW4|]. intros x Hx.
  rewrite length_app, (rbn5_w4_len X HA) in Hx. cbn [length] in Hx.
  apply (mbyte_of_aview SEGS). apply HEQf. lia. }
split.
{ destruct HCASE as [(Hc & _ & (T1 & _)) | (Hc & _ & OB & (T1 & _))].
  - destruct (rbn5d_ch_ovf M 45 Hc) as (EF & _). rewrite EF.
    apply (garr8_frame SEGS (mrestrict (w_H W1) m1)); [exact HG|]. intros x Hx.
    apply (mbyte_of_aview SEGS). apply T1; [lia | lia | cbv beta; lia].
  - destruct (rbn5d_ch_fit M 45 Hc) as (EF0 & EF & _ & _).
    assert (En : Z.of_nat (length (firstn 23 M)) = Z.of_nat (length M)) by (rewrite EF0; reflexivity).
    rewrite En in OB, T1. change (45 mod 256) with 45 in OB.
    rewrite EF. rewrite EF0 in HG.
    apply (garr8_app1 SEGS (mrestrict (w_H W1) m1) (mrestrict (w_H W2) m2) (rbn_F X pos + 64) M 45 HG OB);
      [lia|].
    intros a Ha. apply (mbyte_of_aview SEGS). apply T1; [lia | lia | cbv beta; lia]. }
split; [exact HNM | exact HA].
Qed.
Lemma rbn5d_call : forall X pos regs1 lyc1 Sc1 W1 m1 md1 M,
  rbn_cx B X -> rbn5d_cM X pos regs1 lyc1 Sc1 W1 m1 md1 M ->
  getr regs1 1 = w64 (BASE + AF_both3_reac_box_name + 0x3a4) ->
  getr regs1 10 = w64 (rbn_A X + 152) -> getr regs1 11 = w64 45 ->
  SRr SEGS W1 (cfg_at (fx := ri_fq X) SEGS (BASE + AF_both3_sb_ch) regs1 m1 md1)
    (fun W2 c2 => exists lyc2 Sc2 regs2 m2 md2,
       c2 = cfg_at (fx := ri_fq X) SEGS (BASE + AF_both3_reac_box_name + 0x3a4) regs2 m2 md2 /\
       rbn5d_cM X pos regs2 lyc2 Sc2 W2 m2 md2 (M ++ [45])).
Proof.
intros X pos regs1 lyc1 Sc1 W1 m1 md1 M HX HC R1 R10 R11.
pose proof HC as (HM & HRB & R18 & R20 & R27 & HCL & HW4 & HG & HNM & HA).
destruct (rbn5_F_factsS X pos lyc1 Sc1 W1 m1 md1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
destruct (rbn5_stk_eq X pos lyc1 Sc1 W1 m1 md1 _ _ HM) as [Elo Ehi].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
pose proof HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
assert (Hsp : spZ regs1 = rbn_A X) by (unfold spZ; rewrite B2; unfold w64; apply unsigned_lit_small; lia).
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & _).
pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPst & _).
pose proof HCL as HCL0.
apply rbn5_cells_app in HCL0 as [_ HCr]. apply rbn5_cells_app in HCr as [_ HCn].
unfold rbn_rn in HCn. cbn [rbn_cells] in HCn. destruct HCn as (N0 & N8 & N16 & N24 & _).
pose proof (rbn5_lbuf_name X pos lyc1 Sc1 W1 m1 md1 HX HM) as Hbuf.
destruct Hbuf as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
pose proof (firstn_le_length 23 M) as Hn23.
destruct (rbn5_stk_shadow lyc1 Sc1 W1 m1 md1 (rbn_A X + 152) 28 HAR1 ltac:(lia) ltac:(lia) ltac:(lia))
  as [Hrra Hrhv].
eapply SRr_mono.
{ apply (TSB (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m1 md1 (ri_k X) regs1 (rbn_A X + 152) 45 (rbn_F X pos + 64) 24
    (Z.of_nat (length (firstn 23 M))) []).
  - exact HJ1.
  - exact Hro.
  - rewrite R1. unfold w64.
    replace (BASE + AF_both3_reac_box_name + 0x3a4) with (BASE + (AF_both3_reac_box_name + 0x3a4)) by lia.
    apply ret_ok_codeptr_v; unfold AF_both3_reac_box_name; [lia | reflexivity].
  - unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by (unfold AF_both3_reac_box_name; lia).
    pose proof pa_base_lo as HBL. unfold YImgTop.IMG_LO in HBL. unfold AF_both3_reac_box_name. lia.
  - exact B3.
  - exact B4.
  - exact R10.
  - exact R11.
  - left. split; [left|reflexivity]. unfold s0Z. rewrite getr_same by reg_neq_tac.
    rewrite unsigned_lit_small by lia. lia.
  - rewrite Hsp. lia.
  - rewrite Hsp, HTS. lia.
  - rewrite Hsp. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - unfold amem_range, kHighMemBeg, kHighMemEnd. lia.
  - left. rewrite Hsp. lia.
  - unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP. lia.
  - lia.
  - lia.
  - lia.
  - exact N0.
  - replace (rbn_A X + 152 + 8) with (rbn_A X + 160) by lia. exact N8.
  - replace (rbn_A X + 152 + 16) with (rbn_A X + 168) by lia. exact N16.
  - exact Hrra.
  - exact Hrhv.
  - intros a Ha. split; [left; lia | apply HPst; lia].
  - intros Hlt. rewrite Hsp, HTS.
    split; [lia|]. split; [lia|].
    split; [unfold amem_range in *; lia|].
    split; [apply (range_addressable_sub _ _ (rbn_F X pos + 64) 24); [exact D8 | lia | lia]|].
    split; [apply (rbn5d_hull_sub _ (rbn_F X pos + 64) 24); [exact D9 | lia | lia | lia]|].
    split; [right; lia|].
    split; [unfold off_img in *; lia|].
    split; [left; lia|].
    destruct (D10 (rbn_F X pos + 64 + Z.of_nat (length (firstn 23 M))) ltac:(lia)) as [Hw Hp].
    split; [exact Hw | exact Hp]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & m2 & md2 & -> & HJ2 & HP2 & Hfr2 & Hab2 & HCASE).
exists ly2, S2, regs2, m2, md2. split.
{ unfold cfg_at. rewrite R1. reflexivity. }
rewrite Hsp in HCASE.
exact (rbn5d_chpost X pos regs1 lyc1 Sc1 W1 m1 md1 M regs2 ly2 S2 W2 m2 md2 HX HC HJ2 HP2 Hfr2 Hab2 HCASE).
Qed.
Ltac rbn5d_rr HS r v tac H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = v)
      by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); tac)
  end.
Definition rbn5d_ss1 : sstate := mkSS (AF_both3_reac_box_name + RBN5_D) sr_atoms [] None (mkFacts [] [] []).
Lemma rbn5d_p1 : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (A : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 A -> 0 <= A -> A + 152 < 2 ^ 64 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN5_D) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at (fx := fq) SEGS (BASE + AF_both3_sb_ch) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       aregs_preserved regs regs1 /\
       getr regs1 1 = w64 (BASE + AF_both3_reac_box_name + 0x3a4) /\ getr regs1 10 = w64 (A + 152) /\
       getr regs1 11 = w64 45 /\
       (forall x, mrestrict (w_H W) memc1 x = mrestrict (w_H W) memc x)).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A HJ H9 HA0 HA1.
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call fq _ _ _ _ _ B LAWS) as RUNC.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) rbn5d_ss1
  (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN5_D))) memc
    (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn5d_ss1. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
set (E := Eimg (Ereg regs [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply rbn5_env_agree).
assert (E9 : ew E 9 = Z_to_bv 64 A) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E240 : ew E 240 = Z_to_bv 64 BASE) by (subst E; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
unfold cfg_at, w64.
replace (BASE + AF_both3_reac_box_name + RBN5_D) with (BASE + (AF_both3_reac_box_name + RBN5_D)) by lia.
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_nil. }
assert (KM : forall x, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) memc x).
{ intros x. apply HFr. intros (r & Hr & _). unfold rbn5d_ss1 in Hr. cbn [ss_mem In] in Hr. destruct Hr. }
rbn5d_rr HS (1%bv : bv 5) (Z_to_bv 64 (BASE + AF_both3_reac_box_name + 0x3a4))
  ltac:(cbn [sv_denot]; rewrite E240, unsigned_lit_small by lia; f_equal; unfold AF_both3_reac_box_name; lia) G1.
rbn5d_rr HS (10%bv : bv 5) (Z_to_bv 64 (A + 152))
  ltac:(cbn [sv_denot]; rewrite E9, unsigned_lit_small by lia; reflexivity) G10.
rbn5d_rr HS (11%bv : bv 5) (Z_to_bv 64 45) ltac:(reflexivity) G11.
assert (HPRES : aregs_preserved regs (ms_regs ms)).
{ apply (aregs_preserved_of_st_ok SEGS (w_H W) E _ _ regs [] HS HAE). vm_compute. reflexivity. }
apply SRr_ret. pmkst HS. cbv beta.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [unfold cfg_at, w64; rewrite pa_sigma_sb_ch; reflexivity|].
split; [exact HJ|]. split; [exact HPRES|]. split; [exact G1|]. split; [exact G10|]. split; [exact G11|].
exact KM.
Qed.
Definition rbn5d_ss2 : sstate :=
  mkSS (AF_both3_reac_box_name + 0x3a4) sr_atoms
    [YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]] None
    (mkFacts [(32%nat, mkAF 1 255 0)] [] []).
Lemma rbn5d_entry2 : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) m P c,
  getr regs 20 = w64 P -> 0 <= P -> P + 1 < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) m) P 1 c -> 1 <= c <= 255 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [Z_to_bv 64 c])) rbn5d_ss2
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + 0x3a4))) m
      (seg_rom SEGS))).
Proof.
intros fq W regs m P c H20 HP0 HP1 Hv Hc.
rewrite restrict_mkst_fx.
assert (E20 : ew (Eimg (Ereg regs [Z_to_bv 64 c])) 20 = Z_to_bv 64 P)
  by (rewrite (ew_Eimg_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E32 : ew (Eimg (Ereg regs [Z_to_bv 64 c])) 32 = Z_to_bv 64 c)
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
unfold rbn5d_ss2. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (rbn5_VB _ 20%nat P E20) by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ P 0 1 (SOff 32 0) c).
  + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + cbn. lia.
  + cbn. lia.
  + rewrite Z.add_0_r. exact Hv.
- split; exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, unsigned_lit_small by lia.
  rewrite Z.pow_0_r. split; [lia|]. split; [apply Z.mod_1_r | lia].
Qed.
Lemma rbn5d_p2 : forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  (regs : bvmap 5 word) (P c : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 20 = w64 P -> 0 <= P -> P + 2 < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) memc) P 1 c -> 1 <= c <= 255 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + 0x3a4) regs memc mdc)
    (fun W1 c1 => W1 = W /\ exists (regs1 : bvmap 5 word) (memc1 : word -> option byte) mdc1,
       c1 = cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_box_name + RBN_L2) regs1 memc1 mdc1 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc1 mdc1 k /\
       rbn5d_KR regs regs1 /\
       getr regs1 10 = w64 c /\ getr regs1 21 = w64 (P + 1) /\ getr regs1 24 = w64 (-1) /\
       (forall x, mrestrict (w_H W) memc1 x = mrestrict (w_H W) memc x)).
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P c HJ H20 HP0 HP1 Hv Hc.
pose proof (rbn5d_entry2 fq W regs memc P c H20 HP0 ltac:(lia) Hv Hc) as HS.
pose proof (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS) as RUNTOP.
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (paj_branch (fx := fq) (L := lib_both3_0_listing) (PI := PI)) as BR.
set (E := Eimg (Ereg regs [Z_to_bv 64 c])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 c]) E) by (subst E; apply rbn5_env_agree).
assert (E20 : ew E 20 = Z_to_bv 64 P) by (subst E; rewrite (ew_Eimg_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
assert (E32 : ew E 32 = Z_to_bv 64 c)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HW : forall a, ~ in_wrange E (ss_mem rbn5d_ss2) a).
{ intros a (r & Hr & Hw). unfold rbn5d_ss2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hw. lia. }
unfold cfg_at, w64.
replace (BASE + AF_both3_reac_box_name + 0x3a4) with (BASE + (AF_both3_reac_box_name + 0x3a4)) by lia.
paj_run_to_sh RUNTOP HS HJ (AF_both3_reac_box_name + RBN_L2).
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr.
assert (KM1 : forall x, mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) memc x)
  by (intros x; apply HFr; apply HW).
clear HF HFr HG.
assert (HKP : rbn5d_KR regs (ms_regs ms)).
{ intros r Hin.
  pose proof (regs_kept_of_st_ok_pi E _ _ regs [Z_to_bv 64 c] rbn5d_rl HS HAE ltac:(vm_compute; reflexivity) r Hin) as Hr.
  cbn [ms_regs restrict] in Hr. exact Hr. }
rbn5d_rr HS (10%bv : bv 5) (Z_to_bv 64 c)
  ltac:(rewrite denot_lit_U; f_equal; apply (U_atom E 32 c E32); lia) G10.
rbn5d_rr HS (21%bv : bv 5) (Z_to_bv 64 (P + 1))
  ltac:(rewrite denot_lit_U; f_equal; apply (U_atom_off E 20 P 1 E20); lia) G21.
rbn5d_rr HS (24%bv : bv 5) (w64 (-1))
  ltac:(apply bv_eq; vm_compute; reflexivity) G24.
apply SRr_ret. pmkst HS.
split; [reflexivity|].
exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split.
{ unfold cfg_at, w64.
  replace (BASE + AF_both3_reac_box_name + RBN_L2) with (BASE + 14964) by (unfold AF_both3_reac_box_name, RBN_L2; lia).
  reflexivity. }
split; [exact HJ|]. split; [exact HKP|].
split; [exact G10|]. split; [exact G21|]. split; [exact G24|].
exact KM1.
Qed.
Lemma rbn5d_w4_src : forall X pos lyc1 Sc1 W1 memc1 mdc1,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true false false) ->
  garr8 SEGS (mrestrict (w_H W1) memc1) (rbn_F X pos + 32) (rbm_w4 X ++ [0]) -> rbm_args X ->
  rbn_lsrc W1 memc1 (rbn_F X pos + 32) (rbm_w4 X ++ [0]).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 HX HM HG HA.
destruct (rbn5_F_factsS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rbn5_w4_len X HA) as Hw4.
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & Hsh0).
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 32 ltac:(lia)) as D1. rewrite HFal, Z.add_0_r in D1.
  rewrite D1. replace (32 * (rbn_F X pos / 32)) with ((4 * (rbn_F X pos / 32)) * 8) by lia. apply Z.mod_mul. lia. }
assert (Hlen : Z.of_nat (length (rbm_w4 X ++ [0])) = 5) by (rewrite length_app, Hw4; reflexivity).
assert (Heq4 : shadow_of_addr SHADOW_OFF (rbn_F X pos + 32) = rbn_SH X pos + 4).
{ unfold rbn_SH, shadow_addr, shadow_of_addr.
  replace (rbn_F X pos + 32) with (rbn_F X pos + 4 * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (Hsh4 : aview SEGS (w_H W1) memc1 (shadow_of_addr SHADOW_OFF (rbn_F X pos + 32)) = Some 5).
{ rewrite Heq4. pose proof (Hsh0 4 ltac:(rewrite rbn5_sh_len; lia)) as E.
  change (Z.to_nat 4) with 4%nat in E. rewrite (rbn5_sh_w4 true false false) in E. exact E. }
assert (Hbs : block_shadow (aview SEGS (w_H W1) memc1) SHADOW_OFF (rbn_F X pos + 32) 5).
{ split; [lia|]. split; [lia|]. intros i Hi.
  change ((5 + 7) / 8) with 1 in Hi. assert (i = 0) by lia. subst i.
  rewrite Z.add_0_r.
  replace (if 0 <? 5 / 8 then 0 else 5 mod 8) with 5 by (vm_compute; reflexivity).
  exact Hsh4. }
unfold rbn_lsrc. rewrite Hlen.
split; [exact HG|]. split; [lia|]. split; [lia|]. split; [lia|].
apply (block_shadow_range (aview SEGS (w_H W1) memc1) SHADOW_OFF (rbn_F X pos + 32) 5 (rbn_F X pos + 32) 5 Hbs);
  lia.
Qed.
Lemma rbn5d_l2post : forall X pos regs3 lyc2 Sc2 W2 memc3 mdc3 lyc3 Sc3 W3 regs4 mem4 md4 (Er : Z -> Prop),
  rbn_cx B X -> rbn5d_cM X pos regs3 lyc2 Sc2 W2 memc3 mdc3 (rbm_stem X ++ [45]) ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc3 Sc3 W3 mem4 md4 (ri_k X) ->
  frames Sc3 = frames Sc2 -> ablocks B lyc3 Sc3 = ablocks B lyc2 Sc2 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem4) ->
  rbn_keep_regs regs3 regs4 rbn_cl2 ->
  val_mem SEGS (mrestrict (w_H W3) mem4) (rbn_A X + 168) 8 (Z.of_nat (length (rbm_NB X))) ->
  val_mem SEGS (mrestrict (w_H W3) mem4) (rbn_A X + 176) 4 (rbm_ovf 23 (rbm_NM X)) ->
  garr8 SEGS (mrestrict (w_H W3) mem4) (rbn_F X pos + 64) (rbm_NB X) ->
  tsb_ch_kept B lyc2 Sc2 W2 memc3 W3 mem4 (rbn_A X) Er ->
  (forall a, Er a -> rbn_A X + 168 <= a < rbn_A X + 180 \/ rbn_F X pos + 64 <= a < rbn_F X pos + 88) ->
  rbn5_cT X pos regs4 lyc3 Sc3 W3 mem4 md4.
Proof.
intros X pos regs3 lyc2 Sc2 W2 memc3 mdc3 lyc3 Sc3 W3 regs4 mem4 md4 Er HX HC3 HJ4 Hfrs4 Hab4 Hro4 HK4
  VnF VovF HGNB HTK HEin.
destruct HC3 as (HM3 & HRB3 & R18 & R20 & R27 & HCL3 & HW4 & HG3 & HNM3 & HA3).
destruct (rbn5_F_factsS X pos lyc2 Sc2 W2 memc3 mdc3 _ _ HX HM3) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
destruct HTK as (T1 & T2 & T3 & T4 & T5 & T6).
assert (HEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - TSB_CH_STK <= a < rbn_A X) ->
  ~ (rbn_A X + 168 <= a < rbn_A X + 180) -> ~ (rbn_F X pos + 64 <= a < rbn_F X pos + 88) ->
  aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W2) memc3 a).
{ intros a Ha H1 H2 H3. apply T1; [exact Ha | exact H1 |].
  intros HEa. destruct (HEin a HEa) as [HE | HE]; [exact (H2 HE) | exact (H3 HE)]. }
pose proof HM3 as (_ & _ & _ & Hro3 & _).
assert (HM4 : rbn_mid B X pos lyc3 Sc3 W3 mem4 md4 (fun _ => False) (rbn_sh true true false false)).
{ apply (rbn5_mid_fw X pos lyc2 Sc2 W2 memc3 mdc3 lyc3 Sc3 W3 mem4 md4 _ HX HM3 HJ4 Hfrs4 Hab4 Hro4).
  - rewrite rbn5_sh_len. lia.
  - exact HEQ.
  - intros a Ha H1 Hp. apply (T5 a); [lia | exact H1 | exact Hp].
  - intros a Hia Ho He. apply (T3 a Hia Ho He). }
destruct HRB3 as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
assert (KG : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) rbn_cl2 = false -> getr regs4 r = getr regs3 r)
  by (intros r Hr; exact (rbn5_keep_get regs3 regs4 _ r HK4 Hr)).
assert (HEQs : forall a, rbn_A X <= a < rbn_A X + 168 \/ rbn_A X + 180 <= a < rbn_A X + 320 ->
  aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W2) memc3 a) by (intros a Ha; apply HEQ; lia).
apply rbn5_cells_app in HCL3 as [HCa HCr]. apply rbn5_cells_app in HCr as [HCw HCn].
unfold rbn_rn in HCn. cbn [rbn_cells] in HCn. destruct HCn as (N0 & N8 & _ & _ & _).
unfold rbn5_cT.
split; [exact HM4|].
split.
{ unfold rbn_rbase.
  split; [rewrite KG by reflexivity; exact B2|]. split; [rewrite KG by reflexivity; exact B3|].
  split; [rewrite KG by reflexivity; exact B4|]. split; [rewrite KG by reflexivity; exact B8|].
  split; [rewrite KG by reflexivity; exact B9|]. split; [rewrite KG by reflexivity; exact B19|].
  split; [rewrite KG by reflexivity; exact B22|]. rewrite KG by reflexivity; exact B23. }
split; [rewrite KG by reflexivity; exact R18|].
split; [rewrite KG by reflexivity; exact R27|].
split.
{ apply rbn5_cells_app. split.
  { apply (rbn5_cells_kept (w_H W2) (w_H W3) memc3 mem4); [|exact HCa].
    intros a n v k Hin Hk. pose proof (rbn5_argc_rng X a n v Hin). apply HEQs; lia. }
  apply rbn5_cells_app. split.
  { apply (rbn5_cells_kept (w_H W2) (w_H W3) memc3 mem4); [|exact HCw].
    intros a n v k Hin Hk. pose proof (rbn5_rw_rng X pos 4 0 a n v Hin). apply HEQs; lia. }
  unfold rbn_rn. cbn [rbn_cells].
  split; [apply (val_mem_kept SEGS (w_H W2) (w_H W3) memc3 mem4); [intros k Hk; apply HEQs; lia | exact N0]|].
  split; [apply (val_mem_kept SEGS (w_H W2) (w_H W3) memc3 mem4); [intros k Hk; apply HEQs; lia | exact N8]|].
  split; [exact VnF|]. split; [exact VovF|]. exact I. }
split; [exact HGNB | exact HA3].
Qed.
Lemma rbn5_dash : forall X pos regs lyc1 Sc1 W1 m md,
  rbn_cx B X -> rbn5_cD X pos regs lyc1 Sc1 W1 m md ->
  SRr SEGS W1 (rbn_cfg X RBN5_D regs m md) (rbn_at6 B X).
Proof.
intros X pos regs lyc1 Sc1 W1 m md HX HD.
assert (HC0 : rbn5d_cM X pos regs lyc1 Sc1 W1 m md (rbm_stem X)) by (unfold rbn5d_cM; exact HD).
pose proof HC0 as (HM & HRB & R18 & R20 & R27 & HCL & HW4 & HG & HNM & HA).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
pose proof HM as (HJ1 & Hfrs & Hperm & Hro & _).
assert (Hsp : spZ regs = rbn_A X) by (unfold spZ; rewrite B2; unfold w64; apply unsigned_lit_small; lia).
set (M1 := rbm_stem X ++ [45]) in *.
assert (HMN : rbm_NM X = M1 ++ rbm_w4 X) by (subst M1; rewrite HNM; rewrite <- app_assoc; reflexivity).
unfold rbn_cfg.
eapply SRr_bind.
{ apply (rbn5d_p1 (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m md (ri_k X) regs (rbn_A X) HJ1 B9 ltac:(lia) ltac:(lia)). }
intros Wp cp _ (-> & regs1 & memc1 & mdc1 & -> & HJc1 & HPRES1 & GR1 & GR10 & GR11 & KM1).
assert (HC1 : rbn5d_cM X pos regs1 lyc1 Sc1 W1 memc1 mdc1 (rbm_stem X)).
{ apply (rbn5d_cM_same X pos regs regs1 lyc1 Sc1 W1 m memc1 md mdc1 (rbm_stem X) HX HC0 HJc1 KM1
    (rbn5d_KR_pres _ _ HPRES1)). }
eapply SRr_bind.
{ apply (rbn5d_call X pos regs1 lyc1 Sc1 W1 memc1 mdc1 (rbm_stem X) HX HC1 GR1 GR10 GR11). }
intros W2 c2 _ (lyc2 & Sc2 & regs2 & m2 & md2 & -> & HC2).
pose proof HC2 as (HM2 & HRB2 & R18b & R20b & R27b & HCL2 & HW4b & HGb & HNM2 & HA2).
pose proof HM2 as (HJ2 & _).
destruct (rbn5d_w4_hd X W2 m2 pos HA2 HW4b) as (Hvw4 & Hcw4).
destruct (rbn5_F_factsS X pos lyc2 Sc2 W2 m2 md2 _ _ HX HM2) as (HF4096 & HFceil & HFal & HFapp & HFpr).
eapply SRr_bind.
{ apply (rbn5d_p2 (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 m2 md2 (ri_k X) regs2 (rbn_F X pos + 32) (hd 0 (rbm_w4 X))
    HJ2 R20b ltac:(lia) ltac:(lia) Hvw4 Hcw4). }
intros W3 c3 _ (-> & regs3 & memc3 & mdc3 & -> & HJ3 & KR23 & GR10b & GR21b & GR24b & KM3).
assert (HC3 : rbn5d_cM X pos regs3 lyc2 Sc2 W2 memc3 mdc3 (rbm_stem X ++ [45])).
{ apply (rbn5d_cM_same X pos regs2 regs3 lyc2 Sc2 W2 m2 memc3 md2 mdc3 (rbm_stem X ++ [45]) HX HC2 HJ3 KM3 KR23). }
pose proof HC3 as (HM3 & HRB3 & R18c & R20c & R27c & HCL3 & HW4c & HG3 & HNM3 & HA3).
pose proof HRB3 as (B2c & B3c & B4c & B8c & B9c & B19c & B22c & B23c).
pose proof HM3 as (HJ3b & Hfrs3 & Hperm3 & Hro3 & _ & _ & _ & Hsh0_3).
assert (Hsp3 : spZ regs3 = rbn_A X) by (unfold spZ; rewrite B2c; unfold w64; apply unsigned_lit_small; lia).
set (n0 := Z.of_nat (length (firstn 23 M1))) in *.
set (ov0 := rbm_ovf 23 M1) in *.
pose proof (firstn_le_length 23 M1) as HnM1.
assert (Hn0 : 0 <= n0 <= 23) by (subst n0; lia).
assert (Hov0 : ov0 = 0 \/ ov0 = 1) by (subst ov0; unfold rbm_ovf; destruct (23 <? Z.of_nat (length M1)); [right|left]; reflexivity).
pose proof (rbn5_w4_len X HA3) as Hw4l.
pose proof (rbn5_w4_digits X HA3) as Hw4d.
assert (Hwne : rbm_w4 X <> []) by (intros E; rewrite E in Hw4l; cbn [length] in Hw4l; discriminate).
pose proof HCL3 as HCL3all.
apply rbn5_cells_app in HCL3all as [_ HCr3]. apply rbn5_cells_app in HCr3 as [_ HCn3].
unfold rbn_rn in HCn3. cbn [rbn_cells] in HCn3. destruct HCn3 as (N0 & N8 & N16 & N24 & _).
pose proof (proj1 HJ3b) as HAR3.
pose proof HJ3b as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPst3 & _).
destruct (rbn5_stk_eq X pos lyc2 Sc2 W2 memc3 mdc3 _ _ HM3) as [Elo3 Ehi3].
destruct (rbn5_stk_shadow lyc2 Sc2 W2 memc3 mdc3 (rbn_A X + 152) 28 HAR3 ltac:(lia) ltac:(lia) ltac:(lia))
  as [Hrra Hrhv].
assert (HTS : TSB_CH_STK = 4112) by reflexivity.
assert (Hlcx : rbn_lcx B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
  ((3, pos) :: ri_own X) lyc2 Sc2 W2 memc3 mdc3 (ri_k X) regs3).
{ unfold rbn_lcx. split; [exact HJ3b|]. split; [exact Hro3|]. split; [exact B3c|]. split; [exact B4c|].
  split; [rewrite B9c, B2c; reflexivity|]. split; [exact B22c|]. rewrite Hsp3, HTS.
  split; [lia|]. split; lia. }
assert (Hrec : rbn_lrec B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc2 Sc2 W2
  memc3 (spZ regs3) (spZ regs3 + 152) (rbn_F X pos + 64) 24 n0 ov0).
{ rewrite Hsp3. unfold rbn_lrec.
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold amem_range, kHighMemBeg, kHighMemEnd; lia|].
  split; [unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP; lia|].
  split; [left; lia|].
  split; [lia|]. split; [lia|]. split; [subst n0; lia|]. split; [subst n0; lia|].
  split; [subst ov0; unfold rbm_ovf; destruct (23 <? Z.of_nat (length M1)); lia|].
  split; [exact N0|].
  split; [replace (rbn_A X + 152 + 8) with (rbn_A X + 160) by lia; exact N8|].
  split; [replace (rbn_A X + 152 + 16) with (rbn_A X + 168) by lia; exact N16|].
  split; [replace (rbn_A X + 152 + 24) with (rbn_A X + 176) by lia; exact N24|].
  split; [exact Hrra|]. split; [exact Hrhv|].
  intros a Ha. split; [left; lia | apply HPst3; lia]. }
pose proof (rbn5_lbuf_name X pos lyc2 Sc2 W2 memc3 mdc3 HX HM3) as Hbuf0.
assert (Hbuf : rbn_lbuf B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) ((3, pos) :: ri_own X) lyc2 Sc2 W2
  memc3 (spZ regs3) (spZ regs3 + 152) (rbn_F X pos + 64) 24) by (rewrite Hsp3; exact Hbuf0).
pose proof (rbn5d_w4_src X pos lyc2 Sc2 W2 memc3 mdc3 HX HM3 HW4c HA3) as Hsrc.
assert (Hsep : rbn_lsep (spZ regs3) (spZ regs3 + 152) (rbn_F X pos + 64) 24 (rbn_F X pos + 32)
  (Z.of_nat (length (rbm_w4 X)) + 1)).
{ rewrite Hsp3, Hw4l. unfold rbn_lsep, TSB_CH_STK, ESTACK. lia. }
assert (HGR20 : getr regs3 20 = w64 (rbn_F X pos + 32)) by exact R20c.
assert (POST : forall nF ovF wr W4 c4,
  rbn_lpost B (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 memc3 (ri_k X) regs3 RBN_L2X rbn_cl2
    (spZ regs3 + 152) (rbn_F X pos + 64) n0 nF ovF wr W4 c4 ->
  nF = Z.of_nat (length (rbm_NB X)) -> ovF = rbm_ovf 23 (rbm_NM X) ->
  firstn 23 M1 ++ wr = rbm_NB X -> n0 + Z.of_nat (length wr) <= 23 ->
  SRr SEGS W4 c4 (rbn_at6 B X)).
{ intros nF ovF wr W4 c4
    (lyc4 & Sc4 & regs4 & mem4 & md4 & -> & HJ4 & Hfrs4 & Hab4 & Hro4 & HK4 & VnF' & VovF' & HGwr & HTK)
    EnF EovF Ewr Hbd.
  rewrite Hsp3 in VnF', VovF', HTK.
  assert (HGpref : garr8 SEGS (mrestrict (w_H W4) mem4) (rbn_F X pos + 64) (firstn 23 M1)).
  { apply (garr8_frame SEGS (mrestrict (w_H W2) memc3)); [exact HG3|]. intros a Ha.
    apply (mbyte_of_aview SEGS). destruct HTK as (T1 & _).
    apply (T1 a); [subst n0; lia | subst n0; lia |].
    cbv beta. subst n0. intros [HE | HE]; lia. }
  assert (HGNB : garr8 SEGS (mrestrict (w_H W4) mem4) (rbn_F X pos + 64) (rbm_NB X)).
  { rewrite <- Ewr. apply garr8_app. split; [exact HGpref|].
    replace (rbn_F X pos + 64 + Z.of_nat (length (firstn 23 M1))) with (rbn_F X pos + 64 + n0) by (subst n0; reflexivity).
    exact HGwr. }
  apply (rbn5_tail X pos regs4 lyc4 Sc4 W4 mem4 md4 HX).
  apply (rbn5d_l2post X pos regs3 lyc2 Sc2 W2 memc3 mdc3 lyc4 Sc4 W4 regs4 mem4 md4
    (fun a => rbn_A X + 152 + 16 <= a < rbn_A X + 152 + 28 \/
       rbn_F X pos + 64 + n0 <= a < rbn_F X pos + 64 + n0 + Z.of_nat (length wr))
    HX HC3 HJ4 Hfrs4 Hab4 Hro4 HK4).
  - replace (rbn_A X + 168) with (rbn_A X + 152 + 16) by lia. rewrite EnF in VnF'. exact VnF'.
  - replace (rbn_A X + 176) with (rbn_A X + 152 + 24) by lia. rewrite EovF in VovF'. exact VovF'.
  - exact HGNB.
  - exact HTK.
  - intros a [HE | HE]; [left; lia | right; subst n0; lia]. }
destruct (Z_le_gt_dec (n0 + Z.of_nat (length (rbm_w4 X))) 23) as [Hfit | Hovf].
- pose proof (L2F (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 memc3 mdc3 (ri_k X) regs3 (rbn_F X pos + 32) (rbn_F X pos + 64) n0 ov0
    (rbm_w4 X) ltac:(subst n0; lia)) as RUN.
  unfold rbn_L2_run in RUN.
  eapply SRr_bind.
  { apply RUN; [exact Hlcx | exact Hrec | exact Hbuf | exact Hwne | exact Hw4d | exact Hsrc | exact Hsep
      | subst n0; lia | exact Hov0 | exact GR10b | exact HGR20 | exact GR21b | exact GR24b]. }
  intros W4 c4 _ HPOST.
  destruct (rbn5d_l2_fit M1 (rbm_w4 X) ltac:(rewrite Hw4l; lia) ltac:(subst n0; lia)) as (EA & EN & EO).
  apply (POST (n0 + Z.of_nat (length (rbm_w4 X))) ov0 (rbm_w4 X) W4 c4 HPOST).
  + unfold rbm_NB. rewrite HMN. subst n0. rewrite EN. reflexivity.
  + subst ov0. rewrite HMN. exact EO.
  + unfold rbm_NB. rewrite HMN. subst n0. exact EA.
  + rewrite Hw4l. subst n0. lia.
- pose proof (L2O (ri_fq X) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc2 Sc2 W2 memc3 mdc3 (ri_k X) regs3 (rbn_F X pos + 32) (rbn_F X pos + 64) n0 ov0
    (rbm_w4 X) ltac:(subst n0; lia)) as RUN.
  unfold rbn_L2_run in RUN.
  eapply SRr_bind.
  { apply RUN; [exact Hlcx | exact Hrec | exact Hbuf | exact Hwne | exact Hw4d | exact Hsrc | exact Hsep
      | subst n0; lia | exact Hov0 | exact GR10b | exact HGR20 | exact GR21b | exact GR24b]. }
  intros W4 c4 _ HPOST.
  destruct (rbn5d_l2_ovf M1 (rbm_w4 X) ltac:(subst n0; lia)) as (EA & EN & EO).
  apply (POST 23 1 (firstn (Z.to_nat (23 - n0)) (rbm_w4 X)) W4 c4 HPOST).
  + unfold rbm_NB. rewrite HMN. subst n0. exact EN.
  + subst ov0. rewrite HMN. exact EO.
  + unfold rbm_NB. rewrite HMN. subst n0. exact EA.
  + rewrite length_firstn. subst n0. lia.
Qed.
Lemma rbn5f_aj_strlen_at : forall (fq : YK11.FPState) pc,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI pc ->
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x n (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 x -> 0 < x -> 0 <= n -> n + 1 < 2 ^ 32 -> x + n + 1 <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  first_byte SEGS W memT x (n + 1) 0 n -> src_ok SEGS W regsT memT x (n + 1) -> amem_range x (n + 1) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (n + 1) ->
  shadow_hull_vis (aview SEGS (w_H W) memT) x (n + 1) ->
  (forall a, x + n < a < x + n - (x + n) mod 8 + 8 -> aview SEGS (w_H W) memT a <> None) ->
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memT ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
      c2 = mkCfg (mkst (fx := fq) regs2 raw mem2 (seg_rom SEGS)) md2 /\
      ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
      aregs_preserved regsT regs2 /\ getr regs2 10 = w64 n /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
         aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros fq pc AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x n o raw
  HJ Ha0 Hx0 Hn0 Hn32 Hxn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsrc Hmr Hrad Hhv Htl Hcv.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
  rewrite Hra. exact Hraw. }
eapply SRr_mono.
{ exact (AS lyc Sc W regsT memT mdc x n HPRE Ha0 Hx0 Hn0 Hn32 Hxn Hfb Hsrc Hmr Hrad Hhv Htl Hcv). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS Hsegs STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres | exact Hfr].
Qed.
Definition rbn5f_ss : sstate :=
  mkSS (AF_both3_reac_box_name + RBN_P5) sr_atoms
    [YP09.mkRegion (Some 9%nat) 200 208 0 0 [YP09.mkChunk 200 (CVal 8 (SLit 4))]] None (mkFacts [] [] []).
Lemma rbn5f_entry : forall (fq : YK11.FPState) X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P,
  rbn_cx B X -> rbn_st5 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) rbn5f_ss
    (restrict (w_H W1) (mkst (fx := fq) regs1 (Z_to_bv 64 (BASE + (AF_both3_reac_box_name + RBN_P5))) memc1
      (seg_rom SEGS))).
Proof.
intros fq X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX H5.
pose proof H5 as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22 & R23) & R18 & R20 & R27 & R25 & HC & _).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & _).
pose proof asan_consts as (C1 & _).
assert (B9 : bv_unsigned (ew (Eimg (Ereg regs1 [])) 9%nat) = rbn_A X)
  by (rewrite (ew_Eimg_Ereg_nat regs1 [] 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (V200 : val_mem SEGS (mrestrict (w_H W1) memc1) (rbn_A X + 200) 8 4).
{ apply (rbn5_cells_in _ _ _ _ _ HC). apply in_or_app; right. apply in_or_app; left. right; right; left; reflexivity. }
rewrite restrict_mkst_fx. unfold rbn5f_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ (rbn_A X) 200 8 _ 4); [reflexivity | zside | zside |].
  change (N.to_nat 8) with 8%nat. exact V200.
- cbn. tauto.
- split; [exact I|]. split; exact I.
Qed.
Lemma rbn5f_view : forall (H : word -> bool) (m : word -> option byte) b l j,
  garr8 SEGS (mrestrict H m) b l -> (j < length l)%nat ->
  aview SEGS H m (b + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m b l j HG Hj. destruct (HG j Hj) as [Hv Hr]. exact (rbn5_aview_vm1 _ _ _ _ Hv Hr).
Qed.
Lemma rbn5f_fb : forall W (m : word -> option byte) p s, rbn_str W m p s ->
  first_byte SEGS W m p (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)).
Proof.
intros W m p s (Hch & Hg & _).
assert (Hl : length (s ++ [0]) = S (length s)) by (rewrite length_app; cbn [length]; lia).
split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) s 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rbn5f_view _ m p (s ++ [0]) (Z.to_nat i) Hg ltac:(lia)). f_equal.
    rewrite app_nth1 by lia. reflexivity.
  + assert (Hin : In (nth (Z.to_nat i) s 0) s) by (apply nth_In; lia).
    pose proof (proj1 (Forall_forall _ _) Hch _ Hin) as Hb. cbv beta in Hb. lia.
- intros _.
  rewrite (rbn5f_view _ m p (s ++ [0]) (length s) Hg ltac:(lia)). f_equal.
  rewrite app_nth2 by lia. replace (length s - length s)%nat with 0%nat by lia. reflexivity.
Qed.
Lemma rbn5f_alu_add : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= a + b < 2 ^ 64 ->
  alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
intros a b Ha Hb Hab. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small a), (Z.mod_small b) by lia.
reflexivity.
Qed.
Lemma rbn5f_alu_not : forall a, 0 <= a < 2 ^ 64 ->
  alu64 ALU_XOR (Z_to_bv 64 a) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - a).
Proof.
intros a Ha. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small a) by lia.
change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1). rewrite lxor_allones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma rbn5f_den_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma rbn5f_den_alu : forall E op a b, sv_denot E (SAlu op a b) = alu64 op (sv_denot E a) (sv_denot E b).
Proof. reflexivity. Qed.
Lemma rbn5f_den_lit : forall E z, sv_denot E (SLit z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.
Lemma rbn5f_den_add : forall E n m c v w, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 w ->
  0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n c) (SOff m 0)) = Z_to_bv 64 (v + c + w).
Proof.
intros E n m c v w Hn Hm H1 H2. cbn [sv_denot]. rewrite Hn, Hm, Z.add_0_r.
rewrite (unsigned_lit_small v) by lia. rewrite (unsigned_lit_small w) by lia.
apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma rbn5f_den_code : forall E k, img_env VAL A_LIM E -> sv_denot E (SOff 240%nat k) = Z_to_bv 64 (BASE + k).
Proof. intros E k HE. exact (codeptr_val E k HE). Qed.
Lemma rbn5f_ltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  branch_taken BC_LTU (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
intros a b Ha Hb. cbn [branch_taken]. unfold bv_ltu. rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma rbn5f_amem_sub : forall p n p' n', amem_range p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  amem_range p' n'.
Proof. intros p n p' n' H H1 H2 H3. unfold amem_range in *. lia. Qed.
Lemma rbn5f_ra_sub : forall rd Bs a n a' n',
  range_addressable rd Bs a n -> a <= a' -> a' + n' <= a + n -> range_addressable rd Bs a' n'.
Proof. intros rd Bs a n a' n' H H1 H2 x Hx. apply H. lia. Qed.
Lemma rbn5f_shv_sub : forall rd a n a' n',
  shadow_hull_vis rd a n -> a <= a' -> a' + n' <= a + n -> 0 < n' -> 0 <= a ->
  shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' H H1 H2 H3 H4 s Hs. apply H.
assert (M : forall u v, u <= v -> shadow_addr u / 8 * 8 <= shadow_addr v / 8 * 8).
{ intros u v Huv. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. apply shadow_mono. lia. }
pose proof (M a a' H1). pose proof (M (a' + n' - 1) (a + n - 1) ltac:(lia)). lia.
Qed.
Lemma rbn5f_rn_rng : forall X pos n0 ov0 a n v, In (a, n, v) (rbn_rn X pos n0 ov0) ->
  rbn_A X + 152 <= a /\ a + Z.of_nat n <= rbn_A X + 180.
Proof.
intros X pos n0 ov0 a n v H. unfold rbn_rn in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn5f_low_out : forall X a, rbn_cx B X -> 0 <= a < kHighMemBeg -> ~ (rbn_A X - 8192 <= a < rbn_A X).
Proof.
intros X a HX Ha.
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). lia.
Qed.
Lemma rbn5f_P_out : forall X pos W1 memc1 P a w,
  rbn_cx B X -> rbn_stp X pos W1 memc1 P -> 0 <= w <= 8192 ->
  P <= a < P + Z.of_nat (length (rbm_stem X)) + 8 -> ~ (rbn_A X - w <= a < rbn_A X).
Proof.
intros X pos W1 memc1 P a w HX HSTP Hw Ha.
destruct (rbn5_P_sep X pos P (proj2 HSTP)) as (_ & Hs).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
destruct Hs as [Hl | Hr]; lia.
Qed.
Lemma rbn5f_str_keep : forall X pos W1 memc1 m' P,
  rbn_cx B X -> rbn_stp X pos W1 memc1 P ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X) ->
     aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) memc1 a) ->
  rbn_str W1 m' P (rbm_stem X).
Proof.
intros X pos W1 memc1 m' P HX HSTP HK.
pose proof (proj1 HSTP) as HSTR.
pose proof HSTR as (_ & _ & HP0 & HP63 & _).
pose proof (Z.mod_pos_bound (P + Z.of_nat (length (rbm_stem X))) 8 ltac:(lia)) as M1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (rbn5_str_kept W1 W1 memc1 m' P (rbm_stem X) HSTR).
intros x Hx [Hin | Hsh].
- apply HK; [exact Hx|]. exact (rbn5f_P_out X pos W1 memc1 P x 8192 HX HSTP ltac:(lia) ltac:(lia)).
- apply HK; [exact Hx|]. apply (rbn5f_low_out X x HX). unfold kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma rbn5f_cells_keep : forall X pos (W1 : world SEGS) memc1 m' n0 ov0,
  rbn_cx B X ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X) ->
     aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) memc1 a) ->
  rbn_cells (mrestrict (w_H W1) memc1) (rbn_argc X ++ rbn_rw X pos 4 0 ++ rbn_rn X pos n0 ov0) ->
  rbn_cells (mrestrict (w_H W1) m') (rbn_argc X ++ rbn_rw X pos 4 0 ++ rbn_rn X pos n0 ov0).
Proof.
intros X pos W1 memc1 m' n0 ov0 HX HK HC.
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (rbn5_cells_kept (w_H W1) (w_H W1) memc1 m'); [|exact HC].
intros a n v kk Hin Hk.
assert (Hr : rbn_A X <= a /\ a + Z.of_nat n <= rbn_A X + 212).
{ apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - destruct (rbn5_argc_rng X a n v Hin). lia.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (rbn5_rw_rng X pos 4 0 a n v Hin). lia.
    + destruct (rbn5f_rn_rng X pos n0 ov0 a n v Hin). lia. }
apply HK; lia.
Qed.
Lemma rbn5f_garr_keep : forall X pos lyc1 Sc1 W1 memc1 mdc1 m' d l,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true false false) ->
  rbn_F X pos <= d -> d + Z.of_nat (length l) <= rbn_F X pos + 512 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X) ->
     aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) memc1 a) ->
  garr8 SEGS (mrestrict (w_H W1) memc1) d l -> garr8 SEGS (mrestrict (w_H W1) m') d l.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 m' d l HX HM H1 H2 HK HG.
destruct (rbn5_F_factsS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (garr8_frame SEGS (mrestrict (w_H W1) memc1)); [exact HG|].
intros a Ha. apply (mbyte_of_aview SEGS). apply HK; lia.
Qed.
Lemma rbn5f_mid_keep : forall X pos lyc1 Sc1 W1 memc1 mdc1 m' md',
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true false false) ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m' md' (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X) ->
     aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) memc1 a) ->
  rbn_mid B X pos lyc1 Sc1 W1 m' md' (fun _ => False) (rbn_sh true true false false).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 m' md' HX HM HJ2 HK.
assert (HST : rbn5_step X lyc1 Sc1 W1 W1 memc1 m' (fun _ => False)).
{ apply (rbn5_step_glob X pos lyc1 Sc1 W1 mdc1 _ W1 memc1 m' (fun _ => False) HX HM);
    [intros a [] | intros a Ha Hw _; apply HK; [exact Ha | lia]]. }
apply (rbn5_mid_step X pos lyc1 Sc1 lyc1 Sc1 W1 W1 memc1 mdc1 m' md' _ _ (fun _ => False) HX HM HJ2
  eq_refl (Permutation_refl _) HST ltac:(intros a [])).
apply (rbn5_sh_kept X pos lyc1 Sc1 W1 W1 memc1 mdc1 m' _ (fun _ => False) _ HX HM HST eq_refl
  ltac:(rewrite rbn5_sh_len; lia)).
intros j Hj. right. split; [intros [] | reflexivity].
Qed.
Lemma rbn5f_w4_shadow : forall X pos lyc1 Sc1 W1 memc1 mdc1 m',
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true true false false) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X) ->
     aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) memc1 a) ->
  range_addressable (aview SEGS (w_H W1) m') SHADOW_OFF (rbn_F X pos + 32) 4 /\
  shadow_hull_vis (aview SEGS (w_H W1) m') (rbn_F X pos + 32) 4.
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 m' HX HM HK.
destruct (rbn5_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM)
  as (HF4096 & HFceil & HF64 & HFapp & HFpr & _ & ESH & SH8 & SHlo & SHhi).
pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HM))))))) as HSh.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF8 : rbn_F X pos mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 64 ltac:(lia)) as D1. rewrite HF64, Z.add_0_r in D1.
  rewrite D1. replace (64 * (rbn_F X pos / 64)) with ((8 * (rbn_F X pos / 64)) * 8) by lia.
  apply Z.mod_mul. lia. }
assert (Hd8 : (rbn_F X pos + 32) mod 8 = 0).
{ pose proof (Z.div_mod (rbn_F X pos) 8 ltac:(lia)) as D. rewrite HF8, Z.add_0_r in D. rewrite D.
  replace (8 * (rbn_F X pos / 8) + 32) with ((rbn_F X pos / 8 + 4) * 8) by lia. apply Z.mod_mul. lia. }
assert (Esh : shadow_of_addr SHADOW_OFF (rbn_F X pos + 32) = rbn_SH X pos + 4).
{ unfold shadow_of_addr, rbn_SH, shadow_addr. replace 32 with (4 * 8) by lia.
  rewrite Z.div_add by lia. lia. }
assert (Hlow : forall j, 0 <= j < 64 -> aview SEGS (w_H W1) m' (rbn_SH X pos + j) =
   Some (nth (Z.to_nat j) (rbn_sh true true false false) 0)).
{ intros j Hj. rewrite (HK (rbn_SH X pos + j)); [exact (HSh j ltac:(rewrite rbn5_sh_len; lia)) | lia | ].
  apply (rbn5f_low_out X _ HX). lia. }
split.
- apply (rbn5f_ra_sub _ _ (rbn_F X pos + 32) 5); [|lia|lia].
  apply (range_addressable_partial _ SHADOW_OFF (rbn_F X pos + 32) 5); [|exact Hd8 | lia].
  rewrite Esh, (Hlow 4 ltac:(lia)). reflexivity.
- intros s Hs.
  assert (E1 : shadow_addr (rbn_F X pos + 32) = rbn_SH X pos + 4) by exact Esh.
  assert (E2 : shadow_addr (rbn_F X pos + 32 + 4 - 1) = rbn_SH X pos + 4).
  { unfold rbn_SH, shadow_addr. replace (rbn_F X pos + 32 + 4 - 1) with (rbn_F X pos + 35) by lia.
    pose proof (Z.div_mod (rbn_F X pos) 8 ltac:(lia)) as D. rewrite HF8, Z.add_0_r in D.
    replace (rbn_F X pos + 35) with (8 * (rbn_F X pos / 8) + 35) by lia.
    replace (8 * (rbn_F X pos / 8) + 35) with (35 + (rbn_F X pos / 8) * 8) by lia.
    rewrite Z.div_add by lia. change (35 / 8) with 4. lia. }
  rewrite E1, E2 in Hs.
  pose proof (Z.div_mod (rbn_SH X pos) 8 ltac:(lia)) as DS. rewrite SH8, Z.add_0_r in DS.
  assert (ER : (rbn_SH X pos + 4) / 8 * 8 = rbn_SH X pos).
  { replace (rbn_SH X pos + 4) with (4 + (rbn_SH X pos / 8) * 8) by lia.
    rewrite Z.div_add by lia. change (4 / 8) with 0. lia. }
  replace s with (rbn_SH X pos + (s - rbn_SH X pos)) by lia.
  rewrite ER in Hs. rewrite (Hlow (s - rbn_SH X pos) ltac:(lia)). discriminate.
Qed.
Lemma rbn5f_skipn_iff : forall (s w : list Z), (4 <= length s)%nat -> length w = 4%nat ->
  (skipn (length s - 4) s = w <-> forall i, (i < 4)%nat -> nth (length s - 4 + i) s 0 = nth i w 0).
Proof.
intros s w Hs Hw. split.
- intros <- i Hi. rewrite nth_skipn. reflexivity.
- intros H. apply (nth_ext _ _ 0 0); [rewrite length_skipn; lia|].
  intros j Hj. rewrite length_skipn in Hj. rewrite nth_skipn. apply H. lia.
Qed.
Definition rbn5f_keep : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 27]%bv.
Lemma rbn5f_cD_of : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regs' m' md',
  rbn_cx B X -> rbn_st5 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m' md' (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X) ->
     aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) memc1 a) ->
  (forall r, In r rbn5f_keep -> getr regs' r = getr regs1 r) ->
  rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X ->
  rbn5_cD X pos regs' lyc1 Sc1 W1 m' md'.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regs' m' md' HX H5 HJ' HK HR HNM.
pose proof H5 as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22 & R23) & R18 & R20 & R27 & R25 & HC & HW4 & HNB & HSTP & HA).
pose proof (rbn5_w4_len X HA) as HW4L.
split; [exact (rbn5f_mid_keep X pos lyc1 Sc1 W1 memc1 mdc1 m' md' HX HM HJ' HK)|].
split.
{ split; [rewrite (HR 2%bv ltac:(cbv; tauto)); exact R2|].
  split; [rewrite (HR 3%bv ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (HR 4%bv ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (HR 8%bv ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (HR 9%bv ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (HR 19%bv ltac:(cbv; tauto)); exact R19|].
  split; [rewrite (HR 22%bv ltac:(cbv; tauto)); exact R22 | rewrite (HR 23%bv ltac:(cbv; tauto)); exact R23]. }
split; [rewrite (HR 18%bv ltac:(cbv; tauto)); exact R18|].
split; [rewrite (HR 20%bv ltac:(cbv; tauto)); exact R20|].
split; [rewrite (HR 27%bv ltac:(cbv; tauto)); exact R27|].
split; [exact (rbn5f_cells_keep X pos W1 memc1 m' _ _ HX HK HC)|].
split.
{ apply (rbn5f_garr_keep X pos lyc1 Sc1 W1 memc1 mdc1 m' (rbn_F X pos + 32) (rbm_w4 X ++ [0]) HX HM
    ltac:(lia) ltac:(rewrite length_app, HW4L; cbn [length]; lia) HK HW4). }
split.
{ apply (rbn5f_garr_keep X pos lyc1 Sc1 W1 memc1 mdc1 m' (rbn_F X pos + 64) (firstn 23 (rbm_stem X)) HX HM
    ltac:(lia) ltac:(rewrite length_firstn; lia) HK HNB). }
split; [exact HNM | exact HA].
Qed.
Lemma rbn5f_cT_of : forall X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regs' m' md',
  rbn_cx B X -> rbn_st5 B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 m' md' (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X) ->
     aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) memc1 a) ->
  (forall r, In r rbn5f_keep -> getr regs' r = getr regs1 r) ->
  rbm_NM X = rbm_stem X ->
  rbn5_cT X pos regs' lyc1 Sc1 W1 m' md'.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P regs' m' md' HX H5 HJ' HK HR HNM.
pose proof H5 as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22 & R23) & R18 & R20 & R27 & R25 & HC & HW4 & HNB & HSTP & HA).
split; [exact (rbn5f_mid_keep X pos lyc1 Sc1 W1 memc1 mdc1 m' md' HX HM HJ' HK)|].
split.
{ split; [rewrite (HR 2%bv ltac:(cbv; tauto)); exact R2|].
  split; [rewrite (HR 3%bv ltac:(cbv; tauto)); exact R3|].
  split; [rewrite (HR 4%bv ltac:(cbv; tauto)); exact R4|].
  split; [rewrite (HR 8%bv ltac:(cbv; tauto)); exact R8|].
  split; [rewrite (HR 9%bv ltac:(cbv; tauto)); exact R9|].
  split; [rewrite (HR 19%bv ltac:(cbv; tauto)); exact R19|].
  split; [rewrite (HR 22%bv ltac:(cbv; tauto)); exact R22 | rewrite (HR 23%bv ltac:(cbv; tauto)); exact R23]. }
split; [rewrite (HR 18%bv ltac:(cbv; tauto)); exact R18|].
split; [rewrite (HR 27%bv ltac:(cbv; tauto)); exact R27|].
unfold rbm_NB. rewrite HNM.
split; [exact (rbn5f_cells_keep X pos W1 memc1 m' _ _ HX HK HC)|].
split; [|exact HA].
apply (rbn5f_garr_keep X pos lyc1 Sc1 W1 memc1 mdc1 m' (rbn_F X pos + 64) (firstn 23 (rbm_stem X)) HX HM
  ltac:(lia) ltac:(rewrite length_firstn; lia) HK HNB).
Qed.
Ltac rbn5f_awr :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac rbn5f_keepstep HFx K :=
  cbn [ms_mem mkst] in HFx;
  lazymatch type of HFx with
  | frame_of ?E0 ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1) =>
      let rs' := eval vm_compute in rs in
      change rs with rs' in HFx;
      assert (K : forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m1 a = aview SEGS H m0 a)
        by (intros a Ha; apply (rbn5_kept_frame E0 rs' H m0 m1 (fun _ => False) HFx);
            [ intros b (r & Hr & Hw);
              first [ destruct Hr
                    | destruct Hr as [<- | Hr];
                      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia | destruct Hr ] ]
            | exact Ha | intros [] ])
  end.
Ltac rbn5f_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.
Theorem rbn_seg5 : rbn_seg5_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX H5.
pose proof H5 as (HM & (R2 & R3 & R4 & R8 & R9 & R19 & R22 & R23) & R18 & R20 & R27 & R25 & HC & HW4 & HNB & HSTP & HA).
pose proof HM as (HJ1 & Hfrs1 & Hperm1 & Hro1 & HKP1 & HFr1 & HFL1 & HSh1).
pose proof HSTP as (HSTR & HSEP).
pose proof HSTR as (Hchars & Hgarr & HP0 & HP63 & Hlen32 & Hamr & Hraddr & Hhull & Htail).
destruct (rbn5_A_rngS X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10).
destruct (rbn5_A_rng X HX) as (_ & _ & _ & _ & _ & _ & _ & HSP0).
destruct (rbn5_F_factsS X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF4096 & HFceil & HFal & HFapp & HFpr).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rbn5_w4_len X HA) as HW4L.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HLEN : length (rbm_stem X ++ [0]) = S (length (rbm_stem X)))
  by (rewrite length_app; cbn [length]; lia).
assert (HW4P : length (rbm_w4 X ++ [0]) = 5%nat) by (rewrite length_app, HW4L; cbn [length]; lia).
assert (HFmem : amem_range (rbn_F X pos + 32) 4)
  by (unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia).
assert (HO16 : (rbn_A X - ri_sp0 X) mod 16 = 0).
{ apply Z.mod_divide in AR4; [|lia]. apply Z.mod_divide in HSP0; [|lia].
  destruct AR4 as (q1 & Hq1). destruct HSP0 as (q2 & Hq2).
  replace (rbn_A X - ri_sp0 X) with ((2 * q1 - q2) * 16) by lia. apply Z.mod_mul. lia. }
pose proof (rbn5f_entry (ri_fq X) X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX H5) as HS.
unfold rbn_cfg, cfg_at, w64.
replace (BASE + AF_both3_reac_box_name + RBN_P5) with (BASE + (AF_both3_reac_box_name + RBN_P5)) by lia.
set (fq := ri_fq X) in *.
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call fq _ _ _ _ _ B LAWS) as RUNC.
pose proof (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS) as RUNTOP.
pose (BR := paj_branch (fx := fq) (PI := PI)).
assert (HAE : env_agree 32 (Ereg regs1 []) (Eimg (Ereg regs1 []))) by apply rbn5_env_agree.
remember (Eimg (Ereg regs1 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
paj_run_shc RUNP RUNC HS HJ1.
{ rbn5f_awr. }
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha. apply (rbn5_kept_frame E (ss_mem rbn5f_ss) (w_H W1) memc1 (ms_mem ms) (fun _ => False) HFr);
    [| exact Ha | intros []].
  intros b (r & Hr & Hw). unfold rbn5f_ss in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
clear HF HFr HG.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
rewrite (EE 25%nat 25%bv eq_refl), R25 in Ra0. rewrite (EE 2%nat 2%bv eq_refl), R2 in Rsp.
rewrite (EE 3%nat 3%bv eq_refl), R3 in Rgp. rewrite (EE 4%nat 4%bv eq_refl), R4 in Rtp.
assert (Qsp : spZ (ms_regs ms) = ri_sp0 X + (rbn_A X - ri_sp0 X))
  by (unfold spZ; rewrite Rsp; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X) ->
   aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) memc1 a) by (intros a Ha _; exact (K1 a Ha)).
pose proof (rbn5f_str_keep X pos W1 memc1 (ms_mem ms) P HX HSTP KW) as HSTR1.
pose proof HSTR1 as (Hch1 & Hg1 & _ & _ & _ & _ & Hra1 & Hhv1 & Htl1).
eapply SRr_bind.
{ eapply (rbn5f_aj_strlen_at fq (SIGMA AS___interceptor_trampoline_strlen) (ASTRLEN fq) W1 (ms_regs ms)
    (ms_mem ms) _ _ _ _ _ _ _ _ _ _ _ _ _ P (Z.of_nat (length (rbm_stem X))) (rbn_A X - ri_sp0 X) _ HJ1).
  - exact Ra0.
  - exact HP0.
  - lia.
  - lia.
  - lia.
  - exact Qsp.
  - exact HO16.
  - lia.
  - rewrite HES. lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact (rbn5f_fb W1 (ms_mem ms) P (rbm_stem X) HSTR1).
  - intros a Ha. split.
    + replace a with (P + Z.of_nat (Z.to_nat (a - P))) by lia.
      rewrite (rbn5f_view _ (ms_mem ms) P (rbm_stem X ++ [0]) (Z.to_nat (a - P)) Hg1 ltac:(lia)). discriminate.
    + pose proof (rbn5f_P_out X pos W1 memc1 P a 4096 HX HSTP ltac:(lia) ltac:(lia)) as Hout.
      rewrite Qsp, HES. lia.
  - exact Hamr.
  - exact Hra1.
  - exact Hhv1.
  - exact Htl1.
  - intros a Ha. rewrite (K1 a ltac:(unfold MC_CONSTS_LO, MC_CONSTS_HI in Ha; lia)).
    exact (rbn5_consts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM a Ha). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hfr2).
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X) ->
   aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha Hn. rewrite (Hfr2 a Ha ltac:(rewrite HES; lia)). exact (K1 a Ha). }
jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H W1) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 32)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs1 []) E2) by (rewrite HE2; env_agree_chain HAE).
assert (A36 : ew E2 36 = getr regs2 10) by (rewrite HE2; reflexivity).
clear HE2.
assert (E36 : ew E2 36 = Z_to_bv 64 (Z.of_nat (length (rbm_stem X)))) by (rewrite A36; exact Ha02).
assert (E225 : ew E2 25 = Z_to_bv 64 P)
  by (rewrite OLD2 by lia; rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E220 : ew E2 20 = Z_to_bv 64 (rbn_F X pos + 32))
  by (rewrite OLD2 by lia; rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E2 2 = Z_to_bv 64 (rbn_A X))
  by (rewrite OLD2 by lia; rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E23 : ew E2 3 = Z_to_bv 64 (as_gp B))
  by (rewrite OLD2 by lia; rewrite (EE 3%nat 3%bv eq_refl); exact R3).
assert (E24 : ew E2 4 = Z_to_bv 64 (as_tp B))
  by (rewrite OLD2 by lia; rewrite (EE 4%nat 4%bv eq_refl); exact R4).
psrr_branch_pi RUNP BR HS.
{ rewrite rbn5f_den_off0, rbn5f_den_lit, E36 in Hc.
  rewrite rbn5f_ltu_lit in Hc by lia. apply Z.ltb_lt in Hc.
  assert (HNMd : rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X)
    by (destruct (rbn5_NM_cases X) as [(Hge & _ & _) | (_ & HEd)]; [lia | exact HEd]).
  paj_run_to_sh RUNTOP HS HJ2 14936.
  { rbn5f_awr. }
  rbn5f_keepstep HFr K3. clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 [] rbn5f_keep HS HAE2 ltac:(vm_compute; reflexivity)) as HR.
  cbn [ms_regs restrict] in HR.
  pmkst HS.
  replace (BASE + 14936) with (BASE + AF_both3_reac_box_name + RBN5_D)
    by (unfold AF_both3_reac_box_name, RBN5_D; lia).
  apply (rbn5_dash X pos _ lyc1 Sc1 W1 _ _ HX).
  apply (rbn5f_cD_of X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P _ _ _ HX H5 HJ2);
    [ intros a Ha Hn; rewrite (K3 a Ha); exact (K2 a Ha Hn) | exact HR | exact HNMd ]. }
rewrite rbn5f_den_off0, rbn5f_den_lit, E36 in Hc.
rewrite rbn5f_ltu_lit in Hc by lia. apply Z.ltb_ge in Hc.
paj_run_sh RUNP HS HJ2.
{ rbn5f_awr. }
rbn5f_keepstep HFr K3. clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite !rbn5f_den_alu, !rbn5f_den_off0, !rbn5f_den_lit, E225, E36 in Hc0.
  rewrite rbn5f_alu_not in Hc0 by lia. rewrite rbn5f_ltu_lit in Hc0 by lia.
  apply Z.ltb_lt in Hc0. lia. }
paj_run_sh RUNP HS HJ2.
{ rbn5f_awr. }
rbn5f_keepstep HFr K4. clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite !rbn5f_den_alu, !rbn5f_den_off0, !rbn5f_den_lit, E225, E36 in Hc1.
  rewrite rbn5f_alu_add in Hc1 by lia. rewrite rbn5f_ltu_lit in Hc1 by lia.
  apply Z.ltb_lt in Hc1. lia. }
paj_run_shc RUNP RUNC HS HJ2.
{ rbn5f_awr. }
rbn5f_keepstep HFr K5. clear HF HFr HG.
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X) ->
   aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) memc1 a)
  by (intros a Ha Hn; rewrite (K5 a Ha), (K4 a Ha), (K3 a Ha); exact (K2 a Ha Hn)).
pose proof (rbn5f_str_keep X pos W1 memc1 (ms_mem ms2) P HX HSTP KB) as HSTR2.
pose proof HSTR2 as (Hch2 & Hg2 & _ & _ & _ & _ & Hra2 & Hhv2 & Htl2).
pose proof (rbn5f_garr_keep X pos lyc1 Sc1 W1 memc1 mdc1 (ms_mem ms2) (rbn_F X pos + 32) (rbm_w4 X ++ [0])
  HX HM ltac:(lia) ltac:(rewrite HW4P; lia) KB HW4) as HW42.
destruct (rbn5f_w4_shadow X pos lyc1 Sc1 W1 memc1 mdc1 (ms_mem ms2) HX HM KB) as (HRA4 & HHV4).
pmkst HS.
rbn5f_reg HS (10%bv : bv 5) Rb0. rbn5f_reg HS (11%bv : bv 5) Rb1. rbn5f_reg HS (12%bv : bv 5) Rb2.
rbn5f_reg HS (1%bv : bv 5) Rb1a. rbn5f_reg HS (2%bv : bv 5) Rb2s.
rbn5f_reg HS (3%bv : bv 5) Rb3. rbn5f_reg HS (4%bv : bv 5) Rb4.
rewrite (rbn5f_den_add E2 25 36 (-4) P (Z.of_nat (length (rbm_stem X))) E225 E36
  ltac:(lia) ltac:(lia)) in Rb0.
rewrite rbn5f_den_off0, E220 in Rb1. rewrite rbn5f_den_lit in Rb2.
rewrite (rbn5f_den_code E2 14932 HEI2) in Rb1a.
rewrite rbn5f_den_off0, E22 in Rb2s. rewrite rbn5f_den_off0, E23 in Rb3.
rewrite rbn5f_den_off0, E24 in Rb4.
eapply SRr_bind.
{ eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA AS___interceptor_trampoline_bcmp) (ABCMP fq) W1
    (ms_regs ms2) (ms_mem ms2) (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X)
    (ri_md0 X) ((3, pos) :: ri_own X) lyc1 Sc1 _ (ri_k X)
    (P + -4 + Z.of_nat (length (rbm_stem X))) (rbn_F X pos + 32) 4 (rbn_A X - ri_sp0 X) _ HJ2).
  - rewrite Rb0. reflexivity.
  - rewrite Rb1. reflexivity.
  - rewrite Rb2. reflexivity.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Rb2s. rewrite unsigned_lit_small by lia. lia.
  - exact HO16.
  - lia.
  - rewrite HES. lia.
  - rewrite Rb3. reflexivity.
  - rewrite Rb4. reflexivity.
  - exact Rb1a.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split.
    + replace a with (P + Z.of_nat (Z.to_nat (a - P))) by lia.
      rewrite (rbn5f_view _ (ms_mem ms2) P (rbm_stem X ++ [0]) (Z.to_nat (a - P)) Hg2 ltac:(lia)). discriminate.
    + pose proof (rbn5f_P_out X pos W1 memc1 P a 4096 HX HSTP ltac:(lia) ltac:(lia)) as Hout.
      unfold spZ. rewrite Rb2s, unsigned_lit_small, HES by lia. lia.
  - intros a Ha. split.
    + replace a with (rbn_F X pos + 32 + Z.of_nat (Z.to_nat (a - (rbn_F X pos + 32)))) by lia.
      rewrite (rbn5f_view _ (ms_mem ms2) (rbn_F X pos + 32) (rbm_w4 X ++ [0])
        (Z.to_nat (a - (rbn_F X pos + 32))) HW42 ltac:(lia)). discriminate.
    + unfold spZ. rewrite Rb2s, unsigned_lit_small, HES by lia. lia.
  - intros a Ha.
    pose proof (rbn5f_P_out X pos W1 memc1 P a 8192 HX HSTP ltac:(lia) ltac:(lia)) as Hout.
    rewrite HES. lia.
  - intros a Ha. rewrite HES. lia.
  - exact (rbn5f_amem_sub P (Z.of_nat (length (rbm_stem X)) + 1)
      (P + -4 + Z.of_nat (length (rbm_stem X))) 4 Hamr ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact HFmem.
  - exact (rbn5f_ra_sub _ _ P (Z.of_nat (length (rbm_stem X)) + 1)
      (P + -4 + Z.of_nat (length (rbm_stem X))) 4 Hra2 ltac:(lia) ltac:(lia)).
  - intros _. exact (rbn5f_shv_sub _ P (Z.of_nat (length (rbm_stem X)) + 1)
      (P + -4 + Z.of_nat (length (rbm_stem X))) 4 Hhv2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact HRA4.
  - intros _. exact HHV4. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & v & -> & HJ3 & HP3 & Hv3 & Hcmp & Hfr3 & Hpres3).
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (rbn_A X - 8192 <= a < rbn_A X) ->
   aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha Hn. rewrite (Hfr3 a Ha ltac:(rewrite HES; lia)). exact (KB a Ha Hn). }
assert (VX : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W1) (ms_mem ms2) (P + -4 + Z.of_nat (length (rbm_stem X)) + i) =
  Some (nth (length (rbm_stem X) - 4 + Z.to_nat i)%nat (rbm_stem X) 0)).
{ intros i Hi.
  replace (P + -4 + Z.of_nat (length (rbm_stem X)) + i)
    with (P + Z.of_nat (length (rbm_stem X) - 4 + Z.to_nat i)%nat) by lia.
  rewrite (rbn5f_view _ (ms_mem ms2) P (rbm_stem X ++ [0]) (length (rbm_stem X) - 4 + Z.to_nat i)%nat
    Hg2 ltac:(lia)). f_equal.
  rewrite app_nth1 by lia. reflexivity. }
assert (VY : forall i, 0 <= i < 4 ->
  aview SEGS (w_H W1) (ms_mem ms2) (rbn_F X pos + 32 + i) = Some (nth (Z.to_nat i) (rbm_w4 X) 0)).
{ intros i Hi.
  replace (rbn_F X pos + 32 + i) with (rbn_F X pos + 32 + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (rbn5f_view _ (ms_mem ms2) (rbn_F X pos + 32) (rbm_w4 X ++ [0]) (Z.to_nat i) HW42 ltac:(lia)).
  f_equal. rewrite app_nth1 by lia. reflexivity. }
assert (Hbytes : v = w64 0 <-> skipn (length (rbm_stem X) - 4) (rbm_stem X) = rbm_w4 X).
{ rewrite Hcmp. rewrite (rbn5f_skipn_iff (rbm_stem X) (rbm_w4 X) ltac:(lia) HW4L). split.
  - intros Hall i Hi. specialize (Hall (Z.of_nat i) ltac:(lia)).
    rewrite (VX (Z.of_nat i) ltac:(lia)), (VY (Z.of_nat i) ltac:(lia)) in Hall.
    injection Hall as Hall. rewrite Nat2Z.id in Hall. exact Hall.
  - intros Hall i Hi. rewrite (VX i Hi), (VY i Hi). f_equal. apply Hall. lia. }
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W1) mem3) HP3 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E2 48 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (HAE3 : env_agree 32 (Ereg regs1 []) E3) by (rewrite HE3; env_agree_chain HAE2).
assert (A52 : ew E3 52 = getr regs3 10) by (rewrite HE3; reflexivity).
clear HE3.
psrr_branch_pi RUNP BR HS.
{ rewrite rbn5f_den_off0, rbn5f_den_lit, A52, Hv3 in Hc2.
  assert (Hv0 : v = w64 0) by (apply (proj1 (bv_eqb_true_iff v (Z_to_bv 64 0))); exact Hc2).
  assert (HNMt : rbm_NM X = rbm_stem X).
  { destruct (rbn5_NM_cases X) as [(_ & _ & HEt) | (Hn & _)]; [exact HEt|].
    exfalso. apply Hn. split; [lia | exact (proj1 Hbytes Hv0)]. }
  paj_run_to_sh RUNTOP HS HJ3 15032.
  { rbn5f_awr. }
  rbn5f_keepstep HFr K6. clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 [] rbn5f_keep HS HAE3 ltac:(vm_compute; reflexivity)) as HR.
  cbn [ms_regs restrict] in HR.
  pmkst HS.
  replace (BASE + 15032) with (BASE + AF_both3_reac_box_name + RBN_L2X)
    by (unfold AF_both3_reac_box_name, RBN_L2X; lia).
  apply (rbn5_tail X pos _ lyc1 Sc1 W1 _ _ HX).
  apply (rbn5f_cT_of X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P _ _ _ HX H5 HJ3);
    [ intros a Ha Hn; rewrite (K6 a Ha); exact (KC a Ha Hn) | exact HR | exact HNMt ]. }
rewrite rbn5f_den_off0, rbn5f_den_lit, A52, Hv3 in Hc2.
assert (Hvn : v <> w64 0) by (apply (proj1 (bv_eqb_false_iff v (Z_to_bv 64 0))); exact Hc2).
assert (HNMd : rbm_NM X = rbm_stem X ++ 45 :: rbm_w4 X).
{ destruct (rbn5_NM_cases X) as [(_ & Hsk & _) | (_ & HEd)]; [|exact HEd].
  exfalso. apply Hvn. exact (proj2 Hbytes Hsk). }
paj_run_to_sh RUNTOP HS HJ3 14936.
{ rbn5f_awr. }
rbn5f_keepstep HFr K6. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 [] rbn5f_keep HS HAE3 ltac:(vm_compute; reflexivity)) as HR.
cbn [ms_regs restrict] in HR.
pmkst HS.
replace (BASE + 14936) with (BASE + AF_both3_reac_box_name + RBN5_D)
  by (unfold AF_both3_reac_box_name, RBN5_D; lia).
apply (rbn5_dash X pos _ lyc1 Sc1 W1 _ _ HX).
apply (rbn5f_cD_of X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P _ _ _ HX H5 HJ3);
  [ intros a Ha Hn; rewrite (K6 a Ha); exact (KC a Ha Hn) | exact HR | exact HNMd ].
Qed.
End h.
End f.
End d.
