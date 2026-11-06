(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mremap.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma msa_cuts_app : forall A B l, maps_subtract_all l (A ++ B) = maps_subtract_all (maps_subtract_all l A) B.
Proof. induction A as [|[a n] A IH]; intros B l; [reflexivity|]. cbn [app maps_subtract_all]. apply IH. Qed.

Lemma ivs_hi_irrel : forall (a sz : word) lo hi1 hi2,
  (hi1 < bv_unsigned a + bv_unsigned sz <-> hi2 < bv_unsigned a + bv_unsigned sz) ->
  (hi1 < bv_unsigned a + bv_unsigned sz -> Z.max (bv_unsigned a) hi1 = Z.max (bv_unsigned a) hi2) ->
  iv_subtract a sz lo hi1 = iv_subtract a sz lo hi2.
Proof.
  intros a sz lo hi1 hi2 H1 H2. unfold iv_subtract. cbv zeta.
  destruct H1 as [H1a H1b].
  destruct (Z.ltb_spec hi1 (bv_unsigned a + bv_unsigned sz)) as [E1|E1];
  destruct (Z.ltb_spec hi2 (bv_unsigned a + bv_unsigned sz)) as [E2|E2].
  - rewrite (H2 E1); reflexivity.
  - exfalso. pose proof (H1a E1). lia.
  - exfalso. pose proof (H1b E2). lia.
  - reflexivity.
Qed.

Lemma ivs_lo_irrel : forall (a sz : word) lo1 lo2 hi,
  (bv_unsigned a < lo1 <-> bv_unsigned a < lo2) ->
  (bv_unsigned a < lo1 -> Z.min (bv_unsigned sz) (lo1 - bv_unsigned a) = Z.min (bv_unsigned sz) (lo2 - bv_unsigned a)) ->
  iv_subtract a sz lo1 hi = iv_subtract a sz lo2 hi.
Proof.
  intros a sz lo1 lo2 hi H1 H2. unfold iv_subtract. cbv zeta.
  destruct H1 as [H1a H1b].
  destruct (Z.ltb_spec (bv_unsigned a) lo1) as [E1|E1];
  destruct (Z.ltb_spec (bv_unsigned a) lo2) as [E2|E2].
  - rewrite (H2 E1); reflexivity.
  - exfalso. pose proof (H1a E1). lia.
  - exfalso. pose proof (H1b E2). lia.
  - reflexivity.
Qed.

Lemma iv_pieces : forall (a sz : word) lo hi (b s : word),
  0 < bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= two_pow_64 ->
  In (b, s) (iv_subtract a sz lo hi) ->
  0 < bv_unsigned s /\ bv_unsigned a <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= bv_unsigned a + bv_unsigned sz.
Proof.
  intros a sz lo hi b s Hpos Hfit Hin.
  pose proof (iv_subtract_within a sz lo hi b s Hfit Hin) as Hw.
  split; [|exact Hw].
  unfold iv_subtract in Hin. cbv zeta in Hin.
  pose proof (mremap_word_range a). pose proof (mremap_word_range sz).
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [E1|E1]; cbn in Hin; [| contradiction].
    destruct Hin as [Heq | []]. inversion Heq; subst b s.
    pose proof (Z.min_spec (bv_unsigned sz) (lo - bv_unsigned a)).
    rewrite mremap_u64 by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [E2|E2]; cbn in Hin; [| contradiction].
    destruct Hin as [Heq | []]. inversion Heq; subst b s.
    pose proof (Z.max_spec (bv_unsigned a) hi).
    rewrite (mremap_u64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)) by lia. lia.
Qed.

Lemma ms_disjoint_id : forall l lo hi, lo <= hi ->
  (forall (b s : word), In (b, s) l -> 0 < bv_unsigned s /\ (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)) ->
  maps_subtract l lo hi = l.
Proof.
  induction l as [|[a sz] r IH]; intros lo hi Hlh H; [reflexivity|].
  cbn [maps_subtract]. destruct (H a sz (or_introl eq_refl)) as [Hp Hd].
  rewrite iv_subtract_disjoint by assumption. cbn [app]. f_equal.
  apply IH; [exact Hlh|]. intros b s Hin. exact (H b s (or_intror Hin)).
Qed.

Lemma ivs_pieces_disj : forall (b s : word) lo0 hi0 lo hi, 0 < bv_unsigned s -> bv_unsigned b + bv_unsigned s <= two_pow_64 ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b) -> lo <= hi ->
  maps_subtract (iv_subtract b s lo0 hi0) lo hi = iv_subtract b s lo0 hi0.
Proof.
  intros b s lo0 hi0 lo hi Hp Hf Hd Hlh. apply ms_disjoint_id; [exact Hlh|].
  intros b' s' Hin. destruct (iv_pieces b s lo0 hi0 b' s' Hp Hf Hin) as (H1 & H2 & H3). split; [exact H1|lia].
Qed.

Lemma key_cut : forall (b s c k : word) lo hi,
  0 < bv_unsigned s -> bv_unsigned b + bv_unsigned s <= two_pow_64 ->
  0 <= lo -> lo <= hi -> hi < two_pow_64 ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b) ->
  maps_subtract_all [(b, s)] (iv_subtract c k lo hi) = iv_subtract b s (bv_unsigned c) (bv_unsigned c + bv_unsigned k).
Proof.
  intros b s c k lo hi Hp Hf Hlo Hlh Hhi Hd.
  pose proof (mremap_word_range b). pose proof (mremap_word_range s).
  pose proof (mremap_word_range c). pose proof (mremap_word_range k).
  unfold iv_subtract at 1. cbv zeta.
  destruct (Z.ltb_spec (bv_unsigned c) lo) as [E1|E1];
  destruct (Z.ltb_spec hi (bv_unsigned c + bv_unsigned k)) as [E2|E2]; cbn [app maps_subtract_all].
  -
    pose proof (Z.min_spec (bv_unsigned k) (lo - bv_unsigned c)).
    pose proof (Z.max_spec (bv_unsigned c) hi).
    rewrite !mremap_u64 by lia. cbn [maps_subtract]. rewrite app_nil_r.
    replace (Z.max (bv_unsigned c) hi + (bv_unsigned c + bv_unsigned k - Z.max (bv_unsigned c) hi)) with (bv_unsigned c + bv_unsigned k) by lia.
    destruct Hd as [Hd|Hd].
    + rewrite (ivs_hi_irrel b s (bv_unsigned c) _ (bv_unsigned c + bv_unsigned k)) by lia.
      apply ivs_pieces_disj; lia.
    + rewrite (iv_subtract_disjoint b s) by lia. cbn [maps_subtract]. rewrite app_nil_r.
      apply ivs_lo_irrel; lia.
  -
    pose proof (Z.min_spec (bv_unsigned k) (lo - bv_unsigned c)).
    rewrite !mremap_u64 by lia. cbn [maps_subtract]. rewrite app_nil_r.
    destruct Hd as [Hd|Hd].
    + apply ivs_hi_irrel; lia.
    + rewrite (iv_subtract_disjoint b s) by lia. rewrite (iv_subtract_disjoint b s) by lia. reflexivity.
  -
    pose proof (Z.max_spec (bv_unsigned c) hi).
    rewrite !mremap_u64 by lia. cbn [maps_subtract]. rewrite app_nil_r.
    replace (Z.max (bv_unsigned c) hi + (bv_unsigned c + bv_unsigned k - Z.max (bv_unsigned c) hi)) with (bv_unsigned c + bv_unsigned k) by lia.
    destruct Hd as [Hd|Hd].
    + rewrite (iv_subtract_disjoint b s) by lia. rewrite (iv_subtract_disjoint b s) by lia. reflexivity.
    + apply ivs_lo_irrel; lia.
  -
    destruct Hd as [Hd|Hd]; rewrite (iv_subtract_disjoint b s) by lia; reflexivity.
Qed.

Lemma live_zero_entry : forall (b s : word) Q, bv_unsigned s = 0 -> live_bytes (maps_subtract_all [(b, s)] Q) = 0.
Proof.
  intros b s Q Hz. pose proof (live_bytes_maps_subtract_all_le Q [(b, s)]) as H1.
  pose proof (live_bytes_nonneg (maps_subtract_all [(b, s)] Q)). cbn [live_bytes] in H1. lia.
Qed.

Lemma live_zero_iv : forall (b s : word) lo hi Q, bv_unsigned s = 0 -> lo <= hi -> live_bytes (maps_subtract_all (iv_subtract b s lo hi) Q) = 0.
Proof.
  intros b s lo hi Q Hz Hlh. pose proof (live_bytes_maps_subtract_all_le Q (iv_subtract b s lo hi)) as H1.
  pose proof (live_bytes_iv_subtract_le b s lo hi Hlh).
  pose proof (live_bytes_nonneg (maps_subtract_all (iv_subtract b s lo hi) Q)). lia.
Qed.

Lemma cut_split_live : forall KL l lo hi,
  0 <= lo -> lo <= hi -> hi < two_pow_64 ->
  (forall (b s : word), In (b, s) l -> bv_unsigned b + bv_unsigned s <= two_pow_64 /\
       (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)) ->
  live_bytes (maps_subtract_all l (maps_subtract KL lo hi)) = live_bytes (maps_subtract_all l KL).
Proof.
  induction KL as [|[c k] KL IH]; intros l lo hi Hlo Hlh Hhi Hl; [reflexivity|].
  cbn [maps_subtract]. rewrite msa_cuts_app. cbn [maps_subtract_all].
  rewrite IH by (try assumption; intros b s Hin;
    pose proof (maps_subtract_all_within (iv_subtract c k lo hi) l b s (fun a sz H => proj1 (Hl a sz H)) Hin) as (a & sz & Ha & Hw);
    destruct (Hl a sz Ha) as [Hf Hd]; split; lia).
  clear IH. revert KL. induction l as [|[b s] r IHl]; intros KL.
  - cbn [maps_subtract]. rewrite ?maps_subtract_all_nil. reflexivity.
  - change ((b, s) :: r) with ([(b, s)] ++ r).
    rewrite maps_subtract_all_app, maps_subtract_app, !maps_subtract_all_app, !live_bytes_app.
    rewrite IHl by (intros b' s' Hin; exact (Hl b' s' (or_intror Hin))).
    f_equal. cbn [maps_subtract]. rewrite app_nil_r. destruct (Hl b s (or_introl eq_refl)) as [Hf Hd].
    pose proof (mremap_word_range s). pose proof (mremap_word_range k).
    destruct (Z.eq_dec (bv_unsigned s) 0) as [Hz|Hz].
    + rewrite (live_zero_iv b s) by lia.

      pose proof (live_bytes_maps_subtract_all_le KL (maps_subtract_all [(b, s)] (iv_subtract c k lo hi))) as H1.
      pose proof (live_zero_entry b s (iv_subtract c k lo hi) Hz).
      pose proof (live_bytes_nonneg (maps_subtract_all (maps_subtract_all [(b, s)] (iv_subtract c k lo hi)) KL)). lia.
    + rewrite key_cut by lia. reflexivity.
Qed.

Lemma ms_within_nil : forall l lo hi,
  (forall (b s : word), In (b, s) l -> lo <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= hi) ->
  maps_subtract l lo hi = [].
Proof.
  induction l as [|[a sz] r IH]; intros lo hi H; [reflexivity|].
  cbn [maps_subtract]. destruct (H a sz (or_introl eq_refl)) as [H1 H2].
  unfold iv_subtract at 1. cbv zeta.
  destruct (Z.ltb_spec (bv_unsigned a) lo); [lia|].
  destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [lia|].
  cbn [app]. apply IH. intros b s Hin. exact (H b s (or_intror Hin)).
Qed.
