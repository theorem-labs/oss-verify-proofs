(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxFold FxNumEq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma lin_eqb_true : forall a b, lin_eqb a b = true -> a = b. Proof. apply lin_eqb_eq. Qed.

Lemma u_range : forall E l, 0 <= bv_unsigned (lden E l) < two64.
Proof. intros. pose proof (bv_unsigned_in_range _ (lden E l)) as R. unfold bv_modulus in R. exact R. Qed.

Lemma is_const_u : forall E l c, is_const l = Some c -> bv_unsigned (lden E l) = c.
Proof. intros E l c H. destruct (is_const_sound E l c H) as [-> Hc]. apply u_small64. exact Hc. Qed.

Lemma sgn64_eqm : forall d, eqm (sgn64 d) d.
Proof.
  intros d. unfold sgn64, T63. destruct (Z.ltb d 9223372036854775808); [apply eqm_refl|].
  unfold eqm. replace (d - two64) with (d + (-1) * two64) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma eqm_sub : forall a b c d, eqm a b -> eqm c d -> eqm (a - c) (b - d).
Proof. unfold eqm. intros a b c d H1 H2. rewrite Zminus_mod, H1, H2, <- Zminus_mod. reflexivity. Qed.
Lemma u_eqm_lz : forall E l, eqm (bv_unsigned (lden E l)) (lz E l).
Proof. intros E l. unfold lden. apply eqm_u. Qed.

Lemma u_lden_mod : forall E l, bv_unsigned (lden E l) = lz E l mod two64.
Proof. intros. apply u_lden. Qed.

(* [comment removed for export] *)
Fixpoint tsumz (E : valu) (t : list (positive * Z)) : Z :=
  match t with [] => 0 | (x, k) :: t' => sgn64 k * vz E x + tsumz E t' end.
Definition izl (E : valu) (l : lin) : Z := sgn64 (l_c l) + tsumz E (l_t l).
Lemma tsumz_eqm : forall E t, eqm (tsumz E t) (tsum E t).
Proof.
  intros E t. induction t as [|[x k] t IH]; cbn [tsumz tsum]; [apply eqm_refl|].
  apply eqm_add; [apply eqm_mul; [apply sgn64_eqm | apply eqm_refl] | exact IH].
Qed.
Lemma izl_eqm : forall E l, eqm (izl E l) (lz E l).
Proof. intros E [c t]. unfold izl, lz; cbn [l_c l_t]. apply eqm_add; [apply sgn64_eqm | apply tsumz_eqm]. Qed.
Lemma u_izl : forall E l, 0 <= izl E l <= M64 -> bv_unsigned (lden E l) = izl E l.
Proof.
  intros E l H. rewrite u_lden_mod. pose proof (izl_eqm E l) as He. unfold eqm in He. rewrite <- He.
  apply Z.mod_small. unfold M64, two64 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma same_terms_eqm : forall E l l', l_t l = l_t l' -> eqm (bv_unsigned (lden E l)) (bv_unsigned (lden E l') + (l_c l - l_c l')).
Proof.
  intros E l l' Ht. rewrite !u_lden_mod. unfold eqm. rewrite Z.mod_mod by (unfold two64; lia).
  rewrite Z.add_mod_idemp_l by (unfold two64; lia). f_equal. unfold lz. rewrite Ht. lia.
Qed.

(* [comment removed for export] *)
Lemma testbit_high64 : forall x n, 0 <= x < 2 ^ 64 -> 64 <= n -> Z.testbit x n = false.
Proof.
  intros x n Hx Hn. destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.testbit_0_l|].
  apply Z.bits_above_log2; [lia|]. apply Z.le_lt_trans with 63; [|lia]. apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia.
Qed.
Lemma land_le_r : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= b.
Proof.
  intros a b Ha Hb.
  assert (Hd : Z.land (Z.land b a) (Z.ldiff b a) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.land_spec, Z.ldiff_spec, Z.bits_0.
    destruct (Z.testbit b n), (Z.testbit a n); reflexivity. }
  assert (Hs : Z.land b a + Z.ldiff b a = b).
  { rewrite Z.add_nocarry_lxor by exact Hd. rewrite Z.lxor_lor by exact Hd. rewrite Z.lor_comm. apply Z.lor_ldiff_and. }
  assert (Hn : 0 <= Z.ldiff b a) by (apply Z.ldiff_nonneg; left; exact Hb).
  rewrite Z.land_comm. lia.
Qed.
Lemma land_le_l : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= a.
Proof. intros a b Ha Hb. rewrite Z.land_comm. apply land_le_r; assumption. Qed.

Lemma bits_iv_sound : forall u m v, 0 <= u < two64 -> 0 <= m -> Z.land u m = v -> fst (bits_iv m v) <= u <= snd (bits_iv m v).
Proof.
  intros u m v Hu Hm0 Hm. unfold bits_iv. cbn [fst snd]. split.
  - rewrite <- Hm. apply land_le_l; lia.
  - set (z := Z.land m (Z.lnot v)).
    assert (Hz : Z.land u z = 0).
    { unfold z. rewrite Z.land_assoc, Hm. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lnot_spec, Z.bits_0 by lia.
      destruct (Z.testbit v n); reflexivity. }
    assert (Heq : u = Z.land u (Z.land (Z.lnot z) M64)).
    { apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lnot_spec by lia. rewrite M64_ones, Z.testbit_ones_nonneg by lia.
      assert (Hb : Z.testbit (Z.land u z) n = false) by (rewrite Hz; apply Z.bits_0). rewrite Z.land_spec in Hb.
      destruct (Z.ltb_spec n 64) as [Hn64|Hn64].
      - destruct (Z.testbit u n); destruct (Z.testbit z n); cbn in *; congruence.
      - rewrite (testbit_high64 u n) by (change (2 ^ 64) with two64; lia; exact Hn64). reflexivity. }
    rewrite Heq at 1. apply land_le_r; [lia|]. apply Z.land_nonneg. right. unfold M64; lia.
Qed.

Lemma var_range_sound : forall E fs x, Forall (fact_ok E) fs -> fst (var_range fs x) <= vz E x <= snd (var_range fs x).
Proof.
  intros E fs x HF. induction HF as [|f fs Hok HF IH]; cbn [var_range].
  - cbn [fst snd]. unfold vz. pose proof (u_range E (lvar x)) as R. rewrite lden_lvar in R. unfold M64, two64 in *. lia.
  - destruct f as [c a b tk|l lo hi|l k r|l m v|x' v' j'|xb bsb]; [exact IH| |exact IH| |exact IH|exact IH].
    2: { destruct l as [c0 t0]. destruct c0; [|exact IH|exact IH]. destruct t0 as [|[y k] t1]; [exact IH|].
         destruct k as [|[k|k|]|k]; try exact IH. destruct t1; [|exact IH].
         destruct (Pos.eqb_spec x y) as [->|Hne]; [|exact IH].
         destruct (Z.leb_spec 0 m) as [Hm0|Hm0]; [|exact IH]. cbn [andb].
         cbn [fact_ok] in Hok. change (LIN 0 [(y, 1)]) with (lvar y) in Hok. rewrite lden_lvar in Hok.
         pose proof (bits_iv_sound (vz E y) m v ltac:(unfold vz; pose proof (u_range E (lvar y)) as R; rewrite lden_lvar in R; exact R) Hm0 Hok) as Hb.
         unfold iv_meet. cbn [fst snd] in *. lia. }
    destruct l as [c0 t0]. destruct c0; [|exact IH|exact IH]. destruct t0 as [|[y k] t1]; [exact IH|].
    destruct k as [|[k|k|]|k]; try exact IH. destruct t1; [|exact IH].
    destruct (Pos.eqb_spec x y) as [->|Hne]; [|exact IH].
    cbn [fact_ok] in Hok. change (LIN 0 [(y, 1)]) with (lvar y) in Hok. rewrite lden_lvar in Hok.
    unfold iv_meet. cbn [fst snd]. unfold vz in *. lia.
Qed.

Lemma ne_excl : forall E l d, terms_eqb (l_t l) (l_t d) = true -> bv_unsigned (lden E d) <> 0 ->
  bv_unsigned (lden E l) <> w64 (l_c l - l_c d).
Proof.
  intros E l d Ht Hd Heq. apply terms_eqb_eq in Ht. pose proof (same_terms_eqm E l d Ht) as He2. rewrite Heq in He2.
  assert (Hz : eqm (bv_unsigned (lden E d)) 0).
  { assert (H1 : eqm (0 + (l_c l - l_c d)) (bv_unsigned (lden E d) + (l_c l - l_c d))).
    { eapply eqm_trans; [|exact He2]. rewrite Z.add_0_l. apply eqm_sym, eqm_w64. }
    apply eqm_sym. unfold eqm in *.
    replace 0 with ((0 + (l_c l - l_c d)) + - (l_c l - l_c d)) by lia.
    replace (bv_unsigned (lden E d)) with ((bv_unsigned (lden E d) + (l_c l - l_c d)) + - (l_c l - l_c d)) by lia.
    rewrite Z.add_mod, H1, <- Z.add_mod by (unfold two64; lia). reflexivity. }
  unfold eqm in Hz. rewrite Z.mod_small in Hz by apply u_range. rewrite Z.mod_0_l in Hz by (unfold two64; lia). exact (Hd Hz).
Qed.
Lemma sub_ne0 : forall E a b, lden E a <> lden E b -> bv_unsigned (lden E (lsub b a)) <> 0.
Proof.
  intros E a b Hab Hz. apply Hab. rewrite lden_lsub in Hz. apply bv_eq. rewrite bv_sub_unsigned in Hz. unfold bv_wrap, bv_modulus in Hz.
  pose proof (u_range E a). pose proof (u_range E b). change (2 ^ Z.of_N 64) with two64 in Hz.
  apply Z.mod_divide in Hz; [|unfold two64; lia]. destruct Hz as [q Hq]. assert (q = 0) by (unfold two64 in *; nia). subst q. lia.
Qed.
Lemma ne_refine_sound : forall E fs l acc, Forall (fact_ok E) fs ->
  fst acc <= bv_unsigned (lden E l) <= snd acc -> fst (ne_refine fs l acc) <= bv_unsigned (lden E l) <= snd (ne_refine fs l acc).
Proof.
  intros E fs l acc HF. revert acc. induction HF as [|f fs Hok HF IH]; intros acc Hacc; cbn [ne_refine]; [exact Hacc|].
  destruct f as [c a b tk|l' lo hi|l' k' r'|l' m' v'|x' v' j'|xb bsb]; [|exact (IH acc Hacc)|exact (IH acc Hacc)|exact (IH acc Hacc)|exact (IH acc Hacc)|exact (IH acc Hacc)].
  destruct (ne_c c tk && ne_pre l a b)%bool eqn:Hex0; [|exact (IH acc Hacc)]. apply andb_prop in Hex0 as [Hex _].
  set (ba := if terms_eqb (l_t l) (l_t (lsub b a)) then lsub b a else lsub a b).
  destruct (terms_eqb (l_t l) (l_t ba)) eqn:Ht; [|exact (IH acc Hacc)].
  assert (Hab : lden E a <> lden E b).
  { cbn [fact_ok] in Hok. unfold ne_c in Hex. destruct c; destruct tk; try discriminate; cbn [branch_taken] in Hok; unfold bv_eqb in Hok.
    - apply Z.eqb_neq in Hok. intros H; apply Hok; rewrite H; reflexivity.
    - apply negb_true_iff, Z.eqb_neq in Hok. intros H; apply Hok; rewrite H; reflexivity. }
  assert (Hba : bv_unsigned (lden E ba) <> 0).
  { unfold ba. destruct (terms_eqb (l_t l) (l_t (lsub b a))); [exact (sub_ne0 E a b Hab) | apply sub_ne0; intros H; apply Hab; symmetry; exact H]. }
  pose proof (ne_excl E l ba Ht Hba) as Hne.
  apply IH. destruct (Z.eqb (fst acc) (w64 (l_c l - l_c ba))) eqn:E1.
  - apply Z.eqb_eq in E1. cbn [fst snd]. lia.
  - destruct (Z.eqb (snd acc) (w64 (l_c l - l_c ba))) eqn:E2; [|exact Hacc].
    apply Z.eqb_eq in E2. cbn [fst snd]. lia.
Qed.

Lemma ne_fix_sound : forall E fs l k acc, Forall (fact_ok E) fs ->
  fst acc <= bv_unsigned (lden E l) <= snd acc -> fst (ne_fix k fs l acc) <= bv_unsigned (lden E l) <= snd (ne_fix k fs l acc).
Proof.
  intros E fs l k. induction k as [|k IH]; intros acc HF Hacc; cbn [ne_fix]; [exact Hacc|].
  pose proof (ne_refine_sound E fs l acc HF Hacc) as H1.
  destruct (Z.eqb (fst (ne_refine fs l acc)) (fst acc) && Z.eqb (snd (ne_refine fs l acc)) (snd acc))%bool; [exact H1|].
  exact (IH _ HF H1).
Qed.
Lemma ne_refine'_sound : forall E fs l acc, Forall (fact_ok E) fs ->
  fst acc <= bv_unsigned (lden E l) <= snd acc -> fst (ne_refine' fs l acc) <= bv_unsigned (lden E l) <= snd (ne_refine' fs l acc).
Proof.
  intros E fs l acc HF H. unfold ne_refine'.
  assert (Hk : forall k acc, ne_fixl k fs l acc = ne_fix (List.length k) fs l acc)
    by (induction k as [|f k IHk]; intros acc'; [reflexivity | cbn [ne_fixl ne_fix List.length]; rewrite IHk; reflexivity]).
  rewrite Hk. exact (ne_fix_sound E fs l _ acc HF H).
Qed.

(* [comment removed for export] *)
Lemma var_range'_sound : forall E fs x, Forall (fact_ok E) fs -> fst (var_range' fs x) <= vz E x <= snd (var_range' fs x).
Proof.
  intros E fs x HF. unfold var_range'. pose proof (var_range_sound E fs x HF) as Hv.
  assert (Hu : bv_unsigned (lden E (lvar x)) = vz E x) by (rewrite lden_lvar; reflexivity).
  rewrite <- Hu in *. exact (ne_refine'_sound E fs (lvar x) (var_range fs x) HF Hv).
Qed.

Lemma iv_scale_sound : forall k lo hi v, lo <= v <= hi -> fst (iv_scale k (lo, hi)) <= k * v <= snd (iv_scale k (lo, hi)).
Proof. intros k lo hi v H. unfold iv_scale. destruct (Z.leb_spec 0 k); cbn [fst snd]; nia. Qed.

Lemma t_iv_sound : forall E fs t, Forall (fact_ok E) fs -> fst (t_iv fs t) <= tsumz E t <= snd (t_iv fs t).
Proof.
  intros E fs t HF. induction t as [|[x k] t IH]; cbn [t_iv tsumz]; [cbn; lia|].
  pose proof (var_range'_sound E fs x HF) as Hv. destruct (var_range' fs x) as [lo hi] eqn:Hr. cbn [fst snd] in Hv.
  pose proof (iv_scale_sound (sgn64 k) lo hi (vz E x) Hv) as Hs.
  unfold iv_add. cbn [fst snd]. lia.
Qed.

Lemma l_iv_sound : forall E fs l, Forall (fact_ok E) fs -> fst (l_iv fs l) <= izl E l <= snd (l_iv fs l).
Proof.
  intros E fs l HF. unfold l_iv, izl, iv_add. cbn [fst snd]. pose proof (t_iv_sound E fs (l_t l) HF). lia.
Qed.

Lemma wrap_iv_sound : forall E l v a, eqm v (bv_unsigned (lden E l)) -> fst a <= v <= snd a ->
  fst (wrap_iv a) <= bv_unsigned (lden E l) <= snd (wrap_iv a).
Proof.
  intros E l v a He H. pose proof (u_range E l) as Ru. unfold wrap_iv. destruct (nowrap a) eqn:Hn.
  - unfold nowrap in Hn. apply andb_prop in Hn as [H1 H2]. apply Z.leb_le in H1, H2. unfold eqm in He.
    rewrite (Z.mod_small v) in He by (unfold M64, two64 in *; lia). rewrite Z.mod_small in He by exact Ru. lia.
  - destruct (nowrap (fst a + two64, snd a + two64)) eqn:Hn2.
    + unfold nowrap in Hn2. cbn [fst snd] in *. apply andb_prop in Hn2 as [H1 H2]. apply Z.leb_le in H1, H2. unfold eqm in He.
      rewrite (Z.mod_small (bv_unsigned (lden E l))) in He by exact Ru. replace v with ((v + two64) + (-1) * two64) in He by ring.
      rewrite Z_mod_plus_full in He. rewrite Z.mod_small in He by (unfold M64, two64 in *; lia). lia.
    + unfold iv_top, M64, two64 in *. cbn. lia.
Qed.
Lemma base_range_sound : forall E fs l, Forall (fact_ok E) fs -> fst (base_range fs l) <= bv_unsigned (lden E l) <= snd (base_range fs l).
Proof.
  intros E fs l HF. unfold base_range. apply (wrap_iv_sound E l (izl E l)); [|exact (l_iv_sound E fs l HF)].
  eapply eqm_trans; [apply izl_eqm | apply eqm_sym, u_eqm_lz].
Qed.

Lemma lsub_terms : forall a b, l_t (lsub b a) = tadd (l_t b) (l_t (lneg a)). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u_lsub_le : forall E a b, bv_unsigned (lden E a) <= bv_unsigned (lden E b) ->
  bv_unsigned (lden E (lsub b a)) = bv_unsigned (lden E b) - bv_unsigned (lden E a).
Proof.
  intros E a b H. rewrite lden_lsub, bv_sub_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small.
  pose proof (u_range E a). pose proof (u_range E b). unfold two64 in *. change (2 ^ Z.of_N 64) with 18446744073709551616. lia.
Qed.

Lemma window_eq : forall x y a b, eqm x y -> fst a <= x <= snd a -> fst b <= y <= snd b -> window a b = true -> x = y.
Proof.
  intros x y a b He Ha Hb Hw. unfold window in Hw. apply Z.ltb_lt in Hw. unfold eqm in He.
  assert (Hd : (x - y) mod two64 = 0) by (rewrite Zminus_mod, He, Z.sub_diag; reflexivity).
  apply Z.mod_divide in Hd; [|unfold two64; lia]. destruct Hd as [q Hq].
  assert (q = 0) by (unfold two64 in *; nia). subst q. lia.
Qed.

Lemma meet_win_sound : forall v x acc c, eqm v x -> fst acc <= v <= snd acc -> fst c <= x <= snd c ->
  exists v', eqm v' v /\ fst (meet_win acc c) <= v' <= snd (meet_win acc c).
Proof.
  intros v x acc c He Hv Hx. unfold meet_win. destruct (window acc c) eqn:Hw.
  - pose proof (window_eq v x acc c He Hv Hx Hw). subst x. exists v. split; [apply eqm_refl|]. unfold iv_meet. cbn [fst snd]. lia.
  - destruct (Z.ltb (snd c - fst c) (snd acc - fst acc)).
    + exists x. split; [apply eqm_sym; exact He | exact Hx].
    + exists v. split; [apply eqm_refl | exact Hv].
Qed.

Lemma frange_same_sound : forall E fs l acc, Forall (fact_ok E) fs ->
  (exists v, eqm v (bv_unsigned (lden E l)) /\ fst acc <= v <= snd acc) ->
  exists v, eqm v (bv_unsigned (lden E l)) /\ fst (frange_same fs l acc) <= v <= snd (frange_same fs l acc).
Proof.
  intros E fs l acc HF. revert acc. induction HF as [|f fs Hok HF IH]; intros acc (v & Hv & Hacc); cbn [frange_same]; [exists v; split; assumption|].
  destruct f as [c a b tk|g lo hi|g k' r'|g m' v'|x' v' j'|xb bsb]; try exact (IH acc (ex_intro _ v (conj Hv Hacc))).
  destruct (terms_eqb (l_t g) (l_t l)) eqn:Ht; [|exact (IH acc (ex_intro _ v (conj Hv Hacc)))].
  apply IH. cbn [fact_ok] in Hok. apply terms_eqb_eq in Ht.
  pose proof (same_terms_eqm E l g (eq_sym Ht)) as He.
  assert (He1 : eqm v (bv_unsigned (lden E g) + sgn64 (w64 (l_c l - l_c g)))).
  { eapply eqm_trans; [exact Hv|]. eapply eqm_trans; [exact He|]. apply eqm_add; [apply eqm_refl|].
    eapply eqm_trans; [|apply eqm_sym, sgn64_eqm]. apply eqm_sym, eqm_w64. }
  destruct (meet_win_sound v _ acc (lo + sgn64 (w64 (l_c l - l_c g)), hi + sgn64 (w64 (l_c l - l_c g))) He1 Hacc ltac:(cbn [fst snd]; lia))
    as (v1 & Hv1 & Hr1).
  exists v1. split; [eapply eqm_trans; [exact Hv1 | exact Hv] | exact Hr1].
Qed.

Lemma ne_int_sound : forall E fs l acc, Forall (fact_ok E) fs ->
  (exists v, eqm v (bv_unsigned (lden E l)) /\ fst acc <= v <= snd acc) ->
  exists v, eqm v (bv_unsigned (lden E l)) /\ fst (ne_int fs l acc) <= v <= snd (ne_int fs l acc).
Proof.
  intros E fs l acc HF. revert acc. induction HF as [|f fs Hok HF IH]; intros acc Hacc; cbn [ne_int]; [exact Hacc|].
  destruct f as [c a b tk|l' lo hi|l' k' r'|l' m' v'|x' v' j'|xb bsb]; [|exact (IH acc Hacc)|exact (IH acc Hacc)|exact (IH acc Hacc)|exact (IH acc Hacc)|exact (IH acc Hacc)].
  destruct (ne_c c tk && ne_pre l a b)%bool eqn:Hex0; [|exact (IH acc Hacc)]. apply andb_prop in Hex0 as [Hex _].
  set (ba := if terms_eqb (l_t l) (l_t (lsub b a)) then lsub b a else lsub a b).
  destruct (terms_eqb (l_t l) (l_t ba)) eqn:Ht; [|exact (IH acc Hacc)].
  assert (Hab : lden E a <> lden E b).
  { cbn [fact_ok] in Hok. unfold ne_c in Hex. destruct c; destruct tk; try discriminate; cbn [branch_taken] in Hok; unfold bv_eqb in Hok.
    - apply Z.eqb_neq in Hok. intros H; apply Hok; rewrite H; reflexivity.
    - apply negb_true_iff, Z.eqb_neq in Hok. intros H; apply Hok; rewrite H; reflexivity. }
  assert (Hba : bv_unsigned (lden E ba) <> 0).
  { unfold ba. destruct (terms_eqb (l_t l) (l_t (lsub b a))); [exact (sub_ne0 E a b Hab) | apply sub_ne0; intros H; apply Hab; symmetry; exact H]. }
  pose proof (ne_excl E l ba Ht Hba) as Hne.
  apply IH. destruct Hacc as (v & Hv & Hr).
  assert (Hw : forall y, w64 y = w64 (l_c l - l_c ba) -> eqm v y -> False).
  { intros y Hy Hvy. apply Hne. pose proof (u_range E l) as Ru. rewrite <- Hy. rewrite w64_mod. unfold eqm in *.
    rewrite <- Hvy, Hv. symmetry. apply Z.mod_small. exact Ru. }
  exists v. split; [exact Hv|].
  destruct (Z.eqb (w64 (fst acc)) (w64 (l_c l - l_c ba))) eqn:E1.
  - apply Z.eqb_eq in E1. cbn [fst snd]. assert (v <> fst acc) by (intros ->; exact (Hw (fst acc) E1 (eqm_refl _))). lia.
  - destruct (Z.eqb (w64 (snd acc)) (w64 (l_c l - l_c ba))) eqn:E2; [|exact Hr].
    apply Z.eqb_eq in E2. cbn [fst snd]. assert (v <> snd acc) by (intros ->; exact (Hw (snd acc) E2 (eqm_refl _))). lia.
Qed.
Lemma ne_int_fix_sound : forall E fs l k acc, Forall (fact_ok E) fs ->
  (exists v, eqm v (bv_unsigned (lden E l)) /\ fst acc <= v <= snd acc) ->
  exists v, eqm v (bv_unsigned (lden E l)) /\ fst (ne_int_fix k fs l acc) <= v <= snd (ne_int_fix k fs l acc).
Proof.
  intros E fs l k. induction k as [|k IH]; intros acc HF Hacc; cbn [ne_int_fix]; [exact Hacc|].
  pose proof (ne_int_sound E fs l acc HF Hacc) as H1.
  destruct (Z.eqb (fst (ne_int fs l acc)) (fst acc) && Z.eqb (snd (ne_int fs l acc)) (snd acc))%bool; [exact H1|].
  exact (IH _ HF H1).
Qed.

Lemma srange_sound : forall E fs l, Forall (fact_ok E) fs -> fst (srange fs l) <= bv_unsigned (lden E l) <= snd (srange fs l).
Proof.
  intros E fs l HF. unfold srange.
  assert (Hk : forall k acc', ne_int_fixl k fs l acc' = ne_int_fix (List.length k) fs l acc')
    by (induction k as [|f' k IHk]; intros acc'; [reflexivity | cbn [ne_int_fixl ne_int_fix List.length]; rewrite IHk; reflexivity]).
  pose proof (frange_same_sound E fs l (l_iv fs l) HF
             (ex_intro _ (izl E l) (conj (eqm_trans _ _ _ (izl_eqm E l) (eqm_sym _ _ (u_eqm_lz E l))) (l_iv_sound E fs l HF)))) as H0.
  destruct (nowrap (frange_same fs l (l_iv fs l))).
  - destruct H0 as (v & Hv & Hr). exact (wrap_iv_sound E l v _ Hv Hr).
  - rewrite Hk. destruct (ne_int_fix_sound E fs l (List.length fs) _ HF H0) as (v & Hv & Hr).
    exact (wrap_iv_sound E l v _ Hv Hr).
Qed.

(* [comment removed for export] *)
Lemma lts_ltu_nn : forall E a b, bv_unsigned (lden E a) < T63 -> bv_unsigned (lden E b) < T63 ->
  bv_lts (lden E a) (lden E b) = bv_ltu (lden E a) (lden E b).
Proof.
  intros E a b Ha Hb. pose proof (u_range E a) as Ua. pose proof (u_range E b) as Ub.
  unfold bv_lts, bv_ltu, bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with 9223372036854775808. change (bv_modulus 64) with 18446744073709551616.
  unfold T63 in *. rewrite !Z.mod_small by (unfold two64 in *; lia). f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma u_shift63 : forall E x, bv_unsigned (lden E (laddc x T63)) = bv_signed (lden E x) + T63.
Proof.
  intros E x. rewrite lden_laddc, Z_to_bv_unsigned. unfold bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with T63. change (bv_modulus 64) with two64. lia.
Qed.
Lemma signed_range : forall E x, - T63 <= bv_signed (lden E x) < T63.
Proof.
  intros E x. unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 64) with T63. change (bv_modulus 64) with two64.
  pose proof (Z.mod_pos_bound (bv_unsigned (lden E x) + T63) two64 ltac:(unfold two64; lia)). unfold T63, two64 in *. lia.
Qed.
Lemma signed_const : forall E b c, is_const b = Some c -> bv_signed (lden E b) = sgn64 c.
Proof.
  intros E b c H. pose proof (is_const_u E b c H) as Hu. pose proof (u_range E b) as Ub.
  unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 64) with T63. change (bv_modulus 64) with two64.
  rewrite Hu in *. unfold sgn64. destruct (Z.ltb c T63) eqn:Hc.
  - apply Z.ltb_lt in Hc. rewrite Z.mod_small by (unfold T63, two64 in *; lia). lia.
  - apply Z.ltb_ge in Hc. replace (c + T63) with ((c + T63 - two64) + 1 * two64) by ring.
    rewrite Z_mod_plus_full. rewrite Z.mod_small by (unfold T63, two64 in *; lia). lia.
Qed.
Lemma sgn_const_lt_sound : forall E a b g lo hi, bv_lts (lden E a) (lden E b) = true -> sgn_const_lt a b = Some (g, lo, hi) ->
  lo <= bv_unsigned (lden E g) <= hi.
Proof.
  intros E a b g lo hi Hl H. unfold bv_lts in Hl. apply Z.ltb_lt in Hl. unfold sgn_const_lt in H.
  pose proof (signed_range E a) as Ra. pose proof (signed_range E b) as Rb.
  destruct (is_const b) as [c|] eqn:Hb.
  - injection H as <- <- <-. rewrite u_shift63. rewrite (signed_const E b c Hb) in Hl. lia.
  - destruct (is_const a) as [c|] eqn:Ha; [|discriminate]. injection H as <- <- <-. rewrite u_shift63.
    rewrite (signed_const E a c Ha) in Hl. unfold M64, T63 in *. lia.
Qed.
Lemma sgn_const_ge_sound : forall E a b g lo hi, bv_lts (lden E a) (lden E b) = false -> sgn_const_ge a b = Some (g, lo, hi) ->
  lo <= bv_unsigned (lden E g) <= hi.
Proof.
  intros E a b g lo hi Hl H. unfold bv_lts in Hl. apply Z.ltb_ge in Hl. unfold sgn_const_ge in H.
  pose proof (signed_range E a) as Ra. pose proof (signed_range E b) as Rb.
  destruct (is_const b) as [c|] eqn:Hb.
  - injection H as <- <- <-. rewrite u_shift63. rewrite (signed_const E b c Hb) in Hl. unfold M64, T63 in *. lia.
  - destruct (is_const a) as [c|] eqn:Ha; [|discriminate]. injection H as <- <- <-. rewrite u_shift63.
    rewrite (signed_const E a c Ha) in Hl. lia.
Qed.

Lemma fact_g_sound : forall E fs f g lo hi, Forall (fact_ok E) fs -> fact_ok E f -> fact_g fs f = Some (g, lo, hi) ->
  lo <= bv_unsigned (lden E g) <= hi.
Proof.
  intros E fs f g lo hi HF Hf H. destruct f as [c a b tk|g0 lo0 hi0|g0 k0 r0|g0 m0 v0|x0 v0 j0|xb bsb]; cbn [fact_g] in H; [| |discriminate|discriminate|discriminate|discriminate].
  - cbn [fact_ok] in Hf. pose proof (base_range_sound E fs a HF) as Ra. pose proof (base_range_sound E fs b HF) as Rb.
    pose proof (srange_sound E fs a HF) as Sa. pose proof (srange_sound E fs b HF) as Sb.
    destruct c; destruct tk; try discriminate.
    + injection H as <- <- <-. cbn [branch_taken] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf. rewrite u_lsub_le by lia. lia.
    + injection H as <- <- <-. cbn [branch_taken] in Hf. unfold bv_eqb in Hf. apply negb_false_iff, Z.eqb_eq in Hf. rewrite u_lsub_le by lia. lia.
    + (* [comment removed for export] *)
      cbn [branch_taken] in Hf. destruct (Z.ltb (snd (srange fs a)) T63 && Z.ltb (snd (srange fs b)) T63)%bool eqn:Hnn.
      * apply andb_prop in Hnn as [Hna Hnb]. apply Z.ltb_lt in Hna, Hnb.
        rewrite (lts_ltu_nn E a b ltac:(lia) ltac:(lia)) in Hf. injection H as <- <- <-. unfold bv_ltu in Hf.
        apply Z.ltb_lt in Hf. rewrite u_lsub_le by lia. lia.
      * exact (sgn_const_lt_sound E a b g lo hi Hf H).
    + (* [comment removed for export] *)
      cbn [branch_taken] in Hf. destruct (Z.ltb (snd (srange fs a)) T63 && Z.ltb (snd (srange fs b)) T63)%bool eqn:Hnn.
      * apply andb_prop in Hnn as [Hna Hnb]. apply Z.ltb_lt in Hna, Hnb.
        rewrite (lts_ltu_nn E a b ltac:(lia) ltac:(lia)) in Hf. injection H as <- <- <-. unfold bv_ltu in Hf.
        apply Z.ltb_ge in Hf. rewrite u_lsub_le by lia. lia.
      * exact (sgn_const_ge_sound E a b g lo hi Hf H).
    + (* [comment removed for export] *)
      cbn [branch_taken] in Hf. apply negb_true_iff in Hf. destruct (Z.ltb (snd (srange fs a)) T63 && Z.ltb (snd (srange fs b)) T63)%bool eqn:Hnn.
      * apply andb_prop in Hnn as [Hna Hnb]. apply Z.ltb_lt in Hna, Hnb.
        rewrite (lts_ltu_nn E a b ltac:(lia) ltac:(lia)) in Hf. injection H as <- <- <-. unfold bv_ltu in Hf.
        apply Z.ltb_ge in Hf. rewrite u_lsub_le by lia. lia.
      * exact (sgn_const_ge_sound E a b g lo hi Hf H).
    + (* [comment removed for export] *)
      cbn [branch_taken] in Hf. apply negb_false_iff in Hf. destruct (Z.ltb (snd (srange fs a)) T63 && Z.ltb (snd (srange fs b)) T63)%bool eqn:Hnn.
      * apply andb_prop in Hnn as [Hna Hnb]. apply Z.ltb_lt in Hna, Hnb.
        rewrite (lts_ltu_nn E a b ltac:(lia) ltac:(lia)) in Hf. injection H as <- <- <-. unfold bv_ltu in Hf.
        apply Z.ltb_lt in Hf. rewrite u_lsub_le by lia. lia.
      * exact (sgn_const_lt_sound E a b g lo hi Hf H).
    + injection H as <- <- <-. cbn [branch_taken] in Hf. unfold bv_ltu in Hf. apply Z.ltb_lt in Hf. rewrite u_lsub_le by lia. lia.
    + injection H as <- <- <-. cbn [branch_taken] in Hf. unfold bv_ltu in Hf. apply Z.ltb_ge in Hf. rewrite u_lsub_le by lia. lia.
    + injection H as <- <- <-. cbn [branch_taken] in Hf. unfold bv_ltu in Hf. apply negb_true_iff, Z.ltb_ge in Hf. rewrite u_lsub_le by lia. lia.
    + injection H as <- <- <-. cbn [branch_taken] in Hf. unfold bv_ltu in Hf. apply negb_false_iff, Z.ltb_lt in Hf. rewrite u_lsub_le by lia. lia.
  - injection H as <- <- <-. exact Hf.
Qed.


Lemma rel_iv_sound : forall E fs all l acc, Forall (fact_ok E) fs -> Forall (fact_ok E) all ->
  (exists v, eqm v (bv_unsigned (lden E l)) /\ fst acc <= v <= snd acc) ->
  exists v, eqm v (bv_unsigned (lden E l)) /\ fst (rel_iv fs all l acc) <= v <= snd (rel_iv fs all l acc).
Proof.
  intros E fs all l acc HF Hall. revert acc. induction HF as [|f fs Hok HF IH]; intros acc (v & Hv & Hacc); cbn [rel_iv]; [exists v; split; assumption|].
  destruct (rel_ok l f); [|exact (IH acc (ex_intro _ v (conj Hv Hacc)))].
  destruct (fact_g all f) as [[[g lo] hi]|] eqn:Hg; [|exact (IH acc (ex_intro _ v (conj Hv Hacc)))].
  pose proof (fact_g_sound E all f g lo hi Hall Hok Hg) as Hgr.
  apply IH.
  pose proof (l_iv_sound E all (lsub l g) Hall) as R1. pose proof (l_iv_sound E all (ladd l g) Hall) as R2.
  assert (He1 : eqm v (bv_unsigned (lden E g) + izl E (lsub l g))).
  { eapply eqm_trans; [exact Hv|]. eapply eqm_trans; [apply u_eqm_lz|]. apply eqm_sym.
    eapply eqm_trans; [apply eqm_add; [apply u_eqm_lz | apply izl_eqm]|].
    eapply eqm_trans; [apply eqm_add; [apply eqm_refl | apply lz_lsub]|].
    replace (lz E g + (lz E l - lz E g)) with (lz E l) by lia. apply eqm_refl. }
  assert (He2 : eqm v (izl E (ladd l g) - bv_unsigned (lden E g))).
  { eapply eqm_trans; [exact Hv|]. eapply eqm_trans; [apply u_eqm_lz|]. apply eqm_sym.
    eapply eqm_trans; [apply eqm_sub; [apply izl_eqm | apply u_eqm_lz]|].
    eapply eqm_trans; [apply eqm_sub; [apply lz_ladd | apply eqm_refl]|].
    replace (lz E l + lz E g - lz E g) with (lz E l) by lia. apply eqm_refl. }
  destruct (meet_win_sound v _ acc (lo + fst (l_iv all (lsub l g)), hi + snd (l_iv all (lsub l g))) He1 Hacc ltac:(cbn [fst snd]; lia)) as (v1 & Hv1 & Hacc1).
  assert (He2' : eqm v1 (izl E (ladd l g) - bv_unsigned (lden E g))) by (eapply eqm_trans; [exact Hv1 | exact He2]).
  destruct (meet_win_sound v1 _ _ (fst (l_iv all (ladd l g)) - hi, snd (l_iv all (ladd l g)) - lo) He2' Hacc1 ltac:(cbn [fst snd]; lia)) as (v2 & Hv2 & Hacc2).
  exists v2. split; [eapply eqm_trans; [exact Hv2 | eapply eqm_trans; [exact Hv1 | exact Hv]] | exact Hacc2].
Qed.


(* [comment removed for export] *)
Lemma divide_mul2 : forall a b x y, (a | x) -> (b | y) -> (a * b | x * y).
Proof. intros a b x y [p Hp] [q Hq]. exists (p * q). subst x y. ring. Qed.

Lemma pow2_divide_le : forall a b, 0 <= a <= b -> (2 ^ a | 2 ^ b).
Proof. intros a b H. exists (2 ^ (b - a)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma ctz_f_spec : forall f z, 0 <= z -> 0 <= ctz_f f z <= Z.of_nat f /\ (2 ^ ctz_f f z | z).
Proof.
  induction f as [|f IH]; intros z Hz; cbn [ctz_f].
  - split; [lia|]. exists z. lia.
  - destruct (Z.eqb (Z.land z 1) 0) eqn:E1.
    + destruct (IH (Z.shiftr z 1) ltac:(apply Z.shiftr_nonneg; lia)) as [Hb [q Hq]]. split; [lia|].
      exists q. rewrite Z.pow_add_r by lia.
      assert (Hz2 : z = 2 * Z.shiftr z 1).
      { apply Z.eqb_eq in E1. change 1 with (Z.ones 1) in E1. rewrite Z.land_ones in E1 by lia.
        rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.div_mod z 2 ltac:(lia)). change (2 ^ 1) with 2 in *. lia. }
      set (k := ctz_f f (Z.shiftr z 1)) in *. set (w := Z.shiftr z 1) in *.
      rewrite Hz2, Hq. change (2 ^ 1) with 2. ring.
    + split; [lia|]. exists z. lia.
Qed.

Lemma ctz64_spec : forall z, 0 <= ctz64 z <= 64 /\ (2 ^ ctz64 z | z).
Proof.
  intros z. unfold ctz64. destruct (Z.eqb (w64 z) 0) eqn:Hw.
  - apply Z.eqb_eq in Hw. rewrite w64_mod in Hw. split; [lia|]. apply Z.mod_divide; [lia|]. exact Hw.
  - pose proof (w64_range z) as Hr. destruct (ctz_f_spec 64 (w64 z) ltac:(lia)) as [Hb Hd]. split; [cbn [Z.of_nat] in Hb; lia|].
    set (k := ctz_f 64 (w64 z)) in *. rewrite w64_mod in Hd.
    assert (Hz : z = z mod two64 + (z / two64) * two64) by (pose proof (Z.div_mod z two64 ltac:(unfold two64; lia)); lia).
    rewrite Hz. apply Z.divide_add_r; [exact Hd|]. apply Z.divide_mul_r. change two64 with (2 ^ 64).
    apply pow2_divide_le. cbn [Z.of_nat] in Hb. lia.
Qed.

Lemma var_align_sound : forall E fs x, Forall (fact_ok E) fs -> 0 <= var_align fs x <= 64 /\ (2 ^ var_align fs x | vz E x).
Proof.
  intros E fs x HF. induction HF as [|f fs Hok HF IH]; cbn [var_align].
  - split; [lia|]. exists (vz E x). lia.
  - destruct f as [c a b tk|l lo hi|l k r|l m v|x' v' j'|xb bsb]; try exact IH.
    destruct l as [c0 t0]. destruct c0; [|exact IH|exact IH]. destruct t0 as [|[y k1] t1]; [exact IH|].
    destruct k1 as [|[k1|k1|]|k1]; try exact IH. destruct t1; [|exact IH].
    destruct r as [|r|r]; [|exact IH|exact IH].
    destruct (Pos.eqb_spec x y) as [->|Hne]; [|exact IH].
    cbn [fact_ok] in Hok. change (LIN 0 [(y, 1)]) with (lvar y) in Hok. rewrite lden_lvar in Hok.
    destruct IH as [Hb Hd]. destruct (Z.le_ge_cases (Z.min k 64) (var_align fs y)) as [Hle|Hge].
    + rewrite Z.max_r by exact Hle. split; [lia | exact Hd].
    + rewrite Z.max_l by exact Hge. split; [lia|].
      assert (Hk : 0 <= k) by lia.
      apply Z.divide_trans with (2 ^ k); [apply pow2_divide_le; lia|].
      apply Z.mod_divide; [apply Z.pow_nonzero; lia|]. unfold vz. exact Hok.
Qed.

Lemma t_align_sound : forall E fs t, Forall (fact_ok E) fs -> 0 <= t_align fs t <= 64 /\ (2 ^ t_align fs t | tsum E t).
Proof.
  intros E fs t HF. induction t as [|[x k] t IH]; cbn [t_align tsum].
  - split; [lia|]. exists 0. lia.
  - destruct IH as [Hb Hd]. destruct (ctz64_spec k) as [Hkb Hkd]. destruct (var_align_sound E fs x HF) as [Hvb Hvd].
    set (a1 := Z.min (ctz64 k + var_align fs x) 64). set (a := Z.min a1 (t_align fs t)).
    split; [unfold a, a1; lia|].
    apply Z.divide_add_r.
    + apply Z.divide_trans with (2 ^ (ctz64 k + var_align fs x)).
      * apply pow2_divide_le. unfold a, a1. lia.
      * rewrite Z.pow_add_r by lia. apply divide_mul2; assumption.
    + apply Z.divide_trans with (2 ^ t_align fs t); [apply pow2_divide_le; unfold a, a1; lia | exact Hd].
Qed.

Lemma lalign_sound : forall E fs l, Forall (fact_ok E) fs -> 0 <= lalign fs l <= 64 /\ (2 ^ lalign fs l | bv_unsigned (lden E l)).
Proof.
  intros E fs l HF. destruct (ctz64_spec (l_c l)) as [Hcb Hcd]. destruct (t_align_sound E fs (l_t l) HF) as [Htb Htd].
  unfold lalign. split; [lia|].
  rewrite u_lden_mod. set (a := Z.min (ctz64 (l_c l)) (t_align fs (l_t l))).
  assert (Hd : (2 ^ a | lz E l)).
  { unfold lz. apply Z.divide_add_r.
    - apply Z.divide_trans with (2 ^ ctz64 (l_c l)); [apply pow2_divide_le; unfold a; lia | exact Hcd].
    - apply Z.divide_trans with (2 ^ t_align fs (l_t l)); [apply pow2_divide_le; unfold a; lia | exact Htd]. }
  rewrite Z.mod_eq by (unfold two64; lia). apply Z.divide_sub_r; [exact Hd|].
  apply Z.divide_mul_l. change two64 with (2 ^ 64). apply pow2_divide_le. unfold a. lia.
Qed.

(* [comment removed for export] *)
Lemma var_lowb_sound : forall E fs x k r, Forall (fact_ok E) fs -> 0 <= k -> var_lowb fs x k = Some r -> vz E x mod 2 ^ k = r.
Proof.
  intros E fs x k r HF Hk. induction HF as [|f fs Hok HF IH]; cbn [var_lowb]; [discriminate|].
  intros H. destruct f as [c a b tk|l lo hi|l k' r'|l m v|x' v' j'|xb bsb]; try exact (IH H).
  destruct l as [c0 t0]. destruct c0; [|exact (IH H)|exact (IH H)]. destruct t0 as [|[y k1] t1]; [exact (IH H)|].
  destruct k1 as [|[k1|k1|]|k1]; try exact (IH H). destruct t1; [|exact (IH H)].
  destruct (Pos.eqb x y && Z.leb k k' && Z.leb k' 64)%bool eqn:Hc; [|exact (IH H)].
  injection H as <-. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Pos.eqb_eq in H1. subst y. apply Z.leb_le in H2, H3.
  cbn [fact_ok] in Hok. change (LIN 0 [(x, 1)]) with (lvar x) in Hok. rewrite lden_lvar in Hok.
  rewrite Z.land_ones by exact Hk. rewrite <- Hok. unfold vz.
  rewrite Z.mod_mod_divide; [reflexivity|]. apply pow2_divide_le; lia.
Qed.

Lemma t_lowb_sound : forall E fs t k r, Forall (fact_ok E) fs -> 0 <= k -> t_lowb fs t k = Some r -> tsum E t mod 2 ^ k = r.
Proof.
  intros E fs t k r HF Hk. revert r. induction t as [|[x c] t IH]; intros r H; cbn [t_lowb tsum] in *.
  - injection H as <-. apply Z.mod_0_l. apply Z.pow_nonzero; lia.
  - destruct (t_lowb fs t k) as [r0|] eqn:Ht; [|discriminate]. specialize (IH r0 eq_refl).
    assert (Hpk : 2 ^ k <> 0) by (apply Z.pow_nonzero; lia).
    destruct (Z.eqb (Z.land c (Z.ones k)) 0) eqn:Hc.
    + injection H as <-. apply Z.eqb_eq in Hc. rewrite Z.land_ones in Hc by exact Hk.
      rewrite Z.add_mod by exact Hpk. rewrite Z.mul_mod by exact Hpk. rewrite Hc, Z.mul_0_l, Z.mod_0_l by exact Hpk.
      rewrite Z.add_0_l, Z.mod_mod by exact Hpk. exact IH.
    + set (t0 := Z.min (ctz64 c) k) in *. set (kk := k - t0) in *.
      destruct (var_lowb fs x kk) as [rx|] eqn:Hv; [|discriminate]. injection H as <-.
      destruct (ctz64_spec c) as [Hcb Hcd].
      assert (Ht0 : 0 <= t0 <= k) by (unfold t0; lia).
      assert (Hkk : 0 <= kk) by (unfold kk; lia).
      pose proof (var_lowb_sound E fs x kk rx HF Hkk Hv) as Hx.
      (* [comment removed for export] *)
      assert (Hd : (2 ^ t0 | c)) by (apply Z.divide_trans with (2 ^ ctz64 c); [apply pow2_divide_le; unfold t0; lia | exact Hcd]).
      destruct Hd as [c1 Hc1].
      assert (Hpkk : 2 ^ kk <> 0) by (apply Z.pow_nonzero; lia).
      assert (Hxq : vz E x = rx + 2 ^ kk * (vz E x / 2 ^ kk)) by (rewrite <- Hx; pose proof (Z.div_mod (vz E x) (2 ^ kk) Hpkk); lia).
      assert (Hcx : c * vz E x = c * rx + c1 * (vz E x / 2 ^ kk) * 2 ^ k).
      { rewrite Hxq at 1. rewrite Hc1. replace (2 ^ k) with (2 ^ t0 * 2 ^ kk) by (rewrite <- Z.pow_add_r by lia; f_equal; unfold kk; lia). ring. }
      rewrite Z.land_ones by exact Hk.
      rewrite Z.add_mod by exact Hpk. rewrite Hcx, IH.
      rewrite Z_mod_plus_full. rewrite Z.add_mod_idemp_l by exact Hpk. reflexivity.
Qed.

Lemma lowb_sound : forall E fs l k r, Forall (fact_ok E) fs -> lowb fs l k = Some r -> bv_unsigned (lden E l) mod 2 ^ k = r.
Proof.
  intros E fs l k r HF H. unfold lowb in H.
  destruct (Z.leb 0 k && Z.leb k 64)%bool eqn:Hk; [|discriminate]. apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1, Hk2.
  destruct (t_lowb fs (l_t l) k) as [r0|] eqn:Ht; [|discriminate]. injection H as <-.
  pose proof (t_lowb_sound E fs _ k r0 HF Hk1 Ht) as Hr.
  assert (Hpk : 2 ^ k <> 0) by (apply Z.pow_nonzero; lia).
  rewrite u_lden_mod. rewrite Z.mod_mod_divide by (change two64 with (2 ^ 64); apply pow2_divide_le; lia).
  rewrite Z.land_ones by exact Hk1. unfold lz. rewrite Z.add_mod by exact Hpk. rewrite Hr.
  rewrite (Z.add_mod (l_c l) r0) by exact Hpk. rewrite (Z.mod_small r0 (2 ^ k)); [reflexivity|]. subst r0. apply Z.mod_pos_bound; lia.
Qed.


(* [comment removed for export] *)
Definition tn_ok (u : Z) (t : Z * Z) : Prop := Z.land u (fst t) = snd t.



Lemma tn_and_ok : forall x y a b, tn_ok x a -> tn_ok y b -> tn_ok (Z.land x y) (tn_and a b).
Proof.
  intros x y [m1 v1] [m2 v2] H1 H2. unfold tn_ok, tn_and in *; cbn [fst snd] in *. subst v1 v2.
  apply Z.bits_inj'. intros n Hn. repeat progress (rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec).
  destruct (Z.testbit x n), (Z.testbit y n), (Z.testbit m1 n), (Z.testbit m2 n); reflexivity.
Qed.
Lemma tn_or_ok : forall x y a b, tn_ok x a -> tn_ok y b -> tn_ok (Z.lor x y) (tn_or a b).
Proof.
  intros x y [m1 v1] [m2 v2] H1 H2. unfold tn_ok, tn_or in *; cbn [fst snd] in *. subst v1 v2.
  apply Z.bits_inj'. intros n Hn. repeat progress (rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec).
  destruct (Z.testbit x n), (Z.testbit y n), (Z.testbit m1 n), (Z.testbit m2 n); reflexivity.
Qed.
Lemma tn_xor_ok : forall x y a b, tn_ok x a -> tn_ok y b -> tn_ok (Z.lxor x y) (tn_xor a b).
Proof.
  intros x y [m1 v1] [m2 v2] H1 H2. unfold tn_ok, tn_xor in *; cbn [fst snd] in *. subst v1 v2.
  apply Z.bits_inj'. intros n Hn. repeat progress (rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec).
  destruct (Z.testbit x n), (Z.testbit y n), (Z.testbit m1 n), (Z.testbit m2 n); reflexivity.
Qed.
Lemma tn_join_ok : forall x a b, tn_ok x a -> tn_ok x b -> tn_ok x (tn_join a b).
Proof.
  intros x [m1 v1] [m2 v2] H1 H2. unfold tn_ok, tn_join in *; cbn [fst snd] in *. subst v1 v2.
  apply Z.bits_inj'. intros n Hn. repeat progress (rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec).
  destruct (Z.testbit x n), (Z.testbit m1 n), (Z.testbit m2 n); reflexivity.
Qed.
Lemma tn_top_ok : forall x, tn_ok x tn_top.
Proof. intros x. unfold tn_ok, tn_top; cbn. apply Z.land_0_r. Qed.
Lemma tn_srl_ok : forall x a k, 0 <= x < 2 ^ 64 -> 0 <= k -> tn_ok x a -> tn_ok (Z.shiftr x k) (tn_srl k a).
Proof.
  intros x [m1 v1] k Hx Hk H1. unfold tn_ok, tn_srl in *; cbn [fst snd] in *. subst v1.
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lor_spec, Z.lxor_spec, !Z.shiftr_spec, Z.land_spec by lia.
  destruct (Z_lt_ge_dec (n + k) 64) as [Hlt|Hge].
  - rewrite (Z.ones_spec_low 64 n) by lia. rewrite (Z.ones_spec_low 64 (n + k)) by lia.
    destruct (Z.testbit x (n + k)), (Z.testbit m1 (n + k)); reflexivity.
  - assert (Hxb : Z.testbit x (n + k) = false) by (apply testbit_high64; lia).
    rewrite Hxb. cbn. reflexivity.
Qed.
Lemma tn_sll_ok : forall x a k, 0 <= k -> tn_ok x a -> tn_ok (Z.land (Z.shiftl x k) (Z.ones 64)) (tn_sll k a).
Proof.
  intros x [m1 v1] k Hk H1. unfold tn_ok, tn_sll in *; cbn [fst snd] in *. subst v1.
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lor_spec, !Z.land_spec.
  destruct (Z_lt_ge_dec n k) as [Hlt|Hge].
  - rewrite !Z.shiftl_spec_low by lia. rewrite (Z.ones_spec_low k n) by lia.
    destruct (Z.testbit (Z.ones 64) n), (Z.testbit m1 (n - k)); reflexivity.
  - rewrite !Z.shiftl_spec by lia. rewrite Z.land_spec. rewrite (Z.ones_spec_high k n) by lia.
    destruct (Z.testbit (Z.ones 64) n), (Z.testbit x (n - k)), (Z.testbit m1 (n - k)); reflexivity.
Qed.
Lemma tn_range_ok : forall lo hi u, 0 <= lo <= u -> u <= hi -> hi < 2 ^ 64 -> tn_ok u (tn_range lo hi).
Proof.
  intros lo hi u Hlo Hu Hhi. unfold tn_ok, tn_range. cbn [fst snd].
  set (j := if Z.eqb lo hi then 0 else Z.log2 (Z.lxor lo hi) + 1).
  assert (Hj : 0 <= j) by (unfold j; destruct (Z.eqb lo hi); [lia | pose proof (Z.log2_nonneg (Z.lxor lo hi)); lia]).
  assert (Hsh : Z.shiftr lo j = Z.shiftr hi j).
  { unfold j. destruct (Z.eqb_spec lo hi) as [->|Hne]; [reflexivity|].
    apply Z.bits_inj'. intros n Hn. rewrite !Z.shiftr_spec by lia.
    assert (Hx : Z.testbit (Z.lxor lo hi) (n + (Z.log2 (Z.lxor lo hi) + 1)) = false).
    { apply Z.bits_above_log2; [apply Z.lxor_nonneg; lia | lia]. }
    rewrite Z.lxor_spec in Hx. destruct (Z.testbit lo _), (Z.testbit hi _); cbn in Hx; congruence. }
  assert (Hu' : Z.shiftr u j = Z.shiftr lo j).
  { rewrite !Z.shiftr_div_pow2 in * by lia.
    assert (H1 : lo / 2 ^ j <= u / 2 ^ j) by (apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia | lia]).
    assert (H2 : u / 2 ^ j <= hi / 2 ^ j) by (apply Z.div_le_mono; [apply Z.pow_pos_nonneg; lia | lia]). lia. }
  apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.lnot_spec by lia.
  destruct (Z_lt_ge_dec n j) as [Hlt|Hge].
  - rewrite (Z.ones_spec_low j n) by lia. cbn. rewrite !andb_false_r. reflexivity.
  - rewrite (Z.ones_spec_high j n) by lia. cbn [negb]. rewrite !andb_true_r.
    replace n with ((n - j) + j) by lia. rewrite <- !Z.shiftr_spec by lia. rewrite Hu'. reflexivity.
Qed.

Lemma var_bits_ok : forall E fs x, Forall (fact_ok E) fs -> tn_ok (vz E x) (var_bits fs x).
Proof.
  intros E fs x HF. induction HF as [|f fs Hok HF IH]; cbn [var_bits]; [apply tn_top_ok|].
  destruct f as [c a b tk|l lo hi|l k r|l m v|x' v' j'|xb bsb]; try exact IH.
  destruct l as [c0 t0]. destruct c0; [|exact IH|exact IH]. destruct t0 as [|[y k1] t1]; [exact IH|].
  destruct k1 as [|[k1|k1|]|k1]; try exact IH. destruct t1; [|exact IH].
  destruct (Pos.eqb_spec x y) as [->|Hne]; [|exact IH].
  apply tn_join_ok; [|exact IH]. cbn [fact_ok] in Hok. change (LIN 0 [(y, 1)]) with (lvar y) in Hok. rewrite lden_lvar in Hok.
  exact Hok.
Qed.

Lemma tn_low_ok : forall E fs l, Forall (fact_ok E) fs -> tn_ok (bv_unsigned (lden E l)) (tn_low fs l).
Proof.
  intros E fs l HF. unfold tn_low.
  assert (Hg : forall ks, tn_ok (bv_unsigned (lden E l))
     ((fix go (ks : list Z) := match ks with [] => tn_top | k :: ks' => match lowb fs l k with Some r => (Z.ones k, r) | None => go ks' end end) ks)).
  { induction ks as [|k ks IH]; [apply tn_top_ok|]. cbn.
    destruct (lowb fs l k) as [r|] eqn:Hl; [|exact IH].
    pose proof (lowb_sound E fs l k r HF Hl) as Hr. unfold tn_ok; cbn [fst snd].
    unfold lowb in Hl. destruct (Z.leb 0 k && Z.leb k 64)%bool eqn:Hk; [|discriminate]. apply andb_prop in Hk as [Hk _]. apply Z.leb_le in Hk.
    rewrite Z.land_ones by exact Hk. exact Hr. }
  exact (Hg [64; 32; 16; 12; 8; 4; 3; 2; 1]).
Qed.



Lemma align_iv_sound : forall a r u, 0 <= a -> fst r <= u <= snd r -> (2 ^ a | u) -> fst (align_iv a r) <= u <= snd (align_iv a r).
Proof.
  intros a [lo hi] u Ha Hr [q Hq]. unfold align_iv. cbn [fst snd] in *.
  assert (Hm : 0 < 2 ^ a) by (apply Z.pow_pos_nonneg; lia). set (m := 2 ^ a) in *. subst u. split.
  - apply Z.le_trans with (q * m); [|lia]. apply Z.mul_le_mono_nonneg_r; [lia|].
    assert (Hlt : (lo + m - 1) / m < q + 1) by (apply Z.div_lt_upper_bound; [lia | nia]). lia.
  - apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_lower_bound; lia.
Qed.

Lemma round_to_sound : forall k r v x, 0 <= k -> x mod 2 ^ k = r -> fst v <= x <= snd v -> fst (round_to k r v) <= x <= snd (round_to k r v).
Proof.
  intros k r [lo hi] x Hk Hx Hv. unfold round_to. cbn [fst snd] in *.
  assert (Hm : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). set (m := 2 ^ k) in *.
  pose proof (Z.mod_pos_bound (r - lo) m Hm). pose proof (Z.mod_pos_bound (hi - r) m Hm).
  assert (E1 : (x - lo) mod m = (r - lo) mod m) by (rewrite <- Hx, Zminus_mod_idemp_l; reflexivity).
  assert (E2 : (hi - x) mod m = (hi - r) mod m) by (rewrite <- Hx, Zminus_mod_idemp_r; reflexivity).
  split.
  - pose proof (Z.mod_le (x - lo) m ltac:(lia) Hm). lia.
  - pose proof (Z.mod_le (hi - x) m ltac:(lia) Hm). lia.
Qed.

Lemma lround_sound : forall E fs l v, Forall (fact_ok E) fs ->
  (exists v0, eqm v0 (bv_unsigned (lden E l)) /\ fst v <= v0 <= snd v) ->
  exists v0, eqm v0 (bv_unsigned (lden E l)) /\ fst (lround fs l v) <= v0 <= snd (lround fs l v).
Proof.
  intros E fs l v HF (v0 & Hv0 & Hr). unfold lround. destruct (nowrap v); [exists v0; split; assumption|].
  destruct (lowb fs l 8) as [r|] eqn:Hl; [|exists v0; split; assumption].
  exists v0. split; [exact Hv0|]. apply round_to_sound; [lia| |exact Hr].
  rewrite <- (lowb_sound E fs l 8 r HF Hl). unfold eqm in Hv0.
  rewrite <- (Z.mod_mod_divide v0 two64 (2 ^ 8)) by (exists (2 ^ 56); reflexivity).
  rewrite <- (Z.mod_mod_divide (bv_unsigned (lden E l)) two64 (2 ^ 8)) by (exists (2 ^ 56); reflexivity). rewrite Hv0. reflexivity.
Qed.

Lemma rel_base_sound : forall E fs l, Forall (fact_ok E) fs ->
  exists v, eqm v (bv_unsigned (lden E l)) /\ fst (rel_base fs l) <= v <= snd (rel_base fs l).
Proof.
  intros E fs l HF. unfold rel_base. apply frange_same_sound; [exact HF|].
  apply ne_int_sound; [exact HF|].
  apply rel_iv_sound; [exact HF | exact HF|].
  exists (izl E l). split; [eapply eqm_trans; [apply izl_eqm | apply eqm_sym, u_eqm_lz] | exact (l_iv_sound E fs l HF)].
Qed.

(* [comment removed for export] *)
Lemma rel_iv2_sound : forall E fs all ta l acc, Forall (fact_ok E) fs -> Forall (fact_ok E) all ->
  (exists v, eqm v (bv_unsigned (lden E l)) /\ fst acc <= v <= snd acc) ->
  exists v, eqm v (bv_unsigned (lden E l)) /\ fst (rel_iv2 fs all ta l acc) <= v <= snd (rel_iv2 fs all ta l acc).
Proof.
  intros E fs all ta l acc HF Hall. revert acc. induction HF as [|f fs Hok HF IH]; intros acc (v & Hv & Hacc); cbn [rel_iv2]; [exists v; split; assumption|].
  destruct (rel_ok3 ta f); [|exact (IH acc (ex_intro _ v (conj Hv Hacc)))].
  destruct (fact_g all f) as [[[g lo0] hi0]|] eqn:Hg; [|exact (IH acc (ex_intro _ v (conj Hv Hacc)))].
  pose proof (fact_g_sound E all f g lo0 hi0 Hall Hok Hg) as Hgr0.
  assert (Hk : forall k acc', ne_int_fixl k all g acc' = ne_int_fix (List.length k) all g acc')
    by (induction k as [|f' k IHk]; intros acc'; [reflexivity | cbn [ne_int_fixl ne_int_fix List.length]; rewrite IHk; reflexivity]).
  destruct (ne_int_fixl all all g (lo0, hi0)) as [lo hi] eqn:Hne.
  destruct (ne_int_fix_sound E all g (List.length all) (lo0, hi0) Hall (ex_intro _ (bv_unsigned (lden E g)) (conj (eqm_refl _) Hgr0)))
    as (ug & Hug & Hgr). rewrite <- Hk, Hne in Hgr. cbn [fst snd] in Hgr.
  apply IH.
  destruct (rel_base_sound E all (lsub l g) Hall) as (w1 & Hw1 & R1).
  destruct (rel_base_sound E all (ladd l g) Hall) as (w2 & Hw2 & R2).
  assert (He1 : eqm v (ug + w1)).
  { eapply eqm_trans; [exact Hv|]. eapply eqm_trans; [apply u_eqm_lz|]. apply eqm_sym.
    eapply eqm_trans; [apply eqm_add; [eapply eqm_trans; [exact Hug | apply u_eqm_lz] | eapply eqm_trans; [exact Hw1 | apply u_eqm_lz]]|].
    eapply eqm_trans; [apply eqm_add; [apply eqm_refl | apply lz_lsub]|].
    replace (lz E g + (lz E l - lz E g)) with (lz E l) by lia. apply eqm_refl. }
  assert (He2 : eqm v (w2 - ug)).
  { eapply eqm_trans; [exact Hv|]. eapply eqm_trans; [apply u_eqm_lz|]. apply eqm_sym.
    eapply eqm_trans; [apply eqm_sub; [eapply eqm_trans; [exact Hw2 | apply u_eqm_lz] | eapply eqm_trans; [exact Hug | apply u_eqm_lz]]|].
    eapply eqm_trans; [apply eqm_sub; [apply lz_ladd | apply eqm_refl]|].
    replace (lz E l + lz E g - lz E g) with (lz E l) by lia. apply eqm_refl. }
  destruct (meet_win_sound v _ acc (lo + fst (rel_base all (lsub l g)), hi + snd (rel_base all (lsub l g))) He1 Hacc ltac:(cbn [fst snd]; lia))
    as (v1 & Hv1 & Hacc1).
  assert (He2' : eqm v1 (w2 - ug)) by (eapply eqm_trans; [exact Hv1 | exact He2]).
  destruct (meet_win_sound v1 _ _ (fst (rel_base all (ladd l g)) - hi, snd (rel_base all (ladd l g)) - lo) He2' Hacc1 ltac:(cbn [fst snd]; lia))
    as (v2 & Hv2 & Hacc2).
  exists v2. split; [eapply eqm_trans; [exact Hv2 | eapply eqm_trans; [exact Hv1 | exact Hv]] | exact Hacc2].
Qed.

Lemma irange0_sound : forall E fs l, Forall (fact_ok E) fs -> fst (irange0 fs l) <= bv_unsigned (lden E l) <= snd (irange0 fs l).
Proof.
  intros E fs l HF. unfold irange0.
  - assert (Hv : eqm (izl E l) (bv_unsigned (lden E l))) by (eapply eqm_trans; [apply izl_eqm | apply eqm_sym, u_eqm_lz]).
    assert (Hk : forall k acc, ne_int_fixl k fs l acc = ne_int_fix (List.length k) fs l acc)
      by (induction k as [|f k IHk]; intros acc'; [reflexivity | cbn [ne_int_fixl ne_int_fix List.length]; rewrite IHk; reflexivity]).
    rewrite Hk.
    destruct (ne_int_fix_sound E fs l (List.length fs) _ HF
               (lround_sound E fs l _ HF (rel_iv_sound E fs fs l (l_iv fs l) HF HF (ex_intro _ (izl E l) (conj Hv (l_iv_sound E fs l HF))))))
      as (v' & Hv' & Hr).
    pose proof (wrap_iv_sound E l v' _ Hv' Hr) as H0.
    pose proof (ne_refine'_sound E fs l _ HF H0) as H.
    destruct (Z.ltb 0 (lalign fs l)) eqn:Ha; [|exact H].
    destruct (lalign_sound E fs l HF) as [Hab Had]. apply align_iv_sound; [lia | exact H | exact Had].
Qed.

Lemma ldiv8_eqm : forall E l l', ldiv8 l = Some l' -> eqm (lz E l) (8 * lz E l').
Proof.
  intros E [c t] l' H. unfold ldiv8 in H. cbn [l_c l_t] in H.
  destruct (Z.eqb (Z.rem (sgn64 c) 8) 0 && forallb (fun '(_, k) => Z.eqb (Z.rem (sgn64 k) 8) 0) t)%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hc Ht]. apply Z.eqb_eq in Hc.
  unfold lz; cbn [l_c l_t].
  assert (Hq : forall k, Z.rem (sgn64 k) 8 = 0 -> eqm (8 * w64 (Z.quot (sgn64 k) 8)) k).
  { intros k Hk. eapply eqm_trans; [apply eqm_mul; [apply eqm_refl | apply eqm_w64]|].
    assert (E8 : 8 * Z.quot (sgn64 k) 8 = sgn64 k) by (pose proof (Z.quot_rem' (sgn64 k) 8) as X; rewrite Hk in X; lia).
    rewrite E8. apply sgn64_eqm. }
  assert (HT : eqm (8 * tsum E (List.map (fun '(x, k) => (x, w64 (Z.quot (sgn64 k) 8))) t)) (tsum E t)).
  { clear Hc. induction t as [|[x k] t IH]; cbn [List.map tsum]; [apply eqm_refl|].
    cbn [forallb] in Ht. apply andb_prop in Ht as [Hk Ht]. apply Z.eqb_eq in Hk.
    replace (8 * (w64 (Z.quot (sgn64 k) 8) * vz E x + tsum E (List.map (fun '(x0, k0) => (x0, w64 (Z.quot (sgn64 k0) 8))) t)))
      with (8 * w64 (Z.quot (sgn64 k) 8) * vz E x + 8 * tsum E (List.map (fun '(x0, k0) => (x0, w64 (Z.quot (sgn64 k0) 8))) t)) by ring.
    apply eqm_add; [apply eqm_mul; [exact (Hq k Hk) | apply eqm_refl] | exact (IH Ht)]. }
  apply eqm_sym. rewrite Z.mul_add_distr_l. apply eqm_add; [exact (Hq c Hc) | exact HT].
Qed.

Theorem irange_ref_sound : forall E fs l, Forall (fact_ok E) fs -> fst (irange_ref fs l) <= bv_unsigned (lden E l) <= snd (irange_ref fs l).
Proof.
  intros E fs l HF. unfold irange_ref. destruct (is_const l) as [c|] eqn:Hc.
  - rewrite (is_const_u E l c Hc). cbn. lia.
  - pose proof (irange0_sound E fs l HF) as H0.
    destruct (Z.eqb (snd (irange0 fs l)) (fst (irange0 fs l))); [exact H0|].
    destruct (ldiv8 l) as [l'|] eqn:Hd; [|exact H0].
    pose proof (irange0_sound E fs l' HF) as H1.
    destruct (Z.leb 0 (fst (irange0 fs l')) && Z.ltb (8 * snd (irange0 fs l')) two64)%bool eqn:Hw; [|exact H0].
    apply andb_prop in Hw as [Hw1 Hw2]. apply Z.leb_le in Hw1. apply Z.ltb_lt in Hw2.
    assert (Hv : bv_unsigned (lden E l) = 8 * bv_unsigned (lden E l')).
    { rewrite u_lden_mod. pose proof (ldiv8_eqm E l l' Hd) as X. unfold eqm in X. rewrite X.
      rewrite <- (Z.mul_mod_idemp_r 8 (lz E l') two64) by (unfold two64; lia). rewrite <- u_lden_mod.
      apply Z.mod_small. lia. }
    unfold iv_meet. cbn [fst snd]. rewrite Hv. lia.
Qed.
(* [comment removed for export] *)
Lemma vr_get_set : forall t y r x, vr_get (tset y r t) x = if Pos.eqb x y then r else vr_get t x.
Proof.
  intros t y r x. unfold vr_get. destruct (Pos.eqb x y) eqn:E.
  - apply Pos.eqb_eq in E. subst. rewrite tget_tset_same. reflexivity.
  - apply Pos.eqb_neq in E. rewrite tget_tset_other by congruence. reflexivity.
Qed.
Lemma vr_tbl_eq : forall fs x, vr_get (vr_tbl fs) x = var_range fs x.
Proof.
  induction fs as [|f fs IH]; intros x; [unfold vr_get; cbn [vr_tbl var_range]; rewrite tget_empty; reflexivity|].
  destruct f as [c a b tk|l lo hi|l k r|l m v|l o z|l bs]; cbn [vr_tbl var_range]; try apply IH.
  - destruct l as [c0 t0]. destruct c0 as [|p|p]; try apply IH. destruct t0 as [|[y k] t1]; try apply IH.
    destruct k as [|q|q]; try apply IH. destruct q; try apply IH. destruct t1; try apply IH.
    cbv zeta. rewrite vr_get_set. destruct (Pos.eqb x y) eqn:E; [|apply IH]. apply Pos.eqb_eq in E. subst. rewrite IH. reflexivity.
  - destruct l as [c0 t0]. destruct c0 as [|p|p]; try apply IH. destruct t0 as [|[y k] t1]; try apply IH.
    destruct k as [|q|q]; try apply IH. destruct q; try apply IH. destruct t1; try apply IH.
    destruct (Z.leb 0 m) eqn:Em.
    + cbv zeta. rewrite vr_get_set. destruct (Pos.eqb x y) eqn:E; cbn [andb]; [|apply IH]. apply Pos.eqb_eq in E. subst. rewrite IH. reflexivity.
    + rewrite andb_false_r. apply IH.
Qed.

Lemma ne_sub_cons : forall f fs, ne_sub (f :: fs) = if is_ne f then f :: ne_sub fs else ne_sub fs.
Proof. reflexivity. Qed.
Lemma ne_refine_sub : forall fs l acc, ne_refine (ne_sub fs) l acc = ne_refine fs l acc.
Proof.
  induction fs as [|f fs IH]; intros l acc; [reflexivity|]. rewrite ne_sub_cons.
  destruct f as [c a b tk|? ? ?|? ? ?|? ? ?|? ? ?|? ?]; cbn [is_ne ne_refine]; try apply IH.
  destruct (ne_c c tk) eqn:Ec; cbn [ne_refine]; rewrite ?Ec; cbn [andb]; [|apply IH].
  destruct (ne_pre l a b); [|apply IH]. cbv zeta.
  destruct (terms_eqb (l_t l) (l_t (if terms_eqb (l_t l) (l_t (lsub b a)) then lsub b a else lsub a b))); apply IH.
Qed.
Lemma ne_int_sub : forall fs l acc, ne_int (ne_sub fs) l acc = ne_int fs l acc.
Proof.
  induction fs as [|f fs IH]; intros l acc; [reflexivity|]. rewrite ne_sub_cons.
  destruct f as [c a b tk|? ? ?|? ? ?|? ? ?|? ? ?|? ?]; cbn [is_ne ne_int]; try apply IH.
  destruct (ne_c c tk) eqn:Ec; cbn [ne_int]; rewrite ?Ec; cbn [andb]; [|apply IH].
  destruct (ne_pre l a b); [|apply IH]. cbv zeta.
  destruct (terms_eqb (l_t l) (l_t (if terms_eqb (l_t l) (l_t (lsub b a)) then lsub b a else lsub a b))); apply IH.
Qed.
Lemma ne_fixl_sub : forall k fs l acc, ne_fixl k (ne_sub fs) l acc = ne_fixl k fs l acc.
Proof. induction k as [|f k IH]; intros fs l acc; [reflexivity|]. cbn [ne_fixl]. rewrite ne_refine_sub. cbv zeta. destruct (_ && _)%bool; [reflexivity | apply IH]. Qed.
Lemma ne_int_fixl_sub : forall k fs l acc, ne_int_fixl k (ne_sub fs) l acc = ne_int_fixl k fs l acc.
Proof. induction k as [|f k IH]; intros fs l acc; [reflexivity|]. cbn [ne_int_fixl]. rewrite ne_int_sub. cbv zeta. destruct (_ && _)%bool; [reflexivity | apply IH]. Qed.

Section Eq.
Variable fs : list fact.
Let vt := vr_tbl fs.
Let ne := ne_sub fs.
#[using="Type"] Lemma var_rangeF_eq : forall x, var_rangeF vt ne fs x = var_range' fs x.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. unfold var_rangeF, var_range', ne_refine', vt, ne. rewrite ne_fixl_sub, vr_tbl_eq. reflexivity. Qed.
#[using="Type"] Lemma t_ivF_eq : forall t, t_ivF vt ne fs t = t_iv fs t.
Proof. LiaFast.lf_pins LiaFast.u0. induction t as [|[x k] t IH]; [reflexivity|]. cbn [t_ivF t_iv]. rewrite var_rangeF_eq, IH. reflexivity. Qed.
#[using="Type"] Lemma l_ivF_eq : forall l, l_ivF vt ne fs l = l_iv fs l.
Proof. LiaFast.lf_pins LiaFast.u0. intros l. unfold l_ivF, l_iv. rewrite t_ivF_eq. reflexivity. Qed.
#[using="Type"] Lemma srangeF_eq : forall l, srangeF vt ne fs l = srange fs l.
Proof. LiaFast.lf_pins LiaFast.u0. intros l. unfold srangeF, srange, ne. rewrite l_ivF_eq, ne_int_fixl_sub. reflexivity. Qed.
#[using="Type"] Lemma fact_gF_eq : forall f, fact_gF vt ne fs f = fact_g fs f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros f. destruct f as [c a b tk|? ? ?|? ? ?|? ? ?|? ? ?|? ?]; try reflexivity.
  unfold fact_gF, fact_g, base_rangeF, base_range. rewrite !l_ivF_eq, !srangeF_eq. reflexivity.
Qed.
#[using="Type"] Lemma rel_ivF_eq : forall fs0 l acc, rel_ivF vt ne fs fs0 l acc = rel_iv fs0 fs l acc.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction fs0 as [|f fs0 IH]; intros l acc; [reflexivity|]. cbn [rel_ivF rel_iv].
  destruct (rel_ok l f); [|apply IH]. rewrite fact_gF_eq. destruct (fact_g fs f) as [[[g lo] hi]|]; [|apply IH].
  cbv zeta. rewrite !l_ivF_eq. apply IH.
Qed.
#[using="Type"] Lemma irange0F_eq : forall l, irange0F vt ne fs l = irange0 fs l.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l. unfold irange0F, irange0, ne_refine'. rewrite rel_ivF_eq, l_ivF_eq. unfold ne. rewrite ne_int_fixl_sub, ne_fixl_sub. reflexivity.
Qed.
#[using="Type"] Lemma rel_baseF_eq : forall l, rel_baseF vt ne fs l = rel_base fs l.
Proof. LiaFast.lf_pins LiaFast.u0. intros l. unfold rel_baseF, rel_base, ne. rewrite rel_ivF_eq, l_ivF_eq, ne_int_sub. reflexivity. Qed.
#[using="Type"] Lemma rel_iv2F_eq : forall fs0 ta l acc, rel_iv2F vt ne fs fs0 ta l acc = rel_iv2 fs0 fs ta l acc.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction fs0 as [|f fs0 IH]; intros ta l acc; [reflexivity|]. cbn [rel_iv2F rel_iv2].
  destruct (rel_ok3 ta f); [|apply IH]. rewrite fact_gF_eq. destruct (fact_g fs f) as [[[g lo0] hi0]|]; [|apply IH].
  unfold ne at 1. rewrite ne_int_fixl_sub. destruct (ne_int_fixl fs fs g (lo0, hi0)) as [lo hi]. cbv zeta. rewrite !rel_baseF_eq. apply IH.
Qed.
#[using="Type"] Lemma srl_oneF_eq : forall l g lo hi q k acc, srl_oneF vt ne fs l g lo hi q k acc = srl_one fs l g lo hi q k acc.
Proof. LiaFast.lf_pins LiaFast.u0. intros. unfold srl_oneF, srl_one. cbv zeta. rewrite rel_baseF_eq, rel_iv2F_eq. reflexivity. Qed.
#[using="Type"] Lemma srl_termsF_eq : forall l g lo hi t acc, srl_termsF vt ne fs l g lo hi t acc = srl_terms fs l g lo hi t acc.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l g lo hi t. induction t as [|[q cq] t IH]; intros acc; [reflexivity|]. cbn [srl_termsF srl_terms].
  destruct (pow2_neg cq); [rewrite srl_oneF_eq|]; apply IH.
Qed.
#[using="Type"] Lemma srl_ivF_eq : forall fs0 l acc, srl_ivF vt ne fs fs0 l acc = srl_iv fs0 fs l acc.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction fs0 as [|f fs0 IH]; intros l acc; [reflexivity|].
  destruct f as [c a b tk|g lo hi|? ? ?|? ? ?|? ? ?|? ?]; cbn [srl_ivF srl_iv]; try apply IH.
  - destruct (shares (l_t l) (l_t a) || shares (l_t l) (l_t b))%bool; [|apply IH]. rewrite fact_gF_eq.
    destruct (fact_g fs (FCond c a b tk)) as [[[g lo] hi]|]; [rewrite srl_termsF_eq|]; apply IH.
  - destruct (shares (l_t l) (l_t g)); [rewrite srl_termsF_eq|]; apply IH.
Qed.
#[using="Type"] Lemma irange_x0F_eq : forall l, irange_x0F vt ne fs l =
  (let v := ne_int_fixl fs fs l (lround fs l (srl_iv fs fs l (rel_iv2 fs fs (l_t l) l (rel_iv fs fs l (l_iv fs l))))) in
   let r := ne_refine' fs l (wrap_iv v) in
   let a := lalign fs l in if Z.ltb 0 a then align_iv a r else r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros l. unfold irange_x0F, ne_refine'. rewrite srl_ivF_eq, rel_iv2F_eq, rel_ivF_eq, l_ivF_eq. unfold ne. rewrite ne_int_fixl_sub, ne_fixl_sub. reflexivity.
Qed.
End Eq.
Theorem irange_eq : forall fs l, irange fs l = irange_ref fs l.
Proof.
  intros fs l. unfold irange, irange_ref. destruct (is_const l) eqn:Ec; [reflexivity|]. destruct (longer IR_NUM_MIN fs); [|reflexivity].
  cbv zeta. destruct (IrN.prepS (ne_sub fs) fs (List.filter IrN.is_bare fs) l) as [T cs] eqn:Ep.
  rewrite (irange0S_eq fs l T cs Ep l (fun f => eq_refl)), irange0F_eq.
  destruct (Z.eqb _ _); [reflexivity|]. destruct (ldiv8 l) as [l'|] eqn:Ed; [|reflexivity].
  rewrite (irange0S_eq fs l T cs Ep l' (rel_okN_ldiv8 l l' Ed)), irange0F_eq. reflexivity.
Qed.
Theorem irange_sound : forall E fs l, Forall (fact_ok E) fs -> fst (irange fs l) <= bv_unsigned (lden E l) <= snd (irange fs l).
Proof. intros E fs l HF. rewrite irange_eq. exact (irange_ref_sound E fs l HF). Qed.

Lemma tn_of_ok : forall E fs l, Forall (fact_ok E) fs -> tn_ok (bv_unsigned (lden E l)) (tn_of fs l).
Proof.
  intros E fs l HF. unfold tn_of.
  destruct (is_const l) as [c|] eqn:Hc.
  - unfold tn_ok; cbn [fst snd]. rewrite (is_const_u E l c Hc). rewrite Z.land_ones by lia.
    destruct (is_const_sound E l c Hc) as [_ Hr]. apply Z.mod_small. exact Hr.
  - pose proof (irange_sound E fs l HF) as Hr. destruct (irange fs l) as [lo hi] eqn:Hir. cbn [fst snd] in Hr.
    pose proof (u_range E l) as Ul.
    assert (Ht1 : tn_ok (bv_unsigned (lden E l)) (tn_join (tn_range (Z.max 0 lo) (Z.min (Z.ones 64) hi)) (tn_low fs l))).
    { apply tn_join_ok; [|apply tn_low_ok; exact HF].
      change two64 with (2 ^ 64) in Ul. rewrite Z.ones_equiv.
      apply tn_range_ok; lia. }
    destruct l as [c0 t0]. destruct c0; [|exact Ht1|exact Ht1]. destruct t0 as [|[y k1] t1]; [exact Ht1|].
    destruct k1 as [|[k1|k1|]|k1]; try exact Ht1. destruct t1; [|exact Ht1].
    apply tn_join_ok; [exact Ht1|]. change (LIN 0 [(y, 1)]) with (lvar y). rewrite lden_lvar. apply var_bits_ok. exact HF.
Qed.

(* [comment removed for export] *)
Lemma fcond_lookup_sound : forall E fs c a b tk, Forall (fact_ok E) fs -> fcond_lookup fs c a b = Some tk ->
  branch_taken c (lden E a) (lden E b) = tk.
Proof.
  intros E fs c a b tk Hf. induction Hf as [|f fs Hok Hf IH]; cbn [fcond_lookup]; [discriminate|].
  destruct f as [c' a' b' tk'|l lo hi|l k r|l m v|x' v' j'|xb bsb]; [|exact IH|exact IH|exact IH|exact IH|exact IH].
  destruct (match c, c' with
            | BC_EQ, BC_EQ | BC_NE, BC_NE | BC_LT, BC_LT | BC_GE, BC_GE | BC_LTU, BC_LTU | BC_GEU, BC_GEU => true
            | _, _ => false end && lin_eqb a a' && lin_eqb b b')%bool eqn:Hm; [|exact IH].
  intros H. injection H as <-. apply andb_prop in Hm as [Hm Hb]. apply andb_prop in Hm as [Hc Ha].
  apply lin_eqb_true in Ha, Hb. subst a' b'. cbn [fact_ok] in Hok.
  destruct c; destruct c'; try discriminate; exact Hok.
Qed.

Lemma ltu_by_range_sound : forall E fs a b v, Forall (fact_ok E) fs -> ltu_by_range fs a b = Some v ->
  bv_ltu (lden E a) (lden E b) = v.
Proof.
  intros E fs a b v HF H. unfold ltu_by_range in H.
  pose proof (irange_sound E fs a HF) as Ra. pose proof (irange_sound E fs b HF) as Rb.
  destruct (irange fs a) as [alo ahi]. destruct (irange fs b) as [blo bhi]. cbn [fst snd] in Ra, Rb.
  unfold bv_ltu. pose proof (u_range E a) as Ua. pose proof (u_range E b) as Ub.
  destruct (Z.ltb_spec ahi blo).
  - injection H as <-. apply Z.ltb_lt. lia.
  - destruct (Z.leb_spec bhi alo).
    + injection H as <-. apply Z.ltb_ge. lia.
    + pose proof (irange_sound E fs (lsub b a) HF) as R1. destruct (irange fs (lsub b a)) as [lo1 hi1]. cbn [fst snd] in R1.
      destruct (Z.leb 1 lo1 && Z.ltb (hi1 + ahi) two64)%bool eqn:HH1.
      * injection H as <-. apply andb_prop in HH1 as [H1a H1b]. apply Z.leb_le in H1a. apply Z.ltb_lt in H1b. apply Z.ltb_lt.
        destruct (Z.le_gt_cases (bv_unsigned (lden E b)) (bv_unsigned (lden E a))) as [Hle|Hgt]; [|exact Hgt].
        exfalso. rewrite lden_lsub, bv_sub_unsigned in R1. unfold bv_wrap, bv_modulus in R1. change (2 ^ Z.of_N 64) with two64 in R1.
        destruct (Z.eq_dec (bv_unsigned (lden E b)) (bv_unsigned (lden E a))) as [Heq|Hne].
        -- rewrite Heq, Z.sub_diag, Z.mod_0_l in R1 by (unfold two64; lia). lia.
        -- replace (bv_unsigned (lden E b) - bv_unsigned (lden E a)) with ((bv_unsigned (lden E b) - bv_unsigned (lden E a) + two64) + (-1) * two64) in R1 by lia.
           rewrite Z_mod_plus_full in R1. rewrite Z.mod_small in R1 by lia. lia.
      * pose proof (irange_sound E fs (lsub a b) HF) as R2. destruct (irange fs (lsub a b)) as [lo2 hi2]. cbn [fst snd] in R2.
        destruct (Z.ltb (hi2 + bhi) two64) eqn:HH2; [|discriminate]. injection H as <-. apply Z.ltb_lt in HH2. apply Z.ltb_ge.
        destruct (Z.le_gt_cases (bv_unsigned (lden E b)) (bv_unsigned (lden E a))) as [Hle|Hgt]; [exact Hle|].
        exfalso. rewrite lden_lsub, bv_sub_unsigned in R2. unfold bv_wrap, bv_modulus in R2. change (2 ^ Z.of_N 64) with two64 in R2.
        replace (bv_unsigned (lden E a) - bv_unsigned (lden E b)) with ((bv_unsigned (lden E a) - bv_unsigned (lden E b) + two64) + (-1) * two64) in R2 by lia.
        rewrite Z_mod_plus_full in R2. rewrite Z.mod_small in R2 by lia. lia.
Qed.

Lemma eq_by_range_sound : forall E fs a b v, Forall (fact_ok E) fs -> eq_by_range fs a b = Some v ->
  bv_eqb (lden E a) (lden E b) = v.
Proof.
  intros E fs a b v HF H. unfold eq_by_range in H.
  pose proof (irange_sound E fs (lsub b a) HF) as R. destruct (irange fs (lsub b a)) as [lo hi]. cbn [fst snd] in R.
  rewrite lden_lsub, bv_sub_unsigned in R. unfold bv_wrap, bv_modulus in R. change (2 ^ Z.of_N 64) with two64 in R.
  pose proof (u_range E a) as Ua. pose proof (u_range E b) as Ub. unfold bv_eqb.
  destruct (Z.eqb lo 0 && Z.eqb hi 0)%bool eqn:HH1.
  - injection H as <-. apply andb_prop in HH1 as [H1a H1b]. apply Z.eqb_eq in H1a, H1b. subst lo hi.
    assert (Hm : (bv_unsigned (lden E b) - bv_unsigned (lden E a)) mod two64 = 0) by lia.
    apply Z.mod_divide in Hm; [|unfold two64; lia]. destruct Hm as [q Hq]. assert (q = 0) by (unfold two64 in *; nia). subst q.
    apply Z.eqb_eq. lia.
  - destruct (Z.leb 1 lo && Z.leb hi M64)%bool eqn:HH2.
    + injection H as <-.
      apply andb_prop in HH2 as [H2a _]. apply Z.leb_le in H2a. apply Z.eqb_neq. intros Heq. rewrite Heq, Z.sub_diag, Z.mod_0_l in R by (unfold two64; lia). lia.
    + pose proof (irange_sound E fs (lsub a b) HF) as R'. destruct (irange fs (lsub a b)) as [lo' hi']. cbn [fst snd] in R'.
      rewrite lden_lsub, bv_sub_unsigned in R'. unfold bv_wrap, bv_modulus in R'. change (2 ^ Z.of_N 64) with two64 in R'.
      destruct (Z.leb 1 lo' && Z.leb hi' M64)%bool eqn:HH3; [|discriminate]. injection H as <-.
      apply andb_prop in HH3 as [H3a _]. apply Z.leb_le in H3a. apply Z.eqb_neq. intros Heq. rewrite Heq, Z.sub_diag, Z.mod_0_l in R' by (unfold two64; lia). lia.
Qed.

Lemma lden_eq_of_off0 : forall E a b, lin_off a b = Some 0 -> lden E a = lden E b.
Proof.
  intros E a b Hd. destruct (lin_off_sound E _ _ _ Hd) as [Hv _]. rewrite lden_lsub in Hv.
  apply bv_eq. pose proof (f_equal bv_unsigned Hv) as Hu. rewrite bv_sub_unsigned, u_Z_to_bv in Hu.
  unfold bv_wrap, bv_modulus in Hu. change (2 ^ Z.of_N 64) with two64 in Hu. rewrite Z.mod_0_l in Hu by (unfold two64; lia).
  pose proof (u_range E a) as Ra. pose proof (u_range E b) as Rb.
  apply Z.mod_divide in Hu; [|unfold two64; lia]. destruct Hu as [q Hq].
  assert (q = 0) by (unfold two64 in *; nia). subst q. lia.
Qed.

Lemma lts_ltu : forall E fs a b, Forall (fact_ok E) fs -> nonneg2 fs a b = true -> bv_lts (lden E a) (lden E b) = bv_ltu (lden E a) (lden E b).
Proof.
  intros E fs a b Hf H. unfold nonneg2 in H. apply andb_prop in H as [Ha Hb]. apply Z.ltb_lt in Ha, Hb.
  pose proof (irange_sound E fs a Hf) as Ra. pose proof (irange_sound E fs b Hf) as Rb.
  pose proof (u_range E a) as Ua. pose proof (u_range E b) as Ub.
  unfold bv_lts, bv_ltu, bv_signed, bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with 9223372036854775808. change (bv_modulus 64) with 18446744073709551616.
  unfold T63 in *. rewrite !Z.mod_small by (unfold two64 in *; lia). f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma swin_sound : forall E fs l, Forall (fact_ok E) fs ->
  exists v, eqm v (bv_unsigned (lden E l)) /\ fst (swin fs l) <= v <= snd (swin fs l).
Proof.
  intros E fs l HF. unfold swin.
  assert (Hv : eqm (izl E l) (bv_unsigned (lden E l))) by (eapply eqm_trans; [apply izl_eqm | apply eqm_sym, u_eqm_lz]).
  assert (Hk : forall k acc, ne_int_fixl k fs l acc = ne_int_fix (List.length k) fs l acc)
    by (induction k as [|f k IHk]; intros acc'; [reflexivity | cbn [ne_int_fixl ne_int_fix List.length]; rewrite IHk; reflexivity]).
  rewrite Hk.
  exact (ne_int_fix_sound E fs l (List.length fs) _ HF
           (lround_sound E fs l _ HF (rel_iv_sound E fs fs l (l_iv fs l) HF HF (ex_intro _ (izl E l) (conj Hv (l_iv_sound E fs l HF)))))).
Qed.
Lemma signed_eqm : forall x : bv 64, eqm (bv_signed x) (bv_unsigned x) /\ - T63 <= bv_signed x < T63.
Proof.
  intros x. pose proof (bv_unsigned_in_range _ x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with two64 in R.
  unfold bv_signed, bv_swrap, bv_wrap, eqm. change (bv_half_modulus 64) with T63. change (bv_modulus 64) with two64. unfold T63, two64 in *.
  split; [|Z.div_mod_to_equations; lia].
  rewrite Zminus_mod, Z.mod_mod, <- Zminus_mod by lia.
  replace ((bv_unsigned x + 9223372036854775808) - 9223372036854775808) with (bv_unsigned x) by lia. reflexivity.
Qed.
Lemma eqm_win_eq : forall a b, eqm a b -> - T63 <= a < T63 -> - T63 <= b < T63 -> a = b.
Proof.
  intros a b H Ha Hb. unfold eqm, T63, two64 in *. Z.div_mod_to_equations. nia.
Qed.
Lemma swin_signed : forall E fs l, Forall (fact_ok E) fs -> sfit (swin fs l) = true ->
  fst (swin fs l) <= bv_signed (lden E l) <= snd (swin fs l).
Proof.
  intros E fs l HF Hs. destruct (swin_sound E fs l HF) as (v & Hv & Hr). unfold sfit in Hs.
  apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  destruct (signed_eqm (lden E l)) as [Hs1 Hs2].
  assert (v = bv_signed (lden E l)) as <- by (apply eqm_win_eq; [eapply eqm_trans; [exact Hv | apply eqm_sym; exact Hs1] | lia | lia]).
  exact Hr.
Qed.
Lemma lts_by_win_sound : forall E fs a b t, Forall (fact_ok E) fs -> lts_by_win fs a b = Some t -> bv_lts (lden E a) (lden E b) = t.
Proof.
  intros E fs a b t HF H. unfold lts_by_win in H.
  destruct (sfit (swin fs a) && sfit (swin fs b))%bool eqn:Hab; [|discriminate]. apply andb_prop in Hab as [Ha Hb].
  pose proof (swin_signed E fs a HF Ha) as Sa. pose proof (swin_signed E fs b HF Hb) as Sb.
  unfold bv_lts.
  destruct (Z.ltb (snd (swin fs a)) (fst (swin fs b))) eqn:H1.
  { injection H as <-. apply Z.ltb_lt in H1. apply Z.ltb_lt. lia. }
  destruct (Z.leb (snd (swin fs b)) (fst (swin fs a))) eqn:H2.
  { injection H as <-. apply Z.leb_le in H2. apply Z.ltb_ge. lia. }
  destruct (sfit (swin fs (lsub a b)) && sfit (fst (swin fs a) - snd (swin fs b), snd (swin fs a) - fst (swin fs b)))%bool eqn:Hd; [|discriminate].
  apply andb_prop in Hd as [Hd1 Hd2]. pose proof (swin_signed E fs (lsub a b) HF Hd1) as Sd.
  unfold sfit in Hd2. cbn [fst snd] in Hd2. apply andb_prop in Hd2 as [Hd3 Hd4]. apply Z.leb_le in Hd3. apply Z.ltb_lt in Hd4.
  destruct (signed_eqm (lden E a)) as [Ea Ra]. destruct (signed_eqm (lden E b)) as [Eb Rb]. destruct (signed_eqm (lden E (lsub a b))) as [Ed Rd].
  assert (HD : bv_signed (lden E (lsub a b)) = bv_signed (lden E a) - bv_signed (lden E b)).
  { apply eqm_win_eq; [| exact Rd | lia].
    eapply eqm_trans; [exact Ed|]. rewrite lden_lsub, bv_sub_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    unfold eqm. rewrite Z.mod_mod by (unfold two64; lia). apply eqm_sub; apply eqm_sym; assumption. }
  destruct (Z.ltb (snd (swin fs (lsub a b))) 0) eqn:H3.
  { injection H as <-. apply Z.ltb_lt in H3. apply Z.ltb_lt. lia. }
  destruct (Z.leb 0 (fst (swin fs (lsub a b)))) eqn:H4; [|discriminate].
  injection H as <-. apply Z.leb_le in H4. apply Z.ltb_ge. lia.
Qed.

Lemma ev_br_known_sound : forall E fs c a b tk, Forall (fact_ok E) fs -> ev_br_known fs c a b = Some tk ->
  branch_taken c (lden E a) (lden E b) = tk.
Proof.
  intros E fs c a b tk Hf H. unfold ev_br_known in H.
  destruct (fcond_lookup fs c a b) as [tk'|] eqn:Hl.
  - injection H as <-. exact (fcond_lookup_sound E fs c a b tk' Hf Hl).
  - destruct c; try discriminate; cbn [branch_taken].
    + exact (eq_by_range_sound E fs a b tk Hf H).
    + destruct (eq_by_range fs a b) as [v|] eqn:Hv; [|discriminate]. injection H as <-.
      rewrite (eq_by_range_sound E fs a b v Hf Hv). reflexivity.
    + destruct (nonneg2 fs a b) eqn:Hnn; [|exact (lts_by_win_sound E fs a b tk Hf H)]. rewrite (lts_ltu E fs a b Hf Hnn).
      exact (ltu_by_range_sound E fs a b tk Hf H).
    + destruct (nonneg2 fs a b) eqn:Hnn.
      * rewrite (lts_ltu E fs a b Hf Hnn).
        destruct (ltu_by_range fs a b) as [v|] eqn:Hv; [|discriminate]. injection H as <-.
        rewrite (ltu_by_range_sound E fs a b v Hf Hv). reflexivity.
      * destruct (lts_by_win fs a b) as [v|] eqn:Hv; [|discriminate]. injection H as <-.
        rewrite (lts_by_win_sound E fs a b v Hf Hv). reflexivity.
    + exact (ltu_by_range_sound E fs a b tk Hf H).
    + destruct (ltu_by_range fs a b) as [v|] eqn:Hv; [|discriminate]. injection H as <-.
      rewrite (ltu_by_range_sound E fs a b v Hf Hv). reflexivity.
Qed.

Lemma ev_br_sym_sound : forall E fs c a b tk, Forall (fact_ok E) fs -> ev_br_sym fs c a b = Some tk ->
  branch_taken c (lden E a) (lden E b) = tk.
Proof.
  intros E fs c a b tk Hf H. unfold ev_br_sym in H.
  destruct c; try exact (ev_br_known_sound E fs _ a b tk Hf H);
    (destruct (lin_off a b) as [d|] eqn:Hd; [|exact (ev_br_known_sound E fs _ a b tk Hf H)];
     destruct (Z.eqb d 0) eqn:Hd0; [|exact (ev_br_known_sound E fs _ a b tk Hf H)];
     injection H as <-; apply Z.eqb_eq in Hd0; subst d;
     cbn [branch_taken]; rewrite (lden_eq_of_off0 E a b Hd); unfold bv_eqb; rewrite Z.eqb_refl; reflexivity).
Qed.

Lemma ev_br_sound : forall E fs c a b tk, Forall (fact_ok E) fs -> ev_br fs c a b = Some tk -> branch_taken c (lden E a) (lden E b) = tk.
Proof.
  intros E fs c a b tk Hf H. unfold ev_br in H.
  destruct (is_const a) as [x|] eqn:Ha.
  - destruct (is_const b) as [y|] eqn:Hb; [|exact (ev_br_sym_sound E fs c a b tk Hf H)].
    injection H as <-. destruct (is_const_sound E a x Ha) as [-> Hx]. destruct (is_const_sound E b y Hb) as [-> Hy].
    symmetry. apply br_z_ok; assumption.
  - exact (ev_br_sym_sound E fs c a b tk Hf H).
Qed.

(* [comment removed for export] *)
Lemma div_sub_ceil : forall p u v, 0 < p -> 0 <= v -> (p * u - v) / p = u - (v + p - 1) / p.
Proof.
  intros p u v Hp Hv.
  pose proof (Z.div_mod (v + p - 1) p ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (v + p - 1) p Hp) as Hr.
  set (c := (v + p - 1) / p) in *. set (r' := (v + p - 1) mod p) in *.
  replace (p * u - v) with ((-c) * p + (p - 1 - r') + u * p) by nia.
  rewrite Z.div_add by lia.
  assert (Hq : ((-c) * p + (p - 1 - r')) / p = -c).
  { symmetry. apply Z.div_unique with (p - 1 - r'); [left; lia | ring]. }
  rewrite Hq. ring.
Qed.

Lemma window_exact : forall v u lo hi, eqm v u -> 0 <= u < two64 -> lo <= v <= hi -> 0 <= lo -> hi < two64 -> u = v.
Proof.
  intros v u lo hi He Hu Hv Hlo Hhi. unfold eqm in He. rewrite (Z.mod_small v) in He by lia. rewrite (Z.mod_small u) in He by lia. lia.
Qed.

Lemma srl_win_sound : forall E fs ta d, Forall (fact_ok E) fs ->
  exists v, eqm v (bv_unsigned (lden E d)) /\ fst (srl_win fs ta d) <= v <= snd (srl_win fs ta d).
Proof.
  intros E fs ta d HF. unfold srl_win. cbv zeta.
  destruct (if srl_ok0 (frange_same fs d (l_iv fs d)) then true else negb (srl_possible (frange_same fs d (l_iv fs d)))).
  - apply frange_same_sound; [exact HF|].
    exists (izl E d). split; [eapply eqm_trans; [apply izl_eqm | apply eqm_sym, u_eqm_lz] | exact (l_iv_sound E fs d HF)].
  - exact (rel_iv2_sound E fs fs ta d (rel_base fs d) HF HF (rel_base_sound E fs d HF)).
Qed.

Lemma srl_one_fact_sound : forall E fs k a n y, Forall (fact_ok E) fs -> 0 < k < 64 ->
  bv_unsigned (E n) = Z.shiftr (bv_unsigned (lden E a)) k -> Forall (fact_ok E) (srl_one_fact fs k a (lvar n) y).
Proof.
  intros E fs k a n y HF Hk Hn. unfold srl_one_fact.
  set (pk := 2 ^ k). assert (Hpk : 0 < pk) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpk63 : pk <= 9223372036854775808) by (unfold pk; change 9223372036854775808 with (2 ^ 63); apply Z.pow_le_mono_r; lia).
  assert (Hpk64 : pk * 2 ^ (64 - k) = two64) by (unfold pk; rewrite <- Z.pow_add_r by lia; replace (k + (64 - k)) with 64 by lia; reflexivity).
  pose proof (var_range'_sound E fs y HF) as Hy. set (yr := var_range' fs y) in *.
  set (dl := lsub a (lscale pk (lvar y))). set (du := lsub (lscale pk (lvar y)) a).
  destruct (srl_win_sound E fs (l_t a) dl HF) as (vl & Hvl & Rl).
  destruct (srl_win_sound E fs (l_t a) du HF) as (vu & Hvu & Ru).
  set (wl := srl_win fs (l_t a) dl) in *. set (wu := srl_win fs (l_t a) du) in *.
  pose proof (u_range E a) as Ua. pose proof (u_range E (lvar y)) as Uy. rewrite lden_lvar in Uy.
  unfold vz in Hy. rewrite Z.shiftr_div_pow2 in Hn by lia. fold pk in Hn.
  pose proof (bv_unsigned_in_range _ (E n)) as Un. unfold bv_modulus in Un. change (2 ^ Z.of_N 64) with two64 in Un.
  apply Forall_app. split.
  - destruct (Z.leb 0 (fst wl) && Z.ltb (snd wl) T62 && Z.leb 0 (fst yr) && Z.ltb (pk * snd yr + snd wl) two64)%bool eqn:Hc; [|constructor].
    apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1, H3. apply Z.ltb_lt in H2, H4. unfold T62 in H2.
    constructor; [|constructor]. cbn [fact_ok].
    pose proof (u_range E dl) as Udl.
    assert (Hdl : bv_unsigned (lden E dl) = vl) by (apply (window_exact vl _ (fst wl) (snd wl)); first [exact Hvl | lia | unfold two64 in *; lia]).
    (* [comment removed for export] *)
    assert (Ha : bv_unsigned (lden E a) = pk * bv_unsigned (E y) + vl).
    { assert (Hm : eqm (bv_unsigned (lden E a)) (pk * bv_unsigned (E y) + vl)).
      { eapply eqm_trans; [apply u_eqm_lz|]. apply eqm_sym.
        eapply eqm_trans; [apply eqm_add; [apply eqm_mul; [apply eqm_refl | rewrite <- (lden_lvar E y); apply u_eqm_lz]
                                          | eapply eqm_trans; [exact Hvl | apply u_eqm_lz]]|].
        unfold dl. eapply eqm_trans; [apply eqm_add; [apply eqm_refl | apply lz_lsub]|].
        eapply eqm_trans; [apply eqm_add; [apply eqm_refl | apply eqm_sub; [apply eqm_refl | apply lz_lscale]]|].
        replace (pk * lz E (lvar y) + (lz E a - pk * lz E (lvar y))) with (lz E a) by ring. apply eqm_refl. }
      assert (Hy1 : pk * bv_unsigned (E y) <= pk * snd yr) by (apply Z.mul_le_mono_nonneg_l; lia).
      assert (Hy0 : 0 <= pk * bv_unsigned (E y)) by (apply Z.mul_nonneg_nonneg; lia).
      apply (window_exact (pk * bv_unsigned (E y) + vl) _ 0 (two64 - 1)); first [apply eqm_sym; exact Hm | exact Ua | lia]. }
    rewrite lden_lsub, bv_sub_unsigned, lden_lvar, lden_lvar. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    assert (Hq : bv_unsigned (E n) = bv_unsigned (E y) + vl / pk).
    { rewrite Hn, Ha. rewrite Z.add_comm, Z.mul_comm. rewrite Z.div_add by lia. ring. }
    rewrite Hq. replace (bv_unsigned (E y) + vl / pk - bv_unsigned (E y)) with (vl / pk) by ring.
    assert (0 <= vl / pk) by (apply Z.div_pos; lia).
    assert (vl / pk <= vl) by (apply Z.div_le_upper_bound; [lia|]; rewrite <- (Z.mul_1_l vl) at 1; apply Z.mul_le_mono_nonneg_r; lia).
    rewrite Z.mod_small by (unfold two64; lia). rewrite !Z.shiftr_div_pow2 by lia. fold pk. split; apply Z.div_le_mono; lia.
  - destruct (srl_skip wl); [constructor|]. cbv zeta. fold du. fold wu.
    destruct (Z.leb 0 (fst wu) && Z.ltb (snd wu) T62 && Z.leb (snd wu) (pk * fst yr) && Z.ltb (pk * snd yr) two64)%bool eqn:Hc; [|constructor].
    apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1, H3. apply Z.ltb_lt in H2, H4. unfold T62 in H2.
    constructor; [|constructor]. cbn [fact_ok].
    pose proof (u_range E du) as Udu.
    assert (Hdu : bv_unsigned (lden E du) = vu) by (apply (window_exact vu _ (fst wu) (snd wu)); first [exact Hvu | lia | unfold two64 in *; lia]).
    assert (Ha : bv_unsigned (lden E a) = pk * bv_unsigned (E y) - vu).
    { assert (Hm : eqm (bv_unsigned (lden E a)) (pk * bv_unsigned (E y) - vu)).
      { eapply eqm_trans; [apply u_eqm_lz|]. apply eqm_sym.
        eapply eqm_trans; [apply eqm_sub; [apply eqm_mul; [apply eqm_refl | rewrite <- (lden_lvar E y); apply u_eqm_lz]
                                          | eapply eqm_trans; [exact Hvu | apply u_eqm_lz]]|].
        unfold du. eapply eqm_trans; [apply eqm_sub; [apply eqm_refl | apply lz_lsub]|].
        eapply eqm_trans; [apply eqm_sub; [apply eqm_refl | apply eqm_sub; [apply lz_lscale | apply eqm_refl]]|].
        replace (pk * lz E (lvar y) - (pk * lz E (lvar y) - lz E a)) with (lz E a) by ring. apply eqm_refl. }
      assert (Hy1 : pk * bv_unsigned (E y) <= pk * snd yr) by (apply Z.mul_le_mono_nonneg_l; lia).
      assert (Hy2 : pk * fst yr <= pk * bv_unsigned (E y)) by (apply Z.mul_le_mono_nonneg_l; lia).
      apply (window_exact (pk * bv_unsigned (E y) - vu) _ 0 (two64 - 1)); first [apply eqm_sym; exact Hm | exact Ua | lia]. }
    rewrite lden_lsub, bv_sub_unsigned, lden_lvar, lden_lvar. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    assert (Hq : bv_unsigned (E n) = bv_unsigned (E y) - (vu + pk - 1) / pk).
    { rewrite Hn, Ha. apply div_sub_ceil; lia. }
    rewrite Hq. replace (bv_unsigned (E y) - (bv_unsigned (E y) - (vu + pk - 1) / pk)) with ((vu + pk - 1) / pk) by ring.
    assert (0 <= (vu + pk - 1) / pk) by (apply Z.div_pos; lia).
    assert ((vu + pk - 1) / pk <= vu + pk) by (apply Z.div_le_upper_bound; [lia|];
      apply Z.le_trans with (vu + pk); [lia|]; rewrite <- (Z.mul_1_l (vu + pk)) at 1; apply Z.mul_le_mono_nonneg_r; lia).
    rewrite Z.mod_small by (unfold two64; lia). split; apply Z.div_le_mono; lia.
Qed.

Lemma srl_div_sound : forall E fs k a n, Forall (fact_ok E) fs ->
  bv_unsigned (E n) = Z.shiftr (bv_unsigned (lden E a)) k -> Forall (fact_ok E) (srl_div fs k a (lvar n)).
Proof.
  intros E fs k a n HF Hn. unfold srl_div.
  set (pk := 2 ^ k).
  set (td := List.filter (fun p => (Z.eqb (snd p mod pk) 0 && Z.ltb (snd p) 4611686018427387904)%bool) (l_t a)).
  set (tr := List.filter (fun p => negb (Z.eqb (snd p mod pk) 0 && Z.ltb (snd p) 4611686018427387904)%bool) (l_t a)).
  set (D := LIN 0 (List.map (fun p => (fst p, snd p / pk)) td)).
  set (R := LIN (l_c a) tr).
  destruct td as [|p0 td']; [constructor|].
  destruct (Z.ltb 0 k && Z.ltb k 64 && lin_eqb a (ladd (lscale pk D) R))%bool eqn:Hc; [|constructor].
  apply andb_prop in Hc as [Hc Heq]. apply andb_prop in Hc as [Hk1 Hk2]. apply Z.ltb_lt in Hk1, Hk2. apply lin_eqb_eq in Heq.
  pose proof (irange_sound E fs R HF) as HR. pose proof (irange_sound E fs D HF) as HD.
  destruct (Z.leb 0 (fst (irange fs R)) && Z.leb 0 (fst (irange fs D)) && Z.ltb (snd (irange fs D) * pk + snd (irange fs R)) two64)%bool eqn:Hb;
    [|constructor].
  apply andb_prop in Hb as [Hb Hw]. apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1, Hb2. apply Z.ltb_lt in Hw.
  constructor; [|constructor]. cbn [fact_ok].
  set (uD := bv_unsigned (lden E D)) in *. set (uR := bv_unsigned (lden E R)) in *.
  assert (Hpk : 0 < pk) by (unfold pk; apply Z.pow_pos_nonneg; lia).
  assert (Ha : bv_unsigned (lden E a) = pk * uD + uR).
  { rewrite Heq, lden_ladd, lden_lscale. rewrite bv_add_unsigned, Z_to_bv_unsigned. fold uD uR. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with two64. rewrite Zplus_mod_idemp_l.
    apply Z.mod_small. nia. }
  assert (Hx : bv_unsigned (E n) = uD + Z.shiftr uR k).
  { rewrite Hn, Ha, !Z.shiftr_div_pow2 by lia. fold pk. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
  rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hx. fold uD. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
  replace (uD + Z.shiftr uR k - uD) with (Z.shiftr uR k) by ring.
  assert (Hs0 : 0 <= Z.shiftr uR k) by (apply Z.shiftr_nonneg; lia).
  assert (Hs1 : Z.shiftr uR k <= uR) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_le_upper_bound; [lia|]; nia).
  pose proof (u_range E R) as RR. fold uR in RR.
  rewrite Z.mod_small by lia.
  rewrite !Z.shiftr_div_pow2 by lia. fold pk. split; apply Z.div_le_mono; lia.
Qed.

Lemma srl_facts_eq : forall fs k a x, srl_facts fs k a x = srl_facts_ref fs k a x.
Proof.
  intros fs k a x. unfold srl_facts, srl_facts_ref. destruct (Z.ltb 0 k && Z.ltb k 64)%bool; [|reflexivity].
  destruct (longer IR_FAST_MIN fs); [|reflexivity]. cbv zeta. f_equal. apply map_ext. intros y.
  unfold srl_one_factF, srl_one_fact, srl_winF, srl_win. cbv zeta.
  rewrite !(var_rangeF_eq fs), !(l_ivF_eq fs), !(rel_baseF_eq fs), !(rel_iv2F_eq fs). reflexivity.
Qed.
Lemma srl_facts_sound : forall E fs k a n, Forall (fact_ok E) fs ->
  bv_unsigned (E n) = Z.shiftr (bv_unsigned (lden E a)) k -> Forall (fact_ok E) (srl_facts fs k a (lvar n)).
Proof.
  intros E fs k a n HF Hn. rewrite srl_facts_eq. unfold srl_facts_ref.
  destruct (Z.ltb 0 k && Z.ltb k 64)%bool eqn:Hk; [|constructor].
  apply andb_prop in Hk as [H1 H2]. apply Z.ltb_lt in H1, H2.
  apply Forall_concat. apply Forall_forall. intros l Hl. apply in_map_iff in Hl. destruct Hl as (y & <- & _).
  exact (srl_one_fact_sound E fs k a n y HF ltac:(lia) Hn).
Qed.

(* [comment removed for export] *)
Lemma shift_window : forall k z u v acc w',
  0 <= k <= 64 -> eqm z (2 ^ k * u) -> eqm v u -> fst acc <= v <= snd acc ->
  fst w' <= z / 2 ^ k <= snd w' -> (2 ^ k | z) ->
  Z.max (snd acc) (snd w') - Z.min (fst acc) (fst w') < 2 ^ (64 - k) ->
  fst (iv_meet acc w') <= v <= snd (iv_meet acc w').
Proof.
  intros k z u v acc w' Hk Hz Hv Hacc Hw Hd Hwid.
  assert (Hp : 2 ^ 64 = 2 ^ k * 2 ^ (64 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpk' : 0 < 2 ^ (64 - k)) by (apply Z.pow_pos_nonneg; lia).
  destruct Hd as [y Hy]. rewrite Hy, Z.div_mul in Hw by lia.
  unfold eqm in Hz, Hv. rewrite two64_eq in Hz, Hv.
  assert (H1 : (z - 2 ^ k * u) mod 2 ^ 64 = 0) by (rewrite Zminus_mod, Hz, Z.sub_diag; reflexivity).
  apply Z.mod_divide in H1; [|lia]. destruct H1 as [t Ht].
  assert (H2 : (v - u) mod 2 ^ 64 = 0) by (rewrite Zminus_mod, Hv, Z.sub_diag; reflexivity).
  apply Z.mod_divide in H2; [|lia]. destruct H2 as [t2 Ht2].
  assert (Hyu : y = u + 2 ^ (64 - k) * t).
  { apply (Z.mul_reg_l _ _ (2 ^ k)); [lia|]. rewrite Z.mul_add_distr_l. rewrite Z.mul_assoc, <- Hp.
    rewrite Z.mul_comm, <- Hy. lia. }
  assert (Hvy : v - y = 2 ^ (64 - k) * (2 ^ k * t2 - t)).
  { rewrite Hyu. replace (v - (u + 2 ^ (64 - k) * t)) with ((v - u) - 2 ^ (64 - k) * t) by ring.
    rewrite Ht2, Hp. ring. }
  assert (Hq : 2 ^ k * t2 - t = 0).
  { destruct (Z.eq_dec (2 ^ k * t2 - t) 0) as [H0|H0]; [exact H0|].
    exfalso. unfold iv_meet in *. cbn [fst snd] in *.
    assert (Habs : 2 ^ (64 - k) <= Z.abs (v - y)).
    { rewrite Hvy, Z.abs_mul, Z.abs_eq by lia.
      assert (H1 : 1 <= Z.abs (2 ^ k * t2 - t)) by lia.
      rewrite <- (Z.mul_1_r (2 ^ (64 - k))) at 1. apply Z.mul_le_mono_nonneg_l; lia. }
    lia. }
  rewrite Hq, Z.mul_0_r in Hvy. assert (v = y) by lia. subst v.
  unfold iv_meet. cbn [fst snd]. lia.
Qed.

Lemma srl_one_sound : forall E fs l g lo hi q k acc, Forall (fact_ok E) fs -> lo <= bv_unsigned (lden E g) <= hi -> 0 <= k <= 64 ->
  (exists v, eqm v (bv_unsigned (lden E l)) /\ fst acc <= v <= snd acc) ->
  exists v, eqm v (bv_unsigned (lden E l)) /\ fst (srl_one fs l g lo hi q k acc) <= v <= snd (srl_one fs l g lo hi q k acc).
Proof.
  intros E fs l g lo hi q k acc HF Hg Hk (v & Hv & Hacc). unfold srl_one.
  set (c := if Z.eqb (tcoef (l_t l) q) 1 then 1 else if Z.eqb (tcoef (l_t l) q) M64 then -1 else 0).
  assert (Hc : c = 0 \/ c = 1 \/ c = -1) by (unfold c; destruct (Z.eqb _ 1); [|destruct (Z.eqb _ M64)]; lia).
  destruct (Z.eqb c 0) eqn:Hc0; [exists v; split; assumption|]. apply Z.eqb_neq in Hc0.
  set (m := ladd (lscale (2 ^ k) l) (lscale c g)).
  destruct (rel_iv2_sound E fs fs (l_t m) m (rel_base fs m) HF HF (rel_base_sound E fs m HF)) as (w & Hw & Rw).
  set (wm := rel_iv2 fs fs (l_t m) m (rel_base fs m)) in *.
  set (ug := bv_unsigned (lden E g)) in *. set (ul := bv_unsigned (lden E l)) in *.
  assert (Hm : eqm w (2 ^ k * ul + c * ug)).
  { eapply eqm_trans; [exact Hw|]. eapply eqm_trans; [apply u_eqm_lz|]. unfold m.
    eapply eqm_trans; [apply lz_ladd|]. apply eqm_add; (eapply eqm_trans; [apply lz_lscale|]); apply eqm_mul; try apply eqm_refl;
      apply eqm_sym, u_eqm_lz. }
  set (z := w - c * ug).
  assert (Hz : eqm z (2 ^ k * ul)).
  { unfold z. unfold eqm in *. rewrite Zminus_mod, Hm, <- Zminus_mod. f_equal. ring. }
  assert (Hpk : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hd : (2 ^ k | z)).
  { unfold eqm in Hz. rewrite two64_eq in Hz.
    assert (H1 : (z - 2 ^ k * ul) mod 2 ^ 64 = 0) by (rewrite Zminus_mod, Hz, Z.sub_diag; reflexivity).
    apply Z.mod_divide in H1; [|lia]. destruct H1 as [t Ht].
    assert (Hp : 2 ^ 64 = 2 ^ k * 2 ^ (64 - k)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
    exists (ul + 2 ^ (64 - k) * t). rewrite Hp in Ht. nia. }
  assert (Hzr : fst (if Z.eqb c 1 then (fst wm - hi, snd wm - lo) else (fst wm + lo, snd wm + hi)) <= z <=
                snd (if Z.eqb c 1 then (fst wm - hi, snd wm - lo) else (fst wm + lo, snd wm + hi))).
  { unfold z. destruct (Z.eqb c 1) eqn:H1; cbn [fst snd].
    - apply Z.eqb_eq in H1. rewrite H1. lia.
    - apply Z.eqb_neq in H1. assert (c = -1) by lia. subst c. lia. }
  set (zw := if Z.eqb c 1 then (fst wm - hi, snd wm - lo) else (fst wm + lo, snd wm + hi)) in *.
  assert (Hyw : fst ((fst zw + 2 ^ k - 1) / 2 ^ k, snd zw / 2 ^ k) <= z / 2 ^ k <= snd ((fst zw + 2 ^ k - 1) / 2 ^ k, snd zw / 2 ^ k)).
  { cbn [fst snd]. destruct Hd as [y Hy]. rewrite Hy, Z.div_mul by lia. split.
    - apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia|]. rewrite Hy in Hzr. rewrite Z.mul_succ_r. lia.
    - apply Z.div_le_lower_bound; [lia|]. rewrite Hy in Hzr. lia. }
  destruct (Z.ltb _ (2 ^ (64 - k))) eqn:Hwid; [|exists v; split; assumption].
  apply Z.ltb_lt in Hwid.
  exists v. split; [exact Hv|].
  exact (shift_window k z ul v acc _ Hk Hz Hv Hacc Hyw Hd Hwid).
Qed.

Lemma srl_terms_sound : forall E fs l g lo hi t acc, Forall (fact_ok E) fs -> lo <= bv_unsigned (lden E g) <= hi ->
  (exists v, eqm v (bv_unsigned (lden E l)) /\ fst acc <= v <= snd acc) ->
  exists v, eqm v (bv_unsigned (lden E l)) /\ fst (srl_terms fs l g lo hi t acc) <= v <= snd (srl_terms fs l g lo hi t acc).
Proof.
  intros E fs l g lo hi t. induction t as [|[q cq] t IH]; intros acc HF Hg H; cbn [srl_terms]; [exact H|].
  destruct (pow2_neg cq) as [k|] eqn:Hp; [|exact (IH acc HF Hg H)].
  apply IH; [exact HF | exact Hg|].
  assert (Hk : 0 <= k <= 64).
  { unfold pow2_neg in Hp. destruct (Z.ltb 1 (two64 - cq) && Z.leb (two64 - cq) 65536)%bool eqn:H1; [|discriminate].
    apply andb_prop in H1 as [H1 H2]. apply Z.ltb_lt in H1. apply Z.leb_le in H2.
    destruct (Z.eqb (two64 - cq) (2 ^ Z.log2 (two64 - cq))); [|discriminate]. injection Hp as <-.
    split; [apply Z.log2_nonneg|]. apply Z.le_trans with (Z.log2 65536); [apply Z.log2_le_mono; exact H2 | vm_compute; discriminate]. }
  exact (srl_one_sound E fs l g lo hi q k acc HF Hg Hk H).
Qed.

Lemma srl_iv_sound : forall E fs all l acc, Forall (fact_ok E) fs -> Forall (fact_ok E) all ->
  (exists v, eqm v (bv_unsigned (lden E l)) /\ fst acc <= v <= snd acc) ->
  exists v, eqm v (bv_unsigned (lden E l)) /\ fst (srl_iv fs all l acc) <= v <= snd (srl_iv fs all l acc).
Proof.
  intros E fs all l acc HF Hall. revert acc. induction HF as [|f fs Hok HF IH]; intros acc H; cbn [srl_iv]; [exact H|].
  destruct f as [c a b tk|g lo hi|g k' r'|g m' v'|x' v' j'|xb bsb]; try exact (IH acc H).
  - destruct (shares (l_t l) (l_t a) || shares (l_t l) (l_t b))%bool; [|exact (IH acc H)].
    destruct (fact_g all (FCond c a b tk)) as [[[g lo] hi]|] eqn:Hg; [|exact (IH acc H)].
    apply IH. exact (srl_terms_sound E all l g lo hi (l_t g) acc Hall (fact_g_sound E all _ g lo hi Hall Hok Hg) H).
  - destruct (shares (l_t l) (l_t g)); [|exact (IH acc H)].
    apply IH. cbn [fact_ok] in Hok. exact (srl_terms_sound E all l g lo hi (l_t g) acc Hall Hok H).
Qed.

Theorem irange_x_ref_sound : forall E fs l, Forall (fact_ok E) fs -> fst (irange_x_ref fs l) <= bv_unsigned (lden E l) <= snd (irange_x_ref fs l).
Proof.
  intros E fs l HF. unfold irange_x_ref. destruct (is_const l) as [c|] eqn:Hc.
  - rewrite (is_const_u E l c Hc). cbn. lia.
  - assert (Hv : eqm (izl E l) (bv_unsigned (lden E l))) by (eapply eqm_trans; [apply izl_eqm | apply eqm_sym, u_eqm_lz]).
    assert (Hk : forall k acc, ne_int_fixl k fs l acc = ne_int_fix (List.length k) fs l acc)
      by (induction k as [|f k IHk]; intros acc'; [reflexivity | cbn [ne_int_fixl ne_int_fix List.length]; rewrite IHk; reflexivity]).
    rewrite Hk.
    destruct (ne_int_fix_sound E fs l (List.length fs) _ HF
               (lround_sound E fs l _ HF (srl_iv_sound E fs fs l _ HF HF (rel_iv2_sound E fs fs (l_t l) l _ HF HF (rel_iv_sound E fs fs l (l_iv fs l) HF HF (ex_intro _ (izl E l) (conj Hv (l_iv_sound E fs l HF))))))))
      as (v' & Hv' & Hr).
    pose proof (wrap_iv_sound E l v' _ Hv' Hr) as H0.
    pose proof (ne_refine'_sound E fs l _ HF H0) as H.
    destruct (Z.ltb 0 (lalign fs l)) eqn:Ha; [|exact H].
    destruct (lalign_sound E fs l HF) as [Hab Had]. apply align_iv_sound; [lia | exact H | exact Had].
Qed.
Theorem irange_x_eq : forall fs l, irange_x fs l = irange_x_ref fs l.
Proof.
  intros fs l. unfold irange_x, irange_x_ref. destruct (is_const l); [reflexivity|]. destruct (longer IR_FAST_MIN fs); [|reflexivity].
  rewrite irange_x0N_eq. exact (irange_x0F_eq fs l).
Qed.
Theorem irange_x_sound : forall E fs l, Forall (fact_ok E) fs -> fst (irange_x fs l) <= bv_unsigned (lden E l) <= snd (irange_x fs l).
Proof. intros E fs l HF. rewrite irange_x_eq. exact (irange_x_ref_sound E fs l HF). Qed.
(* [comment removed for export] *)
Lemma t_rivQ_eq : forall fs t, t_rivQ fs t = t_riv fs t.
Proof.
  intros fs t. unfold t_rivQ. destruct (longer IR_NUM_MIN fs); [|reflexivity].
  induction t as [|[y k] t IH]; [reflexivity|]. cbn [t_rivN t_riv]. rewrite IH.
  rewrite rel_topN_ok, rel_ivN_eq, l_ivN_eq, rel_ivF_eq, l_ivF_eq. reflexivity.
Qed.
