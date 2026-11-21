(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItProof.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma pow2_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow2_le : forall a b, 0 <= a <= b -> 2 ^ a <= 2 ^ b.
Proof. intros. apply Z.pow_le_mono_r; lia. Qed.

Lemma pow2_divide : forall a b, 0 <= a <= b -> (2 ^ a | 2 ^ b).
Proof.
  intros a b H. exists (2 ^ (b - a)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma code_op_nonneg : forall e, 0 <= code_op e.
Proof. intros e. unfold code_op. apply Z.land_nonneg. right. lia. Qed.

Lemma code_val_nonneg : forall e, 0 <= code_val e.
Proof. intros e. unfold code_val. apply Z.land_nonneg. right. lia. Qed.

Lemma mod_down : forall a b x y, 0 <= a <= b -> x mod 2 ^ b = y mod 2 ^ b -> x mod 2 ^ a = y mod 2 ^ a.
Proof.
  intros a b x y Hab H.
  rewrite <- (Z.mod_mod_divide x (2 ^ b) (2 ^ a)) by (apply pow2_divide; lia).
  rewrite <- (Z.mod_mod_divide y (2 ^ b) (2 ^ a)) by (apply pow2_divide; lia).
  rewrite H. reflexivity.
Qed.

Lemma subidx_range : forall h r o, 0 <= r -> 0 <= o -> 0 <= h mod 2 ^ (r + o) / 2 ^ r < 2 ^ o.
Proof.
  intros h r o Hr Ho. pose proof (pow2_pos r Hr). pose proof (pow2_pos o Ho).
  pose proof (Z.mod_pos_bound h (2 ^ (r + o)) ltac:(apply pow2_pos; lia)) as Hm.
  set (M := h mod 2 ^ (r + o)) in *. clearbody M.
  rewrite Z.pow_add_r in Hm by lia. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; [lia|]. lia.
Qed.

Lemma subidx_mod : forall h h' r o a b, 0 <= r -> 0 <= o -> 0 <= a -> r + a <= b ->
  h' mod 2 ^ b = h mod 2 ^ b ->
  (h' mod 2 ^ (r + o) / 2 ^ r) mod 2 ^ a = (h mod 2 ^ (r + o) / 2 ^ r) mod 2 ^ a.
Proof.
  intros h h' r o a b Hr Ho Ha Hb E.
  apply Z.bits_inj'. intros i Hi.
  rewrite !Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec i a); [|reflexivity]. cbn [andb].
  rewrite !Z.div_pow2_bits by lia.
  rewrite !Z.testbit_mod_pow2 by lia.
  destruct (Z.ltb_spec (i + r) (r + o)); cbn [andb]; [|reflexivity].
  apply (f_equal (fun z => Z.testbit z (i + r))) in E. rewrite !Z.testbit_mod_pow2 in E by lia.
  replace (i + r <? b) with true in E by (symmetry; apply Z.ltb_lt; lia). exact E.
Qed.

Lemma cl_ext_nonneg : forall v, 0 <= cl_ext v <= 7.
Proof. intros v. unfold cl_ext. repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia. Qed.

Lemma land240_small : forall op, 0 <= op <= 15 -> Z.land op 240 = 0.
Proof.
  intros op H. destruct op as [|p|p]; [reflexivity| |lia].
  do 4 (destruct p as [p|p|]; [| |reflexivity]); cbn in H; lia.
Qed.

Lemma sym_entry_not_link : forall ty s, 0 <= s < nsyms ty -> ~ (1 <= fst (sym_entry ty s) <= 15).
Proof.
  intros ty s Hs H. destruct (sym_entry_nolink ty s Hs) as [E|E]; [lia|].
  unfold may_link_op in E. rewrite (land240_small (fst (sym_entry ty s)) ltac:(lia)) in E. cbn in E. discriminate E.
Qed.

Lemma is_linkb_true : forall e, is_linkb e = true <-> 1 <= code_op e <= 15.
Proof. intros e. unfold is_linkb. rewrite Bool.andb_true_iff, !Z.leb_le. tauto. Qed.
Lemma is_linkb_false : forall e, is_linkb e = false <-> ~ (1 <= code_op e <= 15).
Proof. intros e. rewrite <- is_linkb_true. destruct (is_linkb e); split; congruence. Qed.

Section TBLfacts.
  Variable ty : codetype.
Variable get : Z -> Z.
Variable root : Z.
Variable used : Z.
  Hypothesis HT : TBLg ty get root used.

  Lemma T_root : 1 <= root <= 15. Proof. exact (proj1 HT). Qed.
  Lemma T_used : 2 ^ root <= used. Proof. exact (proj1 (proj2 HT)). Qed.
  Lemma T_shape : forall x, 0 <= x < used -> cell_ok ty root used x (get x).
  Proof. exact (proj1 (proj2 (proj2 HT))). Qed.
  Lemma T_rep_root : rep_root get root. Proof. exact (proj1 (proj2 (proj2 (proj2 HT)))). Qed.
  Lemma T_rep_sub : rep_sub get root. Proof. exact (proj2 (proj2 (proj2 (proj2 HT)))). Qed.

  Lemma pow_root_pos : 0 < 2 ^ root. Proof. apply pow2_pos. pose proof T_root. lia. Qed.

  Lemma root_cell : forall x, 0 <= x < 2 ^ root ->
    1 <= code_bits (get x) <= 15
    /\ (is_linkb (get x) = true ->
        code_bits (get x) = root /\ 1 <= code_op (get x) <= 15 - root
        /\ 2 ^ root <= code_val (get x) /\ code_val (get x) + 2 ^ code_op (get x) <= used)
    /\ (is_linkb (get x) = false ->
        code_bits (get x) <= root
        /\ ((exists s, 0 <= s < nsyms ty /\ code_op (get x) = fst (sym_entry ty s) /\ code_val (get x) = snd (sym_entry ty s))
            \/ code_op (get x) = 64)).
  Proof.
    intros x Hx. pose proof T_root as HR. pose proof T_used as HU.
    destruct (T_shape x ltac:(lia)) as [[(s & len & Hs & Hlen & Hop & Hval & [[Hx1 [Hl1 Hb1]]|[Hx2 _]])|[(Hx1 & Hb & Hop & Hv1 & Hv2)|(Hop & Hb & Hv & Hr1)]]|[Hop [[Hx1 Hb]|[Hx2 Hb]]]].
    -
      pose proof (sym_entry_not_link ty s Hs) as NL. rewrite <- Hop in NL.
      split; [lia|]. split.
      + intros L. apply is_linkb_true in L. exfalso. exact (NL L).
      + intros _. split; [lia|]. left. exists s. repeat split; try assumption; lia.
    - exfalso. lia.
    -
      split; [lia|]. split.
      + intros _. repeat split; lia.
      + intros L. apply is_linkb_false in L. exfalso. apply L. lia.
    -
      split; [lia|]. split.
      + intros L. apply is_linkb_true in L. lia.
      + intros _. split; [lia|]. right. exact Hop.
    -
      split; [lia|]. split.
      + intros L. apply is_linkb_true in L. lia.
      + intros _. split; [lia|]. right. exact Hop.
    - exfalso. lia.
  Qed.

  Lemma sub_cell : forall x y, 0 <= x < 2 ^ root -> is_linkb (get x) = true ->
    0 <= y < 2 ^ code_op (get x) ->
    1 <= code_bits (get (code_val (get x) + y)) <= 15 - root
    /\ is_linkb (get (code_val (get x) + y)) = false
    /\ ((exists s, 0 <= s < nsyms ty
                  /\ code_op (get (code_val (get x) + y)) = fst (sym_entry ty s)
                  /\ code_val (get (code_val (get x) + y)) = snd (sym_entry ty s))
        \/ code_op (get (code_val (get x) + y)) = 64).
  Proof.
    intros x y Hx HL Hy. pose proof T_root as HR.
    destruct (root_cell x Hx) as (_ & RL & _). destruct (RL HL) as (Hb & Hop & Hv1 & Hv2).
    set (x' := code_val (get x) + y).
    assert (Hx' : 2 ^ root <= x' < used) by (subst x'; lia).
    pose proof pow_root_pos.
    destruct (T_shape x' ltac:(lia)) as [[(s & len & Hs & Hlen & Hop' & Hval' & [[Hx1 _]|[Hx2 [Hl2 Hb2]]])|[(Hx1 & _)|(Hop' & Hb' & Hv' & Hr1)]]|[Hop' [[Hx1 Hb']|[Hx2 Hb']]]].
    - exfalso. lia.
    - pose proof (sym_entry_not_link ty s Hs) as NL. rewrite <- Hop' in NL.
      split; [lia|]. split; [apply is_linkb_false; exact NL|]. left. exists s. repeat split; try assumption; lia.
    - exfalso. lia.
    - split; [lia|]. split; [apply is_linkb_false; lia|]. right. exact Hop'.
    - exfalso. lia.
    - split; [lia|]. split; [apply is_linkb_false; lia|]. right. exact Hop'.
  Qed.

  Definition rneedg (h : Z) : Z := code_bits (get (h mod 2 ^ root)).
  Definition lneedg (h : Z) : Z :=
    let e := get (h mod 2 ^ root) in
    if is_linkb e
    then code_bits e + code_bits (get (code_val e + h mod 2 ^ (code_bits e + code_op e) / 2 ^ code_bits e))
    else code_bits e.
  Definition cneedg (h : Z) : Z :=
    let e := get (h mod 2 ^ root) in code_bits e + cl_ext (code_val e).

  Lemma ridx_range : forall h, 0 <= h mod 2 ^ root < 2 ^ root.
  Proof. intros h. apply Z.mod_pos_bound. apply pow_root_pos. Qed.

  Lemma rneedg_range : forall h, 1 <= rneedg h <= 15.
  Proof. intros h. unfold rneedg. exact (proj1 (root_cell _ (ridx_range h))). Qed.

  Lemma lneedg_range : forall h, 1 <= lneedg h <= 15 /\ rneedg h <= lneedg h.
  Proof.
    intros h. unfold lneedg, rneedg. pose proof T_root as HR.
    destruct (root_cell _ (ridx_range h)) as (Hb & RL & RN).
    destruct (is_linkb (get (h mod 2 ^ root))) eqn:L.
    - destruct (RL eq_refl) as (Hb2 & Hop & _).
      pose proof (sub_cell (h mod 2 ^ root) (h mod 2 ^ (code_bits (get (h mod 2 ^ root)) + code_op (get (h mod 2 ^ root))) / 2 ^ code_bits (get (h mod 2 ^ root)))
                    (ridx_range h) L ltac:(apply subidx_range; lia)) as (Hs & _). lia.
    - lia.
  Qed.

  Lemma cneedg_range : forall h, 1 <= cneedg h <= 22 /\ rneedg h <= cneedg h.
  Proof.
    intros h. unfold cneedg, rneedg. pose proof (rneedg_range h) as R. unfold rneedg in R.
    pose proof (cl_ext_nonneg (code_val (get (h mod 2 ^ root)))). lia.
  Qed.

  Lemma same_root_idx : forall h h' b, root <= b -> h' mod 2 ^ b = h mod 2 ^ b ->
    h' mod 2 ^ root = h mod 2 ^ root.
  Proof. intros h h' b Hb E. pose proof T_root. apply (mod_down root b); [lia|exact E]. Qed.

  Lemma rep_root_apply : forall h h' b, 0 <= b < root -> h' mod 2 ^ b = h mod 2 ^ b ->
    code_bits (get (h' mod 2 ^ root)) <= b -> get (h mod 2 ^ root) = get (h' mod 2 ^ root).
  Proof.
    intros h h' b Hb E Hle. pose proof T_root as HR.
    destruct (root_cell _ (ridx_range h')) as (Hb' & RL & RN).
    assert (NL : is_linkb (get (h' mod 2 ^ root)) = false).
    { destruct (is_linkb (get (h' mod 2 ^ root))) eqn:L; [|reflexivity]. destruct (RL eq_refl) as (X & _). lia. }
    apply (T_rep_root (h' mod 2 ^ root) (h mod 2 ^ root) (ridx_range h') (ridx_range h) ltac:(lia)).
    set (c := code_bits (get (h' mod 2 ^ root))) in *.
    rewrite !Z.mod_mod_divide by (apply pow2_divide; lia).
    apply (mod_down c b); [lia|]. symmetry. exact E.
  Qed.

  Lemma rneedg_mono : forall h h' b, 0 <= b -> h' mod 2 ^ b = h mod 2 ^ b ->
    b < rneedg h -> b < rneedg h'.
  Proof.
    intros h h' b Hb E Hn. unfold rneedg in *.
    destruct (Z.lt_ge_cases b (code_bits (get (h' mod 2 ^ root)))) as [X|X]; [exact X|]. exfalso.
    destruct (Z.lt_ge_cases b root) as [Br|Br].
    - rewrite (rep_root_apply h h' b ltac:(lia) E X) in Hn. lia.
    - rewrite (same_root_idx h h' b Br E) in X. lia.
  Qed.

  Lemma lneedg_mono : forall h h' b, 0 <= b -> h' mod 2 ^ b = h mod 2 ^ b ->
    b < lneedg h -> b < lneedg h'.
  Proof.
    intros h h' b Hb E Hn. pose proof T_root as HR.
    pose proof (lneedg_range h') as [R1 R2]. unfold rneedg in R2.
    destruct (Z.lt_ge_cases b (code_bits (get (h' mod 2 ^ root)))) as [X|X]; [lia|].
    destruct (Z.lt_ge_cases b root) as [Br|Br].
    -
      pose proof (rep_root_apply h h' b ltac:(lia) E X) as EQ.
      destruct (root_cell _ (ridx_range h')) as (Hb' & RL & RN).
      assert (NL : is_linkb (get (h' mod 2 ^ root)) = false).
      { destruct (is_linkb (get (h' mod 2 ^ root))) eqn:L; [|reflexivity]. destruct (RL eq_refl) as (Y & _). lia. }
      unfold lneedg in Hn |- *. rewrite EQ, NL in Hn. rewrite NL. exact Hn.
    -
      pose proof (same_root_idx h h' b Br E) as EI.
      unfold lneedg in Hn |- *. rewrite EI in *.
      destruct (is_linkb (get (h mod 2 ^ root))) eqn:L; [|exact Hn].
      destruct (root_cell _ (ridx_range h)) as (Hb0 & RL & _). destruct (RL L) as (Hbr & Hop & Hv1 & Hv2).
      set (e := get (h mod 2 ^ root)) in *.
      set (y := h mod 2 ^ (code_bits e + code_op e) / 2 ^ code_bits e) in *.
      set (y' := h' mod 2 ^ (code_bits e + code_op e) / 2 ^ code_bits e) in *.
      assert (Hy : 0 <= y < 2 ^ code_op e) by (subst y; apply subidx_range; lia).
      assert (Hy' : 0 <= y' < 2 ^ code_op e) by (subst y'; apply subidx_range; lia).
      destruct (Z.lt_ge_cases b (code_bits e + code_bits (get (code_val e + y')))) as [Y|Y]; [exact Y|]. exfalso.
      pose proof (sub_cell (h mod 2 ^ root) y' (ridx_range h) L Hy') as (Sb & _). fold e in Sb.
      assert (EQ : get (code_val e + y) = get (code_val e + y')).
      { apply (T_rep_sub (h mod 2 ^ root) (ridx_range h) ltac:(fold e; lia) y' y Hy' Hy ltac:(fold e; lia)).
        fold e. set (c := code_bits (get (code_val e + y'))) in *.
        subst y y'. symmetry. apply (subidx_mod h h' (code_bits e) (code_op e) c b); try lia. }
      rewrite EQ in Hn. lia.
  Qed.
End TBLfacts.

Lemma decomp_mod : forall x b, 0 <= b -> 0 <= x -> x = x mod 2 ^ b + x / 2 ^ b * 2 ^ b.
Proof. intros x b Hb Hx. pose proof (pow2_pos b Hb). pose proof (Z.div_mod x (2 ^ b) ltac:(lia)). lia. Qed.

Lemma rep_root_b_sound : forall get root, 0 <= root -> rep_root_b get root = true -> rep_root get root.
Proof.
  intros get root Hr H x x' Hx Hx' Hb E. unfold rep_root_b in H.
  pose proof (allz_range 0 (2 ^ root) _ ltac:(rewrite Z.sub_0_r; exact H) x Hx) as Hx0. cbn beta in Hx0.
  set (b := code_bits (get x)) in *.
  replace ((1 <=? b) && (b <=? root)) with true in Hx0 by (symmetry; apply Bool.andb_true_iff; rewrite !Z.leb_le; lia).
  pose proof (pow2_pos b ltac:(lia)) as Pb.
  assert (Hk : 0 <= x' / 2 ^ b < 2 ^ (root - b)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia. replace (b + (root - b)) with root by lia. lia. }
  pose proof (allz_range 0 (2 ^ (root - b)) _ ltac:(rewrite Z.sub_0_r; exact Hx0) (x' / 2 ^ b) Hk) as Hk0. cbn beta in Hk0.
  apply Z.eqb_eq in Hk0. rewrite <- E in Hk0. rewrite <- (decomp_mod x' b) in Hk0 by lia. exact Hk0.
Qed.

Lemma rep_sub_b_sound : forall get root, 0 <= root -> rep_sub_b get root = true -> rep_sub get root.
Proof.
  intros get root Hr H x Hx Hop y y' Hy Hy' Hb E. unfold rep_sub_b in H.
  pose proof (allz_range 0 (2 ^ root) _ ltac:(rewrite Z.sub_0_r; exact H) x Hx) as Hx0. cbn beta in Hx0.
  replace ((1 <=? code_op (get x)) && (code_op (get x) <=? 15)) with true in Hx0
    by (symmetry; apply Bool.andb_true_iff; rewrite !Z.leb_le; lia).
  pose proof (allz_range 0 (2 ^ code_op (get x)) _ ltac:(rewrite Z.sub_0_r; exact Hx0) y Hy) as Hy0. cbn beta in Hy0.
  set (b := code_bits (get (code_val (get x) + y))) in *.
  pose proof (pow2_pos b ltac:(lia)) as Pb.
  destruct (Z.lt_ge_cases (code_op (get x)) b) as [Hbo|Hbo].
  {
    assert (y' = y); [|subst y'; reflexivity].
    pose proof (pow2_le (code_op (get x)) b ltac:(lia)).
    rewrite (Z.mod_small y' (2 ^ b)) in E by lia. rewrite (Z.mod_small y (2 ^ b)) in E by lia. exact E. }
  replace ((1 <=? b) && (b <=? code_op (get x))) with true in Hy0 by (symmetry; apply Bool.andb_true_iff; rewrite !Z.leb_le; lia).
  assert (Hk : 0 <= y' / 2 ^ b < 2 ^ (code_op (get x) - b)).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia. replace (b + (code_op (get x) - b)) with (code_op (get x)) by lia. lia. }
  pose proof (allz_range 0 (2 ^ (code_op (get x) - b)) _ ltac:(rewrite Z.sub_0_r; exact Hy0) (y' / 2 ^ b) Hk) as Hk0. cbn beta in Hk0.
  apply Z.eqb_eq in Hk0. rewrite <- E in Hk0. rewrite <- Z.add_assoc in Hk0. rewrite <- (decomp_mod y' b) in Hk0 by lia. exact Hk0.
Qed.

Lemma tblb_sound : forall ty get root used, tblb ty get root used = true -> TBLg ty get root used.
Proof.
  intros ty get root used H. unfold tblb in H.
  apply andb_prop in H as [H RS]. apply andb_prop in H as [H RR]. apply andb_prop in H as [H SH].
  apply andb_prop in H as [H U]. apply andb_prop in H as [R1 R2].
  apply Z.leb_le in R1. apply Z.leb_le in R2. apply Z.leb_le in U.
  split; [lia|]. split; [exact U|]. split; [|split].
  - intros x Hx. apply cell_ok_b_sound; [lia|].
    exact (allz_range 0 used _ ltac:(rewrite Z.sub_0_r; exact SH) x Hx).
  - apply rep_root_b_sound; [lia|exact RR].
  - apply rep_sub_b_sound; [lia|exact RS].
Qed.

Lemma lenfix_TBLg : TBLg LENS (arr_get lenfix_a) 9 512.
Proof. apply tblb_sound. vm_compute. reflexivity. Qed.

Lemma distfix_TBLg : TBLg DISTS (arr_get distfix_a) 5 32.
Proof. apply tblb_sound. vm_compute. reflexivity. Qed.

Lemma cpok_TBLg : forall ty s p root,
  cpok ty (is_codes s) p root ->
  exists used, TBLg ty (code_at s p) root used
    /\ match p with CDyn ofs => 0 <= ofs /\ ofs + used <= 1444 | CLenfix => used = 512 | CDistfix => used = 32 end.
Proof.
  intros ty s p root H. destruct p as [ofs| |]; cbn [cpok] in H.
  - destruct H as [Ho [used [Hu HT]]]. exists used. split; [exact HT|]. lia.
  - destruct H as [-> ->]. exists 512. split; [exact lenfix_TBLg|reflexivity].
  - destruct H as [-> ->]. exists 32. split; [exact distfix_TBLg|reflexivity].
Qed.

Lemma lneed_lneedg : forall s p root h, lneed s p root h = lneedg (code_at s p) root h.
Proof. reflexivity. Qed.
Lemma cneed_cneedg : forall s h, cneed s h = cneedg (code_at s (is_lencode s)) (is_lenbits s) h.
Proof. reflexivity. Qed.

Definition lens_sym_ok (s : Z) : bool :=
  let '(op, v) := sym_entry LENS s in
  ((op =? 0) && (0 <=? v) && (v <? 256))
  || ((op =? 96) && (v =? 0))
  || ((16 <=? op) && (op <=? 21) && (3 <=? v) && (v + 2 ^ (op - 16) <=? 259))
  || (op =? 203) || (op =? 77).
Lemma lens_sym_cases : forall s, 0 <= s < 288 ->
  let '(op, v) := sym_entry LENS s in
  (op = 0 /\ 0 <= v < 256) \/ (op = 96 /\ v = 0)
  \/ (16 <= op <= 21 /\ 3 <= v /\ v + 2 ^ (op - 16) <= 259) \/ op = 203 \/ op = 77.
Proof.
  intros s Hs.
  pose proof (allz_range 0 288 lens_sym_ok ltac:(vm_compute; reflexivity) s Hs) as H.
  unfold lens_sym_ok in H. destruct (sym_entry LENS s) as [op v].
  repeat (apply Bool.orb_prop in H; destruct H as [H|H]).
  - apply andb_prop in H as [H C]. apply andb_prop in H as [A B].
    apply Z.eqb_eq in A. apply Z.leb_le in B. apply Z.ltb_lt in C. left. lia.
  - apply andb_prop in H as [A B]. apply Z.eqb_eq in A. apply Z.eqb_eq in B. right; left. lia.
  - apply andb_prop in H as [H D]. apply andb_prop in H as [H C]. apply andb_prop in H as [A B].
    apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C. apply Z.leb_le in D. right; right; left. lia.
  - apply Z.eqb_eq in H. lia.
  - apply Z.eqb_eq in H. lia.
Qed.

Definition dists_sym_ok (s : Z) : bool :=
  let '(op, v) := sym_entry DISTS s in
  ((16 <=? op) && (op <=? 29) && (1 <=? v) && (v + 2 ^ (op - 16) <=? 32769))
  || ((op =? 64) && (v =? 0)).
Lemma dists_sym_cases : forall s, 0 <= s < 32 ->
  let '(op, v) := sym_entry DISTS s in
  (16 <= op <= 29 /\ 1 <= v /\ v + 2 ^ (op - 16) <= 32769) \/ (op = 64 /\ v = 0).
Proof.
  intros s Hs.
  pose proof (allz_range 0 32 dists_sym_ok ltac:(vm_compute; reflexivity) s Hs) as H.
  unfold dists_sym_ok in H. destruct (sym_entry DISTS s) as [op v].
  apply Bool.orb_prop in H. destruct H as [H|H].
  - apply andb_prop in H as [H D]. apply andb_prop in H as [H C]. apply andb_prop in H as [A B].
    apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C. apply Z.leb_le in D. left. lia.
  - apply andb_prop in H as [A B]. apply Z.eqb_eq in A. apply Z.eqb_eq in B. right. lia.
Qed.

Lemma order_a_range : forall k, 0 <= k < 19 -> 0 <= arr_get order_a k < 19.
Proof.
  intros k Hk.
  pose proof (allz_range 0 19 (fun k => (0 <=? arr_get order_a k) && (arr_get order_a k <? 19)) ltac:(vm_compute; reflexivity) k Hk) as H.
  cbn beta in H. apply andb_prop in H as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
Qed.
Lemma order_a_onto : forall i, 0 <= i < 19 -> exists k, 0 <= k < 19 /\ arr_get order_a k = i.
Proof.
  intros i Hi.
  pose proof (allz_range 0 19 (fun i => anyz 0 19%nat (fun k => arr_get order_a k =? i)) ltac:(vm_compute; reflexivity) i Hi) as H.
  cbn beta in H. destruct (anyz_true _ _ _ H) as [k [Hk E]]. apply Z.eqb_eq in E. exists k. split; [cbn in Hk; lia|exact E].
Qed.

Lemma dist_op_facts : forall op, 16 <= op <= 29 ->
  Z.land op 240 <> 0 /\ Z.land op 64 = 0 /\ Z.land op 15 = op - 16 /\ Z.land op 16 <> 0.
Proof.
  intros op Hop.
  pose proof (allz_range 16 30 (fun op => negb (Z.land op 240 =? 0) && (Z.land op 64 =? 0) && (Z.land op 15 =? op - 16) && negb (Z.land op 16 =? 0))
                ltac:(vm_compute; reflexivity) op ltac:(lia)) as H.
  cbn beta in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Bool.negb_true_iff in H1. apply Z.eqb_neq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3.
  apply Bool.negb_true_iff in H4. apply Z.eqb_neq in H4. repeat split; assumption.
Qed.

Lemma len_op_facts : forall op, 16 <= op <= 21 ->
  Z.land op 240 <> 0 /\ Z.land op 64 = 0 /\ Z.land op 15 = op - 16 /\ Z.land op 16 <> 0 /\ Z.land op 32 = 0.
Proof.
  intros op Hop.
  pose proof (allz_range 16 22 (fun op => negb (Z.land op 240 =? 0) && (Z.land op 64 =? 0) && (Z.land op 15 =? op - 16) && negb (Z.land op 16 =? 0) && (Z.land op 32 =? 0))
                ltac:(vm_compute; reflexivity) op ltac:(lia)) as H.
  cbn beta in H. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Bool.negb_true_iff in H1. apply Z.eqb_neq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3.
  apply Bool.negb_true_iff in H4. apply Z.eqb_neq in H4. apply Z.eqb_eq in H5. repeat split; assumption.
Qed.

Lemma notlink_land240 : forall ty e,
  ((exists sy, 0 <= sy < nsyms ty /\ code_op e = fst (sym_entry ty sy) /\ code_val e = snd (sym_entry ty sy)) \/ code_op e = 64) ->
  ty <> CODES -> code_op e <> 0 -> Z.land (code_op e) 240 <> 0.
Proof.
  intros ty e [[sy (Hsy & Hop & Hv)]|Hop] Hty Hnz.
  - destruct ty; [congruence| |].
    + cbn [nsyms] in Hsy. pose proof (lens_sym_cases sy Hsy) as L.
      destruct (sym_entry LENS sy) as [op v] eqn:Es. cbn [fst snd] in Hop, Hv. rewrite Hop. rewrite Hop in Hnz.
      destruct L as [[L _]|[[L _]|[(L & _)|[L|L]]]]; try lia.
      * rewrite L. discriminate.
      * exact (proj1 (len_op_facts op L)).
      * rewrite L. discriminate.
      * rewrite L. discriminate.
    + cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L.
      destruct (sym_entry DISTS sy) as [op v] eqn:Es. cbn [fst snd] in Hop, Hv. rewrite Hop.
      destruct L as [(L & _)|[L _]].
      * exact (proj1 (dist_op_facts op L)).
      * rewrite L. discriminate.
  - rewrite Hop. discriminate.
Qed.
