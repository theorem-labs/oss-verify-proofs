(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith PArith NArith List Bool Lia.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDenot.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zdenp_ok : forall E e, zdenp E e = zden E e.
Proof.
  intros E. induction e as [z|i|i|a IHa b IHb|c a IHa|o a IHa b IHb]; try reflexivity.
  - cbn [zdenp zden]. rewrite <- IHa, <- IHb. destruct b as [z| | | | |]; try reflexivity. destruct z; cbn; lia.
  - cbn [zdenp zden]. rewrite <- IHa. destruct c as [|p|p]; try reflexivity.
    + destruct p; cbn [zdenp]; try reflexivity; lia.
    + destruct p; try reflexivity; lia.
  - cbn. rewrite IHa, IHb. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint tden (E : env) (ts : terms) : Z :=
  match ts with [] => 0 | (k, a) :: ts' => k * zden E a + tden E ts' end.

Lemma of_terms_den : forall E ts c, zden E (of_terms ts c) = tden E ts + c.
Proof. intros E; induction ts as [|[k a] ts IH]; intros c; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma lin_of_den : forall E e, tden E (fst (lin_of e)) + snd (lin_of e) = zden E e.
Proof.
  intros E. induction e as [z|i|i|a IHa b IHb|c a IHa|o a IHa b IHb]; cbn; try lia.
  destruct a as [| | | |c a'|]; cbn; try lia.
  destruct (lin_of b) as [ts d] eqn:Hb. cbn. cbn in IHb. lia.
Qed.


(* [comment removed for export] *)
Lemma opk_eqb_eq : forall a b, opk_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; congruence. Qed.

Lemma expr_eqb_eq : forall a b, expr_eqb a b = true -> a = b.
Proof.
  induction a as [z|i|i|a1 IH1 a2 IH2|c a1 IH1|o a1 IH1 a2 IH2]; intros [z'|i'|i'|b1 b2|c' b1|o' b1 b2] H; cbn in H; try discriminate.
  - apply Z.eqb_eq in H. congruence.
  - apply Pos.eqb_eq in H. congruence.
  - apply Pos.eqb_eq in H. congruence.
  - apply andb_prop in H as [H1 H2]. rewrite (IH1 _ H1), (IH2 _ H2). reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite (IH1 _ H2). congruence.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply opk_eqb_eq in H1. rewrite (IH1 _ H2), (IH2 _ H3). congruence.
Qed.

Lemma lex_eq : forall c k, lex c k = Eq -> c = Eq /\ k = Eq.
Proof. intros [] k; cbn; intros; split; congruence. Qed.

Lemma expr_cmp_eq : forall a b, expr_cmp a b = Eq -> a = b.
Proof.
  induction a as [z|i|i|a1 IH1 a2 IH2|c a1 IH1|o a1 IH1 a2 IH2]; intros [z'|i'|i'|b1 b2|c' b1|o' b1 b2] H; cbn in H;
    try discriminate.
  - apply Z.compare_eq in H. congruence.
  - apply Pos.compare_eq in H. congruence.
  - apply Pos.compare_eq in H. congruence.
  - apply lex_eq in H as [H1 H2]. rewrite (IH1 _ H1), (IH2 _ H2). reflexivity.
  - apply lex_eq in H as [H1 H2]. apply Z.compare_eq in H1. rewrite (IH1 _ H2). congruence.
  - apply lex_eq in H as [H1 H]. apply lex_eq in H as [H2 H3]. apply Z.compare_eq in H1.
    rewrite (IH1 _ H2), (IH2 _ H3). destruct o, o'; cbn in H1; try discriminate; reflexivity.
Qed.

Lemma terms_add_den : forall E xs ys, tden E (terms_add xs ys) = tden E xs + tden E ys.
Proof.
  intros E. induction xs as [|[k a] xs IH]; intros ys; [reflexivity|].
  induction ys as [|[k' a'] ys IHy]; [cbn; lia|].
  cbn -[Z.add Z.mul Z.eqb]. destruct (expr_cmp a a') eqn:Hc.
  - apply expr_cmp_eq in Hc. subst a'. destruct (Z.eqb_spec (k + k') 0).
    + rewrite IH. cbn. nia.
    + cbn -[Z.add Z.mul]. rewrite IH. cbn. nia.
  - cbn -[Z.mul Z.add]. rewrite IH. cbn. lia.
  - cbn -[Z.mul Z.add] in IHy |- *.  rewrite IHy. lia.
Qed.

Lemma terms_scale_den : forall E k xs, tden E (terms_scale k xs) = k * tden E xs.
Proof.
  intros E k xs. unfold terms_scale. destruct (Z.eqb_spec k 0); [subst; cbn; lia|].
  induction xs as [|[c a] xs IH]; cbn; [lia|]. rewrite IH. lia.
Qed.

Lemma eadd_den : forall E a b, zden E (eadd a b) = zden E a + zden E b.
Proof.
  intros E a b. unfold eadd.
  destruct (lin_of a) as [xs c] eqn:Ha. destruct (lin_of b) as [ys d] eqn:Hb.
  rewrite of_terms_den, terms_add_den.
  pose proof (lin_of_den E a) as La. pose proof (lin_of_den E b) as Lb. rewrite Ha in La. rewrite Hb in Lb. cbn in La, Lb. lia.
Qed.

Lemma emulc_den : forall E k a, zden E (emulc k a) = k * zden E a.
Proof.
  intros E k a. unfold emulc. destruct (lin_of a) as [xs c] eqn:Ha.
  rewrite of_terms_den, terms_scale_den.
  pose proof (lin_of_den E a) as La. rewrite Ha in La. cbn in La. lia.
Qed.

Lemma esub_den : forall E a b, zden E (esub a b) = zden E a - zden E b.
Proof. intros. unfold esub. rewrite eadd_den, emulc_den. lia. Qed.

Lemma eaddc_den : forall E a k, zden E (eaddc a k) = zden E a + k.
Proof. intros. unfold eaddc. rewrite eadd_den. reflexivity. Qed.

Lemma eatom_den : forall E a, zden E (eatom a) = zden E a.
Proof. intros. cbn. lia. Qed.

Lemma ebase_econst : forall E e, zden E (ebase e) + econst e = zden E e.
Proof.
  intros E e. unfold ebase, econst. rewrite of_terms_den. pose proof (lin_of_den E e). lia.
Qed.

Lemma terms_eqb_eq : forall xs ys, terms_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|[k a] xs IH]; intros [|[k' a'] ys] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply expr_eqb_eq in H2. rewrite (IH _ H3). congruence.
Qed.

Lemma ediff_lit_den : forall E a b d, ediff_lit a b = Some d -> zden E a = zden E b + d.
Proof.
  intros E a b d. unfold ediff_lit.
  destruct (lin_of a) as [xs c] eqn:Ha. destruct (lin_of b) as [ys c'] eqn:Hb.
  destruct (terms_eqb xs ys) eqn:T; [|discriminate]. intros H. injection H; intros <-.
  apply terms_eqb_eq in T. subst ys.
  pose proof (lin_of_den E a) as La. pose proof (lin_of_den E b) as Lb. rewrite Ha in La. rewrite Hb in Lb. cbn in La, Lb. lia.
Qed.

Lemma is_lit_den : forall E e z, is_lit e = Some z -> zden E e = z.
Proof. intros E e z H; destruct e; cbn in H; try discriminate. injection H; intros <-. reflexivity. Qed.

Lemma expr_of_reg_den : forall E r, Z_to_bv 64 (zden E (expr_of_reg r)) = rden E r.
Proof.
  intros E [i|e]; cbn.
  - apply bv_eq. rewrite Z_to_bv_unsigned. rewrite Z.add_0_r, Z.mul_1_l. apply bv_wrap_small. apply bv_unsigned_in_range.
  - rewrite zdenp_ok. reflexivity.
Qed.

Lemma mkreg_shape : forall e, mkreg e = RZ e \/ exists i, e = EAdd (EMulC 1 (EUv i)) (ELit 0).
Proof.
  intros e. unfold mkreg.
  repeat match goal with
         | |- context [match ?x with _ => _ end] => destruct x; try (left; reflexivity)
         end.
  right. eexists. reflexivity.
Qed.
Lemma mkreg_den : forall E e, rden E (mkreg e) = Z_to_bv 64 (zden E e).
Proof.
  intros E e. destruct (mkreg_shape e) as [-> | [i ->]].
  - cbn. rewrite zdenp_ok. reflexivity.
  - cbn. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite Z.mul_1_l, Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition osound (E : env) (O : oracle) : Prop :=
  (forall e, o_ge O e = true -> 0 <= zden E e)
  /\ (forall a, zden E a mod 2 ^ Z.of_N (o_al O a) = 0).

Lemma e_in_sound : forall E O e lo hi, osound E O -> e_in O e lo hi = true -> lo <= zden E e <= hi.
Proof.
  intros E O e lo hi [HO _] H. unfold e_in in H. apply andb_prop in H as [H1 H2].
  apply HO in H1. apply HO in H2. rewrite eadd_den in H1, H2. rewrite emulc_den in H2. cbn in H1, H2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pctz_div : forall p, (2 ^ Z.of_N (pctz p) | Z.pos p).
Proof.
  induction p as [p IH|p IH|]; cbn [pctz].
  - exists (Z.pos p~1). rewrite Z.pow_0_r. lia.
  - rewrite N2Z.inj_succ, Z.pow_succ_r by lia. destruct IH as [q Hq]. exists q. lia.
  - exists 1. rewrite Z.pow_0_r. lia.
Qed.

Lemma zal_div : forall z, z <> 0 -> (2 ^ Z.of_N (zal z) | z).
Proof.
  intros [|p|p] H; [congruence| apply pctz_div |].
  destruct (pctz_div p) as [q Hq]. exists (- q). cbn [zal]. lia.
Qed.

Lemma divide_pow2_le : forall a b x, (a <= b)%N -> (2 ^ Z.of_N b | x) -> (2 ^ Z.of_N a | x).
Proof.
  intros a b x Hab [q Hq]. exists (q * 2 ^ (Z.of_N b - Z.of_N a)).
  rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. replace (Z.of_N b - Z.of_N a + Z.of_N a) with (Z.of_N b) by lia. exact Hq.
Qed.

Lemma mod0_divide : forall x m, 0 < m -> (x mod m = 0 <-> (m | x)).
Proof. intros x m Hm. split; intro H. - apply Z.mod_divide; lia. - apply Z.mod_divide; [lia|exact H]. Qed.


Lemma mul_divide : forall a b x y, (a | x) -> (b | y) -> (a * b | x * y).
Proof. intros a b x y [q Hq] [r Hr]. exists (q * r). subst. lia. Qed.

Lemma land_mod_pow2 : forall x y n, 0 <= n -> Z.land (x mod 2 ^ n) (y mod 2 ^ n) = (Z.land x y) mod 2 ^ n.
Proof.
  intros x y n Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.testbit_mod_pow2, Z.land_spec by lia.
  destruct (Z.ltb i n); reflexivity.
Qed.

Lemma lor_mod_pow2 : forall x y n, 0 <= n -> Z.lor (x mod 2 ^ n) (y mod 2 ^ n) = (Z.lor x y) mod 2 ^ n.
Proof.
  intros x y n Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec, !Z.testbit_mod_pow2, Z.lor_spec by lia.
  destruct (Z.ltb i n); reflexivity.
Qed.

Lemma lxor_mod_pow2 : forall x y n, 0 <= n -> Z.lxor (x mod 2 ^ n) (y mod 2 ^ n) = (Z.lxor x y) mod 2 ^ n.
Proof.
  intros x y n Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec, !Z.testbit_mod_pow2, Z.lxor_spec by lia.
  destruct (Z.ltb i n); reflexivity.
Qed.

Lemma lor_divide_pow2 : forall x y n, 0 <= n -> (2 ^ n | x) -> (2 ^ n | y) -> (2 ^ n | Z.lor x y).
Proof.
  intros x y n Hn Hx Hy. apply mod0_divide; [apply Z.pow_pos_nonneg; lia|].
  rewrite <- lor_mod_pow2 by exact Hn.
  apply mod0_divide in Hx; [|apply Z.pow_pos_nonneg; lia]. apply mod0_divide in Hy; [|apply Z.pow_pos_nonneg; lia].
  rewrite Hx, Hy. reflexivity.
Qed.

Lemma land_divide_pow2_l : forall x y n, 0 <= n -> (2 ^ n | x) -> (2 ^ n | Z.land x y).
Proof.
  intros x y n Hn Hx. apply mod0_divide; [apply Z.pow_pos_nonneg; lia|].
  rewrite <- land_mod_pow2 by exact Hn.
  apply mod0_divide in Hx; [|apply Z.pow_pos_nonneg; lia]. rewrite Hx. apply Z.land_0_l.
Qed.

Lemma land_divide_pow2_r : forall x y n, 0 <= n -> (2 ^ n | y) -> (2 ^ n | Z.land x y).
Proof. intros x y n Hn Hy. rewrite Z.land_comm. apply land_divide_pow2_l; assumption. Qed.

Lemma xal_div : forall E O e, osound E O -> (2 ^ Z.of_N (xal O e) | zden E e).
Proof.
  intros E O e [_ HA]. induction e as [c|i|i|a IHa b IHb|k a IHa|o a IHa b IHb]; cbn [xal zden].
  - destruct (Z.eq_dec c 0) as [->|Hc]; [exists 0; reflexivity| apply zal_div; exact Hc].
  - apply mod0_divide; [apply Z.pow_pos_nonneg; lia|]. apply (HA (EZv i)).
  - apply mod0_divide; [apply Z.pow_pos_nonneg; lia|]. apply (HA (EUv i)).
  - apply Z.divide_add_r; [eapply divide_pow2_le; [apply N.le_min_l| exact IHa] | eapply divide_pow2_le; [apply N.le_min_r| exact IHb]].
  - destruct (Z.eq_dec k 0) as [->|Hk]. { exists 0. reflexivity. }
    rewrite N2Z.inj_add, Z.pow_add_r by lia. apply mul_divide; [apply zal_div; exact Hk| exact IHa].
  - assert (HO : (2 ^ Z.of_N (o_al O (EOp o a b)) | opden o (zden E a) (zden E b))).
    { apply mod0_divide; [apply Z.pow_pos_nonneg; lia|]. apply (HA (EOp o a b)). }
    destruct o; try exact HO; cbn [opden].
    + destruct (N.max_spec (o_al O (EOp OAnd a b)) (N.max (xal O a) (xal O b))) as [[_ ->]|[_ ->]]; [|exact HO].
      destruct (N.max_spec (xal O a) (xal O b)) as [[_ ->]|[_ ->]].
      * apply land_divide_pow2_r; [lia| exact IHb].
      * apply land_divide_pow2_l; [lia| exact IHa].
    + destruct (N.max_spec (o_al O (EOp OOr a b)) (N.min (xal O a) (xal O b))) as [[_ ->]|[_ ->]]; [|exact HO].
      apply lor_divide_pow2; [lia| |].
      * eapply divide_pow2_le; [apply N.le_min_l| exact IHa].
      * eapply divide_pow2_le; [apply N.le_min_r| exact IHb].
Qed.

Lemma terms_al_div : forall E O ts, osound E O -> (2 ^ Z.of_N (terms_al O ts) | tden E ts).
Proof.
  intros E O ts HO. pose proof HO as [_ HA]. induction ts as [|[k a] ts IH]; cbn [terms_al tden].
  - exists 0. reflexivity.
  - apply Z.divide_add_r.
    + eapply divide_pow2_le; [apply N.le_min_l|].
      destruct (Z.eq_dec k 0) as [->|Hk]. { exists 0. reflexivity. }
      rewrite N2Z.inj_add, Z.pow_add_r by lia. apply mul_divide.
      * apply zal_div. exact Hk.
      * apply xal_div. exact HO.
    + eapply divide_pow2_le; [apply N.le_min_r| exact IH].
Qed.

Lemma eal_sound : forall E O e, osound E O -> (2 ^ Z.of_N (eal O e) | zden E e).
Proof.
  intros E O e HO. unfold eal. destruct (lin_of e) as [ts c] eqn:He.
  pose proof (lin_of_den E e) as L. rewrite He in L. cbn in L. rewrite <- L.
  apply Z.divide_add_r.
  - eapply divide_pow2_le; [apply N.le_min_l| apply terms_al_div; exact HO].
  - eapply divide_pow2_le; [apply N.le_min_r|].
    destruct (Z.eq_dec c 0) as [->|Hc]; [exists 0; reflexivity| apply zal_div; exact Hc].
Qed.

Lemma eal_mod : forall E O e j, osound E O -> (j <= eal O e)%N -> zden E e mod 2 ^ Z.of_N j = 0.
Proof.
  intros E O e j HO Hj. apply mod0_divide; [apply Z.pow_pos_nonneg; lia|].
  eapply divide_pow2_le; [exact Hj| apply eal_sound; exact HO].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_low_mask : forall x j, 0 <= j -> Z.land x (2 ^ j - 1) = x mod 2 ^ j.
Proof. intros x j Hj. rewrite <- Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity. Qed.

Lemma land_high_mask : forall x j, 0 <= j -> Z.land x (- 2 ^ j) = x - x mod 2 ^ j.
Proof.
  intros x j Hj.
  assert (E1 : x - x mod 2 ^ j = (x / 2 ^ j) * 2 ^ j).
  { pose proof (Z.div_mod x (2 ^ j) ltac:(apply Z.pow_nonzero; lia)). lia. }
  rewrite E1. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec.
  replace (- 2 ^ j) with (Z.lnot (Z.ones j)) by (unfold Z.lnot, Z.ones; rewrite Z.shiftl_1_l; lia).
  rewrite Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases n j) as [Hlt|Hge].
  - rewrite Z.ones_spec_low by lia. rewrite (Z.mul_pow2_bits_low _ _ _ Hlt). apply andb_false_r.
  - rewrite Z.ones_spec_high by lia. rewrite andb_true_r. rewrite Z.mul_pow2_bits by lia. rewrite Z.div_pow2_bits by lia. f_equal. lia.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma w64_eq : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

Lemma w64_add : forall x y, (Z_to_bv 64 x + Z_to_bv 64 y)%bv = Z_to_bv 64 (x + y).
Proof. intros. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. apply bv_wrap_add_idemp. Qed.

Lemma w64_sub : forall x y, (Z_to_bv 64 x - Z_to_bv 64 y)%bv = Z_to_bv 64 (x - y).
Proof. intros. apply bv_eq. rewrite bv_sub_unsigned, !Z_to_bv_unsigned. apply bv_wrap_sub_idemp. Qed.

Lemma w64_mul : forall x y, (Z_to_bv 64 x * Z_to_bv 64 y)%bv = Z_to_bv 64 (x * y).
Proof. intros. apply bv_eq. rewrite bv_mul_unsigned, !Z_to_bv_unsigned. apply bv_wrap_mul_idemp. Qed.

Lemma w64_and : forall x y, bv_and (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.land x y).
Proof.
  intros. apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  apply land_mod_pow2. cbn; lia.
Qed.

Lemma w64_or : forall x y, bv_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof.
  intros. apply bv_eq. rewrite bv_or_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  apply lor_mod_pow2. cbn; lia.
Qed.

Lemma w64_xor : forall x y, bv_xor (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lxor x y).
Proof.
  intros. apply bv_eq. rewrite bv_xor_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  apply lxor_mod_pow2. cbn; lia.
Qed.

Lemma w64_of_unsigned : forall (w : word), Z_to_bv 64 (bv_unsigned w) = w.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma zlow64_unsigned : forall x, bv_unsigned (Z_to_bv 64 x) = zlow 64 x.
Proof. intros. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithOracle.
  Variable E : env.
  Variable O : oracle.
  Hypothesis HO : osound E O.

  Lemma elow_den : forall e k, 0 <= k -> zden E (elow O e k) = (zden E e) mod 2 ^ k.
  Proof.
    intros e k Hk. unfold elow. destruct (is_lit e) eqn:L.
    - cbn. apply is_lit_den with (E := E) in L. rewrite L. reflexivity.
    - destruct (e_in O e 0 (2 ^ k - 1)) eqn:R.
      + apply e_in_sound with (E := E) in R; [|exact HO]. symmetry. apply Z.mod_small. lia.
      + cbn. unfold zlow. lia.
  Qed.

  Lemma zswrap_small : forall k x, 0 < k -> - 2 ^ (k - 1) <= x <= 2 ^ (k - 1) - 1 -> zswrap k x = x.
  Proof.
    intros k x Hk Hx. unfold zswrap.
    replace (2 ^ k) with (2 * 2 ^ (k - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
    rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma esx_den : forall e k, 0 < k -> zden E (esx O e k) = zswrap k (zden E e).
  Proof.
    intros e k Hk. unfold esx. destruct (is_lit e) eqn:L.
    - cbn. apply is_lit_den with (E := E) in L. rewrite L. reflexivity.
    - destruct (e_in O e (- 2 ^ (k - 1)) (2 ^ (k - 1) - 1)) eqn:R.
      + apply e_in_sound with (E := E) in R; [|exact HO]. symmetry. apply zswrap_small; lia.
      + cbn. lia.
  Qed.

  Lemma zswrap_mod : forall k x, 0 < k -> zswrap k (x mod 2 ^ k) = zswrap k x.
  Proof.
    intros k x Hk. unfold zswrap. f_equal. rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia). reflexivity.
  Qed.

  Lemma zswrap_add_zswrap : forall k x c, 0 < k -> zswrap k (x + zswrap k c) = zswrap k (x + c).
  Proof.
    intros k x c Hk. unfold zswrap. f_equal.
    replace (x + ((c + 2 ^ (k - 1)) mod 2 ^ k - 2 ^ (k - 1)) + 2 ^ (k - 1)) with (x + (c + 2 ^ (k - 1)) mod 2 ^ k) by lia.
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia).
    f_equal. lia.
  Qed.

  Lemma ew32_den : forall e, zden E (ew32 O e) = zswrap 32 (zden E e).
  Proof.
    intros e. unfold ew32. destruct (is_lit e) eqn:L.
    - cbn -[zswrap]. apply is_lit_den with (E := E) in L. rewrite L. reflexivity.
    - destruct (e_s32 O (eadd (ebase e) (ELit (zswrap 32 (econst e))))) eqn:R2.
      { unfold e_s32 in R2. apply e_in_sound with (E := E) in R2; [|exact HO]. rewrite eadd_den in R2 |- *. cbn [zden] in R2 |- *.
        pose proof (ebase_econst E e) as BE.
        replace (zden E e) with (zden E (ebase e) + econst e) by lia. rewrite <- zswrap_add_zswrap by lia.
        symmetry. apply zswrap_small; [lia|]. unfold two31 in R2. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]. lia. }
      destruct (e_s32 O e) eqn:R.
      + unfold e_s32 in R. apply e_in_sound with (E := E) in R; [|exact HO]. symmetry. apply zswrap_small; [lia|].
        unfold two31 in R. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]. lia.
      + rewrite esx_den, elow_den by lia. apply zswrap_mod. lia.
  Qed.

  Lemma eshr_den : forall e k, 0 <= k ->
    Z_to_bv 64 (zden E (eshr O e k)) = Z_to_bv 64 (Z.shiftr (zlow 64 (zden E e)) k).
  Proof.
    intros e k Hk. unfold eshr. destruct (Z.eqb_spec k 0).
    - subst. rewrite Z.shiftr_0_r. apply w64_eq. unfold zlow. rewrite Z.mod_mod by lia. reflexivity.
    - destruct (is_lit e) eqn:L.
      + cbn -[zlow Z.shiftr]. apply is_lit_den with (E := E) in L. rewrite L. reflexivity.
      + cbn -[elow Z.shiftr]. rewrite Z.add_0_r, Z.mul_1_l. rewrite elow_den by lia. reflexivity.
  Qed.

  Lemma eshl_den : forall a k, 0 <= k -> zden E (eshl a k) = zden E a * 2 ^ k.
  Proof. intros. unfold eshl. rewrite emulc_den. lia. Qed.

  Lemma omul_den : forall a b, zden E (eatom (omul a b)) = zden E a * zden E b.
  Proof. intros a b. unfold omul. destruct (expr_cmp a b); cbn; lia. Qed.
  Lemma emul_den : forall a b, zden E (emul a b) = zden E a * zden E b.
  Proof.
    intros a b. unfold emul. destruct (is_lit a) eqn:La; [|destruct (is_lit b) eqn:Lb].
    - apply is_lit_den with (E := E) in La. rewrite emulc_den, La. reflexivity.
    - apply is_lit_den with (E := E) in Lb. rewrite emulc_den, Lb. lia.
    - cbn; lia.
  Qed.
  Lemma emulO_den : forall O' a b, zden E (emulO O' a b) = zden E a * zden E b.
  Proof.
    intros O' a b. unfold emulO. destruct (is_lit a) eqn:La; [|destruct (is_lit b) eqn:Lb].
    - apply is_lit_den with (E := E) in La. rewrite emulc_den, La. reflexivity.
    - apply is_lit_den with (E := E) in Lb. rewrite emulc_den, Lb. lia.
    - destruct (o_kn O' _); cbn; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma exor_den : forall a b, zden E (exor O a b) mod 2 ^ 64 = Z.lxor (zden E a) (zden E b) mod 2 ^ 64.
  Proof.
    intros a b. unfold exor.
    assert (CPL : forall y, (zlow 64 y =? two64 - 1) = true ->
              zden E (if e_u64 O a then eadd (ELit (two64 - 1)) (emulc (-1) a) else eadd (ELit (-1)) (emulc (-1) a)) mod 2 ^ 64
              = Z.lxor (zden E a) y mod 2 ^ 64).
    { intros y Hy. apply Z.eqb_eq in Hy. unfold zlow in Hy.
      transitivity (Z.lxor (zden E a) (-1) mod 2 ^ 64).
      2:{ rewrite <- (lxor_mod_pow2 (zden E a) (-1)), <- (lxor_mod_pow2 (zden E a) y) by lia. rewrite Hy. reflexivity. }
      rewrite Z.lxor_m1_r. unfold Z.lnot, Z.pred.
      destruct (e_u64 O a); rewrite eadd_den, emulc_den; cbn [zden]; unfold two64.
      - replace (18446744073709551616 - 1 + -1 * zden E a) with ((- zden E a + -1) + 1 * 2 ^ 64) by lia.
        rewrite Z.mod_add by lia. reflexivity.
      - f_equal. lia. }
    destruct (is_lit a) as [x|] eqn:La; destruct (is_lit b) as [y|] eqn:Lb;
      try (apply is_lit_den with (E := E) in La); try (apply is_lit_den with (E := E) in Lb);
      try destruct x as [|px|px]; try destruct y as [|py|py];
      try (destruct (zlow 64 _ =? two64 - 1) eqn:Q);
      first [ rewrite ?Lb; apply CPL; exact Q
            | rewrite eatom_den; cbn [zden opden]; reflexivity
            | cbn -[Z.lxor Z.pow Z.modulo]; rewrite ?La, ?Lb, ?Z.lxor_0_l, ?Z.lxor_0_r; reflexivity ].
  Qed.

  Lemma low_mask_pow2 : forall m, 0 < m -> Z.land m (m + 1) = 0 -> m = 2 ^ Z.log2 (m + 1) - 1.
  Proof.
    intros m Hm H.
    destruct (Z.log2_spec (m + 1) ltac:(lia)) as [H1 H2].
    destruct (Z.eq_dec (m + 1) (2 ^ Z.log2 (m + 1))); [lia|]. exfalso.
    assert (Hb1 : Z.testbit (m + 1) (Z.log2 (m + 1)) = true) by (apply Z.bit_log2; lia).
    assert (Hb2 : Z.testbit m (Z.log2 (m + 1)) = true).
    { replace (Z.log2 (m + 1)) with (Z.log2 m); [apply Z.bit_log2; lia|].
      apply Z.le_antisymm.
      - apply Z.log2_le_mono. lia.
      - apply Z.log2_le_pow2; lia. }
    assert (X : Z.testbit (Z.land m (m + 1)) (Z.log2 (m + 1)) = true) by (rewrite Z.land_spec, Hb1, Hb2; reflexivity).
    rewrite H in X. rewrite Z.bits_0 in X. discriminate.
  Qed.

  Lemma high_mask_pow2 : forall m, m < -1 -> Z.land (- m) (- m - 1) = 0 -> m = - 2 ^ Z.log2 (- m).
  Proof.
    intros m Hm H. pose proof (low_mask_pow2 (- m - 1) ltac:(lia)) as P.
    rewrite Z.land_comm in H. replace (- m - 1 + 1) with (- m) in P by lia.
    specialize (P H). lia.
  Qed.
  Lemma low_mask_j_ok : forall m j, low_mask_j m = Some j -> 0 <= j /\ m = 2 ^ j - 1.
  Proof.
    intros m j H. unfold low_mask_j in H.
    destruct (Z.ltb_spec 0 m); [|discriminate]. destruct (Z.eqb_spec (Z.land m (m + 1)) 0); [|discriminate].
    injection H; intros <-. split; [apply Z.log2_nonneg|]. apply low_mask_pow2; assumption.
  Qed.

  Lemma high_mask_j_ok : forall m j, high_mask_j m = Some j -> 0 <= j /\ m = - 2 ^ j.
  Proof.
    intros m j H. unfold high_mask_j in H.
    destruct (Z.ltb_spec m (-1)); [|discriminate]. destruct (Z.eqb_spec (Z.land (- m) (- m - 1)) 0); [|discriminate].
    injection H; intros <-. split; [apply Z.log2_nonneg|]. apply high_mask_pow2; assumption.
  Qed.

  Lemma olit_eqb_den : forall e z, olit_eqb (is_lit e) z = true -> zden E e = z.
  Proof. intros e z H. destruct e; cbn in H; try discriminate. apply Z.eqb_eq in H. cbn. exact H. Qed.

  Lemma eand_den : forall a b, zden E (eand O a b) = Z.land (zden E a) (zden E b).
  Proof.
    intros a b. unfold eand.
    assert (AT : zden E (eatom (EOp OAnd a b)) = Z.land (zden E a) (zden E b)) by (cbn; lia).
    assert (EQ : zden E (if expr_eqb a b then a else eatom (EOp OAnd a b)) = Z.land (zden E a) (zden E b)).
    { destruct (expr_eqb a b) eqn:Q; [|exact AT]. apply expr_eqb_eq in Q. subst. rewrite Z.land_diag. reflexivity. }
    destruct (is_lit a) as [x|] eqn:La; destruct (is_lit b) as [m|] eqn:Lb; cbn [olit_eqb orb];
      try (apply is_lit_den with (E := E) in La); try (apply is_lit_den with (E := E) in Lb).
    - cbn. congruence.
    - rewrite La. destruct (Z.eqb_spec x (-1)) as [->|]; [rewrite Z.land_m1_l; reflexivity|].
      destruct (Z.eqb_spec x 0) as [->|]; [rewrite Z.land_0_l; reflexivity|]. rewrite <- La. exact EQ.
    - destruct (Z.eqb_spec m (-1)) as [->|]; [rewrite Lb, Z.land_m1_r; reflexivity|].
      destruct (Z.eqb_spec m 0) as [->|]; [rewrite Lb, Z.land_0_r; reflexivity|].
      destruct (low_mask_j m) as [j|] eqn:LM.
      + apply low_mask_j_ok in LM as [Hj Hm].
        destruct (N.leb_spec (Z.to_N j) (eal O a)) as [Hle|Hgt].
        * cbn [zden orb]. rewrite Lb, Hm, land_low_mask by lia. symmetry.
          pose proof (eal_mod E O a (Z.to_N j) HO Hle) as M. rewrite Z2N.id in M by lia. exact M.
        * destruct (e_in O a 0 m) eqn:R; [|exact AT].
          apply e_in_sound with (E := E) in R; [|exact HO]. rewrite Lb, Hm, land_low_mask by lia. symmetry. cbn [orb]. apply Z.mod_small. lia.
      + destruct (high_mask_j m) as [j|] eqn:HM; [|exact AT].
        apply high_mask_j_ok in HM as [Hj Hm].
        destruct (N.leb_spec (Z.to_N j) (eal O a)) as [Hle|Hgt]; [|exact AT].
        cbn [orb]. rewrite Lb, Hm, land_high_mask by lia. pose proof (eal_mod E O a (Z.to_N j) HO Hle) as M. rewrite Z2N.id in M by lia. lia.
    - exact EQ.
  Qed.
  Lemma lor_aligned_add : forall a y j, 0 <= j -> a mod 2 ^ j = 0 -> 0 <= y < 2 ^ j -> Z.lor a y = a + y.
  Proof.
    intros a y j Hj Ha Hy.
    assert (L : Z.land a y = 0).
    { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
      destruct (Z_lt_dec n j).
      - replace a with ((a / 2 ^ j) * 2 ^ j) by (pose proof (Z.div_mod a (2 ^ j) ltac:(apply Z.pow_nonzero; lia)); lia).
        rewrite Z.mul_pow2_bits_low by lia. reflexivity.
      - destruct (Z.eq_dec y 0) as [->|]; [rewrite Z.bits_0; apply andb_false_r|].
        rewrite (Z.bits_above_log2 y n); [apply andb_false_r| lia|].
        apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hy)|]. apply Z.pow_le_mono_r; lia. }
    rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
  Qed.
  Lemma eor_den : forall a b, zden E (eor O a b) = Z.lor (zden E a) (zden E b).
  Proof.
    intros a b. unfold eor.
    assert (AT : zden E (eatom (EOp OOr a b)) = Z.lor (zden E a) (zden E b)) by (cbn; lia).
    destruct (is_lit a) as [x|] eqn:La; destruct (is_lit b) as [y|] eqn:Lb;
      try (apply is_lit_den with (E := E) in La); try (apply is_lit_den with (E := E) in Lb).
    - destruct x; cbn -[Z.lor]; rewrite La, Lb; reflexivity.
    - rewrite La. destruct x; [cbn -[Z.lor]; rewrite Z.lor_0_l; reflexivity| |]; destruct (expr_eqb a b) eqn:Q;
        try (apply expr_eqb_eq in Q; subst; rewrite <- La, Z.lor_diag; reflexivity); rewrite <- La; exact AT.
    - destruct (Z.eq_dec y 0) as [->|NZ]; [cbn -[Z.lor]; rewrite Lb, Z.lor_0_r; reflexivity|].
      assert (STEP : zden E (if (0 <? y) && (y <? 2 ^ Z.of_N (eal O a)) then eadd a (ELit y) else eatom (EOp OOr a b)) = Z.lor (zden E a) (zden E b)).
      { destruct (Z.ltb_spec 0 y); destruct (Z.ltb_spec y (2 ^ Z.of_N (eal O a))); cbn [andb]; try exact AT.
        rewrite eadd_den. cbn [zden]. rewrite Lb. symmetry. apply (lor_aligned_add _ _ (Z.of_N (eal O a))); [lia| |lia].
        pose proof (eal_mod E O a (eal O a) HO ltac:(lia)) as M. exact M. }
      destruct y; [exfalso; apply NZ; reflexivity| exact STEP| exact STEP].
    - destruct (expr_eqb a b) eqn:Q; [apply expr_eqb_eq in Q; subst; rewrite Z.lor_diag; reflexivity| exact AT].
  Qed.
End WithOracle.

Lemma lexistsb_existsb : forall {A} (f : A -> bool) l, lexistsb f l = existsb f l.
Proof. intros A f l. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. destruct (f x); reflexivity. Qed.
Lemma lforallb_forallb : forall {A} (f : A -> bool) l, lforallb f l = forallb f l.
Proof. intros A f l. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. destruct (f x); reflexivity. Qed.
Lemma lexistsb_exists : forall {A} (f : A -> bool) l, lexistsb f l = true <-> exists x, In x l /\ f x = true.
Proof. intros A f l. rewrite lexistsb_existsb. apply existsb_exists. Qed.
Lemma lforallb_forall : forall {A} (f : A -> bool) l, lforallb f l = true <-> (forall x, In x l -> f x = true).
Proof. intros A f l. rewrite lforallb_forallb. apply forallb_forall. Qed.
