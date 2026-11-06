(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Btauto.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PropExec AzSymExec3 AzSymExec3Sound AzKBits.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Module KBS.
Import AX2.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Import AX2S.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Import KB.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition kb_ok (b : kbits) (x : Z) : Prop :=
  forall i, 0 <= i < 64 -> Z.testbit (km b) i = true -> Z.testbit x i = Z.testbit (kv b) i.

(* [comment removed for export] *)
Lemma some_inj : forall (A : Type) (x y : A), Some x = Some y -> x = y.
Proof. intros A x y H. exact (f_equal (fun o => match o with Some z => z | None => x end) H). Qed.

(* [comment removed for export] *)
Lemma M64_bit : forall i, 0 <= i -> Z.testbit M64 i = (i <? 64).
Proof. intros i Hi. unfold M64. apply Z.testbit_ones_nonneg; lia. Qed.

Lemma bit_high : forall x j, 0 <= x < 2 ^ 64 -> 64 <= j -> Z.testbit x j = false.
Proof.
  intros x j Hx Hj. rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma ones_bit : forall n i, 0 <= n -> 0 <= i -> Z.testbit (Z.ones n) i = (i <? n).
Proof. intros. apply Z.testbit_ones_nonneg; lia. Qed.

Lemma lit_range : forall b, 0 <= lit b < 2 ^ 64.
Proof. intros b. unfold lit, M64. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.

Lemma shamt_range : forall b, 0 <= shamt b < 64.
Proof. intros b. unfold shamt. rewrite Z.land_ones by lia. change (2 ^ 6) with 64. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Lemma full_lit : forall b x, kb_ok b x -> is_full b = true -> 0 <= x < 2 ^ 64 -> x = lit b.
Proof.
  intros b x Hk Hf Hx. unfold is_full in Hf. apply Z.eqb_eq in Hf.
  apply Z.bits_inj'. intros i Hi. unfold lit. rewrite Z.land_spec, M64_bit by lia.
  destruct (Z.ltb_spec i 64) as [Hlt|Hge].
  - rewrite andb_true_r. apply Hk; [lia|].
    apply (f_equal (fun z => Z.testbit z i)) in Hf. rewrite Z.land_spec, M64_bit in Hf by lia.
    rewrite (proj2 (Z.ltb_lt i 64) Hlt), andb_true_r in Hf. exact Hf.
  - rewrite andb_false_r. apply bit_high; lia.
Qed.

Lemma full_ok : forall z, kb_ok (full z) (z mod 2 ^ 64).
Proof.
  intros z i Hi _. cbn [full kv]. rewrite Z.mod_pow2_bits_low by lia. rewrite Z.land_spec, M64_bit by lia.
  rewrite (proj2 (Z.ltb_lt i 64)) by lia. rewrite andb_true_r. reflexivity.
Qed.
Lemma full_ok' : forall x, 0 <= x < 2 ^ 64 -> kb_ok (full x) x.
Proof. intros x Hx. rewrite <- (Z.mod_small x (2 ^ 64)) at 2 by lia. apply full_ok. Qed.

(* [comment removed for export] *)
Ltac tb_destr :=
  repeat match goal with |- context [Z.testbit ?z ?i] => destruct (Z.testbit z i) end.
Ltac tb_fin :=
  intros; cbn in *; try reflexivity; try discriminate;
  repeat match goal with H : ?a = ?a -> _ |- _ => specialize (H eq_refl) end;
  try congruence; try (exfalso; congruence).

Lemma kb_or_sound : forall a b x y, kb_ok a x -> kb_ok b y -> kb_ok (kb_or a b) (Z.lor x y).
Proof.
  intros a b x y Ha Hb i Hi Hm. cbn [kb_or km kv] in Hm |- *. unfold k1, k0 in *.
  pose proof (Ha i Hi) as HA. pose proof (Hb i Hi) as HB. revert HA HB Hm.
  rewrite !Z.lor_spec, !Z.land_spec, !Z.ldiff_spec. tb_destr; tb_fin.
Qed.

Lemma kb_and_sound : forall a b x y, kb_ok a x -> kb_ok b y -> kb_ok (kb_and a b) (Z.land x y).
Proof.
  intros a b x y Ha Hb i Hi Hm. cbn [kb_and km kv] in Hm |- *. unfold k1, k0 in *.
  pose proof (Ha i Hi) as HA. pose proof (Hb i Hi) as HB. revert HA HB Hm.
  rewrite !Z.lor_spec, !Z.land_spec, !Z.ldiff_spec. tb_destr; tb_fin.
Qed.

Lemma kb_xor_sound : forall a b x y, kb_ok a x -> kb_ok b y -> kb_ok (kb_xor a b) (Z.lxor x y).
Proof.
  intros a b x y Ha Hb i Hi Hm. cbn [kb_xor km kv] in Hm |- *.
  pose proof (Ha i Hi) as HA. pose proof (Hb i Hi) as HB. revert HA HB Hm.
  rewrite !Z.land_spec, !Z.lxor_spec. tb_destr; tb_fin.
Qed.

Lemma kb_srl_sound : forall a x s, 0 <= s < 64 -> 0 <= x < 2 ^ 64 -> kb_ok a x -> kb_ok (kb_srl a s) (Z.shiftr x s).
Proof.
  intros a x s Hs Hx Ha i Hi Hm. cbn [kb_srl km kv] in Hm |- *.
  rewrite !Z.shiftr_spec by lia. rewrite Z.land_spec, M64_bit by lia.
  rewrite Z.lor_spec, Z.shiftr_spec, Z.ldiff_spec, M64_bit, ones_bit in Hm by lia.
  destruct (Z.ltb_spec (i + s) 64) as [Hlt|Hge].
  - rewrite andb_true_r. apply Ha; [lia|].
    destruct (Z.testbit (km a) (i + s)); [reflexivity|]. exfalso.
    rewrite (proj2 (Z.ltb_lt i 64)) in Hm by lia. rewrite (proj2 (Z.ltb_lt i (64 - s))) in Hm by lia. discriminate.
  - rewrite andb_false_r. apply bit_high; lia.
Qed.

Lemma kb_sll_sound : forall a x s, 0 <= s < 64 -> kb_ok a x -> kb_ok (kb_sll a s) ((Z.shiftl x s) mod 2 ^ 64).
Proof.
  intros a x s Hs Ha i Hi Hm. cbn [kb_sll km kv] in Hm |- *.
  rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.lor_spec, ones_bit in Hm by lia.
  destruct (Z.ltb_spec i s) as [Hlt|Hge].
  - rewrite !Z.shiftl_spec_low by lia. reflexivity.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftl_spec_high in Hm by lia. rewrite orb_false_r in Hm.
    apply Ha; [lia | exact Hm].
Qed.

Lemma kb_ext_sound : forall a x lo n, 0 <= x < 2 ^ 64 -> kb_ok a x ->
  kb_ok (kb_ext lo n a) (((x / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ (8 * Z.of_nat n)) mod 2 ^ 64).
Proof.
  intros a x lo n Hx Ha i Hi Hm. cbn [kb_ext km kv] in Hm |- *.
  set (l := 8 * Z.of_nat lo) in *. set (w := 8 * Z.of_nat n) in *.
  assert (Hl : 0 <= l) by lia. assert (Hw : 0 <= w) by lia.
  rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.lor_spec, Z.shiftr_spec, Z.ldiff_spec, M64_bit, ones_bit in Hm by lia.
  rewrite !Z.land_spec, ones_bit, Z.shiftr_spec, Z.land_spec, M64_bit by lia.
  destruct (Z.ltb_spec i w) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite <- Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_spec by lia.
    rewrite andb_true_r. rewrite (proj2 (Z.ltb_lt i 64)) in Hm by lia. cbn [negb andb] in Hm. rewrite orb_false_r in Hm.
    destruct (Z.ltb_spec (i + l) 64) as [Hlt2|Hge2].
    + rewrite andb_true_r. apply Ha; [lia | exact Hm].
    + rewrite andb_false_r. apply bit_high; lia.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite andb_false_r. reflexivity.
Qed.

Lemma kb_range_sound : forall lo hi b x, kb_range lo hi = Some b -> lo <= x <= hi -> kb_ok b x.
Proof.
  intros lo hi b x H Hx. unfold kb_range in H.
  destruct (Z.leb 0 lo && Z.leb lo hi && Z.ltb hi two64)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. unfold two64 in H3.
  set (p := prefix_len lo hi) in H.
  destruct (Z.leb 0 p && Z.leb p 64 && Z.eqb (Z.shiftr lo p) (Z.shiftr hi p))%bool eqn:Hd; [|discriminate].
  apply andb_prop in Hd as [Hd H6]. apply andb_prop in Hd as [H4 H5].
  apply Z.leb_le in H4. apply Z.leb_le in H5. apply Z.eqb_eq in H6.
  apply some_inj in H. subst b. intros i Hi Hm. cbn [km kv] in Hm |- *.
  rewrite Z.ldiff_spec, M64_bit, ones_bit in Hm by lia.
  destruct (Z.ltb_spec i p) as [Hlt|Hge]; [rewrite (proj2 (Z.ltb_lt i 64)) in Hm by lia; discriminate|].
  rewrite Z.land_spec, Z.ldiff_spec, M64_bit, ones_bit by lia.
  rewrite (proj2 (Z.ltb_lt i 64)) by lia. rewrite (proj2 (Z.ltb_ge i p)) by lia. cbn [negb andb]. rewrite andb_true_r.
  assert (X : Z.shiftr x p = Z.shiftr lo p).
  { rewrite !Z.shiftr_div_pow2 in H6 |- * by lia.
    assert (0 < 2 ^ p) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.div_le_mono lo x (2 ^ p) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono x hi (2 ^ p) ltac:(lia) ltac:(lia)). lia. }
  replace i with ((i - p) + p) by lia. rewrite <- !Z.shiftr_spec by lia. rewrite X. reflexivity.
Qed.

(* [comment removed for export] *)
Section Sound.
Variable segs : list Segment.
Variable E : env.
Variable M : word -> option byte.
Variable k : list kentry.
Hypothesis HK : know_ok segs E M k.

#[local] Notation U e := (bv_unsigned (edenot E e)).

Lemma U_range : forall e, 0 <= U e < 2 ^ 64.
Proof. intros e. exact (u64_range (edenot E e)). Qed.

Lemma leaf_sound : forall e b, leaf k e = Some b -> kb_ok b (U e).
Proof.
  intros e b H. unfold leaf in H.
  destruct (xlo k e) as [lo|] eqn:Hl; [|discriminate]. destruct (xhi k e) as [hi|] eqn:Hh; [|discriminate].
  eapply kb_range_sound; [exact H|].
  split; [exact (xlo_sound segs E M k e lo HK Hl) | exact (xhi_sound segs E M k e hi HK Hh)].
Qed.

Lemma orelse_sound : forall r e b, (forall b', r = Some b' -> kb_ok b' (U e)) -> orelse r (leaf k e) = Some b -> kb_ok b (U e).
Proof.
  intros r e b Hr H. unfold orelse in H. destruct r as [b'|]; [injection H as <-; apply Hr; reflexivity | apply leaf_sound; exact H].
Qed.

(* [comment removed for export] *)
Lemma full_edenot : forall a ka, kb_ok ka (U a) -> is_full ka = true -> edenot E a = Z_to_bv 64 (lit ka).
Proof.
  intros a ka Hk Hf. apply bv_eq. rewrite (Z_to_bv_small 64 (lit ka)) by (pose proof (lit_range ka); change (bv_modulus 64) with (2 ^ 64); lia).
  exact (full_lit ka (U a) Hk Hf (U_range a)).
Qed.

Lemma kb_alu_sound : forall op a b ka kb r,
  kb_ok ka (U a) -> kb_ok kb (U b) -> kb_alu op ka kb = Some r -> kb_ok r (U (EAlu op a b)).
Proof.
  intros op a b ka kb r Ha Hb H. unfold kb_alu in H.
  destruct (is_full ka && is_full kb)%bool eqn:Hf.
  - apply andb_prop in Hf as [Fa Fb]. apply some_inj in H; subst.
    cbn [edenot]. rewrite (full_edenot a ka Ha Fa), (full_edenot b kb Hb Fb). unfold zalu. apply full_ok'. apply u64_range.
  - assert (SH : is_full kb = true -> bv_unsigned (bv_and (edenot E b) (Z_to_bv 64 63)) = shamt kb).
    { intros Fb. rewrite bv_and_unsigned, (full_edenot b kb Hb Fb).
      rewrite !Z_to_bv_small by (pose proof (lit_range kb); change (bv_modulus 64) with (2 ^ 64); lia).
      unfold shamt. reflexivity. }
    destruct op; try discriminate H.
    + (* [comment removed for export] *) destruct (is_full kb) eqn:Fb; [|discriminate]. apply some_inj in H; subst.
      cbn [edenot alu64 alu]. rewrite bv_shiftl_unsigned, (SH eq_refl). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      apply kb_sll_sound; [apply shamt_range | exact Ha].
    + (* [comment removed for export] *) apply some_inj in H; subst. cbn [edenot alu64 alu]. rewrite bv_xor_unsigned. apply kb_xor_sound; assumption.
    + (* [comment removed for export] *) destruct (is_full kb) eqn:Fb; [|discriminate]. apply some_inj in H; subst.
      cbn [edenot alu64 alu]. rewrite bv_shiftr_unsigned, (SH eq_refl).
      apply kb_srl_sound; [apply shamt_range | apply U_range | exact Ha].
    + (* [comment removed for export] *) apply some_inj in H; subst. cbn [edenot alu64 alu]. rewrite bv_or_unsigned. apply kb_or_sound; assumption.
    + (* [comment removed for export] *) apply some_inj in H; subst. cbn [edenot alu64 alu]. rewrite bv_and_unsigned. apply kb_and_sound; assumption.
Qed.

Lemma kb_extop_sound : forall sx lo n a ka r,
  kb_ok ka (U a) -> kb_extop sx lo n ka = Some r -> kb_ok r (U (EExt sx lo n a)).
Proof.
  intros sx lo n a ka r Ha H. unfold kb_extop in H.
  destruct (is_full ka) eqn:Fa.
  - apply some_inj in H; subst. cbn [edenot]. rewrite (full_edenot a ka Ha Fa). unfold zext_lit. apply full_ok'. apply u64_range.
  - destruct sx; [discriminate|]. apply some_inj in H; subst. cbn [edenot]. unfold ext_val, ext_Z.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    apply kb_ext_sound; [apply U_range | exact Ha].
Qed.

Theorem kb_eval_sound : forall fuel e b, kb_eval fuel k e = Some b -> kb_ok b (U e).
Proof.
  induction fuel as [|f IH]; intros e b H; [discriminate|]. cbn [kb_eval] in H.
  destruct e as [z | v | op a c | op a c | op a c | op a c | sx lo n a | sx kk i n].
  - apply some_inj in H; subst. cbn [edenot]. rewrite u_lit64a. apply full_ok.
  - apply leaf_sound. exact H.
  - eapply orelse_sound; [|exact H]. intros b' Hr.
    destruct (kb_eval f k a) as [ka|] eqn:Ea; [|discriminate]. destruct (kb_eval f k c) as [kb|] eqn:Ec; [|discriminate].
    exact (kb_alu_sound op a c ka kb b' (IH a ka Ea) (IH c kb Ec) Hr).
  - eapply orelse_sound; [|exact H]. intros b' Hr.
    destruct (kb_eval f k a) as [ka|] eqn:Ea; [|discriminate]. destruct (kb_eval f k c) as [kb|] eqn:Ec; [|discriminate].
    destruct (is_full ka && is_full kb)%bool eqn:Hf; [|discriminate]. apply andb_prop in Hf as [Fa Fb]. apply some_inj in Hr; subst.
    cbn [edenot]. rewrite (full_edenot a ka (IH a ka Ea) Fa), (full_edenot c kb (IH c kb Ec) Fb). unfold zaluw. apply full_ok'. apply u64_range.
  - eapply orelse_sound; [|exact H]. intros b' Hr.
    destruct (kb_eval f k a) as [ka|] eqn:Ea; [|discriminate]. destruct (kb_eval f k c) as [kb|] eqn:Ec; [|discriminate].
    destruct (is_full ka && is_full kb)%bool eqn:Hf; [|discriminate]. apply andb_prop in Hf as [Fa Fb]. apply some_inj in Hr; subst.
    cbn [edenot]. rewrite (full_edenot a ka (IH a ka Ea) Fa), (full_edenot c kb (IH c kb Ec) Fb). unfold zmd. apply full_ok'. apply u64_range.
  - eapply orelse_sound; [|exact H]. intros b' Hr.
    destruct (kb_eval f k a) as [ka|] eqn:Ea; [|discriminate]. destruct (kb_eval f k c) as [kb|] eqn:Ec; [|discriminate].
    destruct (is_full ka && is_full kb)%bool eqn:Hf; [|discriminate]. apply andb_prop in Hf as [Fa Fb]. apply some_inj in Hr; subst.
    cbn [edenot]. rewrite (full_edenot a ka (IH a ka Ea) Fa), (full_edenot c kb (IH c kb Ec) Fb). unfold zmdw. apply full_ok'. apply u64_range.
  - eapply orelse_sound; [|exact H]. intros b' Hr.
    destruct (kb_eval f k a) as [ka|] eqn:Ea; [|discriminate].
    exact (kb_extop_sound sx lo n a ka b' (IH a ka Ea) Hr).
  - apply leaf_sound. exact H.
Qed.

(* [comment removed for export] *)
Theorem kb_lit_eq_sound : forall a e, kb_lit_eq k a e = true -> edenot E a = edenot E e.
Proof.
  intros a e H. unfold kb_lit_eq in H. destruct e as [v | | | | | | |]; try discriminate.
  destruct (kb_eval KB_FUEL k a) as [b|] eqn:He; [|discriminate].
  apply andb_prop in H as [Hf Hv]. apply Z.eqb_eq in Hv.
  rewrite (full_edenot a b (kb_eval_sound KB_FUEL a b He) Hf), Hv. cbn [edenot].
  apply bv_eq. rewrite !Z_to_bv_unsigned, zlit64_eq. unfold bv_wrap, two64. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity.
Qed.
End Sound.
End KBS.
