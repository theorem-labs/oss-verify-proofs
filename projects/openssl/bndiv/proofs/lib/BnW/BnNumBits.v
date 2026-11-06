(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnArith.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition nbw_m (l : Z) : Z :=
  let s5 := (Z.shiftl (Z.b2z (0 <? Z.shiftr l 32)) 5) mod M64 in
  let acc1 := Z.lor s5 (Z.b2z (0 <? l)) in
  let l1 := Z.shiftr l (s5 mod 64) in
  let s4 := (Z.shiftl (Z.b2z (0 <? Z.shiftr l1 16)) 4) mod M64 in
  let acc2 := Z.lor acc1 s4 in
  let l2 := Z.shiftr l1 (s4 mod 64) in
  let s3 := (Z.shiftl (Z.lxor (Z.b2z (l2 <? 256)) 1) 3) mod M64 in
  let acc3 := Z.lor acc2 s3 in
  let l3 := Z.shiftr l2 (s3 mod 64) in
  let s2 := (Z.shiftl (Z.lxor (Z.b2z (l3 <? 16)) 1) 2) mod M64 in
  let acc4 := Z.lor acc3 s2 in
  let l4 := Z.shiftr l3 (s2 mod 64) in
  let s1 := (Z.shiftl (Z.lxor (Z.b2z (l4 <? 4)) 1) 1) mod M64 in
  let acc5 := Z.lor acc4 s1 in
  let l5 := Z.shiftr l4 (s1 mod 64) in
  acc5 + Z.lxor (Z.b2z (l5 <? 2)) 1.

(* [comment removed for export] *)
Definition sel (k l : Z) : Z := if 2 ^ k <=? l then k else 0.

Lemma stage_hi : forall k j l, 0 <= l -> 0 < k < 64 -> 0 <= j < 6 -> k = 2 ^ j ->
  (Z.shiftl (Z.b2z (0 <? Z.shiftr l k)) j) mod M64 = sel k l.
Proof.
  intros k j l Hl Hk Hj E. unfold sel. rewrite Z.shiftr_div_pow2 by lia.
  assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.leb_spec (2 ^ k) l) as [H|H].
  - assert (0 < l / 2 ^ k) by (apply Z.div_str_pos; lia).
    replace (0 <? l / 2 ^ k) with true by (symmetry; apply Z.ltb_lt; assumption).
    cbn [Z.b2z]. rewrite Z.shiftl_mul_pow2 by lia. rewrite <- E, Z.mul_1_l. apply Z.mod_small. lia.
  - rewrite Z.div_small by lia. cbn [Z.ltb Z.compare Z.b2z]. rewrite Z.shiftl_0_l. reflexivity.
Qed.

Lemma stage_lo : forall k j l b, b = 2 ^ k -> 0 <= j < 6 -> k = 2 ^ j -> 0 < k < 64 ->
  (Z.shiftl (Z.lxor (Z.b2z (l <? b)) 1) j) mod M64 = sel k l.
Proof.
  intros k j l b -> Hj E Hk. unfold sel.
  destruct (Z.leb_spec (2 ^ k) l) as [H|H].
  - replace (l <? 2 ^ k) with false by (symmetry; apply Z.ltb_ge; assumption).
    cbn [Z.b2z Z.lxor]. change (Z.lxor 0 1) with 1. rewrite Z.shiftl_mul_pow2 by lia. rewrite <- E, Z.mul_1_l. apply Z.mod_small. lia.
  - replace (l <? 2 ^ k) with true by (symmetry; apply Z.ltb_lt; assumption). cbn [Z.b2z]. change (Z.lxor 1 1) with 0. rewrite Z.shiftl_0_l. reflexivity.
Qed.

Lemma sel_cases : forall k l, sel k l = 0 \/ sel k l = k.
Proof. intros. unfold sel. destruct (2 ^ k <=? l); auto. Qed.

(* [comment removed for export] *)
Lemma stage_log : forall k l, 0 < k -> 0 <= l < 2 ^ (2 * k) ->
  let l' := Z.shiftr l (sel k l) in
  0 <= l' < 2 ^ k /\ (0 < l -> 0 < l' /\ Z.log2 l = sel k l + Z.log2 l') /\ (l = 0 -> l' = 0).
Proof.
  intros k l Hk Hl. unfold sel.
  assert (P : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (E2 : 2 ^ (2 * k) = 2 ^ k * 2 ^ k) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  destruct (Z.leb_spec (2 ^ k) l) as [H|H]; cbv zeta.
  - rewrite Z.shiftr_div_pow2 by lia.
    assert (0 < l / 2 ^ k) by (apply Z.div_str_pos; lia).
    split; [split; [lia|]|split].
    + apply Z.div_lt_upper_bound; lia.
    + intros _. split; [assumption|].
      rewrite <- Z.shiftr_div_pow2 by lia. rewrite Z.log2_shiftr by lia.
      assert (k <= Z.log2 l) by (apply Z.log2_le_pow2; lia). lia.
    + intros ->. lia.
  - rewrite Z.shiftr_0_r. split; [lia|]. split; [intros; split; lia | tauto].
Qed.

Lemma shift_mod64 : forall k l, 0 < k < 64 -> Z.shiftr l (sel k l mod 64) = Z.shiftr l (sel k l).
Proof. intros k l Hk. destruct (sel_cases k l) as [E|E]; rewrite E; [reflexivity|]. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma nbw_m_correct : forall l, 0 <= l < M64 -> nbw_m l = num_bits_word l.
Proof.
  intros l Hl. unfold nbw_m.
  rewrite (stage_hi 32 5 l) by (try reflexivity; lia).
  rewrite (shift_mod64 32 l) by lia.
  pose proof (stage_log 32 l ltac:(lia) ltac:(change (2 ^ (2 * 32)) with M64; lia)) as S5. cbv zeta in S5.
  set (l1 := Z.shiftr l (sel 32 l)) in *. destruct S5 as (R1 & P1 & Z1).
  rewrite (stage_hi 16 4 l1) by (try reflexivity; lia).
  rewrite (shift_mod64 16 l1) by lia.
  pose proof (stage_log 16 l1 ltac:(lia) ltac:(change (2 ^ (2 * 16)) with (2 ^ 32); lia)) as S4. cbv zeta in S4.
  set (l2 := Z.shiftr l1 (sel 16 l1)) in *. destruct S4 as (R2 & P2 & Z2).
  rewrite (stage_lo 8 3 l2 256) by (try reflexivity; lia).
  rewrite (shift_mod64 8 l2) by lia.
  pose proof (stage_log 8 l2 ltac:(lia) ltac:(change (2 ^ (2 * 8)) with (2 ^ 16); lia)) as S3. cbv zeta in S3.
  set (l3 := Z.shiftr l2 (sel 8 l2)) in *. destruct S3 as (R3 & P3 & Z3).
  rewrite (stage_lo 4 2 l3 16) by (try reflexivity; lia).
  rewrite (shift_mod64 4 l3) by lia.
  pose proof (stage_log 4 l3 ltac:(lia) ltac:(change (2 ^ (2 * 4)) with (2 ^ 8); lia)) as S2. cbv zeta in S2.
  set (l4 := Z.shiftr l3 (sel 4 l3)) in *. destruct S2 as (R4 & P4 & Z4).
  rewrite (stage_lo 2 1 l4 4) by (try reflexivity; lia).
  rewrite (shift_mod64 2 l4) by lia.
  pose proof (stage_log 2 l4 ltac:(lia) ltac:(change (2 ^ (2 * 2)) with (2 ^ 4); lia)) as S1. cbv zeta in S1.
  set (l5 := Z.shiftr l4 (sel 2 l4)) in *. destruct S1 as (R5 & P5 & Z5).
  (* [comment removed for export] *)
  assert (E0 : Z.lxor (Z.b2z (l5 <? 2)) 1 = sel 1 l5).
  { unfold sel. change (2 ^ 1) with 2. destruct (Z.leb_spec 2 l5); destruct (Z.ltb_spec l5 2); try lia; reflexivity. }
  rewrite E0.
  pose proof (stage_log 1 l5 ltac:(lia) ltac:(change (2 ^ (2 * 1)) with (2 ^ 2); lia)) as S0. cbv zeta in S0.
  set (l6 := Z.shiftr l5 (sel 1 l5)) in *. destruct S0 as (R6 & P6 & Z6).
  (* [comment removed for export] *)
  assert (EO : Z.lor (Z.lor (Z.lor (Z.lor (Z.lor (sel 32 l) (Z.b2z (0 <? l))) (sel 16 l1)) (sel 8 l2)) (sel 4 l3)) (sel 2 l4)
               = sel 32 l + Z.b2z (0 <? l) + sel 16 l1 + sel 8 l2 + sel 4 l3 + sel 2 l4).
  { destruct (sel_cases 32 l) as [->| ->], (sel_cases 16 l1) as [->| ->], (sel_cases 8 l2) as [->| ->],
             (sel_cases 4 l3) as [->| ->], (sel_cases 2 l4) as [->| ->]; destruct (0 <? l); reflexivity. }
  rewrite EO. clear EO E0.
  unfold num_bits_word. destruct (Z.eqb_spec l 0) as [->|NZ].
  - cbn. reflexivity.
  - assert (L0 : 0 < l) by lia.
    replace (0 <? l) with true by (symmetry; apply Z.ltb_lt; assumption). cbn [Z.b2z].
    destruct (P1 L0) as (L1 & E1). destruct (P2 L1) as (L2 & E2). destruct (P3 L2) as (L3 & E3).
    destruct (P4 L3) as (L4 & E4). destruct (P5 L4) as (L5 & E5). destruct (P6 L5) as (L6 & E6).
    assert (l6 = 1) by (change (2 ^ 1) with 2 in R6; lia).
    rewrite E1, E2, E3, E4, E5, E6, H. change (Z.log2 1) with 0. lia.
Qed.

Lemma num_bits_word_range : forall l, 0 <= l < M64 -> 0 <= num_bits_word l <= 64.
Proof.
  intros l Hl. unfold num_bits_word. destruct (Z.eqb_spec l 0); [lia|].
  assert (Z.log2 l < 64) by (apply Z.log2_lt_pow2; [lia | change (2 ^ 64) with M64; lia]).
  pose proof (Z.log2_nonneg l). lia.
Qed.
