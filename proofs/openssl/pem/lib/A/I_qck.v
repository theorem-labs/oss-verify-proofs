(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Walk.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s I_consts D_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac showall := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x21 := getreg 21%Z in let x22 := getreg 22%Z in let x23 := getreg 23%Z in let x24 := getreg 24%Z in let x25 := getreg 25%Z in let x26 := getreg 26%Z in let x27 := getreg 27%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in let x30 := getreg 30%Z in let x31 := getreg 31%Z in let x2 := getreg 2%Z in let x1 := getreg 1%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "s5=" x21; idtac "s6=" x22; idtac "s7=" x23; idtac "s8=" x24; idtac "s9=" x25; idtac "s10=" x26; idtac "s11=" x27; idtac "t3=" x28; idtac "t4=" x29; idtac "t5=" x30; idtac "t6=" x31; idtac "sp=" x2; idtac "ra=" x1.

(* [comment removed for export] *)
Definition keep (P : Prop) : Prop := P.

(* [comment removed for export] *)
Definition al8 (a : Z) : Z := 8 * (a / 8).

(* [comment removed for export] *)
Definition qc_words (m : mem) (p n : Z) : Prop :=
  1 <= n <= 64 -> exists w1 w2 : word, ro_cells asegs m (al8 (shad p)) [C8 w1] /\ ro_cells asegs m (al8 (shad (p + n - 1))) [C8 w2].

(* [comment removed for export] *)
Definition rng_ok (p n : Z) : Prop := 0 < n -> region_in_mem p n /\ n <= 2^40.

(* [comment removed for export] *)
Definition chk_ok (m : mem) (p n : Z) : Prop := acc asegs m p n /\ qc_words m p n /\ rng_ok p n.

Lemma land_m8' : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = 8 * (x / 8).
Proof.
  intros x Hx. change 18446744073709551608 with (Z.ldiff (Z.ones 64) (Z.ones 3)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^3) with 8. lia.
Qed.

(* [comment removed for export] *)
Lemma sub65_small : forall n, 1 <= n <= 64 ->
  bv_leu (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 n) + -65)) (Z_to_bv 64 (-65)) = false.
Proof.
  intros n Hn. unfold bv_leu. rewrite (unsigned_lit n) by lia. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  apply Z.leb_gt. rewrite !Z.mod_eq by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma sub65_large : forall n, (n = 0 \/ 64 < n) -> n < 2^63 ->
  bv_leu (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 n) + -65)) (Z_to_bv 64 (-65)) = true.
Proof.
  intros n Hn Hn'. unfold bv_leu. rewrite (unsigned_lit n) by lia. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  apply Z.leb_le. rewrite !Z.mod_eq by lia. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma not_overflow : forall p n, 0 <= p -> 0 <= n -> p + n < 2^64 ->
  bv_ltu (bv_not (Z_to_bv 64 p)) (Z_to_bv 64 n) = false.
Proof.
  intros p n H0 H1 H2. unfold bv_ltu. apply Z.ltb_ge.
  rewrite bv_not_unsigned. rewrite !unsigned_lit by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite Z.lnot_eq_pred_opp. rewrite Z.mod_eq by lia. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma lxor_ones64 : forall s, 0 <= s < 2^64 -> Z.lxor s 18446744073709551615 = 18446744073709551615 - s.
Proof.
  intros s Hs. change 18446744073709551615 with (Z.ones 64).
  assert (H : Z.land s (Z.lxor s (Z.ones 64)) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z.ltb_spec i 64) as [L|L].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit s i); reflexivity.
    - rewrite Z.ones_spec_high by lia. replace (Z.testbit s i) with false; [reflexivity|].
      symmetry. apply Z.bits_above_log2; [lia|]. destruct (Z.eq_dec s 0) as [->|NZ]; [cbn; lia|].
      apply Z.log2_lt_pow2; [lia|]. eapply Z.lt_le_trans; [exact (proj2 Hs)| apply Z.pow_le_mono_r; lia]. }
  pose proof (Z.add_nocarry_lxor s (Z.lxor s (Z.ones 64)) H) as E.
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in E. rewrite Z.ones_equiv in E |- *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma acc_shadow_bytes : forall m p n, acc asegs m p n -> 1 <= n -> 0 <= p ->
  forall x, shad p <= x <= shad (p + n - 1) -> exists b, bytes_at asegs m x [b].
Proof.
  intros m p n AC Hn Hp x Hx. unfold shad in Hx.
  set (i := Z.max 0 (8 * (x - SHB) - p)).
  assert (Hi : 0 <= i < n) by (unfold i; Z.div_mod_to_equations; lia).
  destruct (AC i Hi) as (b & Hb & _). exists b.
  replace x with (shad (p + i)); [exact Hb|]. unfold shad, i. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma ro_C1_of_bytes : forall m x b, bytes_at asegs m x [b] -> ro_cells asegs m x [C1 b].
Proof. intros m x b H. split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. exact H. Qed.

Lemma chk_ok_sub : forall m p n, chk_ok m p n -> acc asegs m p n.
Proof. intros m p n [H _]. exact H. Qed.

(* [comment removed for export] *)
Lemma chk_ok_agree : forall m m' p n, chk_ok m p n -> 0 <= p -> p + n <= 2^47 ->
  agree_on (fun x => 0x7fff8000 <= x < 0x10007fff8007) m m' -> chk_ok m' p n.
Proof.
  intros m m' p n (AC & QW & RO) H0 H1 AG. split; [| split; [| exact RO]].
  - intros i Hi. destruct (AC i Hi) as (b & Hb & Ok). exists b. split; [| exact Ok].
    apply (bytes_at_agree asegs m m' _ _ Hb). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [length] in Hx.
    unfold shad, SHB in Hx. Z.div_mod_to_equations. lia.
  - intros Hn. destruct (QW Hn) as (w1 & w2 & W1 & W2). exists w1, w2. split.
    + apply (ro_cells_agree asegs m m' _ _ W1). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [cells_size csize] in Hx.
      unfold al8, shad, SHB in Hx. Z.div_mod_to_equations. lia.
    + apply (ro_cells_agree asegs m m' _ _ W2). apply (agree_sub _ _ _ _ AG). intros x Hx. cbn [cells_size csize] in Hx.
      unfold al8, shad, SHB in Hx. Z.div_mod_to_equations. lia.
Qed.
