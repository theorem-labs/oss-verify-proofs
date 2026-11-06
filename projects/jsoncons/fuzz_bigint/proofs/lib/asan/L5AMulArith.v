(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import BigLinkBase.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigFactsBase BigFactsDigits.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5AMA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A10 (X : Z) : Z := (42949672960 * (X / 4294967296)) mod 2 ^ 64.
Definition B10 (X : Z) : Z := (10 * (((4294967296 * X) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64.
Definition LO (X : Z) : Z := (A10 X + B10 X) mod 2 ^ 64.
Definition LIMB (X c : Z) : Z := (c + LO X) mod 2 ^ 64.
Definition CAR (X c : Z) : Z :=
  ((if LIMB X c <? LO X then 1 else 0) + (((if LO X <? A10 X then 1 else 0) + ((10 * (X / 4294967296)) mod 2 ^ 64 / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64.

Lemma lo32_identity X : 0 <= X < 2 ^ 64 -> LO X = (10 * X) mod 2 ^ 64.
Proof.
  (* [comment removed for export] *)
  unfold LO, A10, B10. change (2 ^ 64) with 18446744073709551616. intros HX.
  pose proof (Z.div_mod X 4294967296 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound X 4294967296 ltac:(lia)) as BX.
  set (Xh := X / 4294967296) in *. set (Xl := X mod 4294967296) in *. clearbody Xh Xl.
  assert (E1: (4294967296 * X) mod 18446744073709551616 = 4294967296 * Xl).
  { symmetry. apply Z.mod_unique with Xh; lia. }
  rewrite E1. rewrite (Z.mul_comm 4294967296 Xl), Z.div_mul by lia.
  rewrite <- Zplus_mod. f_equal. lia.
Qed.
Lemma limb_val X c : 0 <= X < 2 ^ 64 -> 0 <= c <= 9 -> LIMB X c = (10 * X + c) mod 2 ^ 64.
Proof. intros HX Hc. unfold LIMB. rewrite lo32_identity by exact HX. rewrite Z.add_comm, Zplus_mod_idemp_l. reflexivity. Qed.
Lemma car_val X C : 0 <= X < 2 ^ 64 -> 0 <= C <= 9 -> CAR X C = (10 * X + C) / 2 ^ 64.
Proof.
  intros HX HC. unfold CAR, LIMB, LO.
  pose proof (lo32_identity X HX) as ELO. unfold LO in ELO.
  set (A := A10 X) in *. set (B := B10 X) in *.
  assert (HA : 0 <= A < 2 ^ 64) by (subst A; unfold A10; apply Z.mod_pos_bound; lia).
  assert (HB : 0 <= B < 2 ^ 64) by (subst B; unfold B10; apply Z.mod_pos_bound; lia).
  pose proof (BL.carry_ltu_l A B) as C2. unfold BL.inrange, BL.MM, BL.zb in C2. rewrite C2 by lia.
  rewrite ELO. set (lo := (10 * X) mod 2 ^ 64) in *.
  assert (HLO : 0 <= lo < 2 ^ 64) by (subst lo; apply Z.mod_pos_bound; lia).
  pose proof (BL.carry_ltu_r C lo) as C1. unfold BL.inrange, BL.MM, BL.zb in C1. rewrite C1 by lia.
  (* [comment removed for export] *)
  pose proof (Z.div_mod X 4294967296 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound X 4294967296 ltac:(lia)) as BX.
  subst A B. unfold A10, B10 in *.
  set (Xh := X / 4294967296) in *. set (Xl := X mod 4294967296) in *.
  assert (HXh: 0 <= Xh < 4294967296) by (subst Xh; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  clearbody Xh Xl.
  assert (E1: (4294967296 * X) mod 2 ^ 64 = 4294967296 * Xl). { symmetry. apply Z.mod_unique with Xh; lia. }
  rewrite E1 in *. rewrite (Z.mul_comm 4294967296 Xl), Z.div_mul in * by lia.
  rewrite (Z.mod_small (10 * Xl)) in * by lia.
  rewrite (Z.mod_small (10 * Xh)) in * by lia.
  pose proof (Z.div_mod (10 * Xh) 4294967296 ltac:(lia)) as DA. pose proof (Z.mod_pos_bound (10 * Xh) 4294967296 ltac:(lia)) as BA.
  set (a := 10 * Xh / 4294967296) in *. set (b := (10 * Xh) mod 4294967296) in *. clearbody a b.
  assert (E4: (42949672960 * Xh) mod 2 ^ 64 = 4294967296 * b). { symmetry. apply Z.mod_unique with a; lia. }
  rewrite E4 in *.
  assert (E5: 10 * X = 2 ^ 64 * a + (4294967296 * b + 10 * Xl)) by lia.
  set (s := 4294967296 * b + 10 * Xl) in *. assert (Hs : 0 <= s < 2 * 2 ^ 64) by (subst s; lia).
  assert (Elo: lo = s mod 2 ^ 64). { subst lo. rewrite E5. rewrite Z.add_comm, (Z.mul_comm (2 ^ 64) a), Z_mod_plus_full. reflexivity. }
  rewrite E5. replace (2 ^ 64 * a + s + C) with ((s + C) + a * 2 ^ 64) by lia. rewrite Z_div_plus_full by lia.
  clearbody s.
  pose proof (Z.div_mod s (2 ^ 64) ltac:(lia)) as DS. pose proof (Z.mod_pos_bound s (2 ^ 64) ltac:(lia)) as BS.
  rewrite Elo in *. set (q := s / 2 ^ 64) in *. set (r := s mod 2 ^ 64) in *. clearbody q r.
  assert (Hq : 0 <= q <= 1) by lia. assert (Ha : 0 <= a <= 9) by lia.
  assert (Hcr : 0 <= (C + r) / 2 ^ 64 < 2). { split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. }
  rewrite (Z.mod_small (q + a)) by lia. rewrite Z.mod_small by lia.
  rewrite DS. replace (2 ^ 64 * q + r + C) with ((C + r) + q * 2 ^ 64) by lia. rewrite Z_div_plus_full by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma limb_valE X c : 0 <= X < 2 ^ 64 -> 0 <= c <= 9 ->
  ((c + ((((42949672960 * (X / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * X) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
  = (10 * X + c) mod 2 ^ 64.
Proof. intros HX Hc. exact (limb_val X c HX Hc). Qed.
Lemma car_valE X c : 0 <= X < 2 ^ 64 -> 0 <= c <= 9 ->
  (((if ((c + ((((42949672960 * (X / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * X) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) <? ((((42949672960 * (X / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * X) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((if ((((42949672960 * (X / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * X) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64) <? ((42949672960 * (X / 4294967296)) mod 2 ^ 64) then 1 else 0) + (((10 * (X / 4294967296)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)
  = (10 * X + c) / 2 ^ 64.
Proof. intros HX Hc. exact (car_val X c HX Hc). Qed.

(* [comment removed for export] *)
Definition M64 : Z := 2 ^ 64.
Lemma wordi_eq v i : BigFactsDigits.wordi v i = (v / M64 ^ Z.of_nat i) mod M64.
Proof. unfold BigFactsDigits.wordi. rewrite BigFactsBase.M_val. reflexivity. Qed.
Lemma mcarry_eq y v i : BigFactsDigits.mcarry y v i = (y * (v mod M64 ^ Z.of_nat i)) / M64 ^ Z.of_nat i.
Proof. unfold BigFactsDigits.mcarry. rewrite BigFactsBase.M_val. reflexivity. Qed.
Lemma Mpow_pos i : 0 < M64 ^ Z.of_nat i. Proof. apply Z.pow_pos_nonneg; unfold M64; lia. Qed.

Lemma mul_step v i : 0 <= v ->
  let x := BigFactsDigits.wordi v i in let c := BigFactsDigits.mcarry 10 v i in
  (10 * x + c) mod M64 = BigFactsDigits.wordi (10 * v) i /\ (10 * x + c) / M64 = BigFactsDigits.mcarry 10 v (Datatypes.S i).
Proof.
  intros Hv. cbn zeta. rewrite !wordi_eq, !mcarry_eq.
  set (P := M64 ^ Z.of_nat i). pose proof (Mpow_pos i) as PP. fold P in PP.
  assert (PS : M64 ^ Z.of_nat (Datatypes.S i) = P * M64). { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. subst P. apply Z.mul_comm. }
  rewrite PS.
  pose proof (Z.div_mod v P ltac:(lia)) as DV. pose proof (Z.mod_pos_bound v P PP) as BV.
  set (vh := v / P) in *. set (vl := v mod P) in *.
  assert (Hvh : 0 <= vh) by (subst vh; apply Z.div_pos; lia). clearbody vh vl.
  assert (E1 : 10 * v / P = 10 * vh + 10 * vl / P). { rewrite DV. replace (10 * (P * vh + vl)) with (vh * 10 * P + 10 * vl) by lia. rewrite Z_div_plus_full_l by lia. lia. }
  pose proof (Z.div_mod vh M64 ltac:(unfold M64; lia)) as DH. pose proof (Z.mod_pos_bound vh M64 ltac:(unfold M64; lia)) as BH.
  set (x := vh mod M64) in *. set (vhh := vh / M64) in *. clearbody x vhh.
  set (c := 10 * vl / P) in *. assert (Hc : 0 <= c < 10). { subst c. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. } assert (Ec : c = 10 * vl / P) by reflexivity. clearbody c.
  split.
  - rewrite E1, DH. replace (10 * (M64 * vhh + x) + c) with ((10 * x + c) + (10 * vhh) * M64) by lia. rewrite Z_mod_plus_full. reflexivity.
  - (* [comment removed for export] *)
    assert (E2 : v mod (P * M64) = P * x + vl).
    { symmetry. apply Z.mod_unique with vhh. left. unfold M64 in *; nia. rewrite DV, DH. lia. }
    rewrite E2. rewrite <- Z.div_div by (unfold M64 in *; lia).
    replace (10 * (P * x + vl)) with (x * 10 * P + 10 * vl) by lia. rewrite Z_div_plus_full_l by lia. f_equal. rewrite <- Ec. lia.
Qed.

End L5AMA.
