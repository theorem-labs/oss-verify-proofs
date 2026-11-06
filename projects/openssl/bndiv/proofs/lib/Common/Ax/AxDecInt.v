(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mkbv (n : N) (z : Z) : bv n :=
  match decide (BvWf n z) with
  | left H => @BV n z H
  | right _ => Z_to_bv n z
  end.

Lemma mkbv_unsigned (n : N) (z : Z) : 0 <= z < bv_modulus n -> bv_unsigned (mkbv n z) = z.
Proof.
  intros Hz. unfold mkbv. destruct (decide (BvWf n z)) as [H|H]; [reflexivity|].
  exfalso. apply H. apply bv_wf_in_range. exact Hz.
Qed.

Lemma mkbv_eq (n : N) (z : Z) (b : bv n) : bv_unsigned b = z -> mkbv n z = b.
Proof.
  intros <-. apply bv_eq. apply mkbv_unsigned. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fld (x p m : int) : int := ((x / p) mod m)%uint63.

Lemma fld_spec (w : bv 32) (x : int) (lo len : N) (p m : int) :
  to_Z x = bv_unsigned w -> to_Z p = 2 ^ Z.of_N lo -> to_Z m = 2 ^ Z.of_N len ->
  to_Z (fld x p m) = bv_unsigned (bits lo len w).
Proof.
  intros Hx Hp Hm. unfold fld, bits. rewrite bv_extract_unsigned. unfold bv_wrap, bv_modulus.
  rewrite mod_spec, div_spec, Hx, Hp, Hm. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma fld_lt (x p m : int) : 0 < to_Z m -> 0 <= to_Z (fld x p m) < to_Z m.
Proof. intros Hm. unfold fld. rewrite mod_spec. apply Z.mod_pos_bound. exact Hm. Qed.

(* [comment removed for export] *)
Definition R0 : reg := @BV 5 0 I.
Definition R1 : reg := @BV 5 1 I.
Definition R2 : reg := @BV 5 2 I.
Definition R3 : reg := @BV 5 3 I.
Definition R4 : reg := @BV 5 4 I.
Definition R5 : reg := @BV 5 5 I.
Definition R6 : reg := @BV 5 6 I.
Definition R7 : reg := @BV 5 7 I.
Definition R8 : reg := @BV 5 8 I.
Definition R9 : reg := @BV 5 9 I.
Definition R10 : reg := @BV 5 10 I.
Definition R11 : reg := @BV 5 11 I.
Definition R12 : reg := @BV 5 12 I.
Definition R13 : reg := @BV 5 13 I.
Definition R14 : reg := @BV 5 14 I.
Definition R15 : reg := @BV 5 15 I.
Definition R16 : reg := @BV 5 16 I.
Definition R17 : reg := @BV 5 17 I.
Definition R18 : reg := @BV 5 18 I.
Definition R19 : reg := @BV 5 19 I.
Definition R20 : reg := @BV 5 20 I.
Definition R21 : reg := @BV 5 21 I.
Definition R22 : reg := @BV 5 22 I.
Definition R23 : reg := @BV 5 23 I.
Definition R24 : reg := @BV 5 24 I.
Definition R25 : reg := @BV 5 25 I.
Definition R26 : reg := @BV 5 26 I.
Definition R27 : reg := @BV 5 27 I.
Definition R28 : reg := @BV 5 28 I.
Definition R29 : reg := @BV 5 29 I.
Definition R30 : reg := @BV 5 30 I.
Definition R31 : reg := @BV 5 31 I.

Definition reg_of_int (r : int) : reg :=
  if (r <=? 15)%uint63 then
    if (r <=? 7)%uint63 then
      if (r <=? 3)%uint63 then
        if (r <=? 1)%uint63 then
          if (r <=? 0)%uint63 then
            R0
          else
            R1
        else
          if (r <=? 2)%uint63 then
            R2
          else
            R3
      else
        if (r <=? 5)%uint63 then
          if (r <=? 4)%uint63 then
            R4
          else
            R5
        else
          if (r <=? 6)%uint63 then
            R6
          else
            R7
    else
      if (r <=? 11)%uint63 then
        if (r <=? 9)%uint63 then
          if (r <=? 8)%uint63 then
            R8
          else
            R9
        else
          if (r <=? 10)%uint63 then
            R10
          else
            R11
      else
        if (r <=? 13)%uint63 then
          if (r <=? 12)%uint63 then
            R12
          else
            R13
        else
          if (r <=? 14)%uint63 then
            R14
          else
            R15
  else
    if (r <=? 23)%uint63 then
      if (r <=? 19)%uint63 then
        if (r <=? 17)%uint63 then
          if (r <=? 16)%uint63 then
            R16
          else
            R17
        else
          if (r <=? 18)%uint63 then
            R18
          else
            R19
      else
        if (r <=? 21)%uint63 then
          if (r <=? 20)%uint63 then
            R20
          else
            R21
        else
          if (r <=? 22)%uint63 then
            R22
          else
            R23
    else
      if (r <=? 27)%uint63 then
        if (r <=? 25)%uint63 then
          if (r <=? 24)%uint63 then
            R24
          else
            R25
        else
          if (r <=? 26)%uint63 then
            R26
          else
            R27
      else
        if (r <=? 29)%uint63 then
          if (r <=? 28)%uint63 then
            R28
          else
            R29
        else
          if (r <=? 30)%uint63 then
            R30
          else
            R31.

Lemma reg_of_int_spec (r : int) : to_Z r < 32 -> bv_unsigned (reg_of_int r) = to_Z r.
Proof.
  intros Hr. pose proof (to_Z_bounded r) as Hb.
  assert (Hall : forallb (fun k => bv_unsigned (reg_of_int (of_Z (Z.of_nat k))) =? Z.of_nat k) (seq 0 32) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall (Z.to_nat (to_Z r)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in Hall by lia. rewrite of_to_Z in Hall. apply Z.eqb_eq in Hall. exact Hall.
Qed.

(* [comment removed for export] *)
Lemma reg_fld (w : bv 32) (x : int) (lo : N) (p : int) :
  to_Z x = bv_unsigned w -> to_Z p = 2 ^ Z.of_N lo -> reg_of_int (fld x p 32) = bits lo 5 w.
Proof.
  intros Hx Hp. apply bv_eq. rewrite reg_of_int_spec by (pose proof (fld_lt x p 32 ltac:(reflexivity)) as H; change (to_Z 32) with 32 in H; lia).
  apply (fld_spec w x lo 5 p 32 Hx Hp). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma imm_fld (w : bv 32) (x : int) (lo len : N) (p m : int) :
  to_Z x = bv_unsigned w -> to_Z p = 2 ^ Z.of_N lo -> to_Z m = 2 ^ Z.of_N len ->
  mkbv len (to_Z (fld x p m)) = bits lo len w.
Proof. intros Hx Hp Hm. apply mkbv_eq. symmetry. exact (fld_spec w x lo len p m Hx Hp Hm). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition x_of (w : bv 32) : int := of_Z (bv_unsigned w).

Lemma x_of_spec (w : bv 32) : to_Z (x_of w) = bv_unsigned w.
Proof.
  unfold x_of. rewrite of_Z_spec. apply Z.mod_small. pose proof (bv_unsigned_in_range 32 w) as H.
  change (bv_modulus 32) with 4294967296 in H. change wB with 9223372036854775808. lia.
Qed.

Lemma fld_eqb (w : bv 32) (x : int) (lo len : N) (p m c : int) :
  to_Z x = bv_unsigned w -> to_Z p = 2 ^ Z.of_N lo -> to_Z m = 2 ^ Z.of_N len ->
  (fld x p m =? c)%uint63 = true -> bv_unsigned (bits lo len w) = to_Z c.
Proof.
  intros Hx Hp Hm H. apply Uint63.eqb_spec in H. rewrite <- (fld_spec w x lo len p m Hx Hp Hm), H. reflexivity.
Qed.

(* [comment removed for export] *)
Definition ximm_s (x : int) : int := (fld x 33554432 128 * 32 + fld x 128 32)%uint63.
Definition ximm_b (x : int) : int := (fld x 2147483648 2 * 4096 + fld x 128 2 * 2048 + fld x 33554432 64 * 32 + fld x 256 16 * 2)%uint63.
Definition ximm_j (x : int) : int := (fld x 2147483648 2 * 1048576 + fld x 4096 256 * 4096 + fld x 1048576 2 * 2048 + fld x 2097152 1024 * 2)%uint63.

Lemma lor_lo_hi (a b k : Z) : 0 <= a < 2 ^ k -> 0 <= b -> 0 <= k -> Z.lor (b ≪ k) a = b * 2 ^ k + a.
Proof.
  intros Ha Hb Hk. rewrite Z.shiftl_mul_pow2 by lia.
  assert (Hl : Z.land (b * 2 ^ k) a = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n k) as [L|G].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - destruct (Z.eq_dec a 0) as [->|Hnz]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 a n); [apply andb_false_r | lia |].
      apply Z.lt_le_trans with k; [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite <- Z.lxor_lor by exact Hl. rewrite <- Z.add_nocarry_lxor by exact Hl. reflexivity.
Qed.

Lemma poly2 (a b ka : int) : to_Z a * to_Z ka + to_Z b < wB -> to_Z (a * ka + b)%uint63 = to_Z a * to_Z ka + to_Z b.
Proof.
  intros H. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). pose proof (to_Z_bounded ka).
  assert (0 <= to_Z a * to_Z ka) by (apply Z.mul_nonneg_nonneg; lia). set (P1 := to_Z a * to_Z ka) in *.
  assert (E1 : to_Z (a * ka) = P1) by (rewrite mul_spec; apply Z.mod_small; lia).
  rewrite add_spec, E1. apply Z.mod_small. lia.
Qed.

Lemma poly4 (a b c d ka kb kc kd : int) :
  to_Z a * to_Z ka + to_Z b * to_Z kb + to_Z c * to_Z kc + to_Z d * to_Z kd < wB ->
  to_Z (a * ka + b * kb + c * kc + d * kd)%uint63 = to_Z a * to_Z ka + to_Z b * to_Z kb + to_Z c * to_Z kc + to_Z d * to_Z kd.
Proof.
  intros H. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). pose proof (to_Z_bounded c). pose proof (to_Z_bounded d).
  pose proof (to_Z_bounded ka). pose proof (to_Z_bounded kb). pose proof (to_Z_bounded kc). pose proof (to_Z_bounded kd).
  assert (0 <= to_Z a * to_Z ka) by (apply Z.mul_nonneg_nonneg; lia). assert (0 <= to_Z b * to_Z kb) by (apply Z.mul_nonneg_nonneg; lia).
  assert (0 <= to_Z c * to_Z kc) by (apply Z.mul_nonneg_nonneg; lia). assert (0 <= to_Z d * to_Z kd) by (apply Z.mul_nonneg_nonneg; lia).
  set (P1 := to_Z a * to_Z ka) in *. set (P2 := to_Z b * to_Z kb) in *. set (P3 := to_Z c * to_Z kc) in *. set (P4 := to_Z d * to_Z kd) in *.
  assert (E1 : to_Z (a * ka) = P1) by (rewrite mul_spec; apply Z.mod_small; lia).
  assert (E2 : to_Z (b * kb) = P2) by (rewrite mul_spec; apply Z.mod_small; lia).
  assert (E3 : to_Z (c * kc) = P3) by (rewrite mul_spec; apply Z.mod_small; lia).
  assert (E4 : to_Z (d * kd) = P4) by (rewrite mul_spec; apply Z.mod_small; lia).
  assert (E12 : to_Z (a * ka + b * kb) = P1 + P2) by (rewrite add_spec, E1, E2; apply Z.mod_small; lia).
  assert (E123 : to_Z (a * ka + b * kb + c * kc) = P1 + P2 + P3) by (rewrite add_spec, E12, E3; apply Z.mod_small; lia).
  rewrite add_spec, E123, E4. apply Z.mod_small. lia.
Qed.

Lemma imm_s_fld (w : bv 32) (x : int) : to_Z x = bv_unsigned w -> mkbv 12 (to_Z (ximm_s x)) = imm_s w.
Proof.
  intros Hx. apply mkbv_eq. unfold imm_s, ximm_s. rewrite (bv_concat_unsigned 12 5) by reflexivity.
  rewrite <- (fld_spec w x 25 7 33554432 128 Hx eq_refl eq_refl), <- (fld_spec w x 7 5 128 32 Hx eq_refl eq_refl).
  pose proof (fld_lt x 33554432 128 ltac:(reflexivity)) as B1. pose proof (fld_lt x 128 32 ltac:(reflexivity)) as B2.
  change (to_Z 128) with 128 in *. change (to_Z 32) with 32 in *.
  set (a := to_Z (fld x 33554432 128)) in *. set (b := to_Z (fld x 128 32)) in *.
  rewrite poly2 by (change (to_Z 32) with 32; change wB with 9223372036854775808; fold a b; lia).
  change (to_Z 32) with 32. fold a b. change (Z.of_N 5) with 5.
  rewrite (lor_lo_hi b a 5) by (change (2 ^ 5) with 32; lia). change (2 ^ 5) with 32. reflexivity.
Qed.

Lemma imm_b_fld (w : bv 32) (x : int) : to_Z x = bv_unsigned w -> mkbv 13 (to_Z (ximm_b x)) = imm_b w.
Proof.
  intros Hx. apply mkbv_eq. unfold imm_b, ximm_b.
  rewrite (bv_concat_unsigned 13 12) by reflexivity. rewrite (bv_concat_unsigned 12 11) by reflexivity.
  rewrite (bv_concat_unsigned 11 5) by reflexivity. rewrite (bv_concat_unsigned 5 1) by reflexivity.
  rewrite <- (fld_spec w x 31 1 2147483648 2 Hx eq_refl eq_refl), <- (fld_spec w x 7 1 128 2 Hx eq_refl eq_refl),
          <- (fld_spec w x 25 6 33554432 64 Hx eq_refl eq_refl), <- (fld_spec w x 8 4 256 16 Hx eq_refl eq_refl).
  pose proof (fld_lt x 2147483648 2 ltac:(reflexivity)) as B1. pose proof (fld_lt x 128 2 ltac:(reflexivity)) as B2.
  pose proof (fld_lt x 33554432 64 ltac:(reflexivity)) as B3. pose proof (fld_lt x 256 16 ltac:(reflexivity)) as B4.
  change (to_Z 2) with 2 in *. change (to_Z 64) with 64 in *. change (to_Z 16) with 16 in *.
  set (a := to_Z (fld x 2147483648 2)) in *. set (b := to_Z (fld x 128 2)) in *. set (c := to_Z (fld x 33554432 64)) in *. set (d := to_Z (fld x 256 16)) in *.
  rewrite poly4 by (change (to_Z 4096) with 4096; change (to_Z 2048) with 2048; change (to_Z 32) with 32; change (to_Z 2) with 2; change wB with 9223372036854775808; fold a b c d; lia).
  change (to_Z 4096) with 4096. change (to_Z 2048) with 2048. change (to_Z 32) with 32. change (to_Z 2) with 2. fold a b c d.
  change (bv_unsigned (0 : bv 1)) with 0.
  change (Z.of_N 1) with 1. change (Z.of_N 5) with 5. change (Z.of_N 11) with 11. change (Z.of_N 12) with 12.
  rewrite (lor_lo_hi 0 d 1) by lia. change (2 ^ 1) with 2.
  rewrite (lor_lo_hi (d * 2 + 0) c 5) by (change (2 ^ 5) with 32; lia). change (2 ^ 5) with 32.
  rewrite (lor_lo_hi (c * 32 + (d * 2 + 0)) b 11) by (change (2 ^ 11) with 2048; lia). change (2 ^ 11) with 2048.
  rewrite (lor_lo_hi (b * 2048 + (c * 32 + (d * 2 + 0))) a 12) by (change (2 ^ 12) with 4096; lia). change (2 ^ 12) with 4096.
  lia.
Qed.

Lemma imm_j_fld (w : bv 32) (x : int) : to_Z x = bv_unsigned w -> mkbv 21 (to_Z (ximm_j x)) = imm_j w.
Proof.
  intros Hx. apply mkbv_eq. unfold imm_j, ximm_j.
  rewrite (bv_concat_unsigned 21 20) by reflexivity. rewrite (bv_concat_unsigned 20 12) by reflexivity.
  rewrite (bv_concat_unsigned 12 11) by reflexivity. rewrite (bv_concat_unsigned 11 1) by reflexivity.
  rewrite <- (fld_spec w x 31 1 2147483648 2 Hx eq_refl eq_refl), <- (fld_spec w x 12 8 4096 256 Hx eq_refl eq_refl),
          <- (fld_spec w x 20 1 1048576 2 Hx eq_refl eq_refl), <- (fld_spec w x 21 10 2097152 1024 Hx eq_refl eq_refl).
  pose proof (fld_lt x 2147483648 2 ltac:(reflexivity)) as B1. pose proof (fld_lt x 4096 256 ltac:(reflexivity)) as B2.
  pose proof (fld_lt x 1048576 2 ltac:(reflexivity)) as B3. pose proof (fld_lt x 2097152 1024 ltac:(reflexivity)) as B4.
  change (to_Z 2) with 2 in *. change (to_Z 256) with 256 in *. change (to_Z 1024) with 1024 in *.
  set (a := to_Z (fld x 2147483648 2)) in *. set (b := to_Z (fld x 4096 256)) in *. set (c := to_Z (fld x 1048576 2)) in *. set (d := to_Z (fld x 2097152 1024)) in *.
  rewrite poly4 by (change (to_Z 1048576) with 1048576; change (to_Z 4096) with 4096; change (to_Z 2048) with 2048; change (to_Z 2) with 2; change wB with 9223372036854775808; fold a b c d; lia).
  change (to_Z 1048576) with 1048576. change (to_Z 4096) with 4096. change (to_Z 2048) with 2048. change (to_Z 2) with 2. fold a b c d.
  change (bv_unsigned (0 : bv 1)) with 0.
  change (Z.of_N 1) with 1. change (Z.of_N 11) with 11. change (Z.of_N 12) with 12. change (Z.of_N 20) with 20.
  rewrite (lor_lo_hi 0 d 1) by lia. change (2 ^ 1) with 2.
  rewrite (lor_lo_hi (d * 2 + 0) c 11) by (change (2 ^ 11) with 2048; lia). change (2 ^ 11) with 2048.
  rewrite (lor_lo_hi (c * 2048 + (d * 2 + 0)) b 12) by (change (2 ^ 12) with 4096; lia). change (2 ^ 12) with 4096.
  rewrite (lor_lo_hi (b * 4096 + (c * 2048 + (d * 2 + 0))) a 20) by (change (2 ^ 20) with 1048576; lia). change (2 ^ 20) with 1048576.
  lia.
Qed.

(* [comment removed for export] *)
Definition fdec_opimm (x : int) (rd rs1 : reg) : option instr :=
  let f3 := fld x 4096 8 in
  if (f3 =? 0)%uint63 then Some (OpImm ALU_ADD rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else if (f3 =? 7)%uint63 then Some (OpImm ALU_AND rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else if (f3 =? 1)%uint63 then (if (fld x 67108864 64 =? 0)%uint63 then Some (ShiftImm ALU_SLL rd rs1 (mkbv 6 (to_Z (fld x 1048576 64)))) else None)
  else if (f3 =? 5)%uint63 then (if (fld x 67108864 64 =? 0)%uint63 then Some (ShiftImm ALU_SRL rd rs1 (mkbv 6 (to_Z (fld x 1048576 64)))) else if (fld x 67108864 64 =? 16)%uint63 then Some (ShiftImm ALU_SRA rd rs1 (mkbv 6 (to_Z (fld x 1048576 64)))) else None)
  else if (f3 =? 6)%uint63 then Some (OpImm ALU_OR rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else if (f3 =? 4)%uint63 then Some (OpImm ALU_XOR rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else if (f3 =? 3)%uint63 then Some (OpImm ALU_SLTU rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else if (f3 =? 2)%uint63 then Some (OpImm ALU_SLT rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else None.

(* [comment removed for export] *)
Definition fdec_load (x : int) (rd rs1 : reg) : option instr :=
  let f3 := fld x 4096 8 in
  if (f3 =? 3)%uint63 then Some (Load SZ8 true rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else if (f3 =? 2)%uint63 then Some (Load SZ4 true rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else if (f3 =? 4)%uint63 then Some (Load SZ1 false rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else if (f3 =? 0)%uint63 then Some (Load SZ1 true rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else if (f3 =? 1)%uint63 then Some (Load SZ2 true rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else if (f3 =? 5)%uint63 then Some (Load SZ2 false rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else if (f3 =? 6)%uint63 then Some (Load SZ4 false rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else None.

(* [comment removed for export] *)
Definition fdec_store (x : int) (rs1 rs2 : reg) : option instr :=
  let f3 := fld x 4096 8 in
  if (f3 =? 3)%uint63 then Some (Store SZ8 rs1 rs2 (mkbv 12 (to_Z (ximm_s x))))
  else if (f3 =? 2)%uint63 then Some (Store SZ4 rs1 rs2 (mkbv 12 (to_Z (ximm_s x))))
  else if (f3 =? 0)%uint63 then Some (Store SZ1 rs1 rs2 (mkbv 12 (to_Z (ximm_s x))))
  else if (f3 =? 1)%uint63 then Some (Store SZ2 rs1 rs2 (mkbv 12 (to_Z (ximm_s x))))
  else None.

(* [comment removed for export] *)
Definition fdec_branch (x : int) (rs1 rs2 : reg) : option instr :=
  let f3 := fld x 4096 8 in
  if (f3 =? 0)%uint63 then Some (Branch BC_EQ rs1 rs2 (mkbv 13 (to_Z (ximm_b x))))
  else if (f3 =? 1)%uint63 then Some (Branch BC_NE rs1 rs2 (mkbv 13 (to_Z (ximm_b x))))
  else if (f3 =? 4)%uint63 then Some (Branch BC_LT rs1 rs2 (mkbv 13 (to_Z (ximm_b x))))
  else if (f3 =? 5)%uint63 then Some (Branch BC_GE rs1 rs2 (mkbv 13 (to_Z (ximm_b x))))
  else if (f3 =? 6)%uint63 then Some (Branch BC_LTU rs1 rs2 (mkbv 13 (to_Z (ximm_b x))))
  else if (f3 =? 7)%uint63 then Some (Branch BC_GEU rs1 rs2 (mkbv 13 (to_Z (ximm_b x))))
  else None.

(* [comment removed for export] *)
Definition fdec_op (x : int) (rd rs1 rs2 : reg) : option instr :=
  let f3 := fld x 4096 8 in
  let f7 := fld x 33554432 128 in
  if (f7 =? 0)%uint63 then (
    if (f3 =? 0)%uint63 then Some (Op ALU_ADD rd rs1 rs2)
    else if (f3 =? 1)%uint63 then Some (Op ALU_SLL rd rs1 rs2)
    else if (f3 =? 2)%uint63 then Some (Op ALU_SLT rd rs1 rs2)
    else if (f3 =? 3)%uint63 then Some (Op ALU_SLTU rd rs1 rs2)
    else if (f3 =? 4)%uint63 then Some (Op ALU_XOR rd rs1 rs2)
    else if (f3 =? 5)%uint63 then Some (Op ALU_SRL rd rs1 rs2)
    else if (f3 =? 6)%uint63 then Some (Op ALU_OR rd rs1 rs2)
    else if (f3 =? 7)%uint63 then Some (Op ALU_AND rd rs1 rs2)
    else None)
  else if (f7 =? 32)%uint63 then (
    if (f3 =? 0)%uint63 then Some (Op ALU_SUB rd rs1 rs2)
    else if (f3 =? 5)%uint63 then Some (Op ALU_SRA rd rs1 rs2)
    else None)
  else if (f7 =? 1)%uint63 then (
    if (f3 =? 0)%uint63 then Some (Mul M_MUL rd rs1 rs2)
    else if (f3 =? 1)%uint63 then Some (Mul M_MULH rd rs1 rs2)
    else if (f3 =? 2)%uint63 then Some (Mul M_MULHSU rd rs1 rs2)
    else if (f3 =? 3)%uint63 then Some (Mul M_MULHU rd rs1 rs2)
    else if (f3 =? 4)%uint63 then Some (Mul M_DIV rd rs1 rs2)
    else if (f3 =? 5)%uint63 then Some (Mul M_DIVU rd rs1 rs2)
    else if (f3 =? 6)%uint63 then Some (Mul M_REM rd rs1 rs2)
    else if (f3 =? 7)%uint63 then Some (Mul M_REMU rd rs1 rs2)
    else None)
  else None.

(* [comment removed for export] *)
Definition fdec_op32 (x : int) (rd rs1 rs2 : reg) : option instr :=
  let f3 := fld x 4096 8 in
  let f7 := fld x 33554432 128 in
  if (f7 =? 0)%uint63 then (
    if (f3 =? 0)%uint63 then Some (Op32 ALU_ADD rd rs1 rs2)
    else if (f3 =? 1)%uint63 then Some (Op32 ALU_SLL rd rs1 rs2)
    else if (f3 =? 5)%uint63 then Some (Op32 ALU_SRL rd rs1 rs2)
    else None)
  else if (f7 =? 32)%uint63 then (
    if (f3 =? 0)%uint63 then Some (Op32 ALU_SUB rd rs1 rs2)
    else if (f3 =? 5)%uint63 then Some (Op32 ALU_SRA rd rs1 rs2)
    else None)
  else if (f7 =? 1)%uint63 then (
    if (f3 =? 0)%uint63 then Some (Mul32 M_MUL rd rs1 rs2)
    else if (f3 =? 4)%uint63 then Some (Mul32 M_DIV rd rs1 rs2)
    else if (f3 =? 5)%uint63 then Some (Mul32 M_DIVU rd rs1 rs2)
    else if (f3 =? 6)%uint63 then Some (Mul32 M_REM rd rs1 rs2)
    else if (f3 =? 7)%uint63 then Some (Mul32 M_REMU rd rs1 rs2)
    else None)
  else None.

(* [comment removed for export] *)
Definition fdec_opimm32 (x : int) (rd rs1 : reg) : option instr :=
  let f3 := fld x 4096 8 in
  let f7 := fld x 33554432 128 in
  if (f3 =? 0)%uint63 then Some (OpImm32 rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096))))
  else if (f3 =? 1)%uint63 then (if (f7 =? 0)%uint63 then Some (ShiftImm32 ALU_SLL rd rs1 (mkbv 5 (to_Z (fld x 1048576 32)))) else None)
  else if (f3 =? 5)%uint63 then (if (f7 =? 0)%uint63 then Some (ShiftImm32 ALU_SRL rd rs1 (mkbv 5 (to_Z (fld x 1048576 32)))) else if (f7 =? 32)%uint63 then Some (ShiftImm32 ALU_SRA rd rs1 (mkbv 5 (to_Z (fld x 1048576 32)))) else None)
  else None.

(* [comment removed for export] *)
Definition fdec_jalr (x : int) (rd rs1 : reg) : option instr :=
  if (fld x 4096 8 =? 0)%uint63 then Some (Jalr rd rs1 (mkbv 12 (to_Z (fld x 1048576 4096)))) else None.

(* [comment removed for export] *)
Definition fdec_lui (x : int) (rd : reg) : option instr :=
  Some (Lui rd (mkbv 20 (to_Z (fld x 4096 1048576)))).

(* [comment removed for export] *)
Definition fdec_auipc (x : int) (rd : reg) : option instr :=
  Some (Auipc rd (mkbv 20 (to_Z (fld x 4096 1048576)))).

(* [comment removed for export] *)
Definition fdec_jal (x : int) (rd : reg) : option instr :=
  Some (Jal rd (mkbv 21 (to_Z (ximm_j x)))).

Definition fdec (w : bv 32) : option instr :=
  let x := x_of w in
  if (fld x 1 4 =? 3)%uint63 then
    let opc := fld x 1 128 in
    if (opc =? 19)%uint63 then fdec_opimm x (reg_of_int (fld x 128 32)) (reg_of_int (fld x 32768 32))
    else if (opc =? 3)%uint63 then fdec_load x (reg_of_int (fld x 128 32)) (reg_of_int (fld x 32768 32))
    else if (opc =? 35)%uint63 then fdec_store x (reg_of_int (fld x 32768 32)) (reg_of_int (fld x 1048576 32))
    else if (opc =? 99)%uint63 then fdec_branch x (reg_of_int (fld x 32768 32)) (reg_of_int (fld x 1048576 32))
    else if (opc =? 51)%uint63 then fdec_op x (reg_of_int (fld x 128 32)) (reg_of_int (fld x 32768 32)) (reg_of_int (fld x 1048576 32))
    else if (opc =? 59)%uint63 then fdec_op32 x (reg_of_int (fld x 128 32)) (reg_of_int (fld x 32768 32)) (reg_of_int (fld x 1048576 32))
    else if (opc =? 27)%uint63 then fdec_opimm32 x (reg_of_int (fld x 128 32)) (reg_of_int (fld x 32768 32))
    else if (opc =? 103)%uint63 then fdec_jalr x (reg_of_int (fld x 128 32)) (reg_of_int (fld x 32768 32))
    else if (opc =? 55)%uint63 then fdec_lui x (reg_of_int (fld x 128 32))
    else if (opc =? 23)%uint63 then fdec_auipc x (reg_of_int (fld x 128 32))
    else if (opc =? 111)%uint63 then fdec_jal x (reg_of_int (fld x 128 32))
    else None
  else None.

(* [comment removed for export] *)
Ltac fld_hyps w x Hx :=
  repeat match goal with
  | H : (fld x ?p ?m =? ?c)%uint63 = true |- _ =>
      let lo := eval vm_compute in (Z.to_N (Z.log2 (to_Z p))) in
      let len := eval vm_compute in (Z.to_N (Z.log2 (to_Z m))) in
      let c' := eval vm_compute in (to_Z c) in
      let H' := fresh "E" in
      pose proof (fld_eqb w x lo len p m c Hx eq_refl eq_refl H) as H'; change (to_Z c) with c' in H'; clear H
  | H : (fld x ?p ?m =? ?c)%uint63 = false |- _ => clear H
  end.

Ltac fld_fields w x Hx :=
  unfold f_rd, f_rs1, f_rs2, imm_i, imm_u;
  rewrite ?(imm_s_fld w x Hx), ?(imm_b_fld w x Hx), ?(imm_j_fld w x Hx);
  repeat match goal with
  | |- context [reg_of_int (fld x ?p 32)] =>
      let lo := eval vm_compute in (Z.to_N (Z.log2 (to_Z p))) in
      rewrite (reg_fld w x lo p Hx eq_refl)
  | |- context [mkbv ?len (to_Z (fld x ?p ?m))] =>
      let lo := eval vm_compute in (Z.to_N (Z.log2 (to_Z p))) in
      rewrite (imm_fld w x lo len p m Hx eq_refl eq_refl)
  end.

(* [comment removed for export] *)
Ltac leaf_sound w x Hx :=
  (let Hi := fresh "Hi" in intros Hi; injection Hi as <-);
  fld_hyps w x Hx;
  unfold decode_any; match goal with E2 : bv_unsigned (bits 0 2 _) = 3 |- _ => rewrite E2; clear E2 end;
  (destruct (decide (3 = 3)) as [_|N]; [|exfalso; apply N; reflexivity]);
  unfold decode; cbv beta zeta;
  repeat match goal with E' : bv_unsigned (bits _ _ _) = _ |- _ => rewrite E'; clear E' end;
  cbv beta iota;
  try (destruct (decide (0 = 0)) as [_|N]; [|exfalso; apply N; reflexivity]);
  fld_fields w x Hx; reflexivity.

(* [comment removed for export] *)
Ltac group_sound w x Hx :=
  cbv zeta;
  repeat match goal with
  | |- context [if (fld x ?p ?m =? ?c)%uint63 then _ else _] => destruct (fld x p m =? c)%uint63 eqn:?
  end; first [discriminate | leaf_sound w x Hx].

Section Sound.
Variable w : bv 32.
Let x : int := x_of w.
Hypothesis H2 : (fld x 1 4 =? 3)%uint63 = true.
Lemma fdec_opimm_sound (i : instr) : (fld x 1 128 =? 19)%uint63 = true -> fdec_opimm x (reg_of_int (fld x 128 32)) (reg_of_int (fld x 32768 32)) = Some i -> decode_any w = Some (i, 4).
Proof. intros Hopc. pose proof (x_of_spec w) as Hx. fold x in Hx. unfold fdec_opimm. group_sound w x Hx. Qed.

Lemma fdec_load_sound (i : instr) : (fld x 1 128 =? 3)%uint63 = true -> fdec_load x (reg_of_int (fld x 128 32)) (reg_of_int (fld x 32768 32)) = Some i -> decode_any w = Some (i, 4).
Proof. intros Hopc. pose proof (x_of_spec w) as Hx. fold x in Hx. unfold fdec_load. group_sound w x Hx. Qed.

Lemma fdec_store_sound (i : instr) : (fld x 1 128 =? 35)%uint63 = true -> fdec_store x (reg_of_int (fld x 32768 32)) (reg_of_int (fld x 1048576 32)) = Some i -> decode_any w = Some (i, 4).
Proof. intros Hopc. pose proof (x_of_spec w) as Hx. fold x in Hx. unfold fdec_store. group_sound w x Hx. Qed.

Lemma fdec_branch_sound (i : instr) : (fld x 1 128 =? 99)%uint63 = true -> fdec_branch x (reg_of_int (fld x 32768 32)) (reg_of_int (fld x 1048576 32)) = Some i -> decode_any w = Some (i, 4).
Proof. intros Hopc. pose proof (x_of_spec w) as Hx. fold x in Hx. unfold fdec_branch. group_sound w x Hx. Qed.

Lemma fdec_op_sound (i : instr) : (fld x 1 128 =? 51)%uint63 = true -> fdec_op x (reg_of_int (fld x 128 32)) (reg_of_int (fld x 32768 32)) (reg_of_int (fld x 1048576 32)) = Some i -> decode_any w = Some (i, 4).
Proof. intros Hopc. pose proof (x_of_spec w) as Hx. fold x in Hx. unfold fdec_op. group_sound w x Hx. Qed.

Lemma fdec_op32_sound (i : instr) : (fld x 1 128 =? 59)%uint63 = true -> fdec_op32 x (reg_of_int (fld x 128 32)) (reg_of_int (fld x 32768 32)) (reg_of_int (fld x 1048576 32)) = Some i -> decode_any w = Some (i, 4).
Proof. intros Hopc. pose proof (x_of_spec w) as Hx. fold x in Hx. unfold fdec_op32. group_sound w x Hx. Qed.

Lemma fdec_opimm32_sound (i : instr) : (fld x 1 128 =? 27)%uint63 = true -> fdec_opimm32 x (reg_of_int (fld x 128 32)) (reg_of_int (fld x 32768 32)) = Some i -> decode_any w = Some (i, 4).
Proof. intros Hopc. pose proof (x_of_spec w) as Hx. fold x in Hx. unfold fdec_opimm32. group_sound w x Hx. Qed.

Lemma fdec_jalr_sound (i : instr) : (fld x 1 128 =? 103)%uint63 = true -> fdec_jalr x (reg_of_int (fld x 128 32)) (reg_of_int (fld x 32768 32)) = Some i -> decode_any w = Some (i, 4).
Proof. intros Hopc. pose proof (x_of_spec w) as Hx. fold x in Hx. unfold fdec_jalr. group_sound w x Hx. Qed.

Lemma fdec_lui_sound (i : instr) : (fld x 1 128 =? 55)%uint63 = true -> fdec_lui x (reg_of_int (fld x 128 32)) = Some i -> decode_any w = Some (i, 4).
Proof. intros Hopc. pose proof (x_of_spec w) as Hx. fold x in Hx. unfold fdec_lui. group_sound w x Hx. Qed.

Lemma fdec_auipc_sound (i : instr) : (fld x 1 128 =? 23)%uint63 = true -> fdec_auipc x (reg_of_int (fld x 128 32)) = Some i -> decode_any w = Some (i, 4).
Proof. intros Hopc. pose proof (x_of_spec w) as Hx. fold x in Hx. unfold fdec_auipc. group_sound w x Hx. Qed.

Lemma fdec_jal_sound (i : instr) : (fld x 1 128 =? 111)%uint63 = true -> fdec_jal x (reg_of_int (fld x 128 32)) = Some i -> decode_any w = Some (i, 4).
Proof. intros Hopc. pose proof (x_of_spec w) as Hx. fold x in Hx. unfold fdec_jal. group_sound w x Hx. Qed.

End Sound.

Theorem fdec_sound (w : bv 32) (i : instr) : fdec w = Some i -> decode_any w = Some (i, 4).
Proof.
  unfold fdec. cbv zeta. destruct (fld (x_of w) 1 4 =? 3)%uint63 eqn:H2; [|discriminate].
  destruct (fld (x_of w) 1 128 =? 19)%uint63 eqn:E19; [exact (fdec_opimm_sound w H2 i E19)|].
  destruct (fld (x_of w) 1 128 =? 3)%uint63 eqn:E3; [exact (fdec_load_sound w H2 i E3)|].
  destruct (fld (x_of w) 1 128 =? 35)%uint63 eqn:E35; [exact (fdec_store_sound w H2 i E35)|].
  destruct (fld (x_of w) 1 128 =? 99)%uint63 eqn:E99; [exact (fdec_branch_sound w H2 i E99)|].
  destruct (fld (x_of w) 1 128 =? 51)%uint63 eqn:E51; [exact (fdec_op_sound w H2 i E51)|].
  destruct (fld (x_of w) 1 128 =? 59)%uint63 eqn:E59; [exact (fdec_op32_sound w H2 i E59)|].
  destruct (fld (x_of w) 1 128 =? 27)%uint63 eqn:E27; [exact (fdec_opimm32_sound w H2 i E27)|].
  destruct (fld (x_of w) 1 128 =? 103)%uint63 eqn:E103; [exact (fdec_jalr_sound w H2 i E103)|].
  destruct (fld (x_of w) 1 128 =? 55)%uint63 eqn:E55; [exact (fdec_lui_sound w H2 i E55)|].
  destruct (fld (x_of w) 1 128 =? 23)%uint63 eqn:E23; [exact (fdec_auipc_sound w H2 i E23)|].
  destruct (fld (x_of w) 1 128 =? 111)%uint63 eqn:E111; [exact (fdec_jal_sound w H2 i E111)|].
  discriminate.
Qed.

(* [comment removed for export] *)
Definition fdecode (w : bv 32) : option (instr * Z) :=
  match fdec w with
  | Some i => Some (i, 4)
  | None => decode_any w
  end.

Theorem fdecode_eq (w : bv 32) : fdecode w = decode_any w.
Proof. unfold fdecode. destruct (fdec w) as [i|] eqn:E; [symmetry; exact (fdec_sound w i E) | reflexivity]. Qed.
