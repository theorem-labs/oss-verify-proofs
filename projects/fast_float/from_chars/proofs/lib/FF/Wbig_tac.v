(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma zx16_lit : forall z, (0 <= z < 2^16)%Z -> zx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma zx32_lit : forall z, (0 <= z < 2^32)%Z -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land7_aligned : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a mod 8 = 0)%Z -> Z.land (a + b * 8) 7 = 0%Z.
Proof.
  intros a b Ha Hb Hm. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia.
  change (2^3)%Z with 8%Z. rewrite Z.add_mod, Hm, Z.mod_mul by lia. reflexivity.
Qed.
Lemma land7_aligned' : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (a mod 8 = 0)%Z -> Z.land (a + 8 * b) 7 = 0%Z.
Proof. intros. rewrite (Z.mul_comm 8 b). apply land7_aligned; assumption. Qed.
Lemma land7_aligned0 : forall a, (0 <= a)%Z -> (a mod 8 = 0)%Z -> Z.land a 7 = 0%Z.
Proof. intros a Ha Hm. replace a with (a + 0 * 8)%Z by lia. apply land7_aligned; lia. Qed.

(* [comment removed for export] *)
Ltac decide_ltb :=
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; lia)
            | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; lia) ]
  end; cbn [Z.b2z].
Ltac decide_ltb_in H :=
  repeat match type of H with
  | context [Z.ltb ?a ?b] =>
      first [ replace (Z.ltb a b) with true in H by (symmetry; apply Z.ltb_lt; lia)
            | replace (Z.ltb a b) with false in H by (symmetry; apply Z.ltb_ge; lia) ]
  end; cbn [Z.b2z] in H.

(* [comment removed for export] *)
Ltac setcmp :=
  rewrite ?v_sltu_b2z, ?v_sltiu_b2z;
  rewrite ?unsigned_lit by lia;
  try change (bv_wrap 64 1) with 1%Z.

(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.

Lemma smul_lo_word : forall x y c, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> (0 <= c < 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 (x * y + c)) = mul_lo x y c.
Proof.
  intros x y c Hx Hy Hc. rewrite unsigned_lit_wrap. unfold mul_lo.
  rewrite <- Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma smul_carry_word : forall x y c, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> (0 <= c < 2^64)%Z ->
  Z_to_bv 64 (Z.shiftr (x * y) 64 + bv_unsigned (v_sltu (Z_to_bv 64 (x * y + c)) (Z_to_bv 64 (x * y))))
  = Z_to_bv 64 (mul_cout x y c).
Proof.
  intros x y c Hx Hy Hc. rewrite v_sltu_b2z.
  pose proof (zb_b2z_range (bv_unsigned (Z_to_bv 64 (x * y + c)) <? bv_unsigned (Z_to_bv 64 (x * y)))%Z) as Hb.
  rewrite (unsigned_lit (Z.b2z _)) by lia.
  f_equal. unfold mul_cout. rewrite shiftr64_div. f_equal.
  rewrite zb_b2z_if. rewrite (smul_lo_word x y c) by assumption. rewrite unsigned_lit_wrap. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma smul_carry_word' : forall x y c, (0 <= x < 2^64)%Z -> (0 <= y < 2^64)%Z -> (0 <= c < 2^64)%Z ->
  Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 (x * y + c)) (Z_to_bv 64 (x * y))) + Z.shiftr (x * y) 64)
  = Z_to_bv 64 (mul_cout x y c).
Proof. intros. rewrite Z.add_comm. apply smul_carry_word; assumption. Qed.

(* [comment removed for export] *)
Lemma addc_wrap : forall x c, (0 <= x < 2^64)%Z -> (0 <= c < 2^64)%Z ->
  ((x + c) mod 18446744073709551616 < x)%Z -> (2^64 <= x + c)%Z.
Proof.
  intros x c Hx Hc H. destruct (Z.lt_ge_cases (x + c) (2 ^ 64)) as [L|G]; [|exact G].
  exfalso. change 18446744073709551616%Z with (2^64)%Z in H. rewrite Z.mod_small in H by lia. lia.
Qed.
Lemma addc_nowrap : forall x c, (0 <= x < 2^64)%Z -> (0 <= c < 2^64)%Z ->
  (x <= (x + c) mod 18446744073709551616)%Z -> (x + c < 2^64)%Z.
Proof.
  intros x c Hx Hc H. destruct (Z.lt_ge_cases (x + c) (2 ^ 64)) as [L|G]; [exact L|].
  exfalso. change 18446744073709551616%Z with (2^64)%Z in H.
  rewrite <- (Z.mod_unique_pos (x + c) (2^64) 1 (x + c - 2^64)) in H by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma signed_lit : forall z, (-2^63 <= z < 2^63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed. rewrite unsigned_lit_wrap.
  destruct (Z.lt_ge_cases z 0) as [Hneg|Hpos].
  - rewrite <- (Z.mod_unique_pos z (2^64) (-1) (z + 2^64)) by lia.
    replace (z + 2 ^ 64 <? 2 ^ 63)%Z with false by (symmetry; apply Z.ltb_ge; lia). lia.
  - rewrite Z.mod_small by lia.
    replace (z <? 2 ^ 63)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shl48_shr48 : forall x, (0 <= x < 2^16)%Z ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl x 48))) 48 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia.
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_sub : forall segs m A bs off n,
  bytes_at segs m A bs -> (off + n <= length bs)%nat ->
  bytes_at segs m (A + Z.of_nat off) (firstn n (skipn off bs)).
Proof.
  intros segs m A bs off n B H.
  rewrite <- (firstn_skipn off bs) in B. apply bytes_at_app in B. destruct B as [_ B].
  rewrite firstn_length, Nat.min_l in B by lia.
  rewrite <- (firstn_skipn n (skipn off bs)) in B. apply bytes_at_app in B. destruct B as [B _]. exact B.
Qed.

Lemma ro_block : forall segs m A bs off n,
  bytes_at segs m A bs -> (off + n <= length bs)%nat ->
  ro_cells segs m (A + Z.of_nat off) [CB n (firstn n (skipn off bs))].
Proof.
  intros segs m A bs off n B H. split.
  - cbn. split; [| exact I]. rewrite firstn_length, skipn_length. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_sub; assumption.
Qed.

(* [comment removed for export] *)
Lemma f8flag0 : forall e,
  negb (bv_eqb (Z_to_bv 64 (Z.land e (bv_unsigned (Z_to_bv 64 0)))) (Z_to_bv 64 0)) = true -> False.
Proof. intros e H. rewrite (unsigned_lit 0), Z.land_0_r in H by lia. revert H. vm_compute. discriminate. Qed.
Lemma f8flag1 : forall (a : Z), (-2^62 <= a < 2^62)%Z ->
  negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (v_slti (Z_to_bv 64 a) 8)) 1))) (bv_unsigned (Z_to_bv 64 1)))) (Z_to_bv 64 0)) = true ->
  (8 <= a)%Z.
Proof.
  intros a Ha H. unfold v_slti, zsig in H. rewrite signed_lit in H by lia.
  destruct (Z.ltb_spec a 8); [| assumption]. exfalso. revert H. vm_compute. discriminate.
Qed.
Lemma f8flag1' : forall (a : Z), (-2^62 <= a < 2^62)%Z ->
  negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (v_slti (Z_to_bv 64 a) 8)) 1))) (bv_unsigned (Z_to_bv 64 1)))) (Z_to_bv 64 0)) = false ->
  (a < 8)%Z.
Proof.
  intros a Ha H. unfold v_slti, zsig in H. rewrite signed_lit in H by lia.
  destruct (Z.ltb_spec a 8); [assumption|]. exfalso. revert H. vm_compute. discriminate.
Qed.
