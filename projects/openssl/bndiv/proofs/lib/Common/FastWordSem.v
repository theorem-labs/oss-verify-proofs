(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.Common Require Import FastWord.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma w_ltu_bv (a b : w64) : w_ltu a b = bv_ltu (wbv a) (wbv b).
Proof. unfold bv_ltu. rewrite !wbv_unsigned. apply w_ltu_spec. Qed.

Lemma w_lts_bv (a b : w64) : w_lts a b = bv_lts (wbv a) (wbv b).
Proof. unfold bv_lts. rewrite !wbv_signed. apply w_lts_spec. Qed.

Lemma w_eqb_bv (a b : w64) : w_eqb a b = bv_eqb (wbv a) (wbv b).
Proof. unfold bv_eqb. rewrite !wbv_unsigned. apply w_eqb_spec. Qed.

Definition w_branch (bc : branch_cond) (a b : w64) : bool :=
  match bc with
  | BC_EQ => w_eqb a b
  | BC_NE => negb (w_eqb a b)
  | BC_LT => w_lts a b
  | BC_GE => negb (w_lts a b)
  | BC_LTU => w_ltu a b
  | BC_GEU => negb (w_ltu a b)
  end.

Lemma w_branch_ok (bc : branch_cond) (a b : w64) : w_branch bc a b = branch_taken bc (wbv a) (wbv b).
Proof. destruct bc; cbn [w_branch branch_taken]; rewrite ?w_eqb_bv, ?w_lts_bv, ?w_ltu_bv; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition w_alu64 (op : aluop) (a b : w64) : w64 :=
  match op with
  | ALU_ADD => w_add a b
  | ALU_SUB => w_sub a b
  | ALU_SLL => w_sll a (w_shamt6 b)
  | ALU_SLT => if w_lts a b then w_one else w_zero
  | ALU_SLTU => if w_ltu a b then w_one else w_zero
  | ALU_XOR => w_xor a b
  | ALU_SRL => w_srl a (w_shamt6 b)
  | ALU_SRA => w_sra a (w_shamt6 b)
  | ALU_OR => w_or a b
  | ALU_AND => w_and a b
  end.

Lemma wbv_one : wbv w_one = Z_to_bv 64 1.
Proof. reflexivity. Qed.
Lemma wbv_zero : wbv w_zero = Z_to_bv 64 0.
Proof. reflexivity. Qed.

Lemma w_alu64_ok (op : aluop) (a b : w64) : wbv (w_alu64 op a b) = alu64 op (wbv a) (wbv b).
Proof.
  destruct op; unfold alu64, alu; cbn [w_alu64].
  - apply wbv_add.
  - apply wbv_sub.
  - apply wbv_sll.
  - rewrite w_lts_bv. destruct (bv_lts (wbv a) (wbv b)); reflexivity.
  - rewrite w_ltu_bv. destruct (bv_ltu (wbv a) (wbv b)); reflexivity.
  - apply wbv_xor.
  - apply wbv_srl.
  - apply wbv_sra.
  - apply wbv_or.
  - apply wbv_and.
Qed.

Definition w_muldiv (op : mulop) (a b : w64) : w64 :=
  match op with
  | M_MUL => w_mul a b
  | _ => w_of_bv (mul_div op (wbv a) (wbv b))
  end.

Lemma w_muldiv_ok (op : mulop) (a b : w64) : wbv (w_muldiv op a b) = mul_div op (wbv a) (wbv b).
Proof.
  destruct op; cbn [w_muldiv]; try apply wbv_w_of_bv.
  unfold mul_div. apply wbv_mul.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition int_of_bv32 (b : bv 32) : int := of_Z (bv_unsigned b).
Definition bv32_of_int (x : int) : bv 32 := Z_to_bv 32 (to_Z x).

Lemma phi_int_of_bv32 (b : bv 32) : to_Z (int_of_bv32 b) = bv_unsigned b.
Proof.
  unfold int_of_bv32. rewrite of_Z_spec. apply Z.mod_small.
  pose proof (bv_unsigned_in_range 32 b) as H. change (bv_modulus 32) with 4294967296 in H.
  rewrite wB_eq. unfold two63. lia.
Qed.

(* [comment removed for export] *)
Lemma w_sext32_ok (x : int) (r : bv 32) : to_Z x = bv_unsigned r -> wbv (w_sext32 x) = sext 64 r.
Proof.
  intros Hx. pose proof (bv_unsigned_in_range 32 r) as Hr. change (bv_modulus 32) with two32 in Hr.
  apply wbv_eq_iff. unfold sext. rewrite bv_sign_extend_unsigned. rewrite wZ_sext32 by lia.
  unfold bv_signed, bv_swrap, bv_wrap. change (bv_modulus 32) with two32. change (bv_half_modulus 32) with 2147483648.
  change (bv_modulus 64) with two64. rewrite Hx.
  destruct (Z.ltb_spec (bv_unsigned r) 2147483648).
  - rewrite (Z.mod_small (bv_unsigned r + 2147483648)) by (unfold two32 in *; lia).
    rewrite Z.mod_small by (unfold two32, two64 in *; lia). lia.
  - replace (bv_unsigned r + 2147483648) with ((bv_unsigned r + 2147483648 - two32) + 1 * two32) by ring.
    rewrite Z.mod_add by (unfold two32; lia). rewrite (Z.mod_small (bv_unsigned r + 2147483648 - two32) two32) by (unfold two32 in *; lia).
    replace (bv_unsigned r + 2147483648 - two32 - 2147483648) with (bv_unsigned r - two32 + 0) by ring.
    replace (bv_unsigned r - two32 + 0) with ((bv_unsigned r + two64 - two32) + (-1) * two64) by ring.
    rewrite Z.mod_add by (unfold two64; lia). rewrite Z.mod_small by (unfold two32, two64 in *; lia). reflexivity.
Qed.

Lemma low32_wbv (a : w64) : bv_unsigned (low32 (wbv a)) = to_Z (w_low32 a).
Proof.
  unfold low32. rewrite bv_extract_unsigned. rewrite wbv_unsigned. rewrite phi_low32.
  unfold bv_wrap. change (bv_modulus 32) with two32. rewrite Z.shiftr_0_r. reflexivity.
Qed.

(* [comment removed for export] *)
Definition w_alu32 (op : aluop) (x y : int) : int :=
  match op with
  | ALU_ADD => ((x + y) land m32)%uint63
  | ALU_SUB => ((x - y) land m32)%uint63
  | ALU_SLL => ((x << (y land 31)) land m32)%uint63
  | ALU_SRL => (x >> (y land 31))%uint63
  | ALU_SRA =>
      let k := (y land 31)%uint63 in
      if (x land 2147483648 =? 0)%uint63 then (x >> k)%uint63
      else ((x >> k) + (4294967296 - (1 << (32 - k))))%uint63
  | _ => int_of_bv32 (alu32 op (bv32_of_int x) (bv32_of_int y))
  end.

Lemma phi_land31 (y : int) : to_Z (y land 31)%uint63 = to_Z y mod 32.
Proof.
  rewrite land_spec'. change (to_Z 31%uint63) with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma bv32_land31 (Y : bv 32) (y : int) : to_Z y = bv_unsigned Y ->
  bv_unsigned (bv_and Y (Z_to_bv 32 31)) = to_Z (y land 31)%uint63.
Proof.
  intros Hy. rewrite bv_and_unsigned, phi_land31, Hy. rewrite Z_to_bv_unsigned.
  change (bv_wrap 32 31) with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma bv32_of_int_ok (x : int) (X : bv 32) : to_Z x = bv_unsigned X -> bv32_of_int x = X.
Proof. intros H. apply bv_eq. unfold bv32_of_int. rewrite Z_to_bv_unsigned, H. apply bv_wrap_bv_unsigned. Qed.

Lemma w_alu32_ok (op : aluop) (x y : int) (X Y : bv 32) :
  to_Z x = bv_unsigned X -> to_Z y = bv_unsigned Y ->
  to_Z (w_alu32 op x y) = bv_unsigned (alu32 op X Y).
Proof.
  intros Hx Hy. pose proof (bv_unsigned_in_range 32 X) as HX. pose proof (bv_unsigned_in_range 32 Y) as HY.
  change (bv_modulus 32) with two32 in HX, HY.
  pose proof (phi_range x). pose proof (phi_range y).
  unfold alu32, alu. destruct op; cbn [w_alu32];
    try (rewrite phi_int_of_bv32, (bv32_of_int_ok x X Hx), (bv32_of_int_ok y Y Hy); reflexivity).
  - rewrite phi_m32_land, add_spec, wB_eq, Hx, Hy, bv_add_unsigned. unfold bv_wrap. change (bv_modulus 32) with two32.
    rewrite (Z.mod_small (bv_unsigned X + bv_unsigned Y) two63) by (unfold two32, two63 in *; lia). reflexivity.
  - rewrite phi_m32_land, sub_spec, wB_eq, Hx, Hy, bv_sub_unsigned. unfold bv_wrap. change (bv_modulus 32) with two32.
    apply Z.mod_mod_divide. exists 2147483648. reflexivity.
  - (* [comment removed for export] *)
    rewrite phi_m32_land, lsl_spec, wB_eq, bv_shiftl_unsigned, Hx. rewrite (bv32_land31 Y y Hy).
    unfold bv_wrap. change (bv_modulus 32) with two32.
    rewrite Z.shiftl_mul_pow2 by (pose proof (phi_range (y land 31)%uint63); lia).
    apply Z.mod_mod_divide. exists 2147483648. reflexivity.
  - (* [comment removed for export] *)
    rewrite lsr_spec, bv_shiftr_unsigned, Hx. rewrite (bv32_land31 Y y Hy).
    rewrite Z.shiftr_div_pow2 by (pose proof (phi_range (y land 31)%uint63); lia). reflexivity.
  - (* [comment removed for export] *)
    set (k := (y land 31)%uint63).
    assert (Hk : to_Z k = bv_unsigned (bv_and Y (Z_to_bv 32 31))) by (symmetry; apply bv32_land31; exact Hy).
    assert (Hkr : 0 <= to_Z k < 32) by (unfold k; rewrite phi_land31; apply Z.mod_pos_bound; lia).
    rewrite bv_ashiftr_unsigned, <- Hk. unfold bv_signed, bv_swrap, bv_wrap.
    change (bv_modulus 32) with two32. change (bv_half_modulus 32) with 2147483648.
    assert (Hp : 2 ^ (32 - to_Z k) * 2 ^ to_Z k = two32).
    { rewrite <- Z.pow_add_r by lia. replace (32 - to_Z k + to_Z k) with 32 by lia. reflexivity. }
    assert (Hpos : 0 < 2 ^ to_Z k) by (apply Z.pow_pos_nonneg; lia).
    assert (Hpos2 : 0 < 2 ^ (32 - to_Z k)) by (apply Z.pow_pos_nonneg; lia).
    assert (Hq : to_Z x / 2 ^ to_Z k < 2 ^ (32 - to_Z k)).
    { apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_comm, Hp. lia. }
    assert (Hq0 : 0 <= to_Z x / 2 ^ to_Z k) by (apply Z.div_pos; lia).
    assert (Hle : 2 ^ (32 - to_Z k) <= two32) by (change two32 with (2 ^ 32); apply Z.pow_le_mono_r; lia).
    destruct (eqbP (x land 2147483648) 0) as [E|E]; change (to_Z 0%uint63) with 0 in E.
    + (* [comment removed for export] *)
      assert (Hsmall : to_Z x < 2147483648).
      { rewrite land_spec' in E. change (to_Z 2147483648%uint63) with (2 ^ 31) in E.
        destruct (Z_lt_le_dec (to_Z x) 2147483648) as [?|Hge]; [assumption|exfalso].
        assert (Hb : Z.testbit (to_Z x) 31 = true).
        { rewrite Z.testbit_eqb by lia. apply Z.eqb_eq.
          assert (to_Z x / 2 ^ 31 = 1) as -> by (symmetry; apply Z.div_unique with (r := to_Z x - 2 ^ 31); unfold two32 in *; lia).
          reflexivity. }
        assert (Z.testbit (Z.land (to_Z x) (2 ^ 31)) 31 = true) by (rewrite Z.land_spec, Z.pow2_bits_true by lia; rewrite Hb; reflexivity).
        rewrite E in H1. rewrite Z.bits_0 in H1. discriminate. }
      rewrite lsr_spec. rewrite Hx in *.
      rewrite (Z.mod_small (bv_unsigned X + 2147483648)) by (unfold two32 in *; lia).
      replace (bv_unsigned X + 2147483648 - 2147483648) with (bv_unsigned X) by ring.
      rewrite Z.shiftr_div_pow2 by lia. rewrite Z.mod_small by (unfold two32 in *; lia). reflexivity.
    + (* [comment removed for export] *)
      assert (Hbig : 2147483648 <= to_Z x).
      { destruct (Z_lt_le_dec (to_Z x) 2147483648) as [Hlt|?]; [exfalso|assumption].
        apply E. rewrite land_spec'. change (to_Z 2147483648%uint63) with (2 ^ 31).
        apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.eq_dec n 31) as [->|Hne].
        - rewrite Z.bits_above_log2; [reflexivity | lia |].
          destruct (Z.eq_dec (to_Z x) 0) as [->|Hnz]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
        - rewrite Z.pow2_bits_false by lia. apply andb_false_r. }
      assert (Hsub : to_Z (32 - k)%uint63 = 32 - to_Z k).
      { apply phi_sub_le. change (to_Z 32%uint63) with 32. lia. }
      assert (Hsh : to_Z (1 << (32 - k))%uint63 = 2 ^ (32 - to_Z k)).
      { rewrite lsl_spec, Hsub, wB_eq. change (to_Z 1%uint63) with 1. rewrite Z.mul_1_l.
        apply Z.mod_small. unfold two32, two63 in *; lia. }
      assert (Hdf : to_Z (4294967296 - (1 << (32 - k)))%uint63 = two32 - 2 ^ (32 - to_Z k)).
      { rewrite phi_sub_le; rewrite Hsh; change (to_Z 4294967296%uint63) with two32; [reflexivity | lia]. }
      assert (Hx2 : to_Z (x >> k)%uint63 = to_Z x / 2 ^ to_Z k) by apply lsr_spec.
      assert (Hres : to_Z ((x >> k) + (4294967296 - (1 << (32 - k))))%uint63 = to_Z x / 2 ^ to_Z k + (two32 - 2 ^ (32 - to_Z k))).
      { rewrite add_spec, Hx2, Hdf, wB_eq. apply Z.mod_small. unfold two32, two63 in *; lia. }
      rewrite Hres. rewrite Hx in *.
      replace (bv_unsigned X + 2147483648) with ((bv_unsigned X - 2147483648) + 1 * two32) by (unfold two32; ring).
      rewrite Z.mod_add by (unfold two32; lia).
      rewrite (Z.mod_small (bv_unsigned X - 2147483648) two32) by (unfold two32 in *; lia).
      replace (bv_unsigned X - 2147483648 - 2147483648) with (bv_unsigned X + (- 2 ^ (32 - to_Z k)) * 2 ^ to_Z k)
        by (rewrite Z.mul_opp_l, Hp; unfold two32; ring).
      rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_add by lia.
      replace (bv_unsigned X / 2 ^ to_Z k + - 2 ^ (32 - to_Z k)) with
        ((bv_unsigned X / 2 ^ to_Z k + (two32 - 2 ^ (32 - to_Z k))) + (-1) * two32) by ring.
      rewrite Z.mod_add by (unfold two32; lia). rewrite Z.mod_small by (unfold two32 in *; lia). reflexivity.
Qed.

Lemma w_alu32_range (op : aluop) (x y : int) (X Y : bv 32) :
  to_Z x = bv_unsigned X -> to_Z y = bv_unsigned Y -> to_Z (w_alu32 op x y) < two32.
Proof.
  intros Hx Hy. rewrite (w_alu32_ok op x y X Y Hx Hy).
  pose proof (bv_unsigned_in_range 32 (alu32 op X Y)) as H. change (bv_modulus 32) with two32 in H. lia.
Qed.

(* [comment removed for export] *)
Lemma w_op32_ok (op : aluop) (x y : int) (X Y : bv 32) :
  to_Z x = bv_unsigned X -> to_Z y = bv_unsigned Y ->
  wbv (w_sext32 (w_alu32 op x y)) = sext 64 (alu32 op X Y).
Proof. intros Hx Hy. apply w_sext32_ok. apply w_alu32_ok; assumption. Qed.

(* [comment removed for export] *)
Definition w_muldiv32 (op : mulop) (x y : int) : int :=
  match op with
  | M_MUL => ((x * y) land m32)%uint63
  | _ => int_of_bv32 (mul_div op (bv32_of_int x) (bv32_of_int y))
  end.

Lemma w_muldiv32_ok (op : mulop) (x y : int) (X Y : bv 32) :
  to_Z x = bv_unsigned X -> to_Z y = bv_unsigned Y ->
  to_Z (w_muldiv32 op x y) = bv_unsigned (mul_div op X Y).
Proof.
  intros Hx Hy. destruct op; cbn [w_muldiv32];
    try (rewrite phi_int_of_bv32, (bv32_of_int_ok x X Hx), (bv32_of_int_ok y Y Hy); reflexivity).
  unfold mul_div. rewrite phi_m32_land, mul_spec, wB_eq, Hx, Hy, bv_mul_unsigned. unfold bv_wrap.
  change (bv_modulus 32) with two32. apply Z.mod_mod_divide. exists 2147483648. reflexivity.
Qed.
