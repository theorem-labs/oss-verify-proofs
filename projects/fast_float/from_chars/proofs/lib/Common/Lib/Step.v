(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import LiaTuning MState Mem Cells Exec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require FP.

Module ZBridge.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import LiaTuning MState Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inr64 (e : Z) : Prop := (0 <= e < 2^64)%Z.

Lemma zr_word : forall x : word, inr64 (bv_unsigned x).
Proof. intros x. pose proof (bv_unsigned_in_range 64 x). unfold bv_modulus in *. exact H. Qed.
Lemma zr_bv : forall n (x : bv n), (n <= 64)%N -> inr64 (bv_unsigned x).
Proof.
  intros n x Hn. pose proof (bv_unsigned_in_range n x) as H. unfold bv_modulus, inr64 in *.
  split; [lia|]. apply Z.lt_le_trans with (2 ^ Z.of_N n)%Z; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma zr_lit : forall z, (0 <= z < 2^64)%Z -> inr64 z.
Proof. intros; assumption. Qed.
Lemma zr_mod64 : forall e, inr64 (e mod 2^64).
Proof. intros. unfold inr64. apply Z.mod_pos_bound. lia. Qed.
Lemma zr_mod : forall e k, (0 <= k <= 64)%Z -> inr64 (e mod 2^k).
Proof.
  intros e k Hk. unfold inr64. pose proof (Z.mod_pos_bound e (2^k) ltac:(apply Z.pow_pos_nonneg; lia)).
  split; [lia|]. apply Z.lt_le_trans with (2^k)%Z; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma zr_mod_any : forall e p, (0 < p <= 2^64)%Z -> inr64 (e mod p).
Proof. intros e p Hp. unfold inr64. pose proof (Z.mod_pos_bound e p ltac:(lia)). lia. Qed.
Lemma zr_land_l : forall a b, inr64 a -> (0 <= b)%Z -> inr64 (Z.land a b).
Proof.
  intros a b [Ha Ha'] Hb. unfold inr64. pose proof (Z.land_nonneg a b) as Hn.
  split; [lia|].
  destruct (Z.eq_dec (Z.land a b) 0) as [->|Hnz]; [lia|].
  destruct (Z.eq_dec a 0) as [->|Haz]. { rewrite Z.land_0_l. lia. }
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_land a b ltac:(lia) Hb).
  assert (Z.log2 a < 64)%Z by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma zr_land_r : forall a b, (0 <= a)%Z -> inr64 b -> inr64 (Z.land a b).
Proof. intros. rewrite Z.land_comm. apply zr_land_l; assumption. Qed.
(* [comment removed for export] *)
Lemma land_mask_mod : forall e m, (0 <= m < 2^64)%Z -> Z.land e m = Z.land (e mod 2^64) m.
Proof.
  intros e m Hm. apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit m i) with false. { rewrite !andb_false_r. reflexivity. }
    symmetry. destruct (Z.eq_dec m 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma zr_land_lit : forall e m, (0 <= m < 2^64)%Z -> inr64 (Z.land e m).
Proof.
  intros e m Hm. rewrite land_mask_mod by exact Hm. apply zr_land_r; [|exact Hm].
  apply Z.mod_pos_bound. lia.
Qed.
Lemma zr_lor : forall a b, inr64 a -> inr64 b -> inr64 (Z.lor a b).
Proof. intros a b Ha Hb. unfold inr64 in *. apply Z_lor_range; lia. Qed.
Lemma zr_lxor : forall a b, inr64 a -> inr64 b -> inr64 (Z.lxor a b).
Proof. intros a b Ha Hb. unfold inr64 in *. apply Z_lxor_range; lia. Qed.
Lemma zr_shiftr : forall a k, inr64 a -> (0 <= k)%Z -> inr64 (Z.shiftr a k).
Proof. intros a k Ha Hk. unfold inr64 in *. apply Z_shiftr_range; lia. Qed.
Lemma zr_div : forall a k, inr64 a -> (0 < k)%Z -> inr64 (a / k).
Proof.
  intros a k [Ha Ha'] Hk. unfold inr64. split. { apply Z.div_pos; lia. }
  apply Z.le_lt_trans with a; [|lia]. apply Z.div_le_upper_bound; [lia|]. nia.
Qed.
Lemma zr_b2z : forall b, inr64 (Z.b2z b).
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zr_ite : forall (b : bool) x y, inr64 x -> inr64 y -> inr64 (if b then x else y).
Proof. intros [|]; auto. Qed.

Lemma inr64_unsigned_lit : forall e, inr64 e -> bv_unsigned (Z_to_bv 64 e) = e.
Proof. intros e H. apply unsigned_lit. exact H. Qed.

Ltac is_Zlit_zb a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

(* [comment removed for export] *)
Ltac slim := repeat match goal with x := _ : Z |- _ => clearbody x end.
Ltac flia := first [ assumption | slim; lia | lia ].

(* [comment removed for export] *)
Ltac zrange :=
  lazymatch goal with
  | |- inr64 ?e =>
      lazymatch e with
      | bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
      | Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
                              | apply zr_land_l; [zrange | zrange_nonneg] | apply zr_land_r; [zrange_nonneg | zrange] ]
      | Z.lor _ _ => apply zr_lor; [zrange | zrange]
      | Z.lxor _ _ => apply zr_lxor; [zrange | zrange]
      | Z.shiftr _ _ => apply zr_shiftr; [zrange | flia]
      | Z.modulo _ (2^64)%Z => apply zr_mod64
      | Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
      | Z.div _ _ => apply zr_div; [zrange | flia]
      | Z.b2z _ => apply zr_b2z
      | (if _ then _ else _) => apply zr_ite; [zrange | zrange]
      | _ => first [ apply zr_lit; flia
                   | is_var e; progress (unfold e); zrange ]   (* [comment removed for export] *)
      end
  | |- (0 <= ?e < _)%Z => change (inr64 e); zrange
  end
with zrange_nonneg :=
  lazymatch goal with
  | |- (0 <= ?e)%Z =>
      first [ apply (proj1 (A:=(0 <= e)%Z) (B:=(e < 2^64)%Z)); change (inr64 e); zrange
            | apply Z.land_nonneg; left; zrange_nonneg
            | apply Z.lor_nonneg; split; zrange_nonneg
            | apply Z.lxor_nonneg; split; zrange_nonneg   (* [comment removed for export] *)
            | apply Z.shiftr_nonneg; zrange_nonneg
            | apply Z.shiftl_nonneg; zrange_nonneg
            | flia
            | is_var e; progress (unfold e); zrange_nonneg ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Z_to_bv_mod64 : forall e, Z_to_bv 64 (e mod 2^64) = Z_to_bv 64 e.
Proof.
  intros e. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z.
  apply Z.mod_mod. lia.
Qed.


(* [comment removed for export] *)
Lemma zb_land_pow2_small : forall y k, (0 <= y < 2^k)%Z -> (0 <= k)%Z -> Z.land y (2^k) = 0%Z.
Proof.
  intros y k Hy Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec i k) as [->|Hne].
  - rewrite Z.pow2_bits_true by lia. rewrite andb_true_r.
    apply Z.testbit_false; [lia|]. rewrite Z.div_small by lia. reflexivity.
  - rewrite Z.pow2_bits_eqb by lia. replace (k =? i)%Z with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
Qed.
Lemma zb_lxor_pow2_small : forall y k, (0 <= y < 2^k)%Z -> (0 <= k)%Z -> Z.lxor y (2^k) = (y + 2^k)%Z.
Proof. intros. symmetry. apply Z.add_nocarry_lxor. apply zb_land_pow2_small; assumption. Qed.

Lemma zb_lxor_sign : forall x, (0 <= x < 2^64)%Z -> Z.lxor x (2^63) = ((x + 2^63) mod 2^64)%Z.
Proof.
  intros x Hx. destruct (Z.lt_ge_cases x (2^63)).
  - rewrite zb_lxor_pow2_small by lia. rewrite Z.mod_small by lia. reflexivity.
  - set (y := (x - 2^63)%Z). replace x with (y + 2^63)%Z by lia.
    rewrite <- (zb_lxor_pow2_small y 63) at 1 by lia. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
    replace (y + 2^63 + 2^63)%Z with (y + 1 * 2^64)%Z by lia. rewrite Z.mod_add, Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zb_signed : forall x : word,
  bv_signed x = (if bv_unsigned x <? 2^63 then bv_unsigned x else bv_unsigned x - 2^64)%Z.
Proof.
  intros x. pose proof (bv_unsigned_in_range 64 x) as Hr. unfold bv_modulus in Hr.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *. change (2^64 / 2)%Z with (2^63)%Z.
  destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)).
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma bv_eqb_Z : forall x y : word, bv_eqb x y = (bv_unsigned x =? bv_unsigned y)%Z.
Proof. reflexivity. Qed.
Lemma bv_ltu_Z : forall x y : word, bv_ltu x y = (bv_unsigned x <? bv_unsigned y)%Z.
Proof. reflexivity. Qed.

Lemma bv_lts_lxor : forall x y : word,
  bv_lts x y = (Z.lxor (bv_unsigned x) (2^63) <? Z.lxor (bv_unsigned y) (2^63))%Z.
Proof.
  intros x y. unfold bv_lts. rewrite !zb_signed.
  pose proof (bv_unsigned_in_range 64 x) as Hx. pose proof (bv_unsigned_in_range 64 y) as Hy. unfold bv_modulus in *.
  change (2 ^ Z.of_N 64)%Z with (2^64)%Z in *.
  rewrite !zb_lxor_sign by lia.
  destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); destruct (Z.ltb_spec0 (bv_unsigned y) (2^63)).
  - rewrite !Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
  - rewrite (Z.mod_small (bv_unsigned x + _)) by lia.
    rewrite <- (Z.mod_add (bv_unsigned y + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
  - rewrite (Z.mod_small (bv_unsigned y + _)) by lia.
    rewrite <- (Z.mod_add (bv_unsigned x + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
  - rewrite <- (Z.mod_add (bv_unsigned x + _) (-1)), Z.mod_small by lia.
    rewrite <- (Z.mod_add (bv_unsigned y + _) (-1)), Z.mod_small by lia. apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma bv_lts_zero_r : forall x : word, bv_lts x (Z_to_bv 64 0) = (2^63 <=? bv_unsigned x)%Z.
Proof.
  intros x. unfold bv_lts. rewrite (zb_signed x). change (bv_signed (Z_to_bv 64 0)) with 0%Z.
  pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
  destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); apply eq_true_iff_eq; rewrite Z.ltb_lt, Z.leb_le; lia.
Qed.
(* [comment removed for export] *)
Lemma bv_lts_zero_l : forall x : word,
  bv_lts (Z_to_bv 64 0) x = ((0 <? bv_unsigned x) && (bv_unsigned x <? 2^63))%Z.
Proof.
  intros x. unfold bv_lts. rewrite (zb_signed x). change (bv_signed (Z_to_bv 64 0)) with 0%Z.
  pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
  destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)); apply eq_true_iff_eq; rewrite andb_true_iff, !Z.ltb_lt; lia.
Qed.

(* [comment removed for export] *)
Lemma v_sltu_b2z : forall x y : word, v_sltu x y = Z_to_bv 64 (Z.b2z (bv_unsigned x <? bv_unsigned y)%Z).
Proof. intros. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_slt_b2z : forall x y : word,
  v_slt x y = Z_to_bv 64 (Z.b2z (Z.lxor (bv_unsigned x) (2^63) <? Z.lxor (bv_unsigned y) (2^63))%Z).
Proof. intros. unfold v_slt, c_lts. rewrite bv_lts_lxor. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_sltiu_b2z : forall (x : word) imm, v_sltiu x imm = Z_to_bv 64 (Z.b2z (bv_unsigned x <? bv_wrap 64 imm)%Z).
Proof. intros. unfold v_sltiu. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma v_slti_b2z : forall (x : word) imm,
  v_slti x imm = Z_to_bv 64 (Z.b2z (Z.lxor (bv_unsigned x) (2^63) <? imm + 2^63)%Z).
Proof.
  intros. unfold v_slti, zsig. rewrite zb_signed.
  pose proof (bv_unsigned_in_range 64 x) as Hx. unfold bv_modulus in Hx. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hx.
  rewrite zb_lxor_sign by lia.
  destruct (Z.ltb_spec0 (bv_unsigned x) (2^63)).
  - rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec0 (bv_unsigned x) imm); destruct (Z.ltb_spec0 (bv_unsigned x + 2^63) (imm + 2^63)); try reflexivity; exfalso; lia.
  - rewrite <- (Z.mod_add _ (-1)), Z.mod_small by lia.
    destruct (Z.ltb_spec0 (bv_unsigned x - 2^64) imm); destruct (Z.ltb_spec0 (bv_unsigned x + 2^63 + -1 * 2^64) (imm + 2^63)); try reflexivity; exfalso; lia.
Qed.

(* [comment removed for export] *)
Lemma zb_b2z_if : forall b, Z.b2z b = (if b then 1 else 0)%Z.
Proof. intros [|]; reflexivity. Qed.
Lemma zb_b2z_nonzero : forall b, Z.b2z b <> 0%Z <-> b = true.
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zb_b2z_zero : forall b, Z.b2z b = 0%Z <-> b = false.
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zb_b2z_eqb0 : forall b, (Z.b2z b =? 0)%Z = negb b.
Proof. intros [|]; reflexivity. Qed.
Lemma zb_b2z_range : forall b, (0 <= Z.b2z b <= 1)%Z.
Proof. intros [|]; cbv; split; congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zb_land_mask : forall x k, (0 <= k)%Z -> Z.land x (2^k - 1) = (x mod 2^k)%Z.
Proof. intros. rewrite <- Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l. f_equal. Qed.
Lemma zb_land_mask_l : forall x k, (0 <= k)%Z -> Z.land (2^k - 1) x = (x mod 2^k)%Z.
Proof. intros. rewrite Z.land_comm. apply zb_land_mask. assumption. Qed.

Lemma zb_shiftl_mul : forall x k, (0 <= k)%Z -> Z.shiftl x k = (x * 2^k)%Z.
Proof. intros. apply Z.shiftl_mul_pow2. assumption. Qed.
Lemma zb_shiftr_div : forall x k, (0 <= k)%Z -> Z.shiftr x k = (x / 2^k)%Z.
Proof. intros. apply Z.shiftr_div_pow2. assumption. Qed.

(* [comment removed for export] *)
Lemma zb_shl_shr : forall x k, (0 <= x)%Z -> (0 < k < 64)%Z ->
  Z.shiftr ((Z.shiftl x k) mod 2^64) k = (x mod 2^(64 - k))%Z.
Proof.
  intros x k Hx Hk. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace (2^64)%Z with (2^(64-k) * 2^k)%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r by lia. apply Z.div_mul. lia.
Qed.
(* [comment removed for export] *)
Lemma zb_shr_shl : forall x k, (0 <= x)%Z -> (0 <= k)%Z ->
  Z.shiftl (Z.shiftr x k) k = (x - x mod 2^k)%Z.
Proof.
  intros x k Hx Hk. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (Z.div_mod x (2^k) ltac:(lia)). lia.
Qed.

Lemma zb_lor_eq0 : forall a b, (Z.lor a b = 0)%Z <-> (a = 0 /\ b = 0)%Z.
Proof. intros. apply Z.lor_eq_0_iff. Qed.
Lemma zb_lor_eqb0 : forall a b, (0 <= a)%Z -> (0 <= b)%Z -> (Z.lor a b =? 0)%Z = ((a =? 0) && (b =? 0))%Z.
Proof.
  intros a b Ha Hb. apply eq_true_iff_eq. rewrite andb_true_iff, !Z.eqb_eq. apply Z.lor_eq_0_iff.
Qed.
Lemma zb_lxor_eq0 : forall a b, (Z.lxor a b = 0)%Z <-> a = b.
Proof. intros. apply Z.lxor_eq_0_iff. Qed.
Lemma zb_lxor_eqb0 : forall a b, (Z.lxor a b =? 0)%Z = (a =? b)%Z.
Proof.
  intros. apply eq_true_iff_eq. rewrite !Z.eqb_eq. apply Z.lxor_eq_0_iff.
Qed.
Lemma zb_land_lor_distr_l : forall a b m, Z.land (Z.lor a b) m = Z.lor (Z.land a m) (Z.land b m).
Proof. intros. apply Z.land_lor_distr_l. Qed.

(* [comment removed for export] *)
Lemma zb_lxor_ones : forall x, (0 <= x < 2^64)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof.
  intros x Hx. change 18446744073709551615%Z with (Z.ones 64).
  pose proof (Z.add_lnot_diag x).
  assert (E : Z.lxor x (Z.ones 64) = ((Z.lnot x) mod 2^64)%Z).
  { rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
    rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases i 64).
    - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
    - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
      destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia]. }
  rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2^64)) with (2^64 - 1)%Z.
  replace (Z.lnot x) with (-x - 1)%Z by lia.
  rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Ltac mlia := Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zb_fold_lits :=
  repeat match goal with
  | |- context [Z.shiftr ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
  | |- context [Z.shiftl ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  | |- context [Z.lxor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
  | |- context [Z.modulo ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.modulo a b) in change (Z.modulo a b) with v
  | |- context [Z.pow ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.pow a b) in change (Z.pow a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [bv_wrap ?n ?z] => is_Zlit_zb z; let v := eval vm_compute in (bv_wrap n z) in
        replace (bv_wrap n z) with v by (vm_compute; reflexivity)
  | |- context [Z_to_bv 64 ?z] => is_Zlit_zb z;      (* [comment removed for export] *)
        lazymatch eval vm_compute in (Z.leb 18446744073709551616 z) with true => idtac end;
        let v := eval vm_compute in (z mod 18446744073709551616)%Z in
        replace (Z_to_bv 64 z) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity)
  end.

(* [comment removed for export] *)
Lemma unsigned_lit_land : forall e, bv_unsigned (Z_to_bv 64 e) = Z.land e 18446744073709551615.
Proof. intros. rewrite unsigned_lit_wrap. change 18446744073709551615%Z with (Z.ones 64). symmetry. apply Z.land_ones. lia. Qed.
Lemma Z_to_bv_land64 : forall e, Z_to_bv 64 (Z.land e 18446744073709551615) = Z_to_bv 64 e.
Proof. intros. rewrite <- unsigned_lit_land. apply Z_to_bv_bv_unsigned. Qed.
Lemma zb_shl_shr_land : forall x k, (0 <= x)%Z -> (0 < k < 64)%Z ->
  Z.shiftr (Z.land (Z.shiftl x k) 18446744073709551615) k = Z.land x (2^(64 - k) - 1).
Proof.
  intros x k Hx Hk. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite zb_shl_shr, <- zb_land_mask by lia. reflexivity.
Qed.

Ltac zs_wrap e := rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H := rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms :=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
      rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])   (* [comment removed for export] *)
  end.
Ltac zs_idioms_in H :=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] =>
      rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.
(* [comment removed for export] *)
Ltac zs_wrap_land e := rewrite (unsigned_lit_land e).
Ltac zs_wrap_land_in e H := rewrite (unsigned_lit_land e) in H.
Ltac zs_idioms_land :=
  match goal with
  | |- context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_land_in H :=
  match type of H with
  | context [Z.shiftr (Z.land (Z.shiftl ?x ?k) 18446744073709551615) ?k] =>
      rewrite (zb_shl_shr_land x k) in H by (first [lia | zrange_nonneg])
  end.

(* [comment removed for export] *)
Ltac zsimp :=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.

Ltac zb_fold_lits_in H :=
  repeat match type of H with
  | context [Z.shiftr ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v in H
  | context [Z.shiftl ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v in H
  | context [Z.land ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v in H
  | context [Z.lor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v in H
  | context [Z.lxor ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in H
  | context [Z.pow ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.pow a b) in change (Z.pow a b) with v in H
  | context [Z.sub ?a ?b] => is_Zlit_zb a; is_Zlit_zb b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v in H
  | context [bv_wrap ?n ?z] => is_Zlit_zb z; let v := eval vm_compute in (bv_wrap n z) in
        replace (bv_wrap n z) with v in H by (vm_compute; reflexivity)
  end.

Ltac zsimp_in H :=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.

(* [comment removed for export] *)
Ltac decide_tests :=
  repeat match goal with
  | |- context [Z.eqb ?x ?y] =>
      first [ rewrite (proj2 (Z.eqb_eq x y)) by mlia | rewrite (proj2 (Z.eqb_neq x y)) by mlia ]
  | |- context [Z.ltb ?x ?y] =>
      first [ rewrite (proj2 (Z.ltb_lt x y)) by mlia | rewrite (proj2 (Z.ltb_ge x y)) by mlia ]
  | |- context [Z.leb ?x ?y] =>
      first [ rewrite (proj2 (Z.leb_le x y)) by mlia | rewrite (proj2 (Z.leb_gt x y)) by mlia ]
  end; cbn [andb orb negb].

(* [comment removed for export] *)
Lemma b2z_word_nez : forall b, negb (bv_eqb (Z_to_bv 64 (Z.b2z b)) (Z_to_bv 64 0)) = b.
Proof. intros [|]; reflexivity. Qed.
Lemma b2z_word_eqz : forall b, bv_eqb (Z_to_bv 64 (Z.b2z b)) (Z_to_bv 64 0) = negb b.
Proof. intros [|]; reflexivity. Qed.

(* [comment removed for export] *)
Ltac zr_pose e := let H := fresh "R" in assert (H : inr64 e) by zrange; unfold inr64 in H.

(* [comment removed for export] *)
Ltac zb_masks :=
  repeat match goal with
  | |- context [Z.land ?x ?m] =>
      is_Zlit_zb m;
      let k := eval vm_compute in (Z.log2 (m + 1)) in
      let m' := eval vm_compute in (2 ^ k - 1)%Z in
      constr_eq m m';
      let p := eval vm_compute in (2 ^ k)%Z in
      replace (Z.land x m) with (x mod p)%Z by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
  | H : context [Z.land ?x ?m] |- _ =>
      is_Zlit_zb m;
      let k := eval vm_compute in (Z.log2 (m + 1)) in
      let m' := eval vm_compute in (2 ^ k - 1)%Z in
      constr_eq m m';
      let p := eval vm_compute in (2 ^ k)%Z in
      replace (Z.land x m) with (x mod p)%Z in H by (symmetry; change m with (2^k - 1)%Z; change p with (2^k)%Z; apply zb_land_mask; lia)
  end.

(* [comment removed for export] *)
Ltac pose_word_ranges :=
  repeat match goal with
  | |- context [bv_unsigned ?x] =>
      lazymatch goal with
      | _ : (0 <= bv_unsigned x < _)%Z |- _ => fail
      | _ => pose proof (zr_word x : (0 <= bv_unsigned x < 2^64)%Z)
      end
  | _ : context [bv_unsigned ?x] |- _ =>
      lazymatch goal with
      | _ : (0 <= bv_unsigned x < _)%Z |- _ => fail
      | _ => pose proof (zr_word x : (0 <= bv_unsigned x < 2^64)%Z)
      end
  end.

(* [comment removed for export] *)
Ltac zb_bits_norm :=
  intros;
  rewrite ?Z.land_lor_distr_l in *;
  rewrite ?Z.lor_eq_0_iff in *;
  rewrite ?zb_lxor_eq0 in *;
  zb_masks;
  rewrite ?Z.shiftr_div_pow2 in * by lia;
  zb_fold_lits.

Ltac blia := zb_bits_norm; pose_word_ranges; mlia.

(* [comment removed for export] *)
Ltac decide_tests_b :=
  repeat match goal with
  | |- context [Z.eqb ?x ?y] =>
      first [ rewrite (proj2 (Z.eqb_eq x y)) by blia | rewrite (proj2 (Z.eqb_neq x y)) by blia ]
  | |- context [Z.ltb ?x ?y] =>
      first [ rewrite (proj2 (Z.ltb_lt x y)) by blia | rewrite (proj2 (Z.ltb_ge x y)) by blia ]
  | |- context [Z.leb ?x ?y] =>
      first [ rewrite (proj2 (Z.leb_le x y)) by blia | rewrite (proj2 (Z.leb_gt x y)) by blia ]
  end; cbn [andb orb negb].

Lemma zb_negb_eqb0 : forall x, (0 <= x)%Z -> negb (x =? 0)%Z = (0 <? x)%Z.
Proof. intros x Hx. destruct (Z.eqb_spec x 0); destruct (Z.ltb_spec0 0 x); cbn; try reflexivity; exfalso; lia. Qed.

(* [comment removed for export] *)
Lemma Z_to_bv_eqm : forall e1 e2, (e1 mod 2^64 = e2 mod 2^64)%Z -> Z_to_bv 64 e1 = Z_to_bv 64 e2.
Proof. intros e1 e2 H. rewrite <- (Z_to_bv_mod64 e1), <- (Z_to_bv_mod64 e2), H. reflexivity. Qed.

Ltac word_eq_tac :=
  first [ exact eq_refl
        | f_equal; lia
        | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
        | apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ].
End ZBridge.

Export OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.FP OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Definition ro_cells (m : word -> option byte) (A : Z) (cs : list cell) : Prop :=
  cells_at segs m A cs.
Definition rw_cells (m : word -> option byte) (A : Z) (cs : list cell) : Prop :=
  cells_at segs m A cs /\ wr_at segs m A (Z.of_nat (cells_size cs)).

#[using="Type"] Lemma rw_cells_read : forall m A cs k c,
  rw_cells m A cs -> cell_at cs k = Some c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) (csize c) = Some (cbytes c).
Proof. LiaFast.lf_pins LiaFast.u0. intros m A cs k c [H _]. apply cells_at_read. exact H. Qed.

#[using="Type"] Lemma ro_cells_read : forall m A cs k c,
  ro_cells m A cs -> cell_at cs k = Some c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) (csize c) = Some (cbytes c).
Proof. LiaFast.lf_pins LiaFast.u0. intros m A cs k c H. apply cells_at_read. exact H. Qed.

#[using="Type"] Lemma rw_cells_readn : forall m A cs k c n,
  rw_cells m A cs -> cell_at cs k = Some c -> n = csize c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) n = Some (cbytes c).
Proof. LiaFast.lf_pins LiaFast.u0. intros; subst; eapply rw_cells_read; eauto. Qed.

#[using="Type"] Lemma ro_cells_readn : forall m A cs k c n,
  ro_cells m A cs -> cell_at cs k = Some c -> n = csize c ->
  ov_read_bytes segs m (wa (A + Z.of_nat k)) n = Some (cbytes c).
Proof. LiaFast.lf_pins LiaFast.u0. intros; subst; eapply ro_cells_read; eauto. Qed.

#[using="Type"] Lemma rw_cells_read_at : forall m A cs k c n a,
  rw_cells m A cs -> cell_at cs k = Some c -> n = csize c -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes segs m a n = Some (cbytes c).
Proof. LiaFast.lf_pins LiaFast.u0. intros; subst; eapply rw_cells_read; eauto. Qed.

#[using="Type"] Lemma ro_cells_read_at : forall m A cs k c n a,
  ro_cells m A cs -> cell_at cs k = Some c -> n = csize c -> a = wa (A + Z.of_nat k) ->
  ov_read_bytes segs m a n = Some (cbytes c).
Proof. LiaFast.lf_pins LiaFast.u0. intros; subst; eapply ro_cells_read; eauto. Qed.

#[using="Type"] Lemma rw_cells_cb_split : forall m A cs cs2 k n,
  rw_cells m A cs -> cb_split_ok cs k n = true -> cs2 = cb_split cs k n -> rw_cells m A cs2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A cs cs2 k n [Hc Hw] Hok ->. split.
  - apply cells_at_cb_split; assumption.
  - rewrite cells_size_cb_split; [exact Hw| exact (cells_at_wf _ _ _ _ Hc) | exact Hok].
Qed.

#[using="Type"] Lemma ro_cells_cb_split : forall m A cs cs2 k n,
  ro_cells m A cs -> cb_split_ok cs k n = true -> cs2 = cb_split cs k n -> ro_cells m A cs2.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A cs cs2 k n Hc Hok ->. apply cells_at_cb_split; assumption. Qed.

#[using="Type"] Lemma cell_at_bound : forall cs k c, cell_at cs k = Some c -> (k + csize c <= cells_size cs)%nat.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros cs k c H. destruct (cell_at_split cs k c c H) as (pre & post & -> & Hsz & _).
  rewrite cells_size_app. cbn. lia.
Qed.

#[using="Type"] Lemma rw_cells_store_ok : forall m A cs k c (j : nat),
  rw_cells m A cs -> cell_at cs k = Some c -> j = csize c ->
  store_ok segs m (wa (A + Z.of_nat k)) j = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A cs k c j [Hc Hw] Hk ->. pose proof (cell_at_bound _ _ _ Hk).
  apply (wr_at_store_ok segs m A (Z.of_nat (cells_size cs))); [exact Hw| lia | lia].
Qed.

#[using="Type"] Lemma rw_cells_store_ok_at : forall m A cs k c (j : nat) a,
  rw_cells m A cs -> cell_at cs k = Some c -> j = csize c -> a = wa (A + Z.of_nat k) ->
  store_ok segs m a j = true.
Proof. LiaFast.lf_pins LiaFast.u0. intros; subst. eapply rw_cells_store_ok; eauto. Qed.

#[using="Type"] Lemma rw_cells_write : forall m A cs k c c',
  rw_cells m A cs -> cell_at cs k = Some c -> csize c' = csize c -> cell_wf c' ->
  rw_cells (write_to_mem m (wa (A + Z.of_nat k)) (cbytes c')) A (cell_upd cs k c').
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A cs k c c' [Hc Hw] Hk Hsz Hwf. split.
  - eapply cells_at_write; eauto.
  - destruct (cell_at_split cs k c c' Hk) as (pre & post & -> & Hszp & ->).
    rewrite cells_size_app in *. cbn [cells_size] in *. rewrite Hsz. apply wr_at_write. exact Hw.
Qed.

#[using="Type"] Lemma rw_cells_frame : forall m A cs (a : Z) bs,
  rw_cells m A cs -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  rw_cells (write_to_mem m (wa a) bs) A cs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A cs a bs [Hc Hw] Ha Hl Hd. split.
  - apply cells_at_frame; assumption.
  - apply wr_at_write. exact Hw.
Qed.

#[using="Type"] Lemma ro_cells_frame : forall m A cs (a : Z) bs,
  ro_cells m A cs -> (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2^64)%Z ->
  (A + Z.of_nat (cells_size cs) <= a \/ a + Z.of_nat (length bs) <= A)%Z ->
  ro_cells (write_to_mem m (wa a) bs) A cs.
Proof. LiaFast.lf_pins LiaFast.u0. intros. apply cells_at_frame; assumption. Qed.

#[using="Type"] Lemma rw_cells_bound : forall m A cs, rw_cells m A cs -> (0 <= A /\ A + Z.of_nat (cells_size cs) <= 2^64)%Z.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A cs [H _]. eapply cells_at_bound; eauto. Qed.
#[using="Type"] Lemma ro_cells_bound : forall m A cs, ro_cells m A cs -> (0 <= A /\ A + Z.of_nat (cells_size cs) <= 2^64)%Z.
Proof. LiaFast.lf_pins LiaFast.u0. intros m A cs H. eapply cells_at_bound; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mem_inv_store_cbytes : forall m a c',
  mem_inv segs m -> cell_wf c' -> store_ok segs m a (csize c') = true ->
  mem_inv segs (write_to_mem m a (cbytes c')).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m a c' Hinv Hwf Hok. apply mem_inv_store; [assumption|].
  rewrite cbytes_length by assumption. exact Hok.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma unsigned_Z_to_bv_add : forall e d, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) + d) = Z_to_bv 64 (e + d).
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma unsigned_Z_to_bv_add_r : forall e d, Z_to_bv 64 (d + bv_unsigned (Z_to_bv 64 e)) = Z_to_bv 64 (d + e).
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma unsigned_Z_to_bv_sub : forall e d, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 e) - d) = Z_to_bv 64 (e - d).
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

Lemma bv_add_canon : forall (x y : word), (x + y : word) = Z_to_bv 64 (bv_unsigned x + bv_unsigned y).
Proof. intros. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity. Qed.

Lemma Z_to_bv_lit_self : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma wa_of_Z_to_bv : forall E e, E = e -> wa e = Z_to_bv 64 E.
Proof. intros; subst; reflexivity. Qed.
Lemma wa_of_var : forall (x : word) e, bv_unsigned x = e -> wa e = x.
Proof. intros; subst. unfold wa. apply Z_to_bv_lit_self. Qed.

Lemma store_bytes_8' : forall v : word, Z_to_le_bytes 8 (bv_unsigned v) = le8 v.
Proof. exact store_bytes_8. Qed.
Lemma store_bytes_4' : forall v : word, Z_to_le_bytes 4 (bv_unsigned (low32 v)) = le4 v.
Proof. exact store_bytes_4. Qed.
Lemma store_bytes_2' : forall v : word, Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 v)) = le2 v.
Proof. exact store_bytes_2. Qed.
Lemma store_bytes_1' : forall v : word, Z_to_le_bytes 1 (bv_unsigned (bv_extract 0 8 v)) = le1 v.
Proof. exact store_bytes_1. Qed.

(* [comment removed for export] *)
Lemma evt_step_gen : forall segs Q R F pc fc rv m ro w i sz ms1,
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, sz) ->
  lift_result ro (ieff segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = MachineOk ms1 ->
  evt segs Q ms1 -> evt segs Q (MS R F pc fc rv m ro).
Proof.
  intros segs Q R F pc fc rv m ro w i sz ms1 Hf He Hd Hx Hq. eapply evt_step; [|exact Hq].
  split; [reflexivity|]. rewrite (step_gen segs R F pc fc rv m ro w i sz Hf He Hd). exact Hx.
Qed.

(* [comment removed for export] *)
Definition step_pre (segs : list Segment) (pc : word) : option (instr * Z) :=
  match fetch_word segs pc with
  | Some w => if is_ecall w then None else decode_any w
  | None => None
  end.
Lemma evt_step_gen1 : forall segs Q R F pc fc rv m ro i sz ms1,
  step_pre segs pc = Some (i, sz) ->
  lift_result ro (ieff segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = MachineOk ms1 ->
  evt segs Q ms1 -> evt segs Q (MS R F pc fc rv m ro).
Proof.
  intros segs Q R F pc fc rv m ro i sz ms1 Hp Hx Hq. unfold step_pre in Hp.
  destruct (fetch_word segs pc) as [w|] eqn:Hf; [|discriminate Hp].
  destruct (is_ecall w) eqn:He; [discriminate Hp|].
  exact (evt_step_gen segs Q R F pc fc rv m ro w i sz ms1 Hf He Hp Hx Hq).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac kp_zlit a := lazymatch a with Z0 => a | Zpos _ => a | Zneg _ => a end.
Ltac kp_bo t :=
  match t with
  | Z.add ?X ?c => let c' := kp_zlit c in constr:((X, c'))
  | Z.sub ?X ?c => let c' := kp_zlit c in let m := eval vm_compute in (Z.opp c') in constr:((X, m))
  | _ => let c := kp_zlit t in constr:((0%Z, c))
  | _ => constr:((t, 0%Z))
  end.
Ltac kp_diff E A :=
  let e := kp_bo E in let a := kp_bo A in
  lazymatch e with (?X, ?c1) => lazymatch a with (X, ?c2) => eval vm_compute in (c1 - c2)%Z end end.
Ltac kp_ovs_d a n lo hi :=
  let n' := kp_zlit n in
  let d1 := kp_diff a lo in      (* [comment removed for export] *)
  let d3 := lazymatch hi with      (* [comment removed for export] *)
            | Z.add lo ?m => let m' := kp_zlit m in eval vm_compute in (m' - d1)%Z
            | _ => kp_diff hi a
            end in
  lazymatch eval vm_compute in (andb (Z.ltb 0%Z (d1 + n')%Z) (Z.ltb 0%Z d3)) with true => idtac end.
Ltac kp_ovs_in G :=
  lazymatch G with
  | ((?a + ?n <= ?lo \/ ?hi <= ?a) /\ ?R)%Z => first [ kp_ovs_d a n lo hi | kp_ovs_in R ]
  | (?a + ?n <= ?lo \/ ?hi <= ?a)%Z => kp_ovs_d a n lo hi
  end.
Ltac kp_ovs := lazymatch goal with |- ?G => kp_ovs_in G end.
Ltac slia := first [ exact I | (tryif kp_ovs then fail else lia) | split; [ (tryif kp_ovs then fail else lia) | exact I ] ].      (* [comment removed for export] *)

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

(* [comment removed for export] *)
Ltac set_concl g' := change_no_check g'.
Ltac cbv_concl_beta_iota :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota in g in set_concl g'.
Ltac cbv_concl_iota :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv iota in g in set_concl g'.
Ltac cbv_concl_zeta :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv zeta in g in set_concl g'.

(* [comment removed for export] *)
Ltac fold_closed_in_goal :=
  repeat match goal with
  | |- context [bv_unsigned (@BV ?n ?z ?p)] => let v := eval vm_compute in (bv_unsigned (@BV n z p)) in change (bv_unsigned (@BV n z p)) with v
  | |- context [bv_signed (@BV ?n ?z ?p)] => let v := eval vm_compute in (bv_signed (@BV n z p)) in change (bv_signed (@BV n z p)) with v
  | |- context [bv_signed (bv_concat ?n ?a ?b)] => let v := eval vm_compute in (bv_signed (bv_concat n a b)) in is_Zlit v; change (bv_signed (bv_concat n a b)) with v
  | |- context [bv_unsigned (bv_concat ?n ?a ?b)] => let v := eval vm_compute in (bv_unsigned (bv_concat n a b)) in is_Zlit v; change (bv_unsigned (bv_concat n a b)) with v
  | |- context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
        change (bv_unsigned (Z_to_bv n z)) with v
  | |- context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z; let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
        change (bv_signed (Z_to_bv n z)) with v
  | |- context [Z.shiftl ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
  | |- context [Z.shiftr ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  | |- context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
  | |- context [bv_swrap ?n ?z] => is_Zlit z; let v := eval vm_compute in (bv_swrap n z) in
        change (bv_swrap n z) with v
  | |- context [bv_wrap ?n ?z] => is_Zlit z; let v := eval vm_compute in (bv_wrap n z) in
        change (bv_wrap n z) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v
  | |- context [Z.add (Z.add ?x ?a) ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in
        replace (Z.add (Z.add x a) b) with (Z.add x v) by (exact (Z.add_assoc x a b))
  | |- context [Z_to_bv 64 (Z.add ?x 0)] => rewrite (Z.add_0_r x)
  end.

(* [comment removed for export] *)
Ltac fold_lit_load :=
  repeat match goal with
  | |- context [bv_extract 0 ?n (le_bytes_to_word ?bs)] =>
      lazymatch bs with (_ :: _)%list => idtac end;
      let t := constr:(bv_extract 0 n (le_bytes_to_word bs)) in
      let z := eval vm_compute in (bv_unsigned t) in
      is_Zlit z;
      rewrite (bv_lit_eq n t z) by (vm_compute; reflexivity)
  | |- context [@sext ?k 64 (Z_to_bv ?k ?z)] =>
      is_Zlit z;
      let t := constr:(@sext k 64 (Z_to_bv k z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  | |- context [@zext ?k 64 (Z_to_bv ?k ?z)] =>
      is_Zlit z;
      let t := constr:(@zext k 64 (Z_to_bv k z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  | |- context [low32 (Z_to_bv 64 ?z)] =>
      is_Zlit z;
      let t := constr:(low32 (Z_to_bv 64 z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 32 t z') by (vm_compute; reflexivity)
  | |- context [nan_box (Z_to_bv 32 ?z)] =>
      is_Zlit z;
      let t := constr:(nan_box (Z_to_bv 32 z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  end.

(* [comment removed for export] *)
Ltac simp_is_x0 :=
  repeat match goal with
  | |- context [is_x0 ?r] => let v := eval vm_compute in (is_x0 r) in change (is_x0 r) with v
  end; cbv_concl_beta_iota.

(* [comment removed for export] *)
Ltac is_concrete_map R := lazymatch R with TNode _ _ _ => idtac | TEmpty => idtac end.
Ltac map_cbv_get :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota delta [tget] in g in set_concl g'.
Ltac map_cbv_set :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota delta [tset tset64] in g in set_concl g'.

Ltac norm_fchain :=
  repeat match goal with
  | |- context [@bvmap_set 5 word ?k ?x (@bvmap_set 5 word ?k' ?y ?R)] =>
      let a := eval vm_compute in (bv_unsigned k) in
      let b := eval vm_compute in (bv_unsigned k') in
      let c := eval vm_compute in (Z.compare a b) in
      lazymatch c with
      | Eq => rewrite (bvmap_set_set_same' k k' x y R) by reflexivity
      | Gt => rewrite (bvmap_set_set_comm k k' x y R) by reflexivity
      end
  end.

Ltac simp_regs :=
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (reg_get R r) with (match tget p R with Some v => v | None => w0 end);
      map_cbv_get
  | |- context [@bvmap_set 5 word ?r ?v ?R] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (@bvmap_set 5 word r v R) with (tset64 p v R);      (* [comment removed for export] *)
      map_cbv_set
  | |- context [reg_get (@bvmap_set 5 word ?k ?v ?R) ?r] =>
      first [ rewrite (freg_get_same R k r v) by reflexivity
            | rewrite (freg_get_other R k r v) by reflexivity ]
  end;
  norm_fchain.

Ltac exec_cbv :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota zeta delta [lift_result ieff exec with_pc with_regs with_fregs with_fcsr with_resv
     rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
     width_bytes accrue fari_d fcmp_d fari_s fcmp_s] in g in
  set_concl g'.

(* [comment removed for export] *)
Ltac vnorm_rw_for i :=
  lazymatch i with
  | OpImm ALU_ADD _ _ _ => rewrite ?alu_addi
  | OpImm ALU_AND _ _ _ => rewrite ?alu_andi
  | OpImm ALU_OR _ _ _ => rewrite ?alu_ori
  | OpImm ALU_XOR _ _ _ => rewrite ?alu_xori
  | OpImm ALU_SLT _ _ _ => rewrite ?alu_slti
  | OpImm ALU_SLTU _ _ _ => rewrite ?alu_sltiu
  | ShiftImm ALU_SLL _ _ _ => rewrite ?alu_slli
  | ShiftImm ALU_SRL _ _ _ => rewrite ?alu_srli
  | ShiftImm ALU_SRA _ _ _ => rewrite ?alu_srai
  | Op ALU_ADD _ _ _ => rewrite ?alu_add
  | Op ALU_SUB _ _ _ => rewrite ?alu_sub
  | Op ALU_SLT _ _ _ => rewrite ?alu_slt
  | Op ALU_SLTU _ _ _ => rewrite ?alu_sltu
  | Op ALU_AND _ _ _ => rewrite ?alu_and
  | Op ALU_OR _ _ _ => rewrite ?alu_or
  | Op ALU_XOR _ _ _ => rewrite ?alu_xor
  | Op ALU_SLL _ _ _ => rewrite ?alu_sll
  | Op ALU_SRL _ _ _ => rewrite ?alu_srl
  | Op ALU_SRA _ _ _ => rewrite ?alu_sra
  | OpImm32 _ _ _ => rewrite ?w_addiw
  | ShiftImm32 ALU_SLL _ _ _ => rewrite ?w_slliw
  | ShiftImm32 ALU_SRL _ _ _ => rewrite ?w_srliw
  | ShiftImm32 ALU_SRA _ _ _ => rewrite ?w_sraiw
  | Op32 ALU_ADD _ _ _ => rewrite ?w_addw
  | Op32 ALU_SUB _ _ _ => rewrite ?w_subw
  | Op32 ALU_SLL _ _ _ => rewrite ?w_sllw
  | Op32 ALU_SRL _ _ _ => rewrite ?w_srlw
  | Op32 ALU_SRA _ _ _ => rewrite ?w_sraw
  | Mul M_MUL _ _ _ => rewrite ?m_mul
  | Mul M_MULH _ _ _ => rewrite ?m_mulh
  | Mul M_MULHSU _ _ _ => rewrite ?m_mulhsu
  | Mul M_MULHU _ _ _ => rewrite ?m_mulhu
  | Mul M_DIV _ _ _ => rewrite ?m_div
  | Mul M_REM _ _ _ => rewrite ?m_rem
  | Mul32 M_MUL _ _ _ => rewrite ?w_mulw
  | Mul32 M_DIV _ _ _ => rewrite ?w_divw
  | Mul32 M_REM _ _ _ => rewrite ?w_remw
  | Mul32 M_DIVU _ _ _ => rewrite ?w_divuw
  | Mul32 M_REMU _ _ _ => rewrite ?w_remuw
  | Lui _ _ => rewrite ?b_lui
  | Auipc _ _ => rewrite ?b_auipc
  | Load _ _ _ _ _ => rewrite ?b_addsext
  | Store _ _ _ _ => rewrite ?b_addsext
  | FLoad _ _ _ _ => rewrite ?b_addsext
  | FStore _ _ _ _ => rewrite ?b_addsext
  | Jalr _ _ _ => rewrite ?b_addsext
  | Jal _ _ => rewrite ?b_addsext
  | Branch _ _ _ _ => rewrite ?b_addsext
  (* [comment removed for export] *)
  | Fsgnj _ FMT_S _ _ _ => rewrite ?sgnj_self_s, ?sgnjx_self_s, ?sgnjn_self_s
  | Fsgnj _ _ _ _ _ => rewrite ?sgnj_self, ?sgnjx_self, ?sgnjn_self
  | Fmv _ _ _ _ => rewrite ?fmv_x_w_val; fold_lit_load
  | Fari _ _ _ _ _ _ => idtac
  | Fcmp _ _ _ _ _ => idtac
  | Fcvt _ _ _ _ _ => idtac
  | Fsqrt _ _ _ _ => idtac
  | Fminmax _ _ _ _ _ => idtac
  | Fclass _ _ _ => idtac
  | Csr _ _ _ _ => idtac
  | CsrI _ _ _ _ => idtac
  | _ =>
  rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_xori, ?alu_slti, ?alu_sltiu,
          ?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slli, ?alu_srli, ?alu_srai, ?alu_sll, ?alu_srl, ?alu_sra,
          ?w_addiw, ?w_slliw, ?w_srliw, ?w_sraiw, ?w_addw, ?w_subw, ?w_sllw, ?w_srlw, ?w_sraw,
          ?m_mul, ?m_mulh, ?m_mulhsu, ?m_mulhu, ?m_div, ?m_rem, ?w_mulw, ?w_divw, ?w_remw, ?w_divuw, ?w_remuw,
          ?b_addsext, ?b_lui, ?b_auipc
  end.

(* [comment removed for export] *)
Ltac lit_add_lits :=
  repeat match goal with
  | |- context [@bv_add 64 (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] =>
      is_Zlit a; is_Zlit b;
      lazymatch eval vm_compute in (andb (andb (Z.leb 0 a) (Z.ltb a 18446744073709551616))
                                         (andb (Z.leb 0 b) (Z.ltb b 18446744073709551616))) with
      | true => let c := eval vm_compute in (a + b)%Z in change (@bv_add 64 (Z_to_bv 64 a) (Z_to_bv 64 b)) with (Z_to_bv 64 c)
      | false => rewrite (lit_add_lit a b)
      end
  end;
  (match goal with |- context [@bv_add 64 (Z_to_bv 64 _) (Z_to_bv 64 _)] => rewrite ?lit_add_lit | _ => idtac end).
(* [comment removed for export] *)
Ltac ret_pc_lits :=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
       lazymatch eval vm_compute in (andb (Z.leb 0 n) (Z.ltb n 18446744073709551616)) with
       | true => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (apply bv_eq; vm_compute; reflexivity)
       | false => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
       end
  end.
Ltac unfold_vdefs :=
  let g := lazymatch goal with |- ?g => g end in
  let gd := eval cbv beta iota delta [v_addi v_add v_sub v_mul v_andi v_ori v_xori v_and v_or v_xor
         v_slli v_srli v_srai v_sll v_srl v_sra v_lui v_auipc
         v_addiw v_slliw v_srliw v_sraiw v_addw v_subw v_sllw v_srlw v_sraw
         v_mulh v_mulhsu v_mulhu v_mulw btgt] in g in
  tryif constr_eq gd g then idtac else      (* [comment removed for export] *)
  let g' := eval unfold v_addi, v_add, v_sub, v_mul, v_andi, v_ori, v_xori, v_and, v_or, v_xor,
         v_slli, v_srli, v_srai, v_sll, v_srl, v_sra, v_lui, v_auipc,
         v_addiw, v_slliw, v_srliw, v_sraiw, v_addw, v_subw, v_sllw, v_srlw, v_sraw,
         v_mulh, v_mulhsu, v_mulhu, v_mulw, btgt in g in
  set_concl g'.
Ltac vnorm_tail :=
  lit_add_lits;
  (match goal with |- context [w0] => change w0 with (Z_to_bv 64 0) | _ => idtac end);
  (match goal with |- context [w1] => change w1 with (Z_to_bv 64 1) | _ => idtac end);
  unfold_vdefs;
  (match goal with      (* [comment removed for export] *)
   | |- context [Z_to_bv 64 (Z.add (bv_unsigned (Z_to_bv 64 _)) _)] => rewrite ?unsigned_Z_to_bv_add, ?unsigned_Z_to_bv_add_r
   | |- context [Z_to_bv 64 (Z.add _ (bv_unsigned (Z_to_bv 64 _)))] => rewrite ?unsigned_Z_to_bv_add, ?unsigned_Z_to_bv_add_r
   | _ => idtac end);
  fold_closed_in_goal;
  (match goal with |- context [Z_to_bv 64 (bv_unsigned _)] => rewrite ?Z_to_bv_lit_self | _ => idtac end);
  (match goal with |- context [bv_and _ (bv_not _)] =>
     repeat match goal with |- context [@bv_and 64 ?x (@bv_not 64 (Z_to_bv 64 1))] => change (@bv_and 64 x (@bv_not 64 (Z_to_bv 64 1))) with (ret_pc x) end;
     rewrite ?ret_pc_fold
   | _ => idtac end);
  (* [comment removed for export] *)
  ret_pc_lits.

Ltac vnorm_for i := vnorm_rw_for i; vnorm_tail.

Ltac vnorm :=
  rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_xori, ?alu_slti, ?alu_sltiu,
          ?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slli, ?alu_srli, ?alu_srai, ?alu_sll, ?alu_srl, ?alu_sra,
          ?w_addiw, ?w_slliw, ?w_srliw, ?w_sraiw, ?w_addw, ?w_subw, ?w_sllw, ?w_srlw, ?w_sraw,
          ?m_mul, ?m_mulh, ?m_mulhsu, ?m_mulhu, ?m_div, ?m_rem, ?w_mulw, ?w_divw, ?w_remw, ?w_divuw, ?w_remuw,
          ?b_addsext, ?b_lui, ?b_auipc;
  lit_add_lits;
  (match goal with |- context [w0] => change w0 with (Z_to_bv 64 0) | _ => idtac end);
  (match goal with |- context [w1] => change w1 with (Z_to_bv 64 1) | _ => idtac end);
  unfold_vdefs;
  rewrite ?unsigned_Z_to_bv_add, ?unsigned_Z_to_bv_add_r;
  fold_closed_in_goal;
  rewrite ?Z_to_bv_lit_self, ?ret_pc_fold;
  (* [comment removed for export] *)
  ret_pc_lits.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zlit a := lazymatch a with Z0 => a | Zpos _ => a | Zneg _ => a end.

Ltac addr_diff E A :=
  lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
      | X => zlit c1
      | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
      end
  end.

(* [comment removed for export] *)
Ltac addr_expr a :=
  lazymatch a with
  | Z_to_bv 64 ?E => E
  | wa ?E => E
  | _ => constr:(Z.add (bv_unsigned a) 0)
  end.
(* [comment removed for export] *)
Ltac is_natlit n := lazymatch n with O => idtac | S ?k => is_natlit k end.
Ltac zlit_of t :=
  lazymatch t with
  | Z0 => t | Zpos _ => t | Zneg _ => t
  | Z.of_nat ?n => let chk := match n with _ => is_natlit n end in eval cbv in t
  end.
Ltac is_zlit_term a := match a with _ => let v := zlit_of a in idtac end.

(* [comment removed for export] *)
Ltac sb_split a kX :=
  lazymatch a with
  | Z.add ?a1 ?k1 =>
      match constr:(tt) with
      | _ => let d1 := zlit_of k1 in
             lazymatch a1 with
             | Z.add ?a2 ?k2 =>
                 match constr:(tt) with
                 | _ => let d2 := zlit_of k2 in let d := eval vm_compute in (d2 + d1)%Z in
                        kX a2 d constr:(@eq_sym Z _ _ (Z.add_assoc a2 k2 k1))
                 | _ => kX a1 d1 constr:(@eq_refl Z a)
                 end
             | Z.sub ?a2 ?k2 =>
                 match constr:(tt) with
                 | _ => let d2 := zlit_of k2 in let d := eval vm_compute in (d1 - d2)%Z in
                        kX a2 d constr:(@eq_sym Z _ _ (Z.add_assoc a2 (- k2)%Z k1))
                 | _ => kX a1 d1 constr:(@eq_refl Z a)
                 end
             | _ => kX a1 d1 constr:(@eq_refl Z a)
             end
      | _ => kX a 0%Z constr:(@eq_sym Z _ _ (Z.add_0_r a))
      end
  | Z.sub ?a1 ?k1 =>
      match constr:(tt) with
      | _ => let d1 := zlit_of k1 in let d := eval vm_compute in (- d1)%Z in
             kX a1 d constr:(@eq_refl Z a)
      | _ => kX a 0%Z constr:(@eq_sym Z _ _ (Z.add_0_r a))
      end
  | _ => kX a 0%Z constr:(@eq_sym Z _ _ (Z.add_0_r a))
  end.

(* [comment removed for export] *)
Ltac zaddr_eq_fast :=
  lazymatch goal with
  | |- @eq Z ?E ?E' =>
      sb_split E ltac:(fun X d pf =>
        sb_split E' ltac:(fun X' d' pf' =>
          constr_eq X X'; constr_eq d d';
          exact (@eq_trans Z E (X + d)%Z E' pf (@eq_sym Z E' (X + d)%Z pf'))))
  end.

(* [comment removed for export] *)
Ltac addr_eq_fast4 :=
  first [ symmetry; apply wa_of_Z_to_bv; zaddr_eq_fast
        | symmetry; apply wa_of_var; zaddr_eq_fast
        | apply wa_of_Z_to_bv; zaddr_eq_fast
        | apply wa_of_var; zaddr_eq_fast ].
Ltac addr_eq_tac :=
  first [ addr_eq_fast4
        | symmetry; apply wa_of_Z_to_bv; lia
        | symmetry; apply wa_of_var; lia
        | apply wa_of_Z_to_bv; lia
        | apply wa_of_var; lia
        | unfold wa; f_equal; lia
        | symmetry; unfold wa; f_equal; lia ].

(* [comment removed for export] *)
Ltac cells_cbv :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota zeta delta [cell_at cell_upd csize cells_size Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add cbytes] in g in set_concl g'.
Ltac cb_split_cbv :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in g in set_concl g'.

Ltac eval_cb_split cs kn n :=
  eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cb_split cs kn n).
Ltac eval_cb_split_ok cs kn n :=
  eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cb_split_ok cs kn n).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_cells_cb_split0 : forall segs m A cs k n,
  rw_cells segs m A cs -> cb_split_ok cs k n = true -> rw_cells segs m A (cb_split cs k n).
Proof. intros segs m A cs k n H Hok. exact (rw_cells_cb_split segs m A cs (cb_split cs k n) k n H Hok eq_refl). Qed.
Lemma ro_cells_cb_split0 : forall segs m A cs k n,
  ro_cells segs m A cs -> cb_split_ok cs k n = true -> ro_cells segs m A (cb_split cs k n).
Proof. intros segs m A cs k n H Hok. exact (ro_cells_cb_split segs m A cs (cb_split cs k n) k n H Hok eq_refl). Qed.
Ltac split_for_access H segs m A cs kn n :=
  let ok := eval_cb_split_ok cs kn n in
  lazymatch ok with
  | true =>
      let cs2 := eval_cb_split cs kn n in
      lazymatch cs2 with
      | cs => idtac
      | _ => first [ apply (rw_cells_cb_split0 segs m A cs kn n) in H; [ change_no_check (rw_cells segs m A cs2) in H | ]
                   | apply (ro_cells_cb_split0 segs m A cs kn n) in H; [ change_no_check (ro_cells segs m A cs2) in H | ] ];
             [ | cells_cbv; reflexivity ]      (* [comment removed for export] *)
      end
  end.

Ltac eval_cell_at cs kn := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs kn).



(* [comment removed for export] *)
Ltac load_post :=
  (let g := lazymatch goal with |- ?g => g end in
   let g' := eval cbv beta iota delta [cbytes] in g in set_concl g');
  rewrite ?load_u64, ?zext_extract_le4, ?sext_extract_le4, ?zext_extract_le2, ?sext_extract_le2,
          ?zext_extract_le1, ?sext_extract_le1, ?zext_extract_byte, ?sext_extract_byte;
  fold_lit_load.

(* [comment removed for export] *)
Ltac solve_load_base :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        lazymatch eval vm_compute in (andb (Z.ltb (-18446744073709551616)%Z k) (Z.ltb k 0%Z)) with false => idtac end;      (* [comment removed for export] *)
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        lazymatch eval vm_compute in (andb (Z.ltb (-18446744073709551616)%Z k) (Z.ltb k 0%Z)) with false => idtac end;      (* [comment removed for export] *)
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | (* [comment removed for export] *)
                replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; first [word_eq_tac | addr_eq_tac]) ]
    end
  end;
  load_post.

(* [comment removed for export] *)

Ltac solve_load := solve_load_base.

Ltac solve_store :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        lazymatch eval vm_compute in (andb (Z.ltb (-18446744073709551616)%Z k) (Z.ltb k 0%Z)) with false => idtac end;      (* [comment removed for export] *)
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv_concl_beta_iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; first [word_eq_tac | addr_eq_tac]);
                (* [comment removed for export] *)
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; first [word_eq_tac | addr_eq_tac]) ];
        cbv_concl_beta_iota
    end
  end.

(* [comment removed for export] *)
Ltac cell_of_bytes bs :=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))     (* [comment removed for export] *)
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))       (* [comment removed for export] *)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))      (* [comment removed for export] *)
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 2 ?z => constr:(C2 (Z_to_bv 64 z))
  end.

Ltac simpl_sizes :=
  rewrite ?app_length;
  (let g := lazymatch goal with |- ?g => g end in      (* [comment removed for export] *)
   let g' := eval cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in g in set_concl g');
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length;
  (let g := lazymatch goal with |- ?g => g end in
   let g' := eval cbn [length] in g in set_concl g').

Ltac transport_chunks segs m a bs :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac mem_after_store :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    lazymatch goal with
    | H : rw_cells segs m A ?cs |- _ =>
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          (* [comment removed for export] *)
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; try clear m; try rename H' into H
        end
    end
  end.

Ltac mem_after_store_opt :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rm_proof rm c :=
  let z := eval vm_compute in (bv_unsigned rm) in
  lazymatch z with
  | 7%Z =>
      lazymatch c with
      | Core _ _ _ ?fc _ =>
          lazymatch goal with
          | FRM : frm0 fc |- _ => constr:(rmode_dyn rm c (@eq_refl Z 7%Z) FRM)
          | _ => fail 100 "FP instruction with dynamic rounding mode: need a hypothesis [frm0" fc "]"
          end
      end
  | _ =>
      let md := eval vm_compute in (match rmode_of_Z z with Some md => md | None => RNE end) in
      constr:(rmode_static rm c md (@eq_refl bool false) (@eq_refl (option rmode) (Some md)))
  end.

(* [comment removed for export] *)
Ltac exec_pre i :=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fari ?op FMT_D ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_d sz op rd rs1 rs2 rm c _ H)
    | Fari ?op FMT_S ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_s sz op rd rs1 rs2 rm c _ H)
    | Fsqrt FMT_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fsqrt_d sz rd rs1 rm c _ H)
    | Fcmp ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_d sz op rd rs1 rs2 c)
    | Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
    | Fminmax ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fminmax_d sz op rd rs1 rs2 c); cbv_concl_zeta
    | Fcvt FC_W FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_d sz rd rs1 rm c _ H)
    | Fcvt FC_WU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_d sz rd rs1 rm c _ H)
    | Fcvt FC_L FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_d sz rd rs1 rm c _ H)
    | Fcvt FC_LU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_d sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_w sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_L ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_l sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_LU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_lu sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_w sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_wu sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_L ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_l sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_LU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_lu sz rd rs1 rm c _ H)
    | Fcvt FC_W FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_s sz rd rs1 rm c _ H)
    | Fcvt FC_WU FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_s sz rd rs1 rm c _ H)
    | Fcvt FC_L FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_s sz rd rs1 rm c _ H)
    | Fcvt FC_LU FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_s sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_s sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_d sz rd rs1 rm c _ H)
    | Csr ?op ?rd ?rs1 ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csr_rw sz op rd rs1 csr c lo len ltac:(vm_compute; reflexivity)); cbv_concl_zeta;
            simp_is_x0; try change (negb true) with false; try change (negb false) with true; cbv_concl_iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | CsrI ?op ?rd ?uimm ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csri_rw sz op rd uimm csr c lo len ltac:(vm_compute; reflexivity)); cbv_concl_zeta;
            let w := eval vm_compute in (negb (Z.eqb (bv_unsigned uimm) 0)) in
            try change (negb (Z.eqb (bv_unsigned uimm) 0)) with w; cbv_concl_iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | _ => idtac
    end
  end;
  (* [comment removed for export] *)
  try match goal with
  | FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
  end.

(* [comment removed for export] *)
Ltac prove_frm0 :=
  first [ assumption
        | apply frm0_accrue; prove_frm0
        | apply frm0_slice_set_fflags; prove_frm0 ].

Ltac norm_fcsr :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ ?fce _ _ _) =>
      tryif is_var fce then idtac else
      (let fcn := fresh "fc" in
       let E := fresh "Efc" in
       tryif (let H := fresh "FRM" in
              assert (H : frm0 fce) by prove_frm0;
              repeat match goal with
              | H' : frm0 ?f |- _ => lazymatch f with fce => fail | _ => clear H' end
              end;
              remember fce as fcn eqn:E; clear E;
              try rename H into FRM)
       then idtac
       else (remember fce as fcn eqn:E; clear E))
  | _ => idtac
  end.

Ltac post_step i :=
  lazymatch i with
  | Fari _ _ _ _ _ _ => norm_fcsr
  | Fcmp _ _ _ _ _ => norm_fcsr
  | Fcvt _ _ _ _ _ => norm_fcsr
  | Fsqrt _ _ _ _ => norm_fcsr
  | Fminmax _ _ _ _ _ => norm_fcsr
  | Fma _ _ _ _ _ _ _ => norm_fcsr
  | Csr _ _ _ _ => norm_fcsr
  | CsrI _ _ _ _ => norm_fcsr
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac step_core_ref segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply (evt_step_gen1 segs _ R F (Z_to_bv 64 pc) fc rv m ro i sz);      (* [comment removed for export] *)
        [ vm_cast_no_check (@eq_refl _ (Some (i, sz)))
        | exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.


(* [comment removed for export] *)
Ltac simp_reads RR T :=
  repeat match goal with
  | |- context [reg_get RR ?r] =>
      let p := eval vm_compute in (bv_key r) in
      let v := eval cbv beta iota delta [tget] in (tget p T) in
      lazymatch v with
      | Some ?x => change (reg_get RR r) with x
      | None => change (reg_get RR r) with w0
      end
  end.


(* [comment removed for export] *)
Ltac regs_to_tree R := R.
(* [comment removed for export] *)
Ltac is_int_load_rd i :=
  lazymatch i with
  | Load _ _ ?rd _ _ => let z := eval vm_compute in (bv_unsigned rd) in lazymatch z with Z0 => fail | _ => idtac end
  end.
Ltac is_mem_instr i :=
  lazymatch i with
  | Load _ _ _ _ _ => idtac | Store _ _ _ _ => idtac | FLoad _ _ _ _ => idtac | FStore _ _ _ _ => idtac
  end.
(* [comment removed for export] *)
Ltac touches_regs RR :=
  lazymatch goal with
  | |- context [reg_get RR _] => idtac
  | |- context [@bvmap_set 5 word _ _ RR] => idtac
  end.
(* [comment removed for export] *)
Ltac step_unfold_post S1 RR :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv delta [S1 RR] in g in      (* [comment removed for export] *)
  change_no_check g'; clear S1 RR.
Ltac step_fast segs R T F pc fc rv m ro i sz mk :=
          let S1 := fresh "S1" in let RR := fresh "RR" in
          (lazymatch mk with
           | true => refine (let S1 : machine_state := _ in let RR : bvmap 5 word := R in
                             evt_step_gen1 segs _ RR F (Z_to_bv 64 pc) fc rv m ro i sz S1 _ _ _)
           | false => refine (let RR : bvmap 5 word := R in let S1 : machine_state := _ in      (* [comment removed for export] *)
                              evt_step_gen1 segs _ RR F (Z_to_bv 64 pc) fc rv m ro i sz S1 _ _ _)
           end);      (* [comment removed for export] *)
          [ vm_cast_no_check (@eq_refl _ (Some (i, sz)))      (* [comment removed for export] *)
          | exec_pre i;
            exec_cbv;
            simp_is_x0;
            let acc := lazymatch goal with
                       | |- context [reg_get RR _] => constr:(true)
                       | |- context [@bvmap_set 5 word _ _ RR] => constr:(true)
                       | _ => constr:(false)
                       end in
            simp_reads RR T; simp_regs; vnorm_for i;
            try solve_load; try solve_store;
            (tryif is_mem_instr i then vnorm_for i else idtac);
            (lazymatch mk with
             | true => subst RR; lazymatch acc with true => change R with T | false => idtac end; simp_regs
             | false => idtac      (* [comment removed for export] *)
             end);
            exact (@eq_refl _ (MachineOk S1))
          | step_unfold_post S1 RR;
            (tryif is_int_load_rd i then map_cbv_set else idtac);
            simp_regs; vnorm_for i; mem_after_store_opt; post_step i ].
Ltac step_core segs R F pc fc rv m ro :=
  let d := eval vm_compute in (step_pre segs (Z_to_bv 64 pc)) in      (* [comment removed for export] *)
  lazymatch d with
  | Some (?i, ?sz) =>
        lazymatch R with
        | TNode _ _ _ => step_fast segs R R F pc fc rv m ro i sz false
        | _ =>
            let T := regs_to_tree R in
            lazymatch T with
            | TNode _ _ _ => step_fast segs R T F pc fc rv m ro i sz true
            | _ => step_core_ref segs R F pc fc rv m ro
            end
        end
  | None => step_core_ref segs R F pc fc rv m ro      (* [comment removed for export] *)
  end.


Ltac step_fast_entry := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro end.
Ltac step_ref_entry := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core_ref segs R F pc fc rv m ro end.
From Ltac2 Require Ltac2.
Module StepValidate.
  Import Ltac2.
  Ltac2 Type exn ::= [ StepSnap (constr * constr list) ].
  Ltac2 snapshot () : constr * constr list :=
    (Control.goal (), List.flat_map (fun h => let (_, b, t) := h in match b with Some x => [x; t] | None => [t] end) (Control.hyps ())).
  Ltac2 rec eqlist (a : constr list) (b : constr list) : bool :=
    match a with
    | [] => match b with [] => true | _ :: _ => false end
    | x :: a' => match b with [] => false | y :: b' => if Constr.equal x y then eqlist a' b' else false end
    end.
  Ltac2 validate () : unit :=
    let pc := lazy_match! goal with [ |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) ] => pc end in
    let r := Control.case (fun () => ltac1:(step_fast_entry); let sn := snapshot () in Control.zero (StepSnap sn)) in
    match r with
    | Val _ => Control.throw Assertion_failure
    | Err e =>
        match e with
        | StepSnap sn =>
            let (g1, h1) := sn in
            ltac1:(step_ref_entry);
            let (g2, h2) := snapshot () in
            if Bool.and (Constr.equal g1 g2) (eqlist h1 h2) then ()
            else (Message.print (Message.concat (Message.of_string "STEP-DIFF at ") (Message.of_constr pc));
                  (if Constr.equal g1 g2 then Message.print (Message.of_string "  (hyps differ)")
                   else
                   lazy_match! g1 with
                   | evt _ ?q1 (MS ?r1 ?f1 ?p1 ?c1 ?v1 ?m1 _) =>
                     lazy_match! g2 with
                     | evt _ ?q2 (MS ?r2 ?f2 ?p2 ?c2 ?v2 ?m2 _) =>
                       let show := fun (nm : string) (a : constr) (b : constr) =>
                         if Constr.equal a b then () else
                         (Message.print (Message.concat (Message.of_string "  FAST ") (Message.concat (Message.of_string nm) (Message.of_constr a)));
                          Message.print (Message.concat (Message.of_string "  REF  ") (Message.concat (Message.of_string nm) (Message.of_constr b)))) in
                       show "Q: " q1 q2; show "R: " r1 r2; show "F: " f1 f2; show "pc: " p1 p2; show "fc: " c1 c2; show "rv: " v1 v2; show "m: " m1 m2
                     | _ => Message.print (Message.of_constr g2)
                     end
                   | _ => Message.print (Message.of_constr g1)
                   end))
        | _ => Message.print (Message.concat (Message.of_string "STEP-FAST-FAIL at ") (Message.of_constr pc)); ltac1:(step_ref_entry)
        end
    end.
  Ltac2 validate1 () : unit := Control.enter validate.
  Ltac step_validate := ltac2:(validate1 ()).
End StepValidate.
Ltac step :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

(* [comment removed for export] *)
Ltac unfold_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb].
(* [comment removed for export] *)
Ltac fold_lit_ux :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
      replace (bv_unsigned (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  | |- context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
      replace (bv_signed (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  end.
Ltac solve_cond_base :=
  first [ reflexivity
        | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | apply Z.leb_le; lia | apply Z.leb_gt; lia
        | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia ].
Ltac solve_cond_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); solve_cond_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); solve_cond_rec
  | _ => solve_cond_base
  end.
Ltac solve_cond := unfold_cond; fold_lit_ux; solve_cond_rec.
Ltac if_true :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv_concl_iota| symmetry; solve_cond]
  end.
Ltac if_false :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv_concl_iota| symmetry; solve_cond]
  end.
Ltac if_true_by H :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv_concl_iota| symmetry; exact H]
  end.
Ltac if_false_by H :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv_concl_iota| symmetry; exact H]
  end.
(* [comment removed for export] *)
Ltac if_cases H :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      destruct c eqn:H; [ | ]
  end.

(* [comment removed for export] *)
Ltac fold_lit_ux_in H :=
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
      replace (bv_unsigned (Z_to_bv n z)) with v in H by (vm_compute; reflexivity)
  | context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
      replace (bv_signed (Z_to_bv n z)) with v in H by (vm_compute; reflexivity)
  end.
(* [comment removed for export] *)
Ltac zify_bool H :=
  lazymatch type of H with
  | negb _ = true => apply (proj1 (Bool.negb_true_iff _)) in H; zify_bool H
  | negb _ = false => apply (proj1 (Bool.negb_false_iff _)) in H; zify_bool H
  | Z.eqb (Z.b2z ?b) 0 = true => apply Z.eqb_eq in H; apply (proj1 (zb_b2z_zero b)) in H; zify_bool H
  | Z.eqb (Z.b2z ?b) 0 = false => apply Z.eqb_neq in H; apply (proj1 (zb_b2z_nonzero b)) in H; zify_bool H
  | Z.eqb _ _ = true => apply Z.eqb_eq in H
  | Z.eqb _ _ = false => apply Z.eqb_neq in H
  | Z.ltb _ _ = true => apply Z.ltb_lt in H
  | Z.ltb _ _ = false => apply Z.ltb_ge in H
  | Z.leb _ _ = true => apply Z.leb_le in H
  | Z.leb _ _ = false => apply Z.leb_gt in H
  | andb _ _ = true =>
      apply andb_true_iff in H;
      let H1 := fresh H in let H2 := fresh H in destruct H as [H1 H2]; zify_bool H1; zify_bool H2
  | orb _ _ = false =>
      apply orb_false_iff in H;
      let H1 := fresh H in let H2 := fresh H in destruct H as [H1 H2]; zify_bool H1; zify_bool H2
  | _ => idtac
  end.

Ltac zify_cond H :=
  rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H;
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; zsimp_in H;
  zify_bool H.

(* [comment removed for export] *)
Ltac concretize_regs :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      let t := eval vm_compute in R in change R with t
  end.

(* [comment removed for export] *)
Ltac zstep := step; zsimp.
