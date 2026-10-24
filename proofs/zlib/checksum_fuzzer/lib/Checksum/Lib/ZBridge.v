(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import PropExec MState Mem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

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
(* [comment removed for export] *)
Ltac flia := first [ assumption | lazymatch goal with | x := _ : Z |- _ => first [ slim; lia | lia ] | _ => lia end ].

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

(* [comment removed for export] *)
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
(* [comment removed for export] *)
Lemma zb_b2z_nonzero : forall b, Z.b2z b <> 0%Z <-> b = true.
Proof. intros [|]; cbv; split; congruence. Qed.
Lemma zb_b2z_zero : forall b, Z.b2z b = 0%Z <-> b = false.
Proof. intros [|]; cbv; split; congruence. Qed.
(* [comment removed for export] *)
Lemma zb_b2z_range : forall b, (0 <= Z.b2z b <= 1)%Z.
Proof. intros [|]; cbv; split; congruence. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zb_land_mask : forall x k, (0 <= k)%Z -> Z.land x (2^k - 1) = (x mod 2^k)%Z.
Proof. intros. rewrite <- Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l. f_equal. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zb_shl_shr : forall x k, (0 <= x)%Z -> (0 < k < 64)%Z ->
  Z.shiftr ((Z.shiftl x k) mod 2^64) k = (x mod 2^(64 - k))%Z.
Proof.
  intros x k Hx Hk. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  replace (2^64)%Z with (2^(64-k) * 2^k)%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r by lia. apply Z.div_mul. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zb_lor_eq0 : forall a b, (Z.lor a b = 0)%Z <-> (a = 0 /\ b = 0)%Z.
Proof. intros. apply Z.lor_eq_0_iff. Qed.
(* [comment removed for export] *)
Lemma zb_lxor_eq0 : forall a b, (Z.lxor a b = 0)%Z <-> a = b.
Proof. intros. apply Z.lxor_eq_0_iff. Qed.
(* [comment removed for export] *)
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
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma Z_to_bv_eqm : forall e1 e2, (e1 mod 2^64 = e2 mod 2^64)%Z -> Z_to_bv 64 e1 = Z_to_bv 64 e2.
Proof. intros e1 e2 H. rewrite <- (Z_to_bv_mod64 e1), <- (Z_to_bv_mod64 e2), H. reflexivity. Qed.

Ltac word_eq_tac :=
  first [ exact eq_refl
        | f_equal; lia
        | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
        | apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia ].
