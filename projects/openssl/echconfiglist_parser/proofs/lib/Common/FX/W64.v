(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia List Bool Uint63.
From stdpp.bitvector Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record w64 : Set := W64 { wtop : int; wlo : int }.

Definition wZ (w : w64) : Z := (to_Z (wtop w) mod 2) * 2 ^ 63 + to_Z (wlo w).
Definition wS (w : w64) : Z := to_Z (wlo w) - (to_Z (wtop w) mod 2) * 2 ^ 63.
Definition wbv (w : w64) : bv 64 := Z_to_bv 64 (wZ w).

(* [comment removed for export] *)
Definition w_nf (w : w64) : Prop := to_Z (wtop w) < 2.
Definition w_norm (w : w64) : w64 :=
  match w with W64 t l => W64 (t land 1) l end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Ops.
Local Open Scope uint63_scope.

Definition w_zero : w64 := W64 0 0.
Definition w_one : w64 := W64 0 1.
Definition w_ones : w64 := W64 1 0x7FFFFFFFFFFFFFFF.
Definition w_of_int (i : int) : w64 := W64 0 i.
Definition w_of_Z (z : Z) : w64 :=
  W64 (of_Z ((z / 2 ^ 63) mod 2)) (of_Z z).
Definition w_of_bv (b : bv 64) : w64 := w_of_Z (bv_unsigned b).
Definition w_of_bool (b : bool) : w64 := if b then w_one else w_zero.

(* [comment removed for export] *)
Definition w_eqb (a b : w64) : bool :=
  match a, b with
  | W64 ta la, W64 tb lb =>
      if la =? lb then ((ta lxor tb) land 1) =? 0 else false
  end.

Definition w_ltu (a b : w64) : bool :=
  match a, b with
  | W64 ta la, W64 tb lb =>
      let sa := ta land 1 in
      let sb := tb land 1 in
      if sa =? sb then la <? lb else sa <? sb
  end.

Definition w_lts (a b : w64) : bool :=
  match a, b with
  | W64 ta la, W64 tb lb =>
      let sa := ta land 1 in
      let sb := tb land 1 in
      if sa =? sb then la <? lb else sb <? sa
  end.

(* [comment removed for export] *)
Definition w_add (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 tb lb =>
      let lo := la + lb in
      if lo <? la then W64 (ta lxor tb lxor 1) lo else W64 (ta lxor tb) lo
  end.

Definition w_sub (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 tb lb =>
      if la <? lb then W64 (ta lxor tb lxor 1) (la - lb)
      else W64 (ta lxor tb) (la - lb)
  end.

Definition w_and (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 tb lb => W64 (ta land tb) (la land lb)
  end.

Definition w_or (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 tb lb => W64 (ta lor tb) (la lor lb)
  end.

Definition w_xor (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 tb lb => W64 (ta lxor tb) (la lxor lb)
  end.

(* [comment removed for export] *)
Definition w_sll (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 _ lb =>
      let k := lb land 63 in
      if k =? 0 then a else W64 ((la >> (63 - k)) land 1) (la << k)
  end.

Definition w_srl (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 _ lb =>
      let k := lb land 63 in
      if k =? 0 then a else W64 0 ((la >> k) + ((ta land 1) << (63 - k)))
  end.

Definition w_sra (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 _ lb =>
      let k := lb land 63 in
      if (ta land 1) =? 0 then W64 0 (la >> k)
      else W64 1 ((la >> k) + (0x7FFFFFFFFFFFFFFF << (63 - k)))
  end.

Definition w_slt (a b : w64) : w64 := if w_lts a b then w_one else w_zero.
Definition w_sltu (a b : w64) : w64 := if w_ltu a b then w_one else w_zero.

Definition w_alu (op : aluop) (a b : w64) : w64 :=
  match op with
  | ALU_ADD => w_add a b
  | ALU_SUB => w_sub a b
  | ALU_SLL => w_sll a b
  | ALU_SLT => w_slt a b
  | ALU_SLTU => w_sltu a b
  | ALU_XOR => w_xor a b
  | ALU_SRL => w_srl a b
  | ALU_SRA => w_sra a b
  | ALU_OR => w_or a b
  | ALU_AND => w_and a b
  end.

End Ops.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma i63_wB : wB = 2 ^ 63.
Proof. reflexivity. Qed.

Lemma i63_range (x : int) : 0 <= to_Z x < 2 ^ 63.
Proof. rewrite <- i63_wB. apply to_Z_bounded. Qed.

Lemma i63_land_ones (x m : int) (n : Z) :
  to_Z m = Z.ones n -> 0 <= n -> to_Z (x land m) = to_Z x mod 2 ^ n.
Proof. intros Hm Hn. rewrite land_spec', Hm, Z.land_ones by exact Hn. reflexivity. Qed.

Lemma i63_land1 (x : int) : to_Z (x land 1) = to_Z x mod 2.
Proof. apply (i63_land_ones x 1%uint63 1); [reflexivity | lia]. Qed.

Lemma Z_mod2_bit0 a : a mod 2 = Z.b2z (Z.testbit a 0).
Proof. symmetry. apply Z.bit0_mod. Qed.

Lemma i63_lxor_mod2 (x y : int) :
  to_Z (x lxor y) mod 2 = (to_Z x mod 2 + to_Z y mod 2) mod 2.
Proof.
  rewrite lxor_spec'. rewrite !Z_mod2_bit0, Z.lxor_spec.
  destruct (Z.testbit (to_Z x) 0), (Z.testbit (to_Z y) 0); reflexivity.
Qed.

Lemma i63_land_mod2 (x y : int) :
  to_Z (x land y) mod 2 = (to_Z x mod 2) * (to_Z y mod 2).
Proof.
  rewrite land_spec'. rewrite !Z_mod2_bit0, Z.land_spec.
  destruct (Z.testbit (to_Z x) 0), (Z.testbit (to_Z y) 0); reflexivity.
Qed.

Lemma i63_lor_mod2 (x y : int) :
  to_Z (x lor y) mod 2 =
  to_Z x mod 2 + to_Z y mod 2 - (to_Z x mod 2) * (to_Z y mod 2).
Proof.
  rewrite lor_spec'. rewrite !Z_mod2_bit0, Z.lor_spec.
  destruct (Z.testbit (to_Z x) 0), (Z.testbit (to_Z y) 0); reflexivity.
Qed.

Lemma Z_mod2_cases a : a mod 2 = 0 \/ a mod 2 = 1.
Proof. pose proof (Z.mod_pos_bound a 2 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wZ_W64 t l : wZ (W64 t l) = (to_Z t mod 2) * 2 ^ 63 + to_Z l.
Proof. reflexivity. Qed.

Lemma wS_W64 t l : wS (W64 t l) = to_Z l - (to_Z t mod 2) * 2 ^ 63.
Proof. reflexivity. Qed.

Lemma wZ_range w : 0 <= wZ w < 2 ^ 64.
Proof.
  destruct w as [t l]. rewrite wZ_W64.
  pose proof (i63_range l). destruct (Z_mod2_cases (to_Z t)) as [->| ->]; lia.
Qed.

Lemma wS_range w : - 2 ^ 63 <= wS w < 2 ^ 63.
Proof.
  destruct w as [t l]. rewrite wS_W64.
  pose proof (i63_range l). destruct (Z_mod2_cases (to_Z t)) as [->| ->]; lia.
Qed.

Lemma wS_wZ w : wS w = wZ w - (to_Z (wtop w) mod 2) * 2 ^ 64.
Proof. destruct w as [t l]. rewrite wS_W64, wZ_W64. cbn [wtop]. lia. Qed.

Lemma wS_swrap w : wS w = bv_swrap 64 (wZ w).
Proof.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 `div` 2) with (2 ^ 63). change (2 ^ Z.of_N 64) with (2 ^ 64).
  destruct w as [t l]. rewrite wS_W64, wZ_W64.
  pose proof (i63_range l). destruct (Z_mod2_cases (to_Z t)) as [->| ->].
  - rewrite Z.mod_small by lia. lia.
  - replace (1 * 2 ^ 63 + to_Z l + 2 ^ 63) with (to_Z l + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma wbv_unsigned w : bv_unsigned (wbv w) = wZ w.
Proof.
  unfold wbv. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). apply wZ_range.
Qed.

Lemma wbv_signed w : bv_signed (wbv w) = wS w.
Proof. unfold bv_signed. rewrite wbv_unsigned. symmetry. apply wS_swrap. Qed.

Lemma wbv_eq_iff a b : wbv a = wbv b <-> wZ a = wZ b.
Proof.
  split; intros H.
  - rewrite <- !wbv_unsigned, H. reflexivity.
  - apply bv_eq. rewrite !wbv_unsigned. exact H.
Qed.

Lemma wbv_of_wZ w z : wZ w = z mod 2 ^ 64 -> wbv w = Z_to_bv 64 z.
Proof.
  intros H. apply bv_eq. rewrite wbv_unsigned, Z_to_bv_unsigned. exact H.
Qed.

Lemma w_nf_eq a b : w_nf a -> w_nf b -> wZ a = wZ b -> a = b.
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_nf. cbn [wtop]. rewrite !wZ_W64.
  intros Ha Hb H. pose proof (i63_range ta). pose proof (i63_range tb).
  pose proof (i63_range la). pose proof (i63_range lb).
  rewrite (Z.mod_small (to_Z ta)), (Z.mod_small (to_Z tb)) in H by lia.
  assert (to_Z ta = to_Z tb /\ to_Z la = to_Z lb) as [E1 E2] by lia.
  apply to_Z_inj in E1, E2. subst. reflexivity.
Qed.

Lemma w_norm_nf w : w_nf (w_norm w).
Proof.
  destruct w as [t l]. unfold w_nf. cbn [w_norm wtop]. rewrite i63_land1.
  pose proof (Z.mod_pos_bound (to_Z t) 2 ltac:(lia)). lia.
Qed.

Lemma wZ_w_norm w : wZ (w_norm w) = wZ w.
Proof.
  destruct w as [t l]. cbn [w_norm]. rewrite !wZ_W64, i63_land1.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma wbv_w_norm w : wbv (w_norm w) = wbv w.
Proof. apply wbv_eq_iff, wZ_w_norm. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Zpar (x : Z) : Z := x mod 2.

Local Ltac w64_tops :=
  repeat match goal with
  | |- context [to_Z ?t mod 2] =>
      is_var t;
      let E := fresh "Etop" in
      destruct (Z_mod2_cases (to_Z t)) as [E|E]; rewrite !E in *;
      change (to_Z t mod 2) with (Zpar (to_Z t)) in E
  | H : context [to_Z ?t mod 2] |- _ =>
      is_var t;
      let E := fresh "Etop" in
      destruct (Z_mod2_cases (to_Z t)) as [E|E]; rewrite !E in *;
      change (to_Z t mod 2) with (Zpar (to_Z t)) in E
  end.

Local Ltac w64_top t :=
  let E := fresh "Etop" in
  destruct (Z_mod2_cases (to_Z t)) as [E|E]; rewrite !E in *;
  change (to_Z t mod 2) with (Zpar (to_Z t)) in E.

Local Ltac w64_ranges :=
  repeat match goal with
  | |- context [to_Z ?x] =>
      lazymatch goal with
      | _ : 0 <= to_Z x < 2 ^ 63 |- _ => fail
      | _ => pose proof (i63_range x)
      end
  | H : context [to_Z ?x] |- _ =>
      lazymatch goal with
      | _ : 0 <= to_Z x < 2 ^ 63 |- _ => fail
      | _ => pose proof (i63_range x)
      end
  end.

Local Ltac zlia := unfold Zpar in *; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wZ_w_zero : wZ w_zero = 0.
Proof. reflexivity. Qed.
Lemma wZ_w_one : wZ w_one = 1.
Proof. reflexivity. Qed.
Lemma wZ_w_ones : wZ w_ones = 2 ^ 64 - 1.
Proof. reflexivity. Qed.
Lemma wZ_w_of_int i : wZ (w_of_int i) = to_Z i.
Proof. reflexivity. Qed.

Lemma wZ_w_of_Z z : wZ (w_of_Z z) = z mod 2 ^ 64.
Proof.
  unfold w_of_Z. rewrite wZ_W64, !of_Z_spec, i63_wB.
  pose proof (Z.mod_pos_bound (z / 2 ^ 63) 2 ltac:(lia)).
  rewrite (Z.mod_small ((z / 2 ^ 63) mod 2) (2 ^ 63)) by lia.
  rewrite Z.mod_mod by lia.
  change (2 ^ 64) with (2 ^ 63 * 2). rewrite Z.rem_mul_r by lia. lia.
Qed.

Lemma w_of_Z_nf z : w_nf (w_of_Z z).
Proof.
  unfold w_nf, w_of_Z. cbn [wtop]. rewrite of_Z_spec, i63_wB.
  pose proof (Z.mod_pos_bound (z / 2 ^ 63) 2 ltac:(lia)).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma wbv_w_zero : wbv w_zero = w0.
Proof. apply bv_eq. rewrite wbv_unsigned. reflexivity. Qed.
Lemma wbv_w_one : wbv w_one = w1.
Proof. apply bv_eq. rewrite wbv_unsigned. reflexivity. Qed.
Lemma wbv_w_ones : wbv w_ones = Z_to_bv 64 (-1).
Proof. apply bv_eq. rewrite wbv_unsigned. reflexivity. Qed.
Lemma wbv_w_of_Z z : wbv (w_of_Z z) = Z_to_bv 64 z.
Proof. apply wbv_of_wZ, wZ_w_of_Z. Qed.
Lemma wbv_w_of_int i : wbv (w_of_int i) = Z_to_bv 64 (to_Z i).
Proof. reflexivity. Qed.

Lemma wZ_w_of_bv b : wZ (w_of_bv b) = bv_unsigned b.
Proof.
  unfold w_of_bv. rewrite wZ_w_of_Z. apply Z.mod_small.
  pose proof (bv_unsigned_in_range 64 b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in H. exact H.
Qed.

Lemma wbv_w_of_bv b : wbv (w_of_bv b) = b.
Proof. apply bv_eq. rewrite wbv_unsigned. apply wZ_w_of_bv. Qed.

Lemma w_of_bv_wbv w : w_of_bv (wbv w) = w_norm w.
Proof.
  apply w_nf_eq; [apply w_of_Z_nf | apply w_norm_nf |].
  rewrite wZ_w_of_bv, wbv_unsigned, wZ_w_norm. reflexivity.
Qed.

Lemma wZ_w_of_bool b : wZ (w_of_bool b) = if b then 1 else 0.
Proof. destruct b; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma w_eqb_spec a b : w_eqb a b = (wZ a =? wZ b).
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_eqb. rewrite !wZ_W64.
  w64_ranges.
  destruct (eqbP la lb) as [El|El].
  - destruct (eqbP ((ta lxor tb) land 1) 0) as [Et|Et];
      rewrite i63_land1, i63_lxor_mod2, to_Z_0 in Et;
      symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; w64_tops;
      cbn in Et; lia.
  - symmetry. apply Z.eqb_neq. w64_tops; lia.
Qed.

Lemma w_eqb_true_iff a b : w_eqb a b = true <-> wZ a = wZ b.
Proof. rewrite w_eqb_spec. apply Z.eqb_eq. Qed.

Lemma w_eqb_false_iff a b : w_eqb a b = false <-> wZ a <> wZ b.
Proof. rewrite w_eqb_spec. apply Z.eqb_neq. Qed.

Lemma w_eqb_bv a b : w_eqb a b = bv_eqb (wbv a) (wbv b).
Proof. unfold bv_eqb. rewrite !wbv_unsigned. apply w_eqb_spec. Qed.

Lemma w_eqb_true_bv a b : w_eqb a b = true <-> wbv a = wbv b.
Proof. rewrite w_eqb_true_iff. symmetry. apply wbv_eq_iff. Qed.

Lemma w_eqb_refl a : w_eqb a a = true.
Proof. apply w_eqb_true_iff. reflexivity. Qed.

Lemma w_ltu_spec a b : w_ltu a b = (wZ a <? wZ b).
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_ltu. cbv zeta. rewrite !wZ_W64.
  w64_ranges.
  destruct (eqbP (ta land 1) (tb land 1)) as [Et|Et]; rewrite !i63_land1 in Et.
  - rewrite Et. destruct (ltbP la lb); symmetry;
      [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
  - destruct (ltbP (ta land 1) (tb land 1)) as [Hl|Hl]; rewrite !i63_land1 in Hl;
      symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; w64_tops; lia.
Qed.

Lemma w_lts_spec a b : w_lts a b = (wS a <? wS b).
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_lts. cbv zeta. rewrite !wS_W64.
  w64_ranges.
  destruct (eqbP (ta land 1) (tb land 1)) as [Et|Et]; rewrite !i63_land1 in Et.
  - rewrite Et. destruct (ltbP la lb); symmetry;
      [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
  - destruct (ltbP (tb land 1) (ta land 1)) as [Hl|Hl]; rewrite !i63_land1 in Hl;
      symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; w64_tops; lia.
Qed.

Lemma w_ltu_bv a b : w_ltu a b = bv_ltu (wbv a) (wbv b).
Proof. unfold bv_ltu. rewrite !wbv_unsigned. apply w_ltu_spec. Qed.

Lemma w_lts_bv a b : w_lts a b = bv_lts (wbv a) (wbv b).
Proof. unfold bv_lts. rewrite !wbv_signed. apply w_lts_spec. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wZ_testbit t l i :
  0 <= i ->
  Z.testbit (wZ (W64 t l)) i =
  if i <? 63 then Z.testbit (to_Z l) i
  else if i =? 63 then Z.testbit (to_Z t) 0 else false.
Proof.
  intros Hi. rewrite wZ_W64. pose proof (i63_range l) as Hl.
  destruct (Z.ltb_spec i 63) as [Hlt|Hge].
  - rewrite <- (Z.mod_pow2_bits_low _ 63 i) by lia.
    rewrite Z.add_comm, Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
  - replace i with ((i - 63) + 63) at 1 by lia.
    rewrite <- Z.div_pow2_bits by lia.
    rewrite Z.add_comm, Z.div_add by lia. rewrite Z.div_small by lia.
    rewrite Z.add_0_l.
    destruct (Z.eqb_spec i 63) as [->|Hne].
    + change (63 - 63) with 0. change 2 with (2 ^ 1) at 1.
      apply Z.mod_pow2_bits_low. lia.
    + change 2 with (2 ^ 1) at 1. apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma w_bitop_spec (g : int -> int -> int) (f : Z -> Z -> Z)
    (fb : bool -> bool -> bool) :
  (forall x y, to_Z (g x y) = f (to_Z x) (to_Z y)) ->
  (forall a b i, Z.testbit (f a b) i = fb (Z.testbit a i) (Z.testbit b i)) ->
  fb false false = false ->
  forall ta la tb lb,
    wZ (W64 (g ta tb) (g la lb)) = f (wZ (W64 ta la)) (wZ (W64 tb lb)).
Proof.
  intros Hg Hf Hff ta la tb lb. apply Z.bits_inj'. intros i Hi.
  rewrite Hf, !wZ_testbit by exact Hi. rewrite !Hg, !Hf.
  destruct (i <? 63); [reflexivity|]. destruct (i =? 63); [reflexivity|].
  symmetry. exact Hff.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wZ_w_add a b : wZ (w_add a b) = (wZ a + wZ b) mod 2 ^ 64.
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_add. cbv zeta.
  destruct (ltbP (la + lb) la) as [H|H]; rewrite add_spec, i63_wB in H;
    rewrite !wZ_W64, ?i63_lxor_mod2, add_spec, i63_wB, ?to_Z_1;
    w64_ranges; w64_tops; zlia.
Qed.

Lemma wZ_w_sub a b : wZ (w_sub a b) = (wZ a - wZ b) mod 2 ^ 64.
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_sub.
  destruct (ltbP la lb) as [H|H];
    rewrite !wZ_W64, ?i63_lxor_mod2, sub_spec, i63_wB, ?to_Z_1;
    w64_ranges; w64_tops; zlia.
Qed.

Lemma wZ_w_and a b : wZ (w_and a b) = Z.land (wZ a) (wZ b).
Proof.
  destruct a as [ta la], b as [tb lb].
  apply (w_bitop_spec Uint63.land Z.land andb land_spec' Z.land_spec eq_refl).
Qed.

Lemma wZ_w_or a b : wZ (w_or a b) = Z.lor (wZ a) (wZ b).
Proof.
  destruct a as [ta la], b as [tb lb].
  apply (w_bitop_spec Uint63.lor Z.lor orb lor_spec' Z.lor_spec eq_refl).
Qed.

Lemma wZ_w_xor a b : wZ (w_xor a b) = Z.lxor (wZ a) (wZ b).
Proof.
  destruct a as [ta la], b as [tb lb].
  apply (w_bitop_spec Uint63.lxor Z.lxor xorb lxor_spec' Z.lxor_spec eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Zpow2_split k : 0 <= k <= 63 -> 2 ^ k * 2 ^ (63 - k) = 2 ^ 63.
Proof. intros H. rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma Zsll_arith t l k :
  0 <= l < 2 ^ 63 -> 0 <= t -> 1 <= k <= 63 ->
  ((t * 2 ^ 63 + l) * 2 ^ k) mod 2 ^ 64 =
  ((l / 2 ^ (63 - k)) mod 2) * 2 ^ 63 + (l * 2 ^ k) mod 2 ^ 63.
Proof.
  intros Hl Ht Hk.
  pose proof (Zpow2_split k ltac:(lia)) as HPQ.
  assert (HP : 2 ^ k = 2 * 2 ^ (k - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  assert (HP' : 0 < 2 ^ (k - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (HQ : 0 < 2 ^ (63 - k)) by (apply Z.pow_pos_nonneg; lia).
  set (P' := 2 ^ (k - 1)) in *. set (Q := 2 ^ (63 - k)) in *.
  rewrite HP in *.
  pose proof (Z.div_mod l Q ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound l Q ltac:(lia)) as Hr.
  assert (Hq0 : 0 <= l / Q) by (apply Z.div_pos; lia).
  set (q := l / Q) in *. set (r := l mod Q) in *.
  pose proof (Z.div_mod q 2 ltac:(lia)) as Hdm2.
  pose proof (Z.mod_pos_bound q 2 ltac:(lia)) as Hqm.
  set (q2 := q / 2) in *. set (qm := q mod 2) in *.
  assert (Hrb : 0 <= r * (2 * P') < 2 ^ 63).
  { split; [apply Z.mul_nonneg_nonneg; lia|].
    rewrite <- HPQ. rewrite (Z.mul_comm (2 * P') Q).
    apply Z.mul_lt_mono_pos_r; lia. }
  assert (Hlow : (l * (2 * P')) mod 2 ^ 63 = r * (2 * P')).
  { symmetry. apply (Z.mod_unique_pos _ _ q); [exact Hrb|].
    rewrite <- HPQ. rewrite Hdm at 1. ring. }
  rewrite Hlow.
  symmetry. apply (Z.mod_unique_pos _ _ (t * P' + q2)); [lia|].
  rewrite Hdm at 1. rewrite Hdm2.
  change (2 ^ 64) with (2 * 2 ^ 63). rewrite <- HPQ. ring.
Qed.

Lemma Zsrl_arith t l k :
  0 <= l < 2 ^ 63 -> 0 <= t <= 1 -> 1 <= k <= 63 ->
  (t * 2 ^ 63 + l) / 2 ^ k = l / 2 ^ k + (t * 2 ^ (63 - k)) mod 2 ^ 63
  /\ l / 2 ^ k + (t * 2 ^ (63 - k)) mod 2 ^ 63 < 2 ^ 63.
Proof.
  intros Hl Ht Hk.
  pose proof (Zpow2_split k ltac:(lia)) as HPQ.
  assert (HP : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (HQ : 0 < 2 ^ (63 - k)) by (apply Z.pow_pos_nonneg; lia).
  assert (HP2 : 2 <= 2 ^ k).
  { change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; lia. }
  set (P := 2 ^ k) in *. set (Q := 2 ^ (63 - k)) in *.
  assert (HQlt : Q < 2 ^ 63) by nia.
  assert (HtQ : (t * Q) mod 2 ^ 63 = t * Q) by (apply Z.mod_small; nia).
  rewrite HtQ.
  assert (Hdiv : l / P < Q).
  { apply Z.div_lt_upper_bound; lia. }
  assert (0 <= l / P) by (apply Z.div_pos; lia).
  split; [|nia].
  replace (t * 2 ^ 63 + l) with (l + (t * Q) * P) by (rewrite <- HPQ; ring).
  rewrite Z.div_add by lia. reflexivity.
Qed.

Lemma Zsra_arith l k :
  0 <= l < 2 ^ 63 -> 0 <= k <= 63 ->
  ((l - 2 ^ 63) / 2 ^ k) mod 2 ^ 64 =
  1 * 2 ^ 63 + (l / 2 ^ k + ((2 ^ 63 - 1) * 2 ^ (63 - k)) mod 2 ^ 63)
  /\ l / 2 ^ k + ((2 ^ 63 - 1) * 2 ^ (63 - k)) mod 2 ^ 63 < 2 ^ 63.
Proof.
  intros Hl Hk.
  pose proof (Zpow2_split k ltac:(lia)) as HPQ.
  assert (HP : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  assert (HQ : 0 < 2 ^ (63 - k)) by (apply Z.pow_pos_nonneg; lia).
  set (P := 2 ^ k) in *. set (Q := 2 ^ (63 - k)) in *.
  assert (Hones : ((2 ^ 63 - 1) * Q) mod 2 ^ 63 = 2 ^ 63 - Q).
  { symmetry. apply (Z.mod_unique_pos _ _ (Q - 1)); [nia|ring]. }
  rewrite Hones.
  assert (Hdiv : l / P < Q) by (apply Z.div_lt_upper_bound; lia).
  assert (0 <= l / P) by (apply Z.div_pos; lia).
  split; [|lia].
  replace (l - 2 ^ 63) with (l + (- Q) * P) by (rewrite <- HPQ; ring).
  rewrite Z.div_add by lia.
  symmetry. apply (Z.mod_unique_pos _ _ (-1)); lia.
Qed.

(* [comment removed for export] *)
Lemma i63_shamt6 (lb : int) : to_Z (lb land 63) = to_Z lb mod 64.
Proof. apply (i63_land_ones lb 63%uint63 6); [reflexivity | lia]. Qed.

Lemma wZ_mod64 t l : wZ (W64 t l) mod 64 = to_Z l mod 64.
Proof.
  rewrite wZ_W64. change (2 ^ 63) with (2 ^ 57 * 64).
  rewrite Z.mul_assoc, Z.add_comm, Z.mod_add by lia. reflexivity.
Qed.

Lemma i63_sub_small (c k : int) :
  to_Z k <= to_Z c -> to_Z (c - k) = to_Z c - to_Z k.
Proof.
  intros H. rewrite sub_spec, i63_wB. apply Z.mod_small.
  pose proof (i63_range c). pose proof (i63_range k). lia.
Qed.

Lemma wZ_w_sll a b : wZ (w_sll a b) = (wZ a * 2 ^ (wZ b mod 64)) mod 2 ^ 64.
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_sll. cbv zeta.
  rewrite wZ_mod64, <- i63_shamt6.
  pose proof (Z.mod_pos_bound (to_Z lb) 64 ltac:(lia)) as Hk.
  rewrite <- i63_shamt6 in Hk.
  destruct (eqbP (lb land 63) 0) as [E|E]; rewrite to_Z_0 in E.
  - rewrite E, Z.pow_0_r, Z.mul_1_r. symmetry. apply Z.mod_small, wZ_range.
  - set (k := (lb land 63)%uint63) in *.
    assert (Hk63 : to_Z (63 - k) = 63 - to_Z k).
    { apply i63_sub_small. change (to_Z 63) with 63. lia. }
    rewrite !wZ_W64, i63_land1, lsr_spec, lsl_spec, i63_wB, Hk63.
    rewrite Z.mod_mod by lia.
    symmetry. apply Zsll_arith; [apply i63_range | | lia].
    apply Z.mod_pos_bound. lia.
Qed.

Lemma wZ_w_srl a b : wZ (w_srl a b) = wZ a / 2 ^ (wZ b mod 64).
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_srl. cbv zeta.
  rewrite wZ_mod64, <- i63_shamt6.
  pose proof (Z.mod_pos_bound (to_Z lb) 64 ltac:(lia)) as Hk.
  rewrite <- i63_shamt6 in Hk.
  destruct (eqbP (lb land 63) 0) as [E|E]; rewrite to_Z_0 in E.
  - rewrite E, Z.pow_0_r, Z.div_1_r. reflexivity.
  - set (k := (lb land 63)%uint63) in *.
    assert (Hk63 : to_Z (63 - k) = 63 - to_Z k).
    { apply i63_sub_small. change (to_Z 63) with 63. lia. }
    rewrite !wZ_W64.
    change (to_Z 0 mod 2) with 0. rewrite Z.mul_0_l, Z.add_0_l.
    rewrite add_spec, lsr_spec, lsl_spec, i63_wB, Hk63, i63_land1.
    pose proof (Z.mod_pos_bound (to_Z ta) 2 ltac:(lia)) as Ht.
    destruct (Zsrl_arith (to_Z ta mod 2) (to_Z la) (to_Z k)) as [H1 H2];
      [apply i63_range | lia | lia |].
    rewrite H1. apply Z.mod_small. split; [|exact H2].
    apply Z.add_nonneg_nonneg; [apply Z.div_pos; [apply i63_range|]|].
    + apply Z.pow_pos_nonneg; lia.
    + apply Z.mod_pos_bound. lia.
Qed.

Lemma wZ_w_sra a b : wZ (w_sra a b) = (wS a / 2 ^ (wZ b mod 64)) mod 2 ^ 64.
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_sra. cbv zeta.
  rewrite wZ_mod64, <- i63_shamt6.
  pose proof (Z.mod_pos_bound (to_Z lb) 64 ltac:(lia)) as Hk.
  rewrite <- i63_shamt6 in Hk.
  set (k := (lb land 63)%uint63) in *.
  pose proof (i63_range la) as Hla.
  assert (HP : 0 < 2 ^ to_Z k) by (apply Z.pow_pos_nonneg; lia).
  rewrite wS_W64.
  destruct (eqbP (ta land 1) 0) as [E|E]; rewrite i63_land1, to_Z_0 in E.
  - rewrite E, Z.mul_0_l, Z.sub_0_r, wZ_W64, lsr_spec.
    change (to_Z 0 mod 2) with 0. rewrite Z.mul_0_l, Z.add_0_l.
    symmetry. apply Z.mod_small.
    split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; nia.
  - assert (Et : to_Z ta mod 2 = 1)
      by (pose proof (Z.mod_pos_bound (to_Z ta) 2 ltac:(lia)); lia).
    rewrite Et, Z.mul_1_l.
    assert (Hk63 : to_Z (63 - k) = 63 - to_Z k).
    { apply i63_sub_small. change (to_Z 63) with 63. lia. }
    rewrite wZ_W64. change (to_Z 1 mod 2) with 1.
    rewrite add_spec, lsr_spec, lsl_spec, i63_wB, Hk63.
    change (to_Z 9223372036854775807) with (2 ^ 63 - 1).
    destruct (Zsra_arith (to_Z la) (to_Z k)) as [H1 H2]; [lia | lia |].
    rewrite H1. f_equal. apply Z.mod_small. split; [|exact H2].
    apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia|].
    apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_wrap64 z : bv_wrap 64 z = z mod 2 ^ 64.
Proof. reflexivity. Qed.

Lemma bv_shamt6 (b : bv 64) :
  bv_unsigned (bv_and b (Z_to_bv 64 63)) = bv_unsigned b mod 64.
Proof.
  rewrite bv_and_unsigned. change (bv_unsigned (Z_to_bv 64 63)) with (Z.ones 6).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma wbv_w_add a b : wbv (w_add a b) = (wbv a + wbv b)%bv.
Proof.
  apply bv_eq. rewrite bv_add_unsigned, !wbv_unsigned, bv_wrap64. apply wZ_w_add.
Qed.

Lemma wbv_w_sub a b : wbv (w_sub a b) = (wbv a - wbv b)%bv.
Proof.
  apply bv_eq. rewrite bv_sub_unsigned, !wbv_unsigned, bv_wrap64. apply wZ_w_sub.
Qed.

Lemma wbv_w_and a b : wbv (w_and a b) = bv_and (wbv a) (wbv b).
Proof. apply bv_eq. rewrite bv_and_unsigned, !wbv_unsigned. apply wZ_w_and. Qed.

Lemma wbv_w_or a b : wbv (w_or a b) = bv_or (wbv a) (wbv b).
Proof. apply bv_eq. rewrite bv_or_unsigned, !wbv_unsigned. apply wZ_w_or. Qed.

Lemma wbv_w_xor a b : wbv (w_xor a b) = bv_xor (wbv a) (wbv b).
Proof. apply bv_eq. rewrite bv_xor_unsigned, !wbv_unsigned. apply wZ_w_xor. Qed.

Lemma wbv_w_sll a b :
  wbv (w_sll a b) = (wbv a ≪ bv_and (wbv b) (Z_to_bv 64 63))%bv.
Proof.
  apply bv_eq. rewrite bv_shiftl_unsigned, bv_shamt6, !wbv_unsigned, bv_wrap64.
  rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia). apply wZ_w_sll.
Qed.

Lemma wbv_w_srl a b :
  wbv (w_srl a b) = (wbv a ≫ bv_and (wbv b) (Z_to_bv 64 63))%bv.
Proof.
  apply bv_eq. rewrite bv_shiftr_unsigned, bv_shamt6, !wbv_unsigned.
  rewrite Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia). apply wZ_w_srl.
Qed.

Lemma wbv_w_sra a b :
  wbv (w_sra a b) = bv_ashiftr (wbv a) (bv_and (wbv b) (Z_to_bv 64 63)).
Proof.
  apply bv_eq. rewrite bv_ashiftr_unsigned, bv_shamt6, wbv_signed, !wbv_unsigned.
  rewrite bv_wrap64.
  rewrite Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia). apply wZ_w_sra.
Qed.

Lemma wbv_w_slt a b :
  wbv (w_slt a b) = if bv_lts (wbv a) (wbv b) then Z_to_bv 64 1 else Z_to_bv 64 0.
Proof. unfold w_slt. rewrite w_lts_bv. destruct (bv_lts _ _); reflexivity. Qed.

Lemma wbv_w_sltu a b :
  wbv (w_sltu a b) = if bv_ltu (wbv a) (wbv b) then Z_to_bv 64 1 else Z_to_bv 64 0.
Proof. unfold w_sltu. rewrite w_ltu_bv. destruct (bv_ltu _ _); reflexivity. Qed.

Theorem w_alu_spec op a b : wbv (w_alu op a b) = alu64 op (wbv a) (wbv b).
Proof.
  destruct op; unfold alu64, alu; cbn [w_alu].
  - apply wbv_w_add.
  - apply wbv_w_sub.
  - apply wbv_w_sll.
  - apply wbv_w_slt.
  - apply wbv_w_sltu.
  - apply wbv_w_xor.
  - apply wbv_w_srl.
  - apply wbv_w_sra.
  - apply wbv_w_or.
  - apply wbv_w_and.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Ext.
Local Open Scope uint63_scope.

(* [comment removed for export] *)
Local Abbreviation sx8 x :=
  (if x <? 0x80 then W64 0 x else W64 1 (x + 0x7FFFFFFFFFFFFF00)) (only parsing).
Local Abbreviation sx16 x :=
  (if x <? 0x8000 then W64 0 x else W64 1 (x + 0x7FFFFFFFFFFF0000)) (only parsing).
Local Abbreviation sx32 x :=
  (if x <? 0x80000000 then W64 0 x else W64 1 (x + 0x7FFFFFFF00000000)) (only parsing).

Definition w_sext8 (w : w64) : w64 :=
  match w with W64 _ l => let x := l land 0xFF in sx8 x end.
Definition w_sext16 (w : w64) : w64 :=
  match w with W64 _ l => let x := l land 0xFFFF in sx16 x end.
Definition w_sext32 (w : w64) : w64 :=
  match w with W64 _ l => let x := l land 0xFFFFFFFF in sx32 x end.
Definition w_zext8 (w : w64) : w64 :=
  match w with W64 _ l => W64 0 (l land 0xFF) end.
Definition w_zext16 (w : w64) : w64 :=
  match w with W64 _ l => W64 0 (l land 0xFFFF) end.
Definition w_zext32 (w : w64) : w64 :=
  match w with W64 _ l => W64 0 (l land 0xFFFFFFFF) end.

(* [comment removed for export] *)
Definition w_addw (a b : w64) : w64 :=
  match a, b with
  | W64 _ la, W64 _ lb => let x := (la + lb) land 0xFFFFFFFF in sx32 x
  end.
Definition w_subw (a b : w64) : w64 :=
  match a, b with
  | W64 _ la, W64 _ lb => let x := (la - lb) land 0xFFFFFFFF in sx32 x
  end.
Definition w_sllw (a b : w64) : w64 :=
  match a, b with
  | W64 _ la, W64 _ lb =>
      let x := (la << (lb land 31)) land 0xFFFFFFFF in sx32 x
  end.
Definition w_srlw (a b : w64) : w64 :=
  match a, b with
  | W64 _ la, W64 _ lb =>
      let x := (la land 0xFFFFFFFF) >> (lb land 31) in sx32 x
  end.
Definition w_sraw (a b : w64) : w64 :=
  match b with
  | W64 _ lb => w_sra (w_sext32 a) (W64 0 (lb land 31))
  end.

Definition w_alu32 (op : aluop) (a b : w64) : w64 :=
  match op with
  | ALU_ADD => w_addw a b
  | ALU_SUB => w_subw a b
  | ALU_SLL => w_sllw a b
  | ALU_SRL => w_srlw a b
  | ALU_SRA => w_sraw a b
  | _ => (* [comment removed for export] *)
      w_of_bv (sext 64 (alu32 op (low32 (wbv a)) (low32 (wbv b))))
  end.

End Ext.

(* [comment removed for export] *)
Definition zsext (n : N) (z : Z) : Z := bv_wrap 64 (bv_swrap n z).

Lemma zsext8_eq z : zsext 8 z = ((z + 2 ^ 7) mod 2 ^ 8 - 2 ^ 7) mod 2 ^ 64.
Proof. reflexivity. Qed.
Lemma zsext16_eq z : zsext 16 z = ((z + 2 ^ 15) mod 2 ^ 16 - 2 ^ 15) mod 2 ^ 64.
Proof. reflexivity. Qed.
Lemma zsext32_eq z : zsext 32 z = ((z + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) mod 2 ^ 64.
Proof. reflexivity. Qed.

Lemma zsext_mod n z : zsext n (z mod 2 ^ Z.of_N n) = zsext n z.
Proof.
  unfold zsext. f_equal.
  change (z mod 2 ^ Z.of_N n) with (bv_wrap n z). apply bv_swrap_wrap.
Qed.

Lemma wZ_sx8 (x : int) :
  to_Z x < 2 ^ 8 ->
  wZ (if (x <? 0x80)%uint63 then W64 0 x
      else W64 1 (x + 0x7FFFFFFFFFFFFF00)%uint63) = zsext 8 (to_Z x).
Proof.
  intros Hx. rewrite zsext8_eq. pose proof (i63_range x).
  destruct (ltbP x 0x80%uint63) as [H1|H1];
    change (to_Z 128) with (2 ^ 7) in H1; rewrite wZ_W64.
  - change (to_Z 0 mod 2) with 0. zlia.
  - change (to_Z 1 mod 2) with 1. rewrite add_spec, i63_wB.
    change (to_Z 9223372036854775552) with (2 ^ 63 - 2 ^ 8). zlia.
Qed.

Lemma wZ_sx16 (x : int) :
  to_Z x < 2 ^ 16 ->
  wZ (if (x <? 0x8000)%uint63 then W64 0 x
      else W64 1 (x + 0x7FFFFFFFFFFF0000)%uint63) = zsext 16 (to_Z x).
Proof.
  intros Hx. rewrite zsext16_eq. pose proof (i63_range x).
  destruct (ltbP x 0x8000%uint63) as [H1|H1];
    change (to_Z 32768) with (2 ^ 15) in H1; rewrite wZ_W64.
  - change (to_Z 0 mod 2) with 0. zlia.
  - change (to_Z 1 mod 2) with 1. rewrite add_spec, i63_wB.
    change (to_Z 9223372036854710272) with (2 ^ 63 - 2 ^ 16). zlia.
Qed.

Lemma wZ_sx32 (x : int) :
  to_Z x < 2 ^ 32 ->
  wZ (if (x <? 0x80000000)%uint63 then W64 0 x
      else W64 1 (x + 0x7FFFFFFF00000000)%uint63) = zsext 32 (to_Z x).
Proof.
  intros Hx. rewrite zsext32_eq. pose proof (i63_range x).
  destruct (ltbP x 0x80000000%uint63) as [H1|H1];
    change (to_Z 2147483648) with (2 ^ 31) in H1; rewrite wZ_W64.
  - change (to_Z 0 mod 2) with 0. zlia.
  - change (to_Z 1 mod 2) with 1. rewrite add_spec, i63_wB.
    change (to_Z 9223372036854775807 - 0) with (2 ^ 63 - 1 - 0).
    change (to_Z 9223372032559808512) with (2 ^ 63 - 2 ^ 32). zlia.
Qed.

Lemma i63_mask8 x : to_Z (x land 0xFF) = to_Z x mod 2 ^ 8.
Proof. apply (i63_land_ones x 0xFF%uint63 8); [reflexivity | lia]. Qed.
Lemma i63_mask16 x : to_Z (x land 0xFFFF) = to_Z x mod 2 ^ 16.
Proof. apply (i63_land_ones x 0xFFFF%uint63 16); [reflexivity | lia]. Qed.
Lemma i63_mask32 x : to_Z (x land 0xFFFFFFFF) = to_Z x mod 2 ^ 32.
Proof. apply (i63_land_ones x 0xFFFFFFFF%uint63 32); [reflexivity | lia]. Qed.

(* [comment removed for export] *)
Lemma wZ_mod_pow2 t l n :
  0 <= n <= 63 -> wZ (W64 t l) mod 2 ^ n = to_Z l mod 2 ^ n.
Proof.
  intros Hn. rewrite wZ_W64.
  replace (2 ^ 63) with (2 ^ (63 - n) * 2 ^ n)
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_assoc, Z.add_comm, Z.mod_add; [reflexivity|].
  apply Z.pow_nonzero; lia.
Qed.

Lemma wZ_w_sext8 w : wZ (w_sext8 w) = zsext 8 (wZ w).
Proof.
  destruct w as [t l]. unfold w_sext8. cbv zeta.
  rewrite wZ_sx8; rewrite i63_mask8; [|apply Z.mod_pos_bound; lia].
  rewrite <- (wZ_mod_pow2 t l 8) by lia. apply (zsext_mod 8).
Qed.
Lemma wZ_w_sext16 w : wZ (w_sext16 w) = zsext 16 (wZ w).
Proof.
  destruct w as [t l]. unfold w_sext16. cbv zeta.
  rewrite wZ_sx16; rewrite i63_mask16; [|apply Z.mod_pos_bound; lia].
  rewrite <- (wZ_mod_pow2 t l 16) by lia. apply (zsext_mod 16).
Qed.
Lemma wZ_w_sext32 w : wZ (w_sext32 w) = zsext 32 (wZ w).
Proof.
  destruct w as [t l]. unfold w_sext32. cbv zeta.
  rewrite wZ_sx32; rewrite i63_mask32; [|apply Z.mod_pos_bound; lia].
  rewrite <- (wZ_mod_pow2 t l 32) by lia. apply (zsext_mod 32).
Qed.

Lemma wZ_w_zext8 w : wZ (w_zext8 w) = wZ w mod 2 ^ 8.
Proof.
  destruct w as [t l]. unfold w_zext8. rewrite wZ_mod_pow2 by lia.
  rewrite wZ_W64, i63_mask8. change (to_Z 0 mod 2) with 0. lia.
Qed.
Lemma wZ_w_zext16 w : wZ (w_zext16 w) = wZ w mod 2 ^ 16.
Proof.
  destruct w as [t l]. unfold w_zext16. rewrite wZ_mod_pow2 by lia.
  rewrite wZ_W64, i63_mask16. change (to_Z 0 mod 2) with 0. lia.
Qed.
Lemma wZ_w_zext32 w : wZ (w_zext32 w) = wZ w mod 2 ^ 32.
Proof.
  destruct w as [t l]. unfold w_zext32. rewrite wZ_mod_pow2 by lia.
  rewrite wZ_W64, i63_mask32. change (to_Z 0 mod 2) with 0. lia.
Qed.

(* [comment removed for export] *)
Lemma bv_sext64_extract_unsigned (n : N) (b : bv 64) :
  bv_unsigned (sext 64 (bv_extract 0 n b)) = zsext n (bv_unsigned b).
Proof.
  unfold sext. rewrite bv_sign_extend_unsigned. unfold bv_signed.
  rewrite bv_extract_unsigned, Z.shiftr_0_r. unfold zsext. f_equal.
  apply bv_swrap_wrap.
Qed.

Lemma bv_zext64_extract_unsigned (n : N) (b : bv 64) :
  (n <= 64)%N ->
  bv_unsigned (zext 64 (bv_extract 0 n b)) = bv_unsigned b mod 2 ^ Z.of_N n.
Proof.
  intros Hn. unfold zext. rewrite bv_zero_extend_unsigned by exact Hn.
  rewrite bv_extract_unsigned, Z.shiftr_0_r. reflexivity.
Qed.

Lemma wbv_w_sext8 w : wbv (w_sext8 w) = sext 64 (bv_extract 0 8 (wbv w)).
Proof.
  apply bv_eq. rewrite bv_sext64_extract_unsigned, !wbv_unsigned.
  apply wZ_w_sext8.
Qed.
Lemma wbv_w_sext16 w : wbv (w_sext16 w) = sext 64 (bv_extract 0 16 (wbv w)).
Proof.
  apply bv_eq. rewrite bv_sext64_extract_unsigned, !wbv_unsigned.
  apply wZ_w_sext16.
Qed.
Lemma wbv_w_sext32 w : wbv (w_sext32 w) = sext 64 (bv_extract 0 32 (wbv w)).
Proof.
  apply bv_eq. rewrite bv_sext64_extract_unsigned, !wbv_unsigned.
  apply wZ_w_sext32.
Qed.
Lemma wbv_w_zext8 w : wbv (w_zext8 w) = zext 64 (bv_extract 0 8 (wbv w)).
Proof.
  apply bv_eq. rewrite bv_zext64_extract_unsigned, !wbv_unsigned by lia.
  apply wZ_w_zext8.
Qed.
Lemma wbv_w_zext16 w : wbv (w_zext16 w) = zext 64 (bv_extract 0 16 (wbv w)).
Proof.
  apply bv_eq. rewrite bv_zext64_extract_unsigned, !wbv_unsigned by lia.
  apply wZ_w_zext16.
Qed.
Lemma wbv_w_zext32 w : wbv (w_zext32 w) = zext 64 (bv_extract 0 32 (wbv w)).
Proof.
  apply bv_eq. rewrite bv_zext64_extract_unsigned, !wbv_unsigned by lia.
  apply wZ_w_zext32.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_sext64_unsigned (x : bv 32) :
  bv_unsigned (sext 64 x) = zsext 32 (bv_unsigned x).
Proof. reflexivity. Qed.

Lemma bv_low32_unsigned (b : bv 64) : bv_unsigned (low32 b) = bv_unsigned b mod 2 ^ 32.
Proof. unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r. reflexivity. Qed.

Lemma wbv_low32_unsigned t l :
  bv_unsigned (low32 (wbv (W64 t l))) = to_Z l mod 2 ^ 32.
Proof. rewrite bv_low32_unsigned, wbv_unsigned. apply wZ_mod_pow2. lia. Qed.

Lemma bv_wrap32 z : bv_wrap 32 z = z mod 2 ^ 32.
Proof. reflexivity. Qed.

Lemma bv_shamt5 (b : bv 32) :
  bv_unsigned (bv_and b (Z_to_bv 32 31)) = bv_unsigned b mod 32.
Proof.
  rewrite bv_and_unsigned. change (bv_unsigned (Z_to_bv 32 31)) with (Z.ones 5).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma i63_shamt5 (lb : int) : to_Z (lb land 31) = to_Z lb mod 32.
Proof. apply (i63_land_ones lb 31%uint63 5); [reflexivity | lia]. Qed.

Lemma Zmod32_of_mod2p32 z : (z mod 2 ^ 32) mod 32 = z mod 32.
Proof. apply Z.mod_mod_divide. exists (2 ^ 27). reflexivity. Qed.

Lemma Zmod2p32_of_mod2p63 z : (z mod 2 ^ 63) mod 2 ^ 32 = z mod 2 ^ 32.
Proof. apply Z.mod_mod_divide. exists (2 ^ 31). reflexivity. Qed.

(* [comment removed for export] *)
Lemma w32_result (x : int) (R : Z) :
  to_Z x = R mod 2 ^ 32 ->
  wZ (if (x <? 0x80000000)%uint63 then W64 0 x
      else W64 1 (x + 0x7FFFFFFF00000000)%uint63) = zsext 32 R.
Proof.
  intros H. rewrite wZ_sx32.
  - rewrite H. apply (zsext_mod 32).
  - rewrite H. apply Z.mod_pos_bound. lia.
Qed.

Lemma wbv_w_addw a b :
  wbv (w_addw a b) = sext 64 (low32 (wbv a) + low32 (wbv b))%bv.
Proof.
  destruct a as [ta la], b as [tb lb]. apply bv_eq.
  rewrite wbv_unsigned, bv_sext64_unsigned, bv_add_unsigned, !wbv_low32_unsigned.
  unfold w_addw. cbv zeta. rewrite bv_wrap32.
  rewrite (w32_result _ (to_Z la + to_Z lb)).
  - rewrite <- (zsext_mod 32 (_ + _)), <- (zsext_mod 32 (_ mod _)).
    change (2 ^ Z.of_N 32) with (2 ^ 32). f_equal.
    rewrite Z.mod_mod by lia. apply Zplus_mod.
  - rewrite i63_mask32, add_spec, i63_wB. apply Zmod2p32_of_mod2p63.
Qed.

Lemma wbv_w_subw a b :
  wbv (w_subw a b) = sext 64 (low32 (wbv a) - low32 (wbv b))%bv.
Proof.
  destruct a as [ta la], b as [tb lb]. apply bv_eq.
  rewrite wbv_unsigned, bv_sext64_unsigned, bv_sub_unsigned, !wbv_low32_unsigned.
  unfold w_subw. cbv zeta. rewrite bv_wrap32.
  rewrite (w32_result _ (to_Z la - to_Z lb)).
  - rewrite <- (zsext_mod 32 (_ - _)), <- (zsext_mod 32 (_ mod _)).
    change (2 ^ Z.of_N 32) with (2 ^ 32). f_equal.
    rewrite Z.mod_mod by lia. apply Zminus_mod.
  - rewrite i63_mask32, sub_spec, i63_wB. apply Zmod2p32_of_mod2p63.
Qed.

Lemma wbv_w_sllw a b :
  wbv (w_sllw a b) =
  sext 64 (low32 (wbv a) ≪ bv_and (low32 (wbv b)) (Z_to_bv 32 31))%bv.
Proof.
  destruct a as [ta la], b as [tb lb]. apply bv_eq.
  rewrite wbv_unsigned, bv_sext64_unsigned, bv_shiftl_unsigned, bv_shamt5,
    !wbv_low32_unsigned, Zmod32_of_mod2p32.
  unfold w_sllw. cbv zeta. rewrite bv_wrap32.
  pose proof (Z.mod_pos_bound (to_Z lb) 32 ltac:(lia)) as Hk.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (w32_result _ (to_Z la * 2 ^ (to_Z lb mod 32))).
  - rewrite <- (zsext_mod 32 (_ * _)), <- (zsext_mod 32 (_ mod _)).
    change (2 ^ Z.of_N 32) with (2 ^ 32). f_equal.
    rewrite Z.mod_mod by lia. symmetry. apply Z.mul_mod_idemp_l. lia.
  - rewrite i63_mask32, lsl_spec, i63_wB, i63_shamt5. apply Zmod2p32_of_mod2p63.
Qed.

Lemma wbv_w_srlw a b :
  wbv (w_srlw a b) =
  sext 64 (low32 (wbv a) ≫ bv_and (low32 (wbv b)) (Z_to_bv 32 31))%bv.
Proof.
  destruct a as [ta la], b as [tb lb]. apply bv_eq.
  rewrite wbv_unsigned, bv_sext64_unsigned, bv_shiftr_unsigned, bv_shamt5,
    !wbv_low32_unsigned, Zmod32_of_mod2p32.
  unfold w_srlw. cbv zeta.
  pose proof (Z.mod_pos_bound (to_Z lb) 32 ltac:(lia)) as Hk.
  pose proof (Z.mod_pos_bound (to_Z la) (2 ^ 32) ltac:(lia)) as Hx.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (HP : 0 < 2 ^ (to_Z lb mod 32)) by (apply Z.pow_pos_nonneg; lia).
  apply w32_result.
  rewrite lsr_spec, i63_mask32, i63_shamt5. symmetry. apply Z.mod_small.
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; nia.
Qed.

Lemma wS_w_sext32 w : wS (w_sext32 w) = bv_swrap 32 (wZ w).
Proof.
  rewrite wS_swrap, wZ_w_sext32. unfold zsext.
  pose proof (bv_swrap_in_range 32 (wZ w) ltac:(lia)) as H.
  unfold bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 32 `div` 2) with (2 ^ 31) in H.
  set (s := bv_swrap 32 (wZ w)) in *.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 `div` 2) with (2 ^ 63). change (2 ^ Z.of_N 64) with (2 ^ 64).
  zlia.
Qed.

Lemma wbv_w_sraw a b :
  wbv (w_sraw a b) =
  sext 64 (bv_ashiftr (low32 (wbv a)) (bv_and (low32 (wbv b)) (Z_to_bv 32 31))).
Proof.
  destruct b as [tb lb]. apply bv_eq.
  rewrite wbv_unsigned, bv_sext64_unsigned, bv_ashiftr_unsigned, bv_shamt5.
  rewrite wbv_low32_unsigned, Zmod32_of_mod2p32.
  unfold bv_signed. rewrite bv_low32_unsigned, wbv_unsigned.
  unfold w_sraw. rewrite wZ_w_sra, wS_w_sext32, wZ_W64.
  change (to_Z 0 mod 2) with 0. rewrite Z.mul_0_l, Z.add_0_l, i63_shamt5.
  pose proof (Z.mod_pos_bound (to_Z lb) 32 ltac:(lia)) as Hk.
  rewrite (Z.mod_small (to_Z lb mod 32) 64) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  change (wZ a mod 2 ^ 32) with (bv_wrap 32 (wZ a)). rewrite bv_swrap_wrap.
  pose proof (bv_swrap_in_range 32 (wZ a) ltac:(lia)) as H.
  unfold bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 32 `div` 2) with (2 ^ 31) in H.
  set (s := bv_swrap 32 (wZ a)) in *.
  assert (HP : 0 < 2 ^ (to_Z lb mod 32)) by (apply Z.pow_pos_nonneg; lia).
  change (bv_wrap 32 (s / 2 ^ (to_Z lb mod 32)))
    with ((s / 2 ^ (to_Z lb mod 32)) mod 2 ^ Z.of_N 32).
  rewrite (zsext_mod 32). unfold zsext. rewrite bv_wrap64. f_equal.
  symmetry. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 `div` 2) with (2 ^ 31).
  split.
  - apply Z.div_le_lower_bound; nia.
  - apply Z.div_lt_upper_bound; nia.
Qed.

Theorem w_alu32_spec op a b :
  wbv (w_alu32 op a b) = sext 64 (alu32 op (low32 (wbv a)) (low32 (wbv b))).
Proof.
  destruct op; unfold alu32, alu; cbn [w_alu32]; try apply wbv_w_of_bv.
  - apply wbv_w_addw.
  - apply wbv_w_subw.
  - apply wbv_w_sllw.
  - apply wbv_w_srlw.
  - apply wbv_w_sraw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section MulDiv.
Local Open Scope uint63_scope.

Local Abbreviation sx32 x :=
  (if x <? 0x80000000 then W64 0 x else W64 1 (x + 0x7FFFFFFF00000000)) (only parsing).

(* [comment removed for export] *)
Definition w_muldiv_slow (op : mulop) (a b : w64) : w64 :=
  w_of_bv (mul_div op (wbv a) (wbv b)).
Definition w_muldiv32_slow (op : mulop) (a b : w64) : w64 :=
  w_of_bv (sext 64 (mul_div op (low32 (wbv a)) (low32 (wbv b)))).

Definition w_mul (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 tb lb =>
      let (h, l) := mulc la lb in
      W64 ((h lxor (ta land lb) lxor (tb land la)) land 1) l
  end.

Definition w_mulhu (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 tb lb =>
      let (h, _) := mulc la lb in
      if ((ta lor tb) land 1) =? 0 then W64 0 (h >> 1)
      else
        let u := if (ta land 1) =? 0 then 0 else lb in
        let v := if (tb land 1) =? 0 then 0 else la in
        let s1 := h + u in
        let s2 := s1 + v in
        let cc := ((ta land tb) land 1) + (if s1 <? h then 1 else 0)
                  + (if s2 <? s1 then 1 else 0) in
        W64 (cc >> 1) ((s2 >> 1) + ((cc land 1) << 62))
  end.

Definition w_neg_top (a : w64) : bool :=
  match a with W64 ta _ => (ta land 1) =? 1 end.

Definition w_mulhsu (a b : w64) : w64 :=
  let m := w_mulhu a b in
  if w_neg_top a then w_sub m b else m.

Definition w_mulh (a b : w64) : w64 :=
  let m := w_mulhu a b in
  let m1 := if w_neg_top a then w_sub m b else m in
  if w_neg_top b then w_sub m1 a else m1.

Definition w_divu (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 tb lb =>
      if ((ta lor tb) land 1) =? 0 then
        if lb =? 0 then w_ones else W64 0 (la / lb)
      else w_muldiv_slow M_DIVU a b
  end.

Definition w_remu (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 tb lb =>
      if ((ta lor tb) land 1) =? 0 then
        if lb =? 0 then W64 0 la else W64 0 (la mod lb)
      else w_muldiv_slow M_REMU a b
  end.

Definition w_div (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 tb lb =>
      if ((ta lor tb) land 1) =? 0 then
        if lb =? 0 then w_ones else W64 0 (la / lb)
      else w_muldiv_slow M_DIV a b
  end.

Definition w_rem (a b : w64) : w64 :=
  match a, b with
  | W64 ta la, W64 tb lb =>
      if ((ta lor tb) land 1) =? 0 then
        if lb =? 0 then W64 0 la else W64 0 (la mod lb)
      else w_muldiv_slow M_REM a b
  end.

Definition w_muldiv (op : mulop) (a b : w64) : w64 :=
  match op with
  | M_MUL => w_mul a b
  | M_MULH => w_mulh a b
  | M_MULHSU => w_mulhsu a b
  | M_MULHU => w_mulhu a b
  | M_DIV => w_div a b
  | M_DIVU => w_divu a b
  | M_REM => w_rem a b
  | M_REMU => w_remu a b
  end.

(* [comment removed for export] *)
Definition w_mulw (a b : w64) : w64 :=
  match a, b with
  | W64 _ la, W64 _ lb => let x := (la * lb) land 0xFFFFFFFF in sx32 x
  end.

Definition w_divuw (a b : w64) : w64 :=
  match a, b with
  | W64 _ la, W64 _ lb =>
      let y := lb land 0xFFFFFFFF in
      if y =? 0 then w_ones
      else let q := (la land 0xFFFFFFFF) / y in sx32 q
  end.

Definition w_remuw (a b : w64) : w64 :=
  match a, b with
  | W64 _ la, W64 _ lb =>
      let x := la land 0xFFFFFFFF in
      let y := lb land 0xFFFFFFFF in
      if y =? 0 then sx32 x
      else let r := x mod y in sx32 r
  end.

Definition w_divw (a b : w64) : w64 :=
  match a, b with
  | W64 _ la, W64 _ lb =>
      let x := la land 0xFFFFFFFF in
      let y := lb land 0xFFFFFFFF in
      if x <? 0x80000000 then
        if y <? 0x80000000 then
          if y =? 0 then w_ones else W64 0 (x / y)
        else w_muldiv32_slow M_DIV a b
      else w_muldiv32_slow M_DIV a b
  end.

Definition w_remw (a b : w64) : w64 :=
  match a, b with
  | W64 _ la, W64 _ lb =>
      let x := la land 0xFFFFFFFF in
      let y := lb land 0xFFFFFFFF in
      if x <? 0x80000000 then
        if y <? 0x80000000 then
          if y =? 0 then W64 0 x else W64 0 (x mod y)
        else w_muldiv32_slow M_REM a b
      else w_muldiv32_slow M_REM a b
  end.

Definition w_muldiv32 (op : mulop) (a b : w64) : w64 :=
  match op with
  | M_MUL => w_mulw a b
  | M_DIV => w_divw a b
  | M_DIVU => w_divuw a b
  | M_REM => w_remw a b
  | M_REMU => w_remuw a b
  | _ => (* [comment removed for export] *)
      w_muldiv32_slow op a b
  end.

End MulDiv.

Lemma wbv_w_muldiv_slow op a b :
  wbv (w_muldiv_slow op a b) = mul_div op (wbv a) (wbv b).
Proof. apply wbv_w_of_bv. Qed.

Lemma wbv_w_muldiv32_slow op a b :
  wbv (w_muldiv32_slow op a b) =
  sext 64 (mul_div op (low32 (wbv a)) (low32 (wbv b))).
Proof. apply wbv_w_of_bv. Qed.

Create Rewrite HintDb w64db.
#[local] Hint Rewrite add_spec sub_spec lsr_spec lsl_spec i63_land1 i63_land_mod2
  i63_lxor_mod2 i63_lor_mod2 to_Z_0 to_Z_1 i63_wB : w64db.

Lemma wZ_w_mul a b : wZ (w_mul a b) = (wZ a * wZ b) mod 2 ^ 64.
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_mul.
  pose proof (mulc_spec la lb) as Hm. rewrite i63_wB in Hm.
  destruct (mulc la lb) as [h l]. cbn [fst snd] in Hm.
  rewrite !wZ_W64, i63_land1, Z.mod_mod, !i63_lxor_mod2, !i63_land_mod2 by lia.
  w64_ranges.
  w64_top ta; w64_top tb.
  all: match goal with
       | |- _ = ?R mod _ => ring_simplify R; rewrite Hm
       end.
  all: zlia.
Qed.

(* [comment removed for export] *)
Lemma w_tops_even ta tb :
  to_Z ((ta lor tb) land 1)%uint63 = to_Z 0%uint63 ->
  to_Z ta mod 2 = 0 /\ to_Z tb mod 2 = 0.
Proof.
  rewrite i63_land1, i63_lor_mod2, to_Z_0.
  destruct (Z_mod2_cases (to_Z ta)) as [Ea|Ea], (Z_mod2_cases (to_Z tb)) as [Eb|Eb];
    rewrite Ea, Eb; lia.
Qed.

Lemma wZ_even_top t l : to_Z t mod 2 = 0 -> wZ (W64 t l) = to_Z l.
Proof. intros E. rewrite wZ_W64, E. lia. Qed.

Lemma wS_even_top t l : to_Z t mod 2 = 0 -> wS (W64 t l) = to_Z l.
Proof. intros E. rewrite wS_W64, E. lia. Qed.

Lemma Z_mod2_not0 z : z mod 2 <> 0 -> z mod 2 = 1.
Proof. destruct (Z_mod2_cases z); [contradiction | trivial]. Qed.

Lemma wZ_w_mulhu a b : wZ (w_mulhu a b) = (wZ a * wZ b) / 2 ^ 64.
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_mulhu.
  pose proof (mulc_spec la lb) as Hm. rewrite i63_wB in Hm.
  destruct (mulc la lb) as [h l]. cbn [fst snd] in Hm. cbv zeta.
  w64_ranges.
  destruct (eqbP ((ta lor tb) land 1) 0) as [E|E].
  - apply w_tops_even in E. destruct E as [Ea Eb].
    rewrite !wZ_W64, lsr_spec, Ea, Eb.
    change (to_Z 0 mod 2) with 0. change (2 ^ to_Z 1) with 2.
    match goal with |- _ = ?R / _ => ring_simplify R; rewrite Hm end.
    zlia.
  - rewrite i63_land1, i63_lor_mod2, to_Z_0 in E.
    destruct (eqbP (ta land 1) 0) as [Ea|Ea]; rewrite i63_land1, to_Z_0 in Ea;
      [|apply Z_mod2_not0 in Ea];
    (destruct (eqbP (tb land 1) 0) as [Eb|Eb]; rewrite i63_land1, to_Z_0 in Eb;
      [|apply Z_mod2_not0 in Eb]);
    [exfalso; rewrite Ea, Eb in E; apply E; reflexivity | | | ].
    all: match goal with
         | |- context [if (?x <? ?y)%uint63 then _ else _] =>
             destruct (ltbP x y) as [Hc1|Hc1]
         end.
    all: match goal with
         | |- context [if (?x <? ?y)%uint63 then _ else _] =>
             destruct (ltbP x y) as [Hc2|Hc2]
         end.
    all: rewrite !wZ_W64.
    all: autorewrite with w64db in *.
    all: change (to_Z 62) with 62.
    all: rewrite ?Ea, ?Eb in *.
    all: match goal with |- _ = ?R / _ => ring_simplify R; rewrite ?Hm end.
    all: clear E Hm; zlia.
Qed.

Lemma w_neg_top_spec a : w_neg_top a = (to_Z (wtop a) mod 2 =? 1).
Proof.
  destruct a as [ta la]. cbn [w_neg_top wtop].
  destruct (eqbP (ta land 1) 1) as [E|E]; rewrite i63_land1, to_Z_1 in E;
    symmetry; [apply Z.eqb_eq | apply Z.eqb_neq]; exact E.
Qed.

Lemma w_neg_top_wS a : wS a = wZ a - (if w_neg_top a then 2 ^ 64 else 0).
Proof.
  rewrite wS_wZ, w_neg_top_spec.
  destruct (Z_mod2_cases (to_Z (wtop a))) as [E|E]; rewrite E; cbn; lia.
Qed.

Lemma Zdiv_sub_mul x y c : c <> 0 -> (x - y * c) / c = x / c - y.
Proof.
  intros Hc. replace (x - y * c) with (x + (- y) * c) by ring.
  rewrite Z.div_add by exact Hc. ring.
Qed.

Lemma wZ_w_mulhsu a b : wZ (w_mulhsu a b) = ((wS a * wZ b) / 2 ^ 64) mod 2 ^ 64.
Proof.
  unfold w_mulhsu. cbv zeta. rewrite (w_neg_top_wS a).
  pose proof (wZ_range a) as Ha. pose proof (wZ_range b) as Hb.
  assert (Hm : 0 <= wZ a * wZ b / 2 ^ 64 < 2 ^ 64).
  { split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; nia. }
  destruct (w_neg_top a).
  - rewrite wZ_w_sub, wZ_w_mulhu.
    replace ((wZ a - 2 ^ 64) * wZ b) with (wZ a * wZ b - wZ b * 2 ^ 64) by ring.
    rewrite Zdiv_sub_mul by lia. reflexivity.
  - rewrite wZ_w_mulhu, Z.sub_0_r. symmetry. apply Z.mod_small. exact Hm.
Qed.

Lemma wZ_w_mulh a b : wZ (w_mulh a b) = ((wS a * wS b) / 2 ^ 64) mod 2 ^ 64.
Proof.
  unfold w_mulh. cbv zeta. rewrite (w_neg_top_wS a), (w_neg_top_wS b).
  pose proof (wZ_range a) as Ha. pose proof (wZ_range b) as Hb.
  assert (Hm : 0 <= wZ a * wZ b / 2 ^ 64 < 2 ^ 64).
  { split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; nia. }
  destruct (w_neg_top a), (w_neg_top b);
    rewrite ?wZ_w_sub, ?wZ_w_sub, wZ_w_mulhu.
  - replace ((wZ a - 2 ^ 64) * (wZ b - 2 ^ 64))
      with (wZ a * wZ b - (wZ a + wZ b - 2 ^ 64) * 2 ^ 64) by ring.
    rewrite Zdiv_sub_mul by lia. rewrite Zminus_mod_idemp_l.
    replace (wZ a * wZ b / 2 ^ 64 - (wZ a + wZ b - 2 ^ 64))
      with (wZ a * wZ b / 2 ^ 64 - wZ b - wZ a + 1 * 2 ^ 64) by ring.
    rewrite Z.mod_add by lia. reflexivity.
  - replace ((wZ a - 2 ^ 64) * (wZ b - 0)) with (wZ a * wZ b - wZ b * 2 ^ 64) by ring.
    rewrite Zdiv_sub_mul by lia. reflexivity.
  - replace ((wZ a - 0) * (wZ b - 2 ^ 64)) with (wZ a * wZ b - wZ a * 2 ^ 64) by ring.
    rewrite Zdiv_sub_mul by lia. reflexivity.
  - rewrite !Z.sub_0_r. symmetry. apply Z.mod_small. exact Hm.
Qed.

(* [comment removed for export] *)
Lemma wbv_w_mul a b : wbv (w_mul a b) = (wbv a * wbv b)%bv.
Proof.
  apply bv_eq. rewrite bv_mul_unsigned, !wbv_unsigned, bv_wrap64. apply wZ_w_mul.
Qed.

Lemma wbv_w_mulhu a b : wbv (w_mulhu a b) = bv_mulhuu (wbv a) (wbv b).
Proof.
  unfold bv_mulhuu. apply wbv_of_wZ. rewrite !wbv_unsigned, wZ_w_mulhu.
  change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (wZ_range a) as Ha. pose proof (wZ_range b) as Hb.
  symmetry. apply Z.mod_small.
  split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; nia.
Qed.

Lemma wbv_w_mulhsu a b : wbv (w_mulhsu a b) = bv_mulhsu (wbv a) (wbv b).
Proof.
  unfold bv_mulhsu. apply wbv_of_wZ. rewrite wbv_signed, wbv_unsigned, wZ_w_mulhsu.
  change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia.
  reflexivity.
Qed.

Lemma wbv_w_mulh a b : wbv (w_mulh a b) = bv_mulhss (wbv a) (wbv b).
Proof.
  unfold bv_mulhss. apply wbv_of_wZ. rewrite !wbv_signed, wZ_w_mulh.
  change (Z.of_N 64) with 64. rewrite Z.shiftr_div_pow2 by lia.
  reflexivity.
Qed.

Lemma wbv_w_divu a b : wbv (w_divu a b) = mul_div M_DIVU (wbv a) (wbv b).
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_divu.
  destruct (eqbP ((ta lor tb) land 1) 0) as [E|E]; [|apply wbv_w_muldiv_slow].
  apply w_tops_even in E. destruct E as [Ea Eb].
  unfold mul_div. rewrite wbv_unsigned, (wZ_even_top tb lb Eb).
  destruct (eqbP lb 0) as [E0|E0]; rewrite to_Z_0 in E0.
  - rewrite E0. cbn [Z.eqb]. apply wbv_w_ones.
  - destruct (Z.eqb_spec (to_Z lb) 0) as [?|_]; [contradiction|].
    apply bv_eq. rewrite bv_divu_unsigned, !wbv_unsigned.
    rewrite (wZ_even_top ta la Ea), (wZ_even_top tb lb Eb), wZ_W64, div_spec.
    change (to_Z 0 mod 2) with 0. rewrite Z.mul_0_l, Z.add_0_l. reflexivity.
Qed.

Lemma wbv_w_remu a b : wbv (w_remu a b) = mul_div M_REMU (wbv a) (wbv b).
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_remu.
  destruct (eqbP ((ta lor tb) land 1) 0) as [E|E]; [|apply wbv_w_muldiv_slow].
  apply w_tops_even in E. destruct E as [Ea Eb].
  unfold mul_div. rewrite wbv_unsigned, (wZ_even_top tb lb Eb).
  destruct (eqbP lb 0) as [E0|E0]; rewrite to_Z_0 in E0.
  - rewrite E0. cbn [Z.eqb]. apply wbv_eq_iff.
    rewrite (wZ_even_top ta la Ea). reflexivity.
  - destruct (Z.eqb_spec (to_Z lb) 0) as [?|_]; [contradiction|].
    apply bv_eq. rewrite bv_modu_unsigned, !wbv_unsigned.
    rewrite (wZ_even_top ta la Ea), (wZ_even_top tb lb Eb), wZ_W64, mod_spec.
    change (to_Z 0 mod 2) with 0. rewrite Z.mul_0_l, Z.add_0_l. reflexivity.
Qed.

Lemma wbv_w_div a b : wbv (w_div a b) = mul_div M_DIV (wbv a) (wbv b).
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_div.
  destruct (eqbP ((ta lor tb) land 1) 0) as [E|E]; [|apply wbv_w_muldiv_slow].
  apply w_tops_even in E. destruct E as [Ea Eb].
  unfold mul_div. rewrite wbv_unsigned, (wZ_even_top tb lb Eb).
  destruct (eqbP lb 0) as [E0|E0]; rewrite to_Z_0 in E0.
  - rewrite E0. cbn [Z.eqb]. apply wbv_w_ones.
  - destruct (Z.eqb_spec (to_Z lb) 0) as [?|_]; [contradiction|].
    apply bv_eq. rewrite bv_quots_unsigned, !wbv_signed, wbv_unsigned.
    rewrite (wS_even_top ta la Ea), (wS_even_top tb lb Eb), wZ_W64, div_spec.
    change (to_Z 0 mod 2) with 0.
    pose proof (i63_range la). pose proof (i63_range lb).
    rewrite Z.quot_div_nonneg by lia. rewrite bv_wrap64, Z.mod_small;
      [rewrite Z.mul_0_l, Z.add_0_l; reflexivity|].
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; nia.
Qed.

Lemma wbv_w_rem a b : wbv (w_rem a b) = mul_div M_REM (wbv a) (wbv b).
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_rem.
  destruct (eqbP ((ta lor tb) land 1) 0) as [E|E]; [|apply wbv_w_muldiv_slow].
  apply w_tops_even in E. destruct E as [Ea Eb].
  unfold mul_div. rewrite wbv_unsigned, (wZ_even_top tb lb Eb).
  destruct (eqbP lb 0) as [E0|E0]; rewrite to_Z_0 in E0.
  - rewrite E0. cbn [Z.eqb]. apply wbv_eq_iff.
    rewrite (wZ_even_top ta la Ea). reflexivity.
  - destruct (Z.eqb_spec (to_Z lb) 0) as [?|_]; [contradiction|].
    apply bv_eq. rewrite bv_rems_unsigned, !wbv_signed, wbv_unsigned.
    rewrite (wS_even_top ta la Ea), (wS_even_top tb lb Eb), wZ_W64, mod_spec.
    change (to_Z 0 mod 2) with 0.
    pose proof (i63_range la). pose proof (i63_range lb).
    rewrite Z.rem_mod_nonneg by lia.
    rewrite bv_wrap64, (Z.mod_small (to_Z la mod to_Z lb) (2 ^ 64));
      [rewrite Z.mul_0_l, Z.add_0_l; reflexivity|].
    pose proof (Z.mod_pos_bound (to_Z la) (to_Z lb) ltac:(lia)). lia.
Qed.

Theorem w_muldiv_spec op a b :
  wbv (w_muldiv op a b) = mul_div op (wbv a) (wbv b).
Proof.
  destruct op; cbn [w_muldiv].
  - apply wbv_w_mul.
  - apply wbv_w_mulh.
  - apply wbv_w_mulhsu.
  - apply wbv_w_mulhu.
  - apply wbv_w_div.
  - apply wbv_w_divu.
  - apply wbv_w_rem.
  - apply wbv_w_remu.
Qed.

(* [comment removed for export] *)

Lemma wbv_w_mulw a b :
  wbv (w_mulw a b) = sext 64 (low32 (wbv a) * low32 (wbv b))%bv.
Proof.
  destruct a as [ta la], b as [tb lb]. apply bv_eq.
  rewrite wbv_unsigned, bv_sext64_unsigned, bv_mul_unsigned, !wbv_low32_unsigned.
  unfold w_mulw. cbv zeta. rewrite bv_wrap32.
  rewrite (w32_result _ (to_Z la * to_Z lb)).
  - rewrite <- (zsext_mod 32 (_ * _)), <- (zsext_mod 32 (_ mod _)).
    change (2 ^ Z.of_N 32) with (2 ^ 32). f_equal.
    rewrite Z.mod_mod by lia. apply Zmult_mod.
  - rewrite i63_mask32, mul_spec, i63_wB. apply Zmod2p32_of_mod2p63.
Qed.

Lemma zsext32_ones : zsext 32 (bv_unsigned (Z_to_bv 32 (-1))) = wZ w_ones.
Proof. reflexivity. Qed.

Lemma zsext32_small z : 0 <= z < 2 ^ 31 -> zsext 32 z = z.
Proof. intros H. rewrite zsext32_eq. zlia. Qed.

Lemma bv_swrap32_small z : 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros H. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32 `div` 2) with (2 ^ 31). lia.
Qed.

Lemma wbv_w_divuw a b :
  wbv (w_divuw a b) = sext 64 (mul_div M_DIVU (low32 (wbv a)) (low32 (wbv b))).
Proof.
  destruct a as [ta la], b as [tb lb]. apply bv_eq.
  rewrite wbv_unsigned, bv_sext64_unsigned. unfold mul_div, w_divuw. cbv zeta.
  rewrite !wbv_low32_unsigned.
  pose proof (Z.mod_pos_bound (to_Z la) (2 ^ 32) ltac:(lia)) as Hx.
  pose proof (Z.mod_pos_bound (to_Z lb) (2 ^ 32) ltac:(lia)) as Hy.
  destruct (eqbP (lb land 0xFFFFFFFF) 0) as [E0|E0]; rewrite i63_mask32, to_Z_0 in E0.
  - rewrite E0. cbn [Z.eqb]. symmetry. apply zsext32_ones.
  - destruct (Z.eqb_spec (to_Z lb mod 2 ^ 32) 0) as [?|_]; [contradiction|].
    rewrite bv_divu_unsigned, !wbv_low32_unsigned.
    apply w32_result. rewrite div_spec, !i63_mask32.
    symmetry. apply Z.mod_small.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; nia.
Qed.

Lemma wbv_w_remuw a b :
  wbv (w_remuw a b) = sext 64 (mul_div M_REMU (low32 (wbv a)) (low32 (wbv b))).
Proof.
  destruct a as [ta la], b as [tb lb]. apply bv_eq.
  rewrite wbv_unsigned, bv_sext64_unsigned. unfold mul_div, w_remuw. cbv zeta.
  rewrite !wbv_low32_unsigned.
  pose proof (Z.mod_pos_bound (to_Z la) (2 ^ 32) ltac:(lia)) as Hx.
  pose proof (Z.mod_pos_bound (to_Z lb) (2 ^ 32) ltac:(lia)) as Hy.
  destruct (eqbP (lb land 0xFFFFFFFF) 0) as [E0|E0]; rewrite i63_mask32, to_Z_0 in E0.
  - rewrite E0. cbn [Z.eqb]. rewrite wbv_low32_unsigned.
    apply w32_result. rewrite i63_mask32. symmetry. apply Z.mod_mod. lia.
  - destruct (Z.eqb_spec (to_Z lb mod 2 ^ 32) 0) as [?|_]; [contradiction|].
    rewrite bv_modu_unsigned, !wbv_low32_unsigned.
    apply w32_result. rewrite mod_spec, !i63_mask32.
    symmetry. apply Z.mod_small.
    pose proof (Z.mod_pos_bound (to_Z la mod 2 ^ 32) (to_Z lb mod 2 ^ 32) ltac:(lia)).
    lia.
Qed.

Lemma wbv_w_divw a b :
  wbv (w_divw a b) = sext 64 (mul_div M_DIV (low32 (wbv a)) (low32 (wbv b))).
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_divw. cbv zeta.
  destruct (ltbP (la land 0xFFFFFFFF) 0x80000000) as [Hx|Hx];
    [|apply wbv_w_muldiv32_slow].
  destruct (ltbP (lb land 0xFFFFFFFF) 0x80000000) as [Hy|Hy];
    [|apply wbv_w_muldiv32_slow].
  rewrite i63_mask32 in Hx, Hy.
  change (to_Z 2147483648) with (2 ^ 31) in Hx, Hy.
  pose proof (Z.mod_pos_bound (to_Z la) (2 ^ 32) ltac:(lia)) as Hx0.
  pose proof (Z.mod_pos_bound (to_Z lb) (2 ^ 32) ltac:(lia)) as Hy0.
  apply bv_eq. rewrite wbv_unsigned, bv_sext64_unsigned. unfold mul_div.
  rewrite !wbv_low32_unsigned.
  destruct (eqbP (lb land 0xFFFFFFFF) 0) as [E0|E0]; rewrite i63_mask32, to_Z_0 in E0.
  - rewrite E0. cbn [Z.eqb]. symmetry. apply zsext32_ones.
  - destruct (Z.eqb_spec (to_Z lb mod 2 ^ 32) 0) as [?|_]; [contradiction|].
    rewrite bv_quots_unsigned. unfold bv_signed. rewrite !wbv_low32_unsigned.
    rewrite !bv_swrap32_small by lia.
    rewrite Z.quot_div_nonneg by lia.
    set (x := to_Z la mod 2 ^ 32) in *. set (y := to_Z lb mod 2 ^ 32) in *.
    assert (Hq : 0 <= x / y < 2 ^ 31).
    { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; nia. }
    rewrite bv_wrap32, (Z.mod_small (x / y)) by lia.
    rewrite zsext32_small by exact Hq.
    rewrite wZ_W64, div_spec, !i63_mask32. change (to_Z 0 mod 2) with 0.
    rewrite Z.mul_0_l, Z.add_0_l. reflexivity.
Qed.

Lemma wbv_w_remw a b :
  wbv (w_remw a b) = sext 64 (mul_div M_REM (low32 (wbv a)) (low32 (wbv b))).
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_remw. cbv zeta.
  destruct (ltbP (la land 0xFFFFFFFF) 0x80000000) as [Hx|Hx];
    [|apply wbv_w_muldiv32_slow].
  destruct (ltbP (lb land 0xFFFFFFFF) 0x80000000) as [Hy|Hy];
    [|apply wbv_w_muldiv32_slow].
  rewrite i63_mask32 in Hx, Hy.
  change (to_Z 2147483648) with (2 ^ 31) in Hx, Hy.
  pose proof (Z.mod_pos_bound (to_Z la) (2 ^ 32) ltac:(lia)) as Hx0.
  pose proof (Z.mod_pos_bound (to_Z lb) (2 ^ 32) ltac:(lia)) as Hy0.
  apply bv_eq. rewrite wbv_unsigned, bv_sext64_unsigned. unfold mul_div.
  rewrite !wbv_low32_unsigned.
  destruct (eqbP (lb land 0xFFFFFFFF) 0) as [E0|E0]; rewrite i63_mask32, to_Z_0 in E0.
  - rewrite E0. cbn [Z.eqb]. rewrite wbv_low32_unsigned.
    rewrite zsext32_small by lia.
    rewrite wZ_W64, !i63_mask32. change (to_Z 0 mod 2) with 0.
    rewrite Z.mul_0_l, Z.add_0_l. reflexivity.
  - destruct (Z.eqb_spec (to_Z lb mod 2 ^ 32) 0) as [?|_]; [contradiction|].
    rewrite bv_rems_unsigned. unfold bv_signed. rewrite !wbv_low32_unsigned.
    rewrite !bv_swrap32_small by lia.
    rewrite Z.rem_mod_nonneg by lia.
    set (x := to_Z la mod 2 ^ 32) in *. set (y := to_Z lb mod 2 ^ 32) in *.
    assert (Hr : 0 <= x mod y < 2 ^ 31).
    { pose proof (Z.mod_pos_bound x y ltac:(lia)). lia. }
    rewrite bv_wrap32, (Z.mod_small (x mod y) (2 ^ 32)) by lia.
    rewrite zsext32_small by exact Hr.
    rewrite wZ_W64, mod_spec, !i63_mask32. change (to_Z 0 mod 2) with 0.
    rewrite Z.mul_0_l, Z.add_0_l. reflexivity.
Qed.

Theorem w_muldiv32_spec op a b :
  wbv (w_muldiv32 op a b) =
  sext 64 (mul_div op (low32 (wbv a)) (low32 (wbv b))).
Proof.
  destruct op; cbn [w_muldiv32]; try apply wbv_w_muldiv32_slow.
  - apply wbv_w_mulw.
  - apply wbv_w_divw.
  - apply wbv_w_divuw.
  - apply wbv_w_remw.
  - apply wbv_w_remuw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition w_branch (c : branch_cond) (a b : w64) : bool :=
  match c with
  | BC_EQ => w_eqb a b
  | BC_NE => if w_eqb a b then false else true
  | BC_LT => w_lts a b
  | BC_GE => if w_lts a b then false else true
  | BC_LTU => w_ltu a b
  | BC_GEU => if w_ltu a b then false else true
  end.

Theorem w_branch_spec c a b :
  w_branch c a b = branch_taken c (wbv a) (wbv b).
Proof.
  destruct c; cbn [w_branch branch_taken];
    rewrite ?w_eqb_bv, ?w_lts_bv, ?w_ltu_bv;
    try reflexivity;
    match goal with |- context [if ?x then _ else _] => destruct x end;
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition w_amo (op : amoop) (old src : w64) : w64 :=
  match op with
  | AMO_SWAP => src
  | AMO_ADD => w_add old src
  | AMO_XOR => w_xor old src
  | AMO_AND => w_and old src
  | AMO_OR => w_or old src
  | AMO_MIN => if w_lts old src then old else src
  | AMO_MAX => if w_lts old src then src else old
  | AMO_MINU => if w_ltu old src then old else src
  | AMO_MAXU => if w_ltu old src then src else old
  end.

Theorem w_amo_spec op old src :
  wbv (w_amo op old src) = amo_val op (wbv old) (wbv src).
Proof.
  destruct op; cbn [w_amo amo_val]; rewrite <- ?w_lts_bv, <- ?w_ltu_bv.
  - reflexivity.
  - apply wbv_w_add.
  - apply wbv_w_xor.
  - apply wbv_w_and.
  - apply wbv_w_or.
  - destruct (w_lts old src); reflexivity.
  - destruct (w_lts old src); reflexivity.
  - destruct (w_ltu old src); reflexivity.
  - destruct (w_ltu old src); reflexivity.
Qed.

(* [comment removed for export] *)
Definition w_amo32 (op : amoop) (old src : w64) : w64 :=
  match op with
  | AMO_SWAP => src
  | AMO_ADD => w_add old src
  | AMO_XOR => w_xor old src
  | AMO_AND => w_and old src
  | AMO_OR => w_or old src
  | AMO_MIN => if w_lts (w_sext32 old) (w_sext32 src) then old else src
  | AMO_MAX => if w_lts (w_sext32 old) (w_sext32 src) then src else old
  | AMO_MINU => if w_ltu (w_zext32 old) (w_zext32 src) then old else src
  | AMO_MAXU => if w_ltu (w_zext32 old) (w_zext32 src) then src else old
  end.

Lemma Zbitop_mod_pow2 (f : Z -> Z -> Z) (fb : bool -> bool -> bool) :
  (forall a b i, Z.testbit (f a b) i = fb (Z.testbit a i) (Z.testbit b i)) ->
  fb false false = false ->
  forall a b n, 0 <= n -> (f a b) mod 2 ^ n = f (a mod 2 ^ n) (b mod 2 ^ n).
Proof.
  intros Hf Hff a b n Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Hf, !Z.testbit_mod_pow2, Hf by exact Hn.
  destruct (i <? n); cbn [andb]; [reflexivity | symmetry; exact Hff].
Qed.

Lemma w_lts_sext32 a b :
  w_lts (w_sext32 a) (w_sext32 b) = bv_lts (low32 (wbv a)) (low32 (wbv b)).
Proof.
  rewrite w_lts_spec, !wS_w_sext32. unfold bv_lts, bv_signed.
  rewrite !bv_low32_unsigned, !wbv_unsigned.
  change (wZ a mod 2 ^ 32) with (bv_wrap 32 (wZ a)).
  change (wZ b mod 2 ^ 32) with (bv_wrap 32 (wZ b)).
  rewrite !bv_swrap_wrap. reflexivity.
Qed.

Lemma w_ltu_zext32 a b :
  w_ltu (w_zext32 a) (w_zext32 b) = bv_ltu (low32 (wbv a)) (low32 (wbv b)).
Proof.
  rewrite w_ltu_spec, !wZ_w_zext32. unfold bv_ltu.
  rewrite !bv_low32_unsigned, !wbv_unsigned. reflexivity.
Qed.

Theorem w_amo32_spec op old src :
  low32 (wbv (w_amo32 op old src)) =
  amo_val op (low32 (wbv old)) (low32 (wbv src)).
Proof.
  destruct op; cbn [w_amo32 amo_val];
    rewrite <- ?w_lts_sext32, <- ?w_ltu_zext32.
  - reflexivity.
  - apply bv_eq. rewrite bv_add_unsigned, !bv_low32_unsigned, !wbv_unsigned.
    rewrite wZ_w_add, bv_wrap32.
    rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
    apply Zplus_mod.
  - apply bv_eq. rewrite bv_xor_unsigned, !bv_low32_unsigned, !wbv_unsigned.
    rewrite wZ_w_xor. apply (Zbitop_mod_pow2 Z.lxor xorb Z.lxor_spec eq_refl). lia.
  - apply bv_eq. rewrite bv_and_unsigned, !bv_low32_unsigned, !wbv_unsigned.
    rewrite wZ_w_and. apply (Zbitop_mod_pow2 Z.land andb Z.land_spec eq_refl). lia.
  - apply bv_eq. rewrite bv_or_unsigned, !bv_low32_unsigned, !wbv_unsigned.
    rewrite wZ_w_or. apply (Zbitop_mod_pow2 Z.lor orb Z.lor_spec eq_refl). lia.
  - destruct (w_lts _ _); reflexivity.
  - destruct (w_lts _ _); reflexivity.
  - destruct (w_ltu _ _); reflexivity.
  - destruct (w_ltu _ _); reflexivity.
Qed.

(* [comment removed for export] *)
Corollary w_amo32_exec op old src (old32 : bv 32) :
  low32 (wbv old) = old32 ->
  low32 (wbv (w_amo32 op old src)) = amo_val op old32 (low32 (wbv src)) /\
  wbv (w_sext32 old) = sext 64 old32.
Proof.
  intros <-. split; [apply w_amo32_spec | apply wbv_w_sext32].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Cell.
Local Open Scope uint63_scope.

(* [comment removed for export] *)
Definition w_extract (i s : int) (c : w64) : w64 :=
  if s =? 8 then c
  else
    match c with
    | W64 t l =>
        let sh := i << 3 in
        let x := if sh =? 0 then l
                 else (l >> sh) + ((t land 1) << (63 - sh)) in
        W64 0 (x land ((1 << (s << 3)) - 1))
    end.

(* [comment removed for export] *)
Definition w_insert (i s : int) (c v : w64) : w64 :=
  if s =? 8 then v
  else
    match c, v with
    | W64 t l, W64 _ vl =>
        let sh := i << 3 in
        let w := s << 3 in
        let e := sh + w in
        let f := vl land ((1 << w) - 1) in
        let low := l land ((1 << sh) - 1) in
        if e =? 64 then W64 (f >> (w - 1)) (low + (f << sh))
        else W64 t (low + (f << sh) + ((l >> e) << e))
    end.

(* [comment removed for export] *)
Definition w_byte (i : int) (w : w64) : int :=
  match w with
  | W64 t l =>
      if i =? 7 then (l >> 56) + ((t land 1) << 7)
      else (l >> (i << 3)) land 255
  end.

End Cell.

Lemma i63_mask_pow2 (k : int) :
  to_Z k <= 62 -> to_Z ((1 << k) - 1)%uint63 = 2 ^ to_Z k - 1.
Proof.
  intros Hk. pose proof (i63_range k) as Hk0.
  assert (Hp : 0 < 2 ^ to_Z k < 2 ^ 63).
  { split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]. }
  rewrite sub_spec, lsl_spec, to_Z_1, i63_wB, Z.mul_1_l.
  rewrite (Z.mod_small (2 ^ to_Z k)) by lia. apply Z.mod_small. lia.
Qed.

Lemma i63_land_mask (x k : int) :
  to_Z k <= 62 -> to_Z (x land ((1 << k) - 1))%uint63 = to_Z x mod 2 ^ to_Z k.
Proof.
  intros Hk. pose proof (i63_range k) as Hk0.
  apply i63_land_ones; [|lia].
  rewrite i63_mask_pow2 by exact Hk. rewrite Z.ones_equiv. lia.
Qed.

Lemma i63_lsl3 (i : int) : to_Z i <= 8 -> to_Z (i << 3)%uint63 = 8 * to_Z i.
Proof.
  intros Hi. pose proof (i63_range i). rewrite lsl_spec, i63_wB.
  change (2 ^ to_Z 3) with 8. rewrite Z.mod_small by lia. lia.
Qed.

Theorem wZ_w_extract i s c :
  1 <= to_Z s -> to_Z i + to_Z s <= 8 ->
  wZ (w_extract i s c) = (wZ c / 2 ^ (8 * to_Z i)) mod 2 ^ (8 * to_Z s).
Proof.
  intros Hs His. pose proof (i63_range i) as Hi0. unfold w_extract.
  destruct (eqbP s 8) as [E8|E8]; change (to_Z 8) with 8 in E8.
  - replace (to_Z i) with 0 by lia. rewrite E8.
    change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r. symmetry.
    apply Z.mod_small. apply wZ_range.
  - destruct c as [t l]. cbv zeta.
    assert (Hsh : to_Z (i << 3)%uint63 = 8 * to_Z i) by (apply i63_lsl3; lia).
    assert (Hw : to_Z (s << 3)%uint63 = 8 * to_Z s) by (apply i63_lsl3; lia).
    rewrite (wZ_W64 0%uint63). change (to_Z 0 mod 2) with 0.
    rewrite Z.mul_0_l, Z.add_0_l.
    rewrite i63_land_mask by lia. rewrite Hw.
    destruct (eqbP (i << 3) 0) as [E0|E0]; rewrite Hsh, to_Z_0 in E0.
    + replace (8 * to_Z i) with 0 by lia. rewrite Z.pow_0_r, Z.div_1_r.
      symmetry. apply wZ_mod_pow2. lia.
    + f_equal. rewrite add_spec, lsr_spec, Hsh, lsl_spec, i63_land1, i63_wB.
      rewrite i63_sub_small by (change (to_Z 63) with 63; lia).
      change (to_Z 63) with 63. rewrite Hsh, wZ_W64.
      pose proof (Z.mod_pos_bound (to_Z t) 2 ltac:(lia)) as Ht.
      destruct (Zsrl_arith (to_Z t mod 2) (to_Z l) (8 * to_Z i)) as [H1 H2];
        [apply i63_range | lia | lia |].
      rewrite H1. apply Z.mod_small. split; [|exact H2].
      apply Z.add_nonneg_nonneg.
      * apply Z.div_pos; [apply i63_range | apply Z.pow_pos_nonneg; clear - Hi0; lia].
      * apply Z.mod_pos_bound. clear. lia.
Qed.

Lemma wZ_w_extract_lt i s c :
  1 <= to_Z s -> to_Z i + to_Z s <= 8 ->
  0 <= wZ (w_extract i s c) < 2 ^ (8 * to_Z s).
Proof.
  intros Hs His. rewrite wZ_w_extract by assumption.
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

(* [comment removed for export] *)
Lemma Zins_hi f sh w :
  0 <= f < 2 ^ w -> 1 <= w -> 0 <= sh -> sh + w = 64 ->
  (f * 2 ^ sh) mod 2 ^ 63 = (f mod 2 ^ (w - 1)) * 2 ^ sh /\
  f * 2 ^ sh = (f / 2 ^ (w - 1)) * 2 ^ 63 + (f mod 2 ^ (w - 1)) * 2 ^ sh /\
  0 <= f / 2 ^ (w - 1) <= 1 /\
  0 <= (f mod 2 ^ (w - 1)) * 2 ^ sh <= 2 ^ 63 - 2 ^ sh.
Proof.
  intros Hf Hw Hsh He.
  assert (HPQ : 2 ^ (w - 1) * 2 ^ sh = 2 ^ 63).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (HW : 2 ^ w = 2 * 2 ^ (w - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  assert (HQ : 0 < 2 ^ (w - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (HP : 0 < 2 ^ sh) by (apply Z.pow_pos_nonneg; lia).
  set (Q := 2 ^ (w - 1)) in *. set (P := 2 ^ sh) in *.
  pose proof (Z.div_mod f Q ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound f Q ltac:(lia)) as Hr.
  assert (Hq : 0 <= f / Q <= 1).
  { split; [apply Z.div_pos; lia|].
    assert (f / Q < 2) by (apply Z.div_lt_upper_bound; lia). lia. }
  set (q := f / Q) in *. set (r := f mod Q) in *.
  assert (Hrb : 0 <= r * P <= 2 ^ 63 - P).
  { rewrite <- HPQ. split; [apply Z.mul_nonneg_nonneg; lia|].
    replace (Q * P - P) with ((Q - 1) * P) by ring.
    apply Z.mul_le_mono_nonneg_r; lia. }
  assert (Hsplit : f * P = q * 2 ^ 63 + r * P).
  { rewrite Hdm at 1. rewrite <- HPQ. ring. }
  split; [symmetry; apply (Z.mod_unique_pos _ _ q); [lia|]; rewrite Hsplit; ring|].
  repeat split; lia.
Qed.

Lemma Zins_lo t l e :
  0 <= l < 2 ^ 63 -> 0 <= e <= 63 ->
  (t * 2 ^ 63 + l) / 2 ^ e * 2 ^ e = t * 2 ^ 63 + l / 2 ^ e * 2 ^ e /\
  0 <= l / 2 ^ e * 2 ^ e <= 2 ^ 63 - 2 ^ e.
Proof.
  intros Hl He.
  pose proof (Zpow2_split e He) as HPQ.
  assert (HP : 0 < 2 ^ e) by (apply Z.pow_pos_nonneg; lia).
  assert (HQ : 0 < 2 ^ (63 - e)) by (apply Z.pow_pos_nonneg; lia).
  set (P := 2 ^ e) in *. set (Q := 2 ^ (63 - e)) in *.
  assert (Hd : 0 <= l / P <= Q - 1).
  { split; [apply Z.div_pos; lia|].
    assert (l / P < Q) by (apply Z.div_lt_upper_bound; lia). lia. }
  split.
  - replace (t * 2 ^ 63 + l) with (l + (t * Q) * P) by (rewrite <- HPQ; ring).
    rewrite Z.div_add by lia. rewrite <- HPQ. ring.
  - split; [apply Z.mul_nonneg_nonneg; lia|].
    rewrite <- HPQ. replace (P * Q - P) with ((Q - 1) * P) by ring.
    apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Theorem wZ_w_insert i s c v :
  1 <= to_Z s -> to_Z i + to_Z s <= 8 ->
  wZ (w_insert i s c v) =
  wZ c mod 2 ^ (8 * to_Z i)
  + (wZ v mod 2 ^ (8 * to_Z s)) * 2 ^ (8 * to_Z i)
  + (wZ c / 2 ^ (8 * (to_Z i + to_Z s))) * 2 ^ (8 * (to_Z i + to_Z s)).
Proof.
  intros Hs His. pose proof (i63_range i) as Hi0. unfold w_insert.
  destruct (eqbP s 8) as [E8|E8]; change (to_Z 8) with 8 in E8.
  - replace (to_Z i) with 0 by lia. rewrite E8.
    change (8 * (0 + 8)) with 64. change (8 * 0) with 0. change (8 * 8) with 64.
    pose proof (wZ_range c). pose proof (wZ_range v).
    rewrite Z.pow_0_r, Z.mod_1_r, Z.mul_1_r, Z.div_small, (Z.mod_small (wZ v)) by lia.
    lia.
  - destruct c as [t l], v as [tv vl]. cbv zeta.
    assert (Hsh : to_Z (i << 3)%uint63 = 8 * to_Z i) by (apply i63_lsl3; lia).
    assert (Hw : to_Z (s << 3)%uint63 = 8 * to_Z s) by (apply i63_lsl3; lia).
    assert (He : to_Z ((i << 3) + (s << 3))%uint63 = 8 * (to_Z i + to_Z s)).
    { rewrite add_spec, Hsh, Hw, i63_wB. rewrite Z.mod_small by lia. lia. }
    set (I := to_Z i) in *. set (S := to_Z s) in *.
    set (sh := (i << 3)%uint63) in *. set (w := (s << 3)%uint63) in *.
    assert (HPi : 0 < 2 ^ (8 * I)) by (apply Z.pow_pos_nonneg; clear - Hi0; lia).
    assert (HPs : 0 < 2 ^ (8 * S)) by (apply Z.pow_pos_nonneg; clear - Hs; lia).
    assert (HPe : 2 ^ (8 * (I + S)) = 2 ^ (8 * I) * 2 ^ (8 * S)).
    { rewrite <- Z.pow_add_r by (clear - Hi0 Hs; lia). f_equal. clear. lia. }
    assert (HS7 : S <= 7) by (clear - E8 His Hi0; lia).
    pose proof (i63_range l) as Hl.
    assert (Hf : to_Z (vl land ((1 << w) - 1))%uint63 = to_Z vl mod 2 ^ (8 * S)).
    { rewrite i63_land_mask by lia. rewrite Hw. reflexivity. }
    assert (Hlow : to_Z (l land ((1 << sh) - 1))%uint63 = to_Z l mod 2 ^ (8 * I)).
    { rewrite i63_land_mask by lia. rewrite Hsh. reflexivity. }
    set (f := (vl land ((1 << w) - 1))%uint63) in *.
    set (low := (l land ((1 << sh) - 1))%uint63) in *.
    pose proof (Z.mod_pos_bound (to_Z vl) (2 ^ (8 * S)) HPs) as Hfb.
    pose proof (Z.mod_pos_bound (to_Z l) (2 ^ (8 * I)) HPi) as Hlb.
    rewrite (wZ_mod_pow2 t l) by lia. rewrite (wZ_mod_pow2 tv vl) by lia.
    destruct (eqbP (sh + w) 64) as [E64|E64];
      rewrite He in E64; change (to_Z 64) with 64 in E64.
    + (* [comment removed for export] *)
      rewrite E64.
      pose proof (wZ_range (W64 t l)) as Hc.
      rewrite (Z.div_small (wZ (W64 t l)) (2 ^ 64)) by lia.
      rewrite Z.mul_0_l, Z.add_0_r.
      destruct (Zins_hi (to_Z vl mod 2 ^ (8 * S)) (8 * I) (8 * S))
        as (H1 & H2 & H3 & H4); [lia | lia | lia | lia |].
      rewrite wZ_W64, lsr_spec, add_spec, lsl_spec, i63_wB, Hf, Hlow, Hsh.
      rewrite i63_sub_small by (rewrite Hw, to_Z_1; clear - Hs; lia).
      rewrite Hw, to_Z_1.
      remember (to_Z vl mod 2 ^ (8 * S)) as fz eqn:Ef.
      remember (fz / 2 ^ (8 * S - 1)) as fh eqn:Efh.
      remember (fz mod 2 ^ (8 * S - 1)) as fl eqn:Efl.
      remember (to_Z l mod 2 ^ (8 * I)) as lw eqn:Elw.
      remember (2 ^ (8 * I)) as P eqn:EP.
      rewrite (Z.mod_small fh 2) by lia.
      rewrite H1.
      clear Ef Efh Efl Elw EP Hf Hlow H1 Hfb HPs.
      rewrite Z.mod_small by lia. lia.
    + (* [comment removed for export] *)
      assert (He56 : 8 * (I + S) <= 56) by lia.
      destruct (Zins_lo (to_Z t mod 2) (to_Z l) (8 * (I + S))) as [H1 H2]; [lia | lia |].
      rewrite (wZ_W64 t l), H1.
      assert (Hfs : 0 <= (to_Z vl mod 2 ^ (8 * S)) * 2 ^ (8 * I)
                    <= 2 ^ (8 * (I + S)) - 2 ^ (8 * I)).
      { split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite HPe.
        replace (2 ^ (8 * I) * 2 ^ (8 * S) - 2 ^ (8 * I))
          with ((2 ^ (8 * S) - 1) * 2 ^ (8 * I)) by ring.
        apply Z.mul_le_mono_nonneg_r; lia. }
      assert (HPe63 : 2 ^ (8 * (I + S)) <= 2 ^ 56)
        by (apply Z.pow_le_mono_r; clear - He56 Hi0 Hs; lia).
      rewrite wZ_W64, !add_spec, !lsl_spec, lsr_spec, i63_wB, Hf, Hlow, Hsh, He.
      remember (to_Z vl mod 2 ^ (8 * S)) as fz eqn:Ef.
      remember (to_Z l mod 2 ^ (8 * I)) as lw eqn:Elw.
      remember (to_Z l / 2 ^ (8 * (I + S)) * 2 ^ (8 * (I + S))) as hi eqn:Ehi.
      remember (fz * 2 ^ (8 * I)) as fs eqn:Efs.
      remember (2 ^ (8 * I)) as P eqn:EP.
      remember (2 ^ (8 * (I + S))) as Pe eqn:EPe.
      remember (to_Z t mod 2) as tt eqn:Ett.
      clear Ef Elw Ehi Efs EP EPe Ett Hf Hlow H1 HPe Hfb HPs.
      rewrite (Z.mod_small fs) by lia.
      rewrite (Z.mod_small hi) by lia.
      rewrite (Z.mod_small (lw + fs)) by lia.
      rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem to_Z_w_byte i w :
  to_Z i <= 7 -> to_Z (w_byte i w) = (wZ w / 2 ^ (8 * to_Z i)) mod 256.
Proof.
  intros Hi. destruct w as [t l]. unfold w_byte.
  pose proof (i63_range i) as Hi0. pose proof (i63_range l) as Hl.
  pose proof (Z.mod_pos_bound (to_Z t) 2 ltac:(lia)) as Ht.
  rewrite wZ_W64.
  destruct (eqbP i 7) as [E7|E7]; change (to_Z 7) with 7 in E7.
  - rewrite E7. change (8 * 7) with 56.
    rewrite add_spec, lsr_spec, lsl_spec, i63_land1, i63_wB.
    change (2 ^ to_Z 56) with (2 ^ 56). change (2 ^ to_Z 7) with (2 ^ 7).
    remember (to_Z t mod 2) as tt eqn:Ett. clear Ett. zlia.
  - assert (Hsh : to_Z (i << 3)%uint63 = 8 * to_Z i) by (apply i63_lsl3; lia).
    rewrite land_spec', lsr_spec, Hsh. change (to_Z 255) with (Z.ones 8).
    rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
    set (k := 8 * to_Z i) in *.
    assert (HP : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    assert (HPQ : 2 ^ 63 = 2 ^ (55 - k) * 256 * 2 ^ k).
    { change 256 with (2 ^ 8). rewrite <- !Z.pow_add_r by lia. f_equal. lia. }
    rewrite HPQ.
    replace (to_Z t mod 2 * (2 ^ (55 - k) * 256 * 2 ^ k) + to_Z l)
      with (to_Z l + (to_Z t mod 2 * 2 ^ (55 - k) * 256) * 2 ^ k) by ring.
    rewrite Z.div_add by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma to_Z_w_byte_lt i w : to_Z i <= 7 -> 0 <= to_Z (w_byte i w) < 256.
Proof. intros Hi. rewrite to_Z_w_byte by exact Hi. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Definition w_bytes (w : w64) : list byte := Z_to_le_bytes 8 (wZ w).

Lemma Z_to_bv8_mod z : Z_to_bv 8 (z mod 256) = Z_to_bv 8 z.
Proof.
  apply bv_eq. rewrite !Z_to_bv_unsigned. change (z mod 256) with (bv_wrap 8 z).
  apply bv_wrap_idemp.
Qed.

Lemma Z_to_le_bytes_map : forall n z,
  Z_to_le_bytes n z =
  map (fun j => Z_to_bv 8 (z / 2 ^ (8 * Z.of_nat j))) (seq 0 n).
Proof.
  induction n as [|n IH]; intros z; [reflexivity|].
  cbn [Z_to_le_bytes seq map]. f_equal.
  - change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r. reflexivity.
  - rewrite IH, <- seq_shift, map_map. apply map_ext. intros j.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia).
    rewrite <- Z.pow_add_r by lia. do 3 f_equal. lia.
Qed.

Lemma Z_to_le_bytes_nth n z j :
  (j < n)%nat ->
  nth_error (Z_to_le_bytes n z) j = Some (Z_to_bv 8 (z / 2 ^ (8 * Z.of_nat j))).
Proof.
  intros Hj. rewrite Z_to_le_bytes_map.
  rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec j n) as [_|?]; [|lia]. reflexivity.
Qed.

Lemma Z_to_le_bytes_app : forall n m z,
  Z_to_le_bytes (n + m) z =
  Z_to_le_bytes n z ++ Z_to_le_bytes m (z / 2 ^ (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros m z.
  - cbn [Nat.add Z_to_le_bytes app]. change (2 ^ (8 * Z.of_nat 0)) with 1.
    rewrite Z.div_1_r. reflexivity.
  - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH. f_equal. f_equal.
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.div_div by (try apply Z.pow_pos_nonneg; lia).
    rewrite <- Z.pow_add_r by lia. do 2 f_equal. lia.
Qed.

Lemma Z_to_le_bytes_mod : forall n m z,
  (n <= m)%nat ->
  Z_to_le_bytes n (z mod 2 ^ (8 * Z.of_nat m)) = Z_to_le_bytes n z.
Proof.
  intros n m z Hnm. rewrite !Z_to_le_bytes_map. apply map_ext_in.
  intros j Hj. apply in_seq in Hj.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with (2 ^ 8).
  set (a := 8 * Z.of_nat j). set (b := 8 * Z.of_nat m).
  assert (Hab : 0 <= a /\ a + 8 <= b) by (unfold a, b; lia).
  assert (HPa : 0 < 2 ^ a) by (apply Z.pow_pos_nonneg; lia).
  replace (2 ^ b) with (2 ^ a * (2 ^ 8 * 2 ^ (b - a - 8)))
    by (rewrite <- !Z.pow_add_r by lia; f_equal; lia).
  assert (HPc : 0 < 2 ^ (b - a - 8)) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm (2 ^ a)), Z.div_add by lia.
  rewrite (Z.div_small (z mod 2 ^ a)) by (apply Z.mod_pos_bound; lia).
  rewrite Z.add_0_l.
  rewrite Z.rem_mul_r by lia.
  rewrite (Z.mul_comm (2 ^ 8)), Z.mod_add by lia.
  apply Z.mod_mod. lia.
Qed.

Lemma length_w_bytes w : length (w_bytes w) = 8%nat.
Proof. apply length_Z_to_le_bytes. Qed.

Theorem le_bytes_to_word_w_bytes w : le_bytes_to_word (w_bytes w) = wbv w.
Proof.
  unfold le_bytes_to_word, w_bytes.
  rewrite bytes_le_to_Z_of_le_bytes by apply wZ_range.
  apply bv_eq. rewrite Z_to_bv_unsigned, wbv_unsigned.
  change (8 * Z.of_nat 8) with 64. rewrite bv_wrap64, Z.mod_mod by lia.
  apply Z.mod_small, wZ_range.
Qed.

Theorem w_bytes_eq w :
  w_bytes w =
  [ Z_to_bv 8 (to_Z (w_byte 0 w)); Z_to_bv 8 (to_Z (w_byte 1 w));
    Z_to_bv 8 (to_Z (w_byte 2 w)); Z_to_bv 8 (to_Z (w_byte 3 w));
    Z_to_bv 8 (to_Z (w_byte 4 w)); Z_to_bv 8 (to_Z (w_byte 5 w));
    Z_to_bv 8 (to_Z (w_byte 6 w)); Z_to_bv 8 (to_Z (w_byte 7 w)) ].
Proof.
  unfold w_bytes. rewrite Z_to_le_bytes_map. cbn [seq map].
  rewrite !to_Z_w_byte by (cbn; lia). rewrite !Z_to_bv8_mod.
  reflexivity.
Qed.

Corollary le_bytes_to_word_w_byte w :
  le_bytes_to_word
    [ Z_to_bv 8 (to_Z (w_byte 0 w)); Z_to_bv 8 (to_Z (w_byte 1 w));
      Z_to_bv 8 (to_Z (w_byte 2 w)); Z_to_bv 8 (to_Z (w_byte 3 w));
      Z_to_bv 8 (to_Z (w_byte 4 w)); Z_to_bv 8 (to_Z (w_byte 5 w));
      Z_to_bv 8 (to_Z (w_byte 6 w)); Z_to_bv 8 (to_Z (w_byte 7 w)) ] = wbv w.
Proof. rewrite <- w_bytes_eq. apply le_bytes_to_word_w_bytes. Qed.

Lemma w_bytes_nth w j :
  (j < 8)%nat ->
  nth_error (w_bytes w) j = Some (Z_to_bv 8 (wZ w / 2 ^ (8 * Z.of_nat j))).
Proof. apply Z_to_le_bytes_nth. Qed.

Lemma w_bytes_nth_byte w (i : int) :
  to_Z i <= 7 ->
  nth_error (w_bytes w) (Z.to_nat (to_Z i)) = Some (Z_to_bv 8 (to_Z (w_byte i w))).
Proof.
  intros Hi. pose proof (i63_range i) as Hi0.
  rewrite w_bytes_nth by lia. rewrite to_Z_w_byte by exact Hi.
  rewrite Z_to_bv8_mod, Z2Nat.id by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem w_bytes_extract (i s : int) c :
  1 <= to_Z s -> to_Z i + to_Z s <= 8 ->
  firstn (Z.to_nat (to_Z s)) (skipn (Z.to_nat (to_Z i)) (w_bytes c)) =
  Z_to_le_bytes (Z.to_nat (to_Z s)) (wZ (w_extract i s c)).
Proof.
  intros Hs His. pose proof (i63_range i) as Hi0.
  rewrite wZ_w_extract by assumption.
  set (ni := Z.to_nat (to_Z i)). set (ns := Z.to_nat (to_Z s)).
  assert (Hni : Z.of_nat ni = to_Z i) by (unfold ni; lia).
  assert (Hns : Z.of_nat ns = to_Z s) by (unfold ns; lia).
  rewrite <- Hni, <- Hns. rewrite Z_to_le_bytes_mod by lia.
  unfold w_bytes.
  replace 8%nat with (ni + (ns + (8 - ni - ns)))%nat by lia.
  rewrite Z_to_le_bytes_app, Z_to_le_bytes_app.
  rewrite skipn_app, skipn_all2 by (rewrite length_Z_to_le_bytes; lia).
  rewrite length_Z_to_le_bytes, Nat.sub_diag, skipn_O. cbn [app].
  rewrite firstn_app, firstn_all2 by (rewrite length_Z_to_le_bytes; lia).
  rewrite length_Z_to_le_bytes, Nat.sub_diag, firstn_O. apply app_nil_r.
Qed.

Theorem w_bytes_insert (i s : int) c v :
  1 <= to_Z s -> to_Z i + to_Z s <= 8 ->
  w_bytes (w_insert i s c v) =
  firstn (Z.to_nat (to_Z i)) (w_bytes c)
  ++ Z_to_le_bytes (Z.to_nat (to_Z s)) (wZ v)
  ++ skipn (Z.to_nat (to_Z i) + Z.to_nat (to_Z s)) (w_bytes c).
Proof.
  intros Hs His. pose proof (i63_range i) as Hi0.
  unfold w_bytes. rewrite wZ_w_insert by assumption.
  set (ni := Z.to_nat (to_Z i)). set (ns := Z.to_nat (to_Z s)).
  assert (Hni : Z.of_nat ni = to_Z i) by (unfold ni; lia).
  assert (Hns : Z.of_nat ns = to_Z s) by (unfold ns; lia).
  rewrite <- Hni, <- Hns.
  assert (Hlen : exists r, 8%nat = (ni + (ns + r))%nat)
    by (exists (8 - ni - ns)%nat; clear - Hni Hns His; lia).
  destruct Hlen as [r Hlen].
  set (z := wZ c). set (x := wZ v).
  set (a := 8 * Z.of_nat ni). set (b := 8 * Z.of_nat ns).
  replace (8 * (Z.of_nat ni + Z.of_nat ns)) with (a + b) by (unfold a, b; lia).
  assert (Ha : 0 <= a) by (unfold a; lia). assert (Hb : 0 <= b) by (unfold b; lia).
  assert (HPa : 0 < 2 ^ a) by (apply Z.pow_pos_nonneg; lia).
  assert (HPb : 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (HPab : 2 ^ (a + b) = 2 ^ a * 2 ^ b) by (apply Z.pow_add_r; lia).
  set (z' := z mod 2 ^ a + x mod 2 ^ b * 2 ^ a + z / 2 ^ (a + b) * 2 ^ (a + b)).
  assert (H1 : z' mod 2 ^ a = z mod 2 ^ a).
  { unfold z'. rewrite HPab.
    replace (z mod 2 ^ a + x mod 2 ^ b * 2 ^ a + z / (2 ^ a * 2 ^ b) * (2 ^ a * 2 ^ b))
      with (z mod 2 ^ a + (x mod 2 ^ b + z / (2 ^ a * 2 ^ b) * 2 ^ b) * 2 ^ a) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_mod. lia. }
  assert (H2 : z' / 2 ^ a = x mod 2 ^ b + z / 2 ^ (a + b) * 2 ^ b).
  { unfold z'. rewrite HPab.
    replace (z mod 2 ^ a + x mod 2 ^ b * 2 ^ a + z / (2 ^ a * 2 ^ b) * (2 ^ a * 2 ^ b))
      with (z mod 2 ^ a + (x mod 2 ^ b + z / (2 ^ a * 2 ^ b) * 2 ^ b) * 2 ^ a) by ring.
    rewrite Z.div_add by lia.
    rewrite Z.div_small by (apply Z.mod_pos_bound; lia). lia. }
  assert (H3 : (z' / 2 ^ a) mod 2 ^ b = x mod 2 ^ b).
  { rewrite H2, Z.mod_add by lia. apply Z.mod_mod. lia. }
  assert (H4 : z' / 2 ^ a / 2 ^ b = z / 2 ^ (a + b)).
  { rewrite H2, Z.div_add by lia.
    rewrite Z.div_small by (apply Z.mod_pos_bound; lia). lia. }
  rewrite Hlen.
  rewrite !Z_to_le_bytes_app. fold a b.
  rewrite firstn_app, firstn_all2 by (rewrite length_Z_to_le_bytes; lia).
  rewrite length_Z_to_le_bytes, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite skipn_app, skipn_all2 by (rewrite length_Z_to_le_bytes; lia).
  rewrite length_Z_to_le_bytes.
  replace (ni + ns - ni)%nat with ns by (clear; lia). cbn [app].
  rewrite skipn_app, skipn_all2 by (rewrite length_Z_to_le_bytes; lia).
  rewrite length_Z_to_le_bytes, Nat.sub_diag, skipn_O. cbn [app].
  f_equal; [|f_equal].
  - rewrite <- (Z_to_le_bytes_mod ni ni z'), <- (Z_to_le_bytes_mod ni ni z) by lia.
    fold a. rewrite H1. reflexivity.
  - rewrite <- (Z_to_le_bytes_mod ns ns (z' / 2 ^ a)), <- (Z_to_le_bytes_mod ns ns x) by lia.
    fold b. rewrite H3. reflexivity.
  - rewrite H4. rewrite Z.div_div by lia. rewrite <- HPab. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem load_value_of_bytes (n : N) (s : nat) x :
  0 <= x -> (s <= 8)%nat -> Z.of_N n = 8 * Z.of_nat s ->
  bv_extract 0 n (le_bytes_to_word (Z_to_le_bytes s x)) = Z_to_bv n x.
Proof.
  intros Hx Hs Hn. unfold le_bytes_to_word.
  rewrite bytes_le_to_Z_of_le_bytes by exact Hx.
  apply bv_eq. rewrite bv_extract_unsigned, !Z_to_bv_unsigned, Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus. rewrite Hn. change (Z.of_N 64) with 64.
  assert (HP : 0 < 2 ^ (8 * Z.of_nat s)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound x (2 ^ (8 * Z.of_nat s)) HP) as Hm.
  assert (2 ^ (8 * Z.of_nat s) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (Z.mod_small (x mod _) (2 ^ 64)) by lia.
  apply Z.mod_mod. lia.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_firstn n m z :
  (n <= m)%nat -> firstn n (Z_to_le_bytes m z) = Z_to_le_bytes n z.
Proof.
  intros Hnm. replace m with (n + (m - n))%nat by lia.
  rewrite Z_to_le_bytes_app, firstn_app, firstn_all2
    by (rewrite length_Z_to_le_bytes; lia).
  rewrite length_Z_to_le_bytes, Nat.sub_diag, firstn_O. apply app_nil_r.
Qed.

(* [comment removed for export] *)
Theorem store_bytes_of_word (nb : N) (s : nat) v :
  Z.of_N nb = 8 * Z.of_nat s -> (s <= 8)%nat ->
  Z_to_le_bytes s (bv_unsigned (bv_extract 0 nb (wbv v))) = Z_to_le_bytes s (wZ v).
Proof.
  intros Hn Hs. rewrite bv_extract_unsigned, Z.shiftr_0_r, wbv_unsigned.
  unfold bv_wrap, bv_modulus. rewrite Hn. apply Z_to_le_bytes_mod. lia.
Qed.

Corollary store_bytes_firstn (nb : N) (s : nat) v :
  Z.of_N nb = 8 * Z.of_nat s -> (s <= 8)%nat ->
  Z_to_le_bytes s (bv_unsigned (bv_extract 0 nb (wbv v))) = firstn s (w_bytes v).
Proof.
  intros Hn Hs. rewrite store_bytes_of_word by assumption.
  symmetry. apply Z_to_le_bytes_firstn. exact Hs.
Qed.

Lemma store_bytes_64 v : Z_to_le_bytes 8 (bv_unsigned (wbv v)) = w_bytes v.
Proof. rewrite wbv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Theorem w_load_bytes (i s : int) c :
  1 <= to_Z s -> to_Z i + to_Z s <= 8 ->
  le_bytes_to_word
    (firstn (Z.to_nat (to_Z s)) (skipn (Z.to_nat (to_Z i)) (w_bytes c)))
  = wbv (w_extract i s c).
Proof.
  intros Hs His. pose proof (i63_range i) as Hi0.
  rewrite w_bytes_extract by assumption.
  pose proof (wZ_w_extract_lt i s c Hs His) as Hlt.
  unfold le_bytes_to_word. rewrite bytes_le_to_Z_of_le_bytes by lia.
  rewrite Z2Nat.id by lia. rewrite Z.mod_small by exact Hlt. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wbv_w_zext8_small w : wZ w < 2 ^ 8 -> wbv (w_zext8 w) = wbv w.
Proof.
  intros H. apply wbv_eq_iff. rewrite wZ_w_zext8. apply Z.mod_small.
  pose proof (wZ_range w). lia.
Qed.
Lemma wbv_w_zext16_small w : wZ w < 2 ^ 16 -> wbv (w_zext16 w) = wbv w.
Proof.
  intros H. apply wbv_eq_iff. rewrite wZ_w_zext16. apply Z.mod_small.
  pose proof (wZ_range w). lia.
Qed.
Lemma wbv_w_zext32_small w : wZ w < 2 ^ 32 -> wbv (w_zext32 w) = wbv w.
Proof.
  intros H. apply wbv_eq_iff. rewrite wZ_w_zext32. apply Z.mod_small.
  pose proof (wZ_range w). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section OfBytes.
Local Open Scope uint63_scope.

(* [comment removed for export] *)
Definition w_of_bytes8 (b0 b1 b2 b3 b4 b5 b6 b7 : int) : w64 :=
  W64 (b7 >> 7)
      (b0 + (b1 << 8) + (b2 << 16) + (b3 << 24) + (b4 << 32) + (b5 << 40)
       + (b6 << 48) + ((b7 land 127) << 56)).

End OfBytes.

Theorem wZ_w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7 :
  to_Z b0 < 256 -> to_Z b1 < 256 -> to_Z b2 < 256 -> to_Z b3 < 256 ->
  to_Z b4 < 256 -> to_Z b5 < 256 -> to_Z b6 < 256 -> to_Z b7 < 256 ->
  wZ (w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7) =
  to_Z b0 + 2 ^ 8 * to_Z b1 + 2 ^ 16 * to_Z b2 + 2 ^ 24 * to_Z b3
  + 2 ^ 32 * to_Z b4 + 2 ^ 40 * to_Z b5 + 2 ^ 48 * to_Z b6 + 2 ^ 56 * to_Z b7.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7. unfold w_of_bytes8.
  rewrite wZ_W64, !add_spec, !lsl_spec, lsr_spec, land_spec', i63_wB.
  change (to_Z 127) with (Z.ones 7). rewrite Z.land_ones by lia.
  change (2 ^ to_Z 7) with (2 ^ 7). change (2 ^ to_Z 8) with (2 ^ 8).
  change (2 ^ to_Z 16) with (2 ^ 16). change (2 ^ to_Z 24) with (2 ^ 24).
  change (2 ^ to_Z 32) with (2 ^ 32). change (2 ^ to_Z 40) with (2 ^ 40).
  change (2 ^ to_Z 48) with (2 ^ 48). change (2 ^ to_Z 56) with (2 ^ 56).
  w64_ranges. zlia.
Qed.

Theorem w_byte_w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7 :
  to_Z b0 < 256 -> to_Z b1 < 256 -> to_Z b2 < 256 -> to_Z b3 < 256 ->
  to_Z b4 < 256 -> to_Z b5 < 256 -> to_Z b6 < 256 -> to_Z b7 < 256 ->
  let w := w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7 in
  w_byte 0 w = b0 /\ w_byte 1 w = b1 /\ w_byte 2 w = b2 /\ w_byte 3 w = b3 /\
  w_byte 4 w = b4 /\ w_byte 5 w = b5 /\ w_byte 6 w = b6 /\ w_byte 7 w = b7.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7 w.
  pose proof (wZ_w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7 H0 H1 H2 H3 H4 H5 H6 H7) as Hw.
  fold w in Hw.
  pose proof (i63_range b0). pose proof (i63_range b1). pose proof (i63_range b2).
  pose proof (i63_range b3). pose proof (i63_range b4). pose proof (i63_range b5).
  pose proof (i63_range b6). pose proof (i63_range b7).
  repeat split; apply to_Z_inj; rewrite to_Z_w_byte by (cbn; lia); rewrite Hw;
    match goal with
    | |- context [2 ^ (8 * to_Z ?j)] =>
        let e := eval cbv in (8 * to_Z j) in change (8 * to_Z j) with e
    end; clear Hw; zlia.
Qed.

Corollary w_bytes_w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7 :
  to_Z b0 < 256 -> to_Z b1 < 256 -> to_Z b2 < 256 -> to_Z b3 < 256 ->
  to_Z b4 < 256 -> to_Z b5 < 256 -> to_Z b6 < 256 -> to_Z b7 < 256 ->
  w_bytes (w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7) =
  [ Z_to_bv 8 (to_Z b0); Z_to_bv 8 (to_Z b1); Z_to_bv 8 (to_Z b2);
    Z_to_bv 8 (to_Z b3); Z_to_bv 8 (to_Z b4); Z_to_bv 8 (to_Z b5);
    Z_to_bv 8 (to_Z b6); Z_to_bv 8 (to_Z b7) ].
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 H7.
  destruct (w_byte_w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7 H0 H1 H2 H3 H4 H5 H6 H7)
    as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7).
  rewrite w_bytes_eq, E0, E1, E2, E3, E4, E5, E6, E7. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Conv.
Local Open Scope uint63_scope.

(* [comment removed for export] *)
Definition w_addi (a : w64) (i : int) : w64 :=
  match a with
  | W64 ta la =>
      let lo := la + i in
      if lo <? la then W64 (ta lxor 1) lo else W64 ta lo
  end.

Definition w_subi (a : w64) (i : int) : w64 :=
  match a with
  | W64 ta la => if la <? i then W64 (ta lxor 1) (la - i) else W64 ta (la - i)
  end.

(* [comment removed for export] *)
Definition w_andi (a : w64) (m : int) : w64 :=
  match a with W64 _ la => W64 0 (la land m) end.

(* [comment removed for export] *)
Definition w_jalr_target (a imm : w64) : w64 :=
  match w_add a imm with W64 t l => W64 t ((l >> 1) << 1) end.

(* [comment removed for export] *)
Definition w_fits63 (a : w64) : bool :=
  match a with W64 ta _ => (ta land 1) =? 0 end.

End Conv.

Lemma wZ_w_addi a i : wZ (w_addi a i) = (wZ a + to_Z i) mod 2 ^ 64.
Proof.
  destruct a as [ta la]. unfold w_addi. cbv zeta.
  destruct (ltbP (la + i) la) as [H|H]; rewrite add_spec, i63_wB in H;
    rewrite !wZ_W64, ?i63_lxor_mod2, add_spec, i63_wB, ?to_Z_1;
    w64_ranges; w64_top ta; zlia.
Qed.

Lemma wZ_w_subi a i : wZ (w_subi a i) = (wZ a - to_Z i) mod 2 ^ 64.
Proof.
  destruct a as [ta la]. unfold w_subi.
  destruct (ltbP la i) as [H|H];
    rewrite !wZ_W64, ?i63_lxor_mod2, sub_spec, i63_wB, ?to_Z_1;
    w64_ranges; w64_top ta; zlia.
Qed.

Lemma wbv_w_addi a i : wbv (w_addi a i) = (wbv a + Z_to_bv 64 (to_Z i))%bv.
Proof.
  apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, wbv_unsigned, wZ_w_addi.
  rewrite Z_to_bv_unsigned, !bv_wrap64. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma wbv_w_subi a i : wbv (w_subi a i) = (wbv a - Z_to_bv 64 (to_Z i))%bv.
Proof.
  apply bv_eq. rewrite bv_sub_unsigned, wbv_unsigned, wbv_unsigned, wZ_w_subi.
  rewrite Z_to_bv_unsigned, !bv_wrap64. rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma wZ_w_andi a m : wZ (w_andi a m) = Z.land (wZ a) (to_Z m).
Proof.
  destruct a as [ta la]. unfold w_andi.
  transitivity (wZ (W64 (ta land 0) (la land m))).
  { rewrite land0_r. reflexivity. }
  rewrite (w_bitop_spec Uint63.land Z.land andb land_spec' Z.land_spec eq_refl).
  reflexivity.
Qed.

Lemma Zland_clear_bit0 x : 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 2) = 2 * (x / 2).
Proof.
  intros Hx. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec.
  change (2 ^ 64 - 2) with (Z.shiftl (Z.ones 63) 1).
  replace (2 * (x / 2)) with (Z.shiftl (Z.shiftr x 1) 1)
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; change (2 ^ 1) with 2; ring).
  rewrite !Z.shiftl_spec by lia.
  destruct (Z.eq_dec i 0) as [->|Hne].
  - change (0 - 1) with (-1). rewrite (Z.testbit_neg_r (Z.ones 63) (-1)) by lia.
    rewrite (Z.testbit_neg_r (Z.shiftr x 1) (-1)) by lia. apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - 1 + 1) with i by lia.
    destruct (Z.lt_ge_cases i 64) as [Hlt|Hge].
    + rewrite Z.ones_spec_low by lia. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
      symmetry. rewrite <- (Z.mod_small x (2 ^ 64)) by lia.
      apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma wZ_w_jalr_target a imm :
  wZ (w_jalr_target a imm) = 2 * (((wZ a + wZ imm) mod 2 ^ 64) / 2).
Proof.
  unfold w_jalr_target. rewrite <- wZ_w_add.
  destruct (w_add a imm) as [t l].
  rewrite !wZ_W64, lsl_spec, lsr_spec, i63_wB. change (2 ^ to_Z 1) with 2.
  w64_ranges. w64_top t; zlia.
Qed.

Lemma wbv_w_jalr_target a imm :
  wbv (w_jalr_target a imm) = bv_and (wbv a + wbv imm) (bv_not w1).
Proof.
  apply bv_eq. rewrite bv_and_unsigned, bv_add_unsigned, !wbv_unsigned, bv_wrap64.
  change (bv_unsigned (bv_not w1)) with (2 ^ 64 - 2).
  rewrite Zland_clear_bit0 by (apply Z.mod_pos_bound; lia).
  apply wZ_w_jalr_target.
Qed.

Lemma w_fits63_spec a : w_fits63 a = (wZ a <? 2 ^ 63).
Proof.
  destruct a as [ta la]. unfold w_fits63. rewrite wZ_W64.
  pose proof (i63_range la).
  destruct (eqbP (ta land 1) 0) as [E|E]; rewrite i63_land1, to_Z_0 in E;
    symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; w64_top ta; unfold Zpar in *; lia.
Qed.

Lemma w_fits63_wlo a : w_fits63 a = true -> to_Z (wlo a) = wZ a.
Proof.
  destruct a as [ta la]. unfold w_fits63. cbn [wlo]. rewrite wZ_W64.
  intros E. apply Uint63.eqb_spec in E. apply (f_equal to_Z) in E.
  rewrite i63_land1, to_Z_0 in E. rewrite E. lia.
Qed.

Lemma wlo_mod_pow2 a n : 0 <= n <= 63 -> to_Z (wlo a) mod 2 ^ n = wZ a mod 2 ^ n.
Proof. intros Hn. destruct a as [t l]. symmetry. apply wZ_mod_pow2. exact Hn. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma i63_lt2_cases (t : int) : to_Z t < 2 -> t = 0%uint63 \/ t = 1%uint63.
Proof.
  intros H. pose proof (i63_range t).
  assert (to_Z t = 0 \/ to_Z t = 1) as [E|E] by lia; [left | right];
    apply to_Z_inj; exact E.
Qed.

Lemma w_nf_W64_0 l : w_nf (W64 0 l).
Proof. unfold w_nf. cbn. lia. Qed.
Lemma w_nf_W64_1 l : w_nf (W64 1 l).
Proof. unfold w_nf. cbn. lia. Qed.
Lemma w_nf_land1 t l : w_nf (W64 (t land 1) l).
Proof.
  unfold w_nf. cbn [wtop]. rewrite i63_land1.
  pose proof (Z.mod_pos_bound (to_Z t) 2 ltac:(lia)). lia.
Qed.

Lemma w_zero_nf : w_nf w_zero. Proof. apply w_nf_W64_0. Qed.
Lemma w_one_nf : w_nf w_one. Proof. apply w_nf_W64_0. Qed.
Lemma w_ones_nf : w_nf w_ones. Proof. apply w_nf_W64_1. Qed.
Lemma w_of_int_nf i : w_nf (w_of_int i). Proof. apply w_nf_W64_0. Qed.
Lemma w_of_bv_nf b : w_nf (w_of_bv b). Proof. apply w_of_Z_nf. Qed.

Local Ltac w_nf_cases :=
  repeat match goal with
  | H : w_nf (W64 ?t _) |- _ =>
      unfold w_nf in H; cbn [wtop] in H;
      destruct (i63_lt2_cases t H) as [-> | ->]; clear H
  end.

Local Ltac w_nf_solve :=
  repeat match goal with
  | |- w_nf (if ?c then _ else _) => destruct c
  | |- w_nf (W64 (_ land 1) _) => apply w_nf_land1
  | |- w_nf (W64 0 _) => apply w_nf_W64_0
  | |- w_nf (W64 1 _) => apply w_nf_W64_1
  | |- w_nf (W64 _ _) => unfold w_nf; cbn [wtop]; reflexivity
  end.

Lemma w_add_nf a b : w_nf a -> w_nf b -> w_nf (w_add a b).
Proof.
  destruct a as [ta la], b as [tb lb]. intros Ha Hb. w_nf_cases;
    unfold w_add; cbv zeta; w_nf_solve.
Qed.
Lemma w_sub_nf a b : w_nf a -> w_nf b -> w_nf (w_sub a b).
Proof.
  destruct a as [ta la], b as [tb lb]. intros Ha Hb. w_nf_cases;
    unfold w_sub; w_nf_solve.
Qed.
Lemma w_and_nf a b : w_nf a -> w_nf b -> w_nf (w_and a b).
Proof.
  destruct a as [ta la], b as [tb lb]. intros Ha Hb. w_nf_cases;
    unfold w_and; w_nf_solve.
Qed.
Lemma w_or_nf a b : w_nf a -> w_nf b -> w_nf (w_or a b).
Proof.
  destruct a as [ta la], b as [tb lb]. intros Ha Hb. w_nf_cases;
    unfold w_or; w_nf_solve.
Qed.
Lemma w_xor_nf a b : w_nf a -> w_nf b -> w_nf (w_xor a b).
Proof.
  destruct a as [ta la], b as [tb lb]. intros Ha Hb. w_nf_cases;
    unfold w_xor; w_nf_solve.
Qed.
Lemma w_sll_nf a b : w_nf a -> w_nf (w_sll a b).
Proof.
  destruct a as [ta la], b as [tb lb]. intros Ha. unfold w_sll. cbv zeta.
  destruct (_ =? _)%uint63; [exact Ha | apply w_nf_land1].
Qed.
Lemma w_srl_nf a b : w_nf a -> w_nf (w_srl a b).
Proof.
  destruct a as [ta la], b as [tb lb]. intros Ha. unfold w_srl. cbv zeta.
  destruct (_ =? _)%uint63; [exact Ha | apply w_nf_W64_0].
Qed.
Lemma w_sra_nf a b : w_nf (w_sra a b).
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_sra. cbv zeta. w_nf_solve.
Qed.
Lemma w_slt_nf a b : w_nf (w_slt a b).
Proof. unfold w_slt. destruct (w_lts a b); apply w_nf_W64_0. Qed.
Lemma w_sltu_nf a b : w_nf (w_sltu a b).
Proof. unfold w_sltu. destruct (w_ltu a b); apply w_nf_W64_0. Qed.

Theorem w_alu_nf op a b : w_nf a -> w_nf b -> w_nf (w_alu op a b).
Proof.
  intros Ha Hb. destruct op; cbn [w_alu];
    auto using w_add_nf, w_sub_nf, w_sll_nf, w_slt_nf, w_sltu_nf, w_xor_nf,
      w_srl_nf, w_sra_nf, w_or_nf, w_and_nf.
Qed.

Lemma w_sext8_nf w : w_nf (w_sext8 w).
Proof. destruct w. unfold w_sext8. cbv zeta. w_nf_solve. Qed.
Lemma w_sext16_nf w : w_nf (w_sext16 w).
Proof. destruct w. unfold w_sext16. cbv zeta. w_nf_solve. Qed.
Lemma w_sext32_nf w : w_nf (w_sext32 w).
Proof. destruct w. unfold w_sext32. cbv zeta. w_nf_solve. Qed.
Lemma w_zext8_nf w : w_nf (w_zext8 w).
Proof. destruct w. apply w_nf_W64_0. Qed.
Lemma w_zext16_nf w : w_nf (w_zext16 w).
Proof. destruct w. apply w_nf_W64_0. Qed.
Lemma w_zext32_nf w : w_nf (w_zext32 w).
Proof. destruct w. apply w_nf_W64_0. Qed.

Theorem w_alu32_nf op a b : w_nf (w_alu32 op a b).
Proof.
  destruct op; cbn [w_alu32]; try apply w_of_bv_nf;
    destruct a as [ta la], b as [tb lb].
  - unfold w_addw. cbv zeta. w_nf_solve.
  - unfold w_subw. cbv zeta. w_nf_solve.
  - unfold w_sllw. cbv zeta. w_nf_solve.
  - unfold w_srlw. cbv zeta. w_nf_solve.
  - unfold w_sraw. apply w_sra_nf.
Qed.

Lemma w_mulhu_nf a b : w_nf (w_mulhu a b).
Proof.
  destruct a as [ta la], b as [tb lb]. unfold w_mulhu.
  destruct (mulc la lb) as [h l]. cbv zeta.
  destruct (_ =? _)%uint63; [apply w_nf_W64_0|].
  unfold w_nf. cbn [wtop]. rewrite lsr_spec, !add_spec, i63_land1, i63_wB.
  change (2 ^ to_Z 1) with 2.
  pose proof (Z.mod_pos_bound (to_Z (ta land tb)) 2 ltac:(lia)).
  destruct (_ <? _)%uint63, (_ <? _)%uint63; rewrite ?to_Z_0, ?to_Z_1; zlia.
Qed.

Theorem w_muldiv_nf op a b : w_nf a -> w_nf b -> w_nf (w_muldiv op a b).
Proof.
  intros Ha Hb. destruct op; cbn [w_muldiv].
  - destruct a as [ta la], b as [tb lb]. unfold w_mul.
    destruct (mulc la lb). apply w_nf_land1.
  - unfold w_mulh. cbv zeta.
    destruct (w_neg_top a), (w_neg_top b);
      auto using w_sub_nf, w_mulhu_nf.
  - unfold w_mulhsu. cbv zeta. destruct (w_neg_top a); auto using w_sub_nf, w_mulhu_nf.
  - apply w_mulhu_nf.
  - destruct a as [ta la], b as [tb lb]. unfold w_div, w_muldiv_slow.
    repeat (destruct (_ =? _)%uint63); auto using w_nf_W64_0, w_ones_nf, w_of_bv_nf.
  - destruct a as [ta la], b as [tb lb]. unfold w_divu, w_muldiv_slow.
    repeat (destruct (_ =? _)%uint63); auto using w_nf_W64_0, w_ones_nf, w_of_bv_nf.
  - destruct a as [ta la], b as [tb lb]. unfold w_rem, w_muldiv_slow.
    repeat (destruct (_ =? _)%uint63); auto using w_nf_W64_0, w_ones_nf, w_of_bv_nf.
  - destruct a as [ta la], b as [tb lb]. unfold w_remu, w_muldiv_slow.
    repeat (destruct (_ =? _)%uint63); auto using w_nf_W64_0, w_ones_nf, w_of_bv_nf.
Qed.

Theorem w_muldiv32_nf op a b : w_nf (w_muldiv32 op a b).
Proof.
  destruct op; cbn [w_muldiv32]; try apply w_of_bv_nf;
    destruct a as [ta la], b as [tb lb].
  - unfold w_mulw. cbv zeta. w_nf_solve.
  - unfold w_divw, w_muldiv32_slow. cbv zeta.
    repeat (destruct (_ <? _)%uint63); try apply w_of_bv_nf.
    destruct (_ =? _)%uint63; auto using w_nf_W64_0, w_ones_nf.
  - unfold w_divuw. cbv zeta.
    destruct (_ =? _)%uint63; [apply w_ones_nf | w_nf_solve].
  - unfold w_remw, w_muldiv32_slow. cbv zeta.
    repeat (destruct (_ <? _)%uint63); try apply w_of_bv_nf.
    destruct (_ =? _)%uint63; auto using w_nf_W64_0.
  - unfold w_remuw. cbv zeta.
    destruct (_ =? _)%uint63; w_nf_solve.
Qed.

Theorem w_amo_nf op a b : w_nf a -> w_nf b -> w_nf (w_amo op a b).
Proof.
  intros Ha Hb. destruct op; cbn [w_amo];
    repeat match goal with |- w_nf (if ?c then _ else _) => destruct c end;
    auto using w_add_nf, w_xor_nf, w_and_nf, w_or_nf.
Qed.

Theorem w_amo32_nf op a b : w_nf a -> w_nf b -> w_nf (w_amo32 op a b).
Proof.
  intros Ha Hb. destruct op; cbn [w_amo32];
    repeat match goal with |- w_nf (if ?c then _ else _) => destruct c end;
    auto using w_add_nf, w_xor_nf, w_and_nf, w_or_nf.
Qed.

Lemma w_extract_nf i s c : w_nf c -> w_nf (w_extract i s c).
Proof.
  intros Hc. unfold w_extract. destruct (_ =? _)%uint63; [exact Hc|].
  destruct c. apply w_nf_W64_0.
Qed.

Lemma w_insert_nf i s c v :
  1 <= to_Z s -> to_Z i + to_Z s <= 8 -> w_nf c -> w_nf v -> w_nf (w_insert i s c v).
Proof.
  intros Hs His Hc Hv. pose proof (i63_range i) as Hi0. unfold w_insert.
  destruct (eqbP s 8) as [E8|E8]; [exact Hv|]. change (to_Z 8) with 8 in E8.
  destruct c as [t l], v as [tv vl]. cbv zeta.
  destruct (_ =? _)%uint63; [|exact Hc].
  unfold w_nf. cbn [wtop].
  assert (Hw : to_Z (s << 3)%uint63 = 8 * to_Z s) by (apply i63_lsl3; lia).
  rewrite lsr_spec, i63_land_mask by lia.
  rewrite i63_sub_small by (rewrite Hw, to_Z_1; lia). rewrite Hw, to_Z_1.
  assert (HP : 0 < 2 ^ (8 * to_Z s - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (HW : 2 ^ (8 * to_Z s) = 2 * 2 ^ (8 * to_Z s - 1)).
  { rewrite <- Z.pow_succ_r by lia. f_equal. lia. }
  pose proof (Z.mod_pos_bound (to_Z vl) (2 ^ (8 * to_Z s)) ltac:(lia)) as Hf.
  apply Z.div_lt_upper_bound; [exact HP|].
  remember (to_Z vl mod 2 ^ (8 * to_Z s)) as f. remember (2 ^ (8 * to_Z s - 1)) as P.
  clear - Hf HW. lia.
Qed.

Lemma w_of_bytes8_nf b0 b1 b2 b3 b4 b5 b6 b7 :
  to_Z b7 < 256 -> w_nf (w_of_bytes8 b0 b1 b2 b3 b4 b5 b6 b7).
Proof.
  intros H7. unfold w_nf, w_of_bytes8. cbn [wtop]. rewrite lsr_spec.
  change (2 ^ to_Z 7) with 128. pose proof (i63_range b7). zlia.
Qed.

Lemma w_addi_nf a i : w_nf a -> w_nf (w_addi a i).
Proof.
  destruct a as [ta la]. intros Ha. w_nf_cases; unfold w_addi; cbv zeta; w_nf_solve.
Qed.
Lemma w_subi_nf a i : w_nf a -> w_nf (w_subi a i).
Proof.
  destruct a as [ta la]. intros Ha. w_nf_cases; unfold w_subi; w_nf_solve.
Qed.
Lemma w_andi_nf a m : w_nf (w_andi a m).
Proof. destruct a. apply w_nf_W64_0. Qed.
Lemma w_jalr_target_nf a imm : w_nf a -> w_nf imm -> w_nf (w_jalr_target a imm).
Proof.
  intros Ha Hb. unfold w_jalr_target. pose proof (w_add_nf a imm Ha Hb) as H.
  destruct (w_add a imm). exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma low32_sext64 {n : N} (b : bv n) : low32 (sext 64 b) = sext 32 b.
Proof.
  apply bv_eq. rewrite bv_low32_unsigned. unfold sext.
  rewrite !bv_sign_extend_unsigned.
  change (bv_wrap 64 (bv_signed b) mod 2 ^ 32)
    with (bv_wrap 32 (bv_wrap 64 (bv_signed b))).
  apply bv_wrap_bv_wrap. lia.
Qed.

Lemma low32_zext64 {n : N} (b : bv n) : low32 (zext 64 b) = zext 32 b.
Proof.
  apply bv_eq. rewrite bv_low32_unsigned. unfold zext.
  rewrite !bv_zero_extend_unsigned'.
  change (bv_wrap 64 (bv_unsigned b) mod 2 ^ 32)
    with (bv_wrap 32 (bv_wrap 64 (bv_unsigned b))).
  apply bv_wrap_bv_wrap. lia.
Qed.

(* [comment removed for export] *)
Corollary w_alu32_imm_spec op a {n : N} (imm : bv n) :
  wbv (w_alu32 op a (w_of_bv (sext 64 imm))) =
  sext 64 (alu32 op (low32 (wbv a)) (sext 32 imm)).
Proof. rewrite w_alu32_spec, wbv_w_of_bv, low32_sext64. reflexivity. Qed.

Corollary w_alu32_shamt_spec op a {n : N} (sh : bv n) :
  wbv (w_alu32 op a (w_of_bv (zext 64 sh))) =
  sext 64 (alu32 op (low32 (wbv a)) (zext 32 sh)).
Proof. rewrite w_alu32_spec, wbv_w_of_bv, low32_zext64. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Module W64Tests.
  Local Open Scope Z_scope.
  Definition T (z : Z) : w64 := w_of_Z z.
  Definition m1 : Z := 2 ^ 64 - 1.          (* [comment removed for export] *)
  Definition smin : Z := 2 ^ 63.            (* [comment removed for export] *)
  Definition smax : Z := 2 ^ 63 - 1.
  Definition neg (z : Z) : Z := 2 ^ 64 - z. (* [comment removed for export] *)

  (* [comment removed for export] *)
  Goal wZ (w_add (T m1) (T 1)) = 0. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_add (T smax) (T 1)) = smin. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sub (T 0) (T 1)) = m1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sub (T smin) (T 1)) = smax. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sll (T 1) (T 63)) = smin. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sll (T 3) (T 63)) = smin. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sll (T 5) (T 64)) = 5. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_srl (T m1) (T 1)) = smax. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_srl (T smin) (T 63)) = 1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sra (T (neg 8)) (T 1)) = neg 4. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sra (T smin) (T 63)) = m1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sra (T (neg 8)) (T 0)) = neg 8. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sra (T smax) (T 62)) = 1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_slt (T m1) (T 0)) = 1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sltu (T m1) (T 0)) = 0. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_slt (T smin) (T smax)) = 1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sltu (T smin) (T smax)) = 0. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sltu (T smax) (T smin)) = 1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_slt (T 5) (T 5)) = 0. Proof. vm_compute. reflexivity. Qed.
  Goal w_eqb (W64 2 7) (W64 0 7) = true. Proof. vm_compute. reflexivity. Qed.
  Goal w_eqb (W64 1 7) (W64 0 7) = false. Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition A : Z := 0xFEDCBA9876543210.
  Definition B : Z := 0x923456789ABCDEF1.
  Goal wZ (w_mul (T A) (T B)) = (A * B) mod 2 ^ 64. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_mulhu (T A) (T B)) = (A * B) / 2 ^ 64. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_mulh (T A) (T B)) = ((A - 2 ^ 64) * (B - 2 ^ 64) / 2 ^ 64) mod 2 ^ 64.
  Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_mulhsu (T A) (T B)) = ((A - 2 ^ 64) * B / 2 ^ 64) mod 2 ^ 64.
  Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_mulhu (T m1) (T m1)) = 2 ^ 64 - 2. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_divu (T 7) (T 0)) = m1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_remu (T 7) (T 0)) = 7. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_div (T smin) (T m1)) = smin. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_rem (T smin) (T m1)) = 0. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_div (T (neg 7)) (T 2)) = neg 3. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_rem (T (neg 7)) (T 2)) = neg 1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_divu (T m1) (T 2)) = smax. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_div (T 100) (T 7)) = 14. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_rem (T 100) (T 7)) = 2. Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition sx (z : Z) : Z := 0xFFFFFFFF00000000 + z.
  Goal wZ (w_addw (T 0x7FFFFFFF) (T 1)) = sx 0x80000000. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_addw (T 0xFFFFFFFF) (T 1)) = 0. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_subw (T 0) (T 1)) = m1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sllw (T 1) (T 31)) = sx 0x80000000. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sllw (T 1) (T 32)) = 1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_srlw (T 0x80000000) (T 0)) = sx 0x80000000. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_srlw (T 0x1234567880000000) (T 4)) = 0x08000000. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sraw (T 0x80000000) (T 4)) = sx 0xF8000000. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sraw (T 0x40000000) (T 4)) = 0x04000000. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_mulw (T 0x10000) (T 0x8000)) = sx 0x80000000. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_divw (T (neg 7)) (T 2)) = neg 3. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_remw (T (neg 7)) (T 2)) = neg 1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_divw (T 7) (T 0)) = m1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_divw (T 0x80000000) (T 0xFFFFFFFF)) = sx 0x80000000. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_divuw (T 0xFFFFFFFF) (T 2)) = 0x7FFFFFFF. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_divuw (T 0x100000002) (T 2)) = 1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_remuw (T 0xFFFFFFFF) (T 0)) = m1. Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition C : Z := 0x8877665544332211.
  Goal wZ (w_sext8 (T 0x80)) = neg 0x80. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sext16 (T 0x17FFF)) = 0x7FFF. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_sext32 (T C)) = 0x44332211. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_zext32 (T m1)) = 0xFFFFFFFF. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_extract 7 1 (T C)) = 0x88. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_extract 4 4 (T C)) = 0x88776655. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_extract 6 2 (T C)) = 0x8877. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_extract 0 4 (T C)) = 0x44332211. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_extract 3 2 (T C)) = 0x5544. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_extract 0 8 (T C)) = C. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_insert 7 1 (T C) (T 0x1FF)) = 0xFF77665544332211. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_insert 7 1 (T C) (T 0x17F)) = 0x7F77665544332211. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_insert 4 4 (T C) (T 0xAABBCCDDEEFF0011)) = 0xEEFF001144332211.
  Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_insert 0 4 (T C) (T m1)) = 0x88776655FFFFFFFF. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_insert 3 2 (T C) (T 0xABCD)) = 0x887766ABCD332211. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_insert 0 8 (T C) (T 5)) = 5. Proof. vm_compute. reflexivity. Qed.
  Goal (w_byte 0 (T C), w_byte 3 (T C), w_byte 7 (T C)) = (0x11, 0x44, 0x88)%uint63.
  Proof. vm_compute. reflexivity. Qed.
  Goal w_of_bytes8 0x11 0x22 0x33 0x44 0x55 0x66 0x77 0x88 = T C.
  Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_jalr_target (T 0x1003) (T (neg 2))) = 0x1000. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_addi (T m1) 2) = 1. Proof. vm_compute. reflexivity. Qed.
  Goal wZ (w_subi (T 1) 2) = m1. Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition vals : list Z :=
    [0; 1; 2; 31; 32; 63; 64; 0x7FFFFFFF; 0x80000000; 0xFFFFFFFF; 0x100000000;
     smax; smin; smin + 1; m1; m1 - 1; A; B].
  Definition alu_ops := [ALU_ADD; ALU_SUB; ALU_SLL; ALU_SLT; ALU_SLTU; ALU_XOR;
                         ALU_SRL; ALU_SRA; ALU_OR; ALU_AND].
  Definition mul_ops := [M_MUL; M_MULH; M_MULHSU; M_MULHU; M_DIV; M_DIVU; M_REM; M_REMU].
  Definition grid (f : Z -> Z -> bool) : bool :=
    forallb (fun x => forallb (f x) vals) vals.
  Goal forallb (fun op => grid (fun x y =>
         wZ (w_alu op (T x) (T y)) =?
         bv_unsigned (alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y)))) alu_ops = true.
  Proof. vm_cast_no_check (eq_refl true). Qed.
  Goal forallb (fun op => grid (fun x y =>
         wZ (w_alu32 op (T x) (T y)) =?
         bv_unsigned (sext 64 (alu32 op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))))))
         alu_ops = true.
  Proof. vm_cast_no_check (eq_refl true). Qed.
  Goal forallb (fun op => grid (fun x y =>
         wZ (w_muldiv op (T x) (T y)) =?
         bv_unsigned (mul_div op (Z_to_bv 64 x) (Z_to_bv 64 y)))) mul_ops = true.
  Proof. vm_cast_no_check (eq_refl true). Qed.
  Goal forallb (fun op => grid (fun x y =>
         wZ (w_muldiv32 op (T x) (T y)) =?
         bv_unsigned (sext 64 (mul_div op (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 y))))))
         mul_ops = true.
  Proof. vm_cast_no_check (eq_refl true). Qed.
  Goal forallb (fun c => grid (fun x y =>
         Bool.eqb (w_branch c (T x) (T y))
                  (branch_taken c (Z_to_bv 64 x) (Z_to_bv 64 y))))
         [BC_EQ; BC_NE; BC_LT; BC_GE; BC_LTU; BC_GEU] = true.
  Proof. vm_cast_no_check (eq_refl true). Qed.
End W64Tests.
