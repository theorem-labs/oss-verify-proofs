(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module ZXA.

Abbreviation M64 := 18446744073709551616.
Abbreviation M32 := 4294967296.
Abbreviation H64 := 9223372036854775808.
Abbreviation H32 := 2147483648.
Lemma M64_eq : M64 = 2 ^ 64. Proof. reflexivity. Qed.
Lemma M32_eq : M32 = 2 ^ 32. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive zx : Type :=
| ZL (z : Z)                       (* [comment removed for export] *)
| ZV (n : nat)                     (* [comment removed for export] *)
| ZAdd (a b : zx) | ZSub (a b : zx) | ZMul (a b : zx)
| ZAnd (a b : zx) | ZOr (a b : zx) | ZXor (a b : zx)   (* [comment removed for export] *)
| ZModP (a : zx) (k : Z)           (* [comment removed for export] *)
| ZDivP (a : zx) (k : Z)           (* [comment removed for export] *)
| ZShlv (a b : zx)                 (* [comment removed for export] *)
| ZShrv (a b : zx)                 (* [comment removed for export] *)
| ZSw (w : N) (a : zx)             (* [comment removed for export] *)
| ZLt (a b : zx)                   (* [comment removed for export] *)
| ZAlu (op : aluop) (a b : zx)     (* [comment removed for export] *)
| ZAluw (op : aluop) (a b : zx).   (* [comment removed for export] *)

Definition env := nat -> Z.

(* [comment removed for export] *)
Definition zalu (op : aluop) (a b : Z) : Z :=
  let ua := a mod M64 in let ub := b mod M64 in
  match op with
  | ALU_ADD => ua + ub
  | ALU_SUB => ua - ub
  | ALU_SLL => Z.shiftl ua (ub mod 64)
  | ALU_SLT => if bv_swrap 64 ua <? bv_swrap 64 ub then 1 else 0
  | ALU_SLTU => if ua <? ub then 1 else 0
  | ALU_XOR => Z.lxor ua ub
  | ALU_SRL => Z.shiftr ua (ub mod 64)
  | ALU_SRA => Z.shiftr (bv_swrap 64 ua) (ub mod 64)
  | ALU_OR => Z.lor ua ub
  | ALU_AND => Z.land ua ub
  end.

Definition zaluw (op : aluop) (a b : Z) : Z :=
  let ua := a mod M64 in let ub := b mod M64 in
  match op with
  | ALU_ADD => bv_swrap 32 (ua + ub)
  | ALU_SUB => bv_swrap 32 (ua - ub)
  | ALU_SLL => bv_swrap 32 (Z.shiftl ua (ub mod 32))
  | ALU_SRL => bv_swrap 32 (Z.shiftr (bv_wrap 32 ua) (ub mod 32))
  | ALU_SRA => bv_swrap 32 (Z.shiftr (bv_swrap 32 ua) (ub mod 32))
  | _ => 0   (* [comment removed for export] *)
  end.

Definition op32_ok (op : aluop) : bool :=
  match op with ALU_ADD | ALU_SUB | ALU_SLL | ALU_SRL | ALU_SRA => true | _ => false end.

Fixpoint ev (E : env) (e : zx) : Z :=
  match e with
  | ZL z => z
  | ZV n => E n
  | ZAdd a b => ev E a + ev E b
  | ZSub a b => ev E a - ev E b
  | ZMul a b => ev E a * ev E b
  | ZAnd a b => Z.land (ev E a) (ev E b)
  | ZOr a b => Z.lor (ev E a) (ev E b)
  | ZXor a b => Z.lxor (ev E a) (ev E b)
  | ZModP a k => ev E a mod 2 ^ k
  | ZDivP a k => ev E a / 2 ^ k
  | ZShlv a b => ev E a * 2 ^ ev E b
  | ZShrv a b => ev E a / 2 ^ ev E b
  | ZSw w a => bv_swrap w (ev E a)
  | ZLt a b => if ev E a <? ev E b then 1 else 0
  | ZAlu op a b => zalu op (ev E a) (ev E b)
  | ZAluw op a b => zaluw op (ev E a) (ev E b)
  end.

(* [comment removed for export] *)
Definition wd (E : env) (e : zx) : word := Z_to_bv 64 (ev E e).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_Z2bv64 : forall z, bv_unsigned (Z_to_bv 64 z) = z mod M64.
Proof. intros. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma Z2bv_mod : forall z, Z_to_bv 64 (z mod M64) = Z_to_bv 64 z.
Proof. intros. apply bv_eq. rewrite !u_Z2bv64. rewrite M64_eq. apply Z.mod_mod. lia. Qed.

(* [comment removed for export] *)
Lemma Z2bv_eqm : forall a b, a mod M64 = b mod M64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. rewrite <- (Z2bv_mod a), <- (Z2bv_mod b), H. reflexivity. Qed.

Lemma zalu_ok : forall op a b,
  alu64 op (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (zalu op a b).
Proof.
  intros op a b. destruct op; cbn [zalu].
  - rewrite alu_add. unfold v_add. rewrite !u_Z2bv64. reflexivity.
  - rewrite alu_sub. unfold v_sub. rewrite !u_Z2bv64. reflexivity.
  - rewrite alu_sll. unfold v_sll. rewrite !u_Z2bv64. reflexivity.
  - rewrite alu_slt. unfold v_slt, c_lts, bv_lts, bv_signed. rewrite !u_Z2bv64. destruct (_ <? _); reflexivity.
  - rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite !u_Z2bv64. destruct (_ <? _); reflexivity.
  - rewrite alu_xor. unfold v_xor. rewrite !u_Z2bv64. reflexivity.
  - rewrite alu_srl. unfold v_srl. rewrite !u_Z2bv64. reflexivity.
  - rewrite alu_sra. unfold v_sra, bv_signed. rewrite !u_Z2bv64. reflexivity.
  - rewrite alu_or. unfold v_or. rewrite !u_Z2bv64. reflexivity.
  - rewrite alu_and. unfold v_and. rewrite !u_Z2bv64. reflexivity.
Qed.

Lemma zaluw_ok : forall op a b, op32_ok op = true ->
  sext 64 (alu32 op (low32 (Z_to_bv 64 a)) (low32 (Z_to_bv 64 b))) = Z_to_bv 64 (zaluw op a b).
Proof.
  intros op a b Hop. destruct op; cbn [zaluw]; try discriminate.
  - rewrite w_addw. unfold v_addw. rewrite !u_Z2bv64. reflexivity.
  - rewrite w_subw. unfold v_subw. rewrite !u_Z2bv64. reflexivity.
  - rewrite w_sllw. unfold v_sllw. rewrite !u_Z2bv64. reflexivity.
  - rewrite w_srlw. unfold v_srlw. rewrite !u_Z2bv64. reflexivity.
  - rewrite w_sraw. unfold v_sraw. rewrite !u_Z2bv64. reflexivity.
Qed.

Lemma zmul_ok : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros. rewrite m_mul. unfold v_mul. rewrite !u_Z2bv64. apply Z2bv_eqm.
  rewrite M64_eq. rewrite <- Zmult_mod. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vitab := list (option (Z * Z)).

Definition vi_ok (E : env) (vi : vitab) : Prop :=
  forall n lo hi, nth n vi None = Some (lo, hi) -> lo <= E n <= hi.

Definition itv_add (x y : option (Z * Z)) : option (Z * Z) :=
  match x, y with Some (a, b), Some (c, d) => Some (a + c, b + d) | _, _ => None end.
Definition itv_sub (x y : option (Z * Z)) : option (Z * Z) :=
  match x, y with Some (a, b), Some (c, d) => Some (a - d, b - c) | _, _ => None end.
(* [comment removed for export] *)
Definition itv_mul (x y : option (Z * Z)) : option (Z * Z) :=
  match x, y with
  | Some (a, b), Some (c, d) => if (0 <=? a) && (0 <=? c) then Some (a * c, b * d) else None
  | _, _ => None
  end.
Definition itv_modp (x : option (Z * Z)) (k : Z) : option (Z * Z) :=
  if k <? 0 then None else
  match x with
  | Some (a, b) => if (0 <=? a) && (b <? 2 ^ k) then Some (a, b) else Some (0, 2 ^ k - 1)
  | None => Some (0, 2 ^ k - 1)
  end.
Definition itv_divp (x : option (Z * Z)) (k : Z) : option (Z * Z) :=
  if k <? 0 then None else
  match x with Some (a, b) => Some (a / 2 ^ k, b / 2 ^ k) | None => None end.
Definition itv_sw (w : N) (x : option (Z * Z)) : option (Z * Z) :=
  if 0 <? Z.of_N w then
    let h := 2 ^ (Z.of_N w - 1) in
    match x with
    | Some (a, b) => if (- h <=? a) && (b <? h) then Some (a, b) else Some (- h, h - 1)
    | None => Some (- h, h - 1)
    end
  else None.
(* [comment removed for export] *)
Definition itv_shlv (x y : option (Z * Z)) : option (Z * Z) :=
  match x, y with
  | Some (a, b), Some (c, d) => if (0 <=? a) && (0 <=? c) then Some (a * 2 ^ c, b * 2 ^ d) else None
  | _, _ => None
  end.
Definition itv_shrv (x y : option (Z * Z)) : option (Z * Z) :=
  match x, y with
  | Some (a, b), Some (c, d) => if (0 <=? a) && (0 <=? c) then Some (a / 2 ^ d, b / 2 ^ c) else None
  | _, _ => None
  end.
Definition itv_land (x y : option (Z * Z)) : option (Z * Z) :=
  match x, y with
  | Some (a, b), Some (c, d) => if (0 <=? a) && (0 <=? c) then Some (0, Z.min b d) else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition up2 (b : Z) : Z := 2 ^ Z.log2_up (b + 1).
Definition itv_lor (x y : option (Z * Z)) : option (Z * Z) :=
  match x, y with
  | Some (a, b), Some (c, d) => if (0 <=? a) && (0 <=? c) then Some (0, up2 (Z.max b d) - 1) else None
  | _, _ => None
  end.

Fixpoint itv (vi : vitab) (e : zx) : option (Z * Z) :=
  match e with
  | ZL z => Some (z, z)
  | ZV n => nth n vi None
  | ZAdd a b => itv_add (itv vi a) (itv vi b)
  | ZSub a b => itv_sub (itv vi a) (itv vi b)
  | ZMul a b => itv_mul (itv vi a) (itv vi b)
  | ZAnd a b => itv_land (itv vi a) (itv vi b)
  | ZOr a b => itv_lor (itv vi a) (itv vi b)
  | ZXor a b => itv_lor (itv vi a) (itv vi b)
  | ZModP a k => itv_modp (itv vi a) k
  | ZDivP a k => itv_divp (itv vi a) k
  | ZShlv a b => itv_shlv (itv vi a) (itv vi b)
  | ZShrv a b => itv_shrv (itv vi a) (itv vi b)
  | ZSw w a => itv_sw w (itv vi a)
  | ZLt _ _ => Some (0, 1)
  | ZAlu op _ _ => match op with
                   | ALU_SLT | ALU_SLTU => Some (0, 1)
                   | ALU_XOR | ALU_OR | ALU_AND | ALU_SRL => Some (0, M64 - 1)
                   | _ => None
                   end
  | ZAluw _ _ _ => Some (- H32, H32 - 1)
  end.

(* [comment removed for export] *)
Definition within (vi : vitab) (e : zx) (lo hi : Z) : bool :=
  match itv vi e with Some (a, b) => (lo <=? a) && (b <=? hi) | None => false end.

Definition inU (vi : vitab) (e : zx) : bool := within vi e 0 (M64 - 1).
Definition inS (vi : vitab) (e : zx) : bool := within vi e (- H64) (H64 - 1).
Definition inS32 (vi : vitab) (e : zx) : bool := within vi e (- H32) (H32 - 1).

(* [comment removed for export] *)

Lemma lor_below_pow2 : forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros a b k Hk Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |].
  intros i Hi. rewrite Z.lor_spec, (Z_testbit_high k a i), (Z_testbit_high k b i) by lia. reflexivity.
Qed.

Lemma lxor_below_pow2 : forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lxor a b < 2 ^ k.
Proof.
  intros a b k Hk Ha Hb. split; [apply Z.lxor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia | apply Z.lxor_nonneg; lia |].
  intros i Hi. rewrite Z.lxor_spec, (Z_testbit_high k a i), (Z_testbit_high k b i) by lia. reflexivity.
Qed.

Lemma up2_spec : forall b, 0 <= b -> b < up2 b /\ 0 <= Z.log2_up (b + 1).
Proof.
  intros b Hb. unfold up2. split; [|apply Z.log2_up_nonneg].
  destruct (Z.eq_dec b 0) as [->|]; [vm_compute; reflexivity|].
  pose proof (Z.log2_up_spec (b + 1) ltac:(lia)). lia.
Qed.

Lemma land_upper : forall a b, 0 <= a -> 0 <= b -> Z.land a b <= Z.min a b.
Proof.
  intros a b Ha Hb.
  assert (H1 : Z.land a b <= a).
  { apply (Z.ldiff_le (Z.land a b) a Ha). rewrite Z.ldiff_land, (Z.land_comm a b), <- Z.land_assoc, Z.land_lnot_diag. apply Z.land_0_r. }
  assert (H2 : Z.land a b <= b).
  { apply (Z.ldiff_le (Z.land a b) b Hb). rewrite Z.ldiff_land, <- Z.land_assoc, Z.land_lnot_diag. apply Z.land_0_r. }
  lia.
Qed.

Lemma bv_swrap_range : forall w z, 0 < Z.of_N w ->
  - 2 ^ (Z.of_N w - 1) <= bv_swrap w z < 2 ^ (Z.of_N w - 1).
Proof.
  intros w z Hw. pose proof (bv_swrap_in_range w z ltac:(lia)) as H.
  unfold bv_half_modulus, bv_modulus in H.
  replace (2 ^ Z.of_N w) with (2 * 2 ^ (Z.of_N w - 1)) in H by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  rewrite Z.mul_comm, Z.div_mul in H by lia. lia.
Qed.

Lemma bv_swrap_id : forall w z, 0 < Z.of_N w ->
  - 2 ^ (Z.of_N w - 1) <= z < 2 ^ (Z.of_N w - 1) -> bv_swrap w z = z.
Proof.
  intros w z Hw Hz. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N w) with (2 * 2 ^ (Z.of_N w - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Lemma itv_sound : forall E vi e lo hi, vi_ok E vi -> itv vi e = Some (lo, hi) -> lo <= ev E e <= hi.
Proof.
  intros E vi e. induction e; intros lo hi Hvi H; cbn [itv ev] in H |- *.
  - injection H as <- <-. lia.
  - exact (Hvi _ _ _ H).
  - destruct (itv vi e1) as [[a b]|] eqn:E1; destruct (itv vi e2) as [[c d]|] eqn:E2; cbn in H; try discriminate.
    injection H as <- <-. specialize (IHe1 a b Hvi eq_refl). specialize (IHe2 c d Hvi eq_refl). lia.
  - destruct (itv vi e1) as [[a b]|] eqn:E1; destruct (itv vi e2) as [[c d]|] eqn:E2; cbn in H; try discriminate.
    injection H as <- <-. specialize (IHe1 a b Hvi eq_refl). specialize (IHe2 c d Hvi eq_refl). lia.
  - destruct (itv vi e1) as [[a b]|] eqn:E1; destruct (itv vi e2) as [[c d]|] eqn:E2; cbn in H; try discriminate.
    destruct (Z.leb_spec 0 a); destruct (Z.leb_spec 0 c); cbn in H; try discriminate.
    injection H as <- <-. specialize (IHe1 a b Hvi eq_refl). specialize (IHe2 c d Hvi eq_refl). nia.
  - destruct (itv vi e1) as [[a b]|] eqn:E1; destruct (itv vi e2) as [[c d]|] eqn:E2; cbn in H; try discriminate.
    destruct (Z.leb_spec 0 a); destruct (Z.leb_spec 0 c); cbn in H; try discriminate.
    injection H as <- <-. specialize (IHe1 a b Hvi eq_refl). specialize (IHe2 c d Hvi eq_refl).
    split; [apply Z.land_nonneg; lia|]. pose proof (land_upper (ev E e1) (ev E e2) ltac:(lia) ltac:(lia)). lia.
  - destruct (itv vi e1) as [[a b]|] eqn:E1; destruct (itv vi e2) as [[c d]|] eqn:E2; cbn in H; try discriminate.
    destruct (Z.leb_spec 0 a); destruct (Z.leb_spec 0 c); cbn in H; try discriminate.
    injection H as <- <-. specialize (IHe1 a b Hvi eq_refl). specialize (IHe2 c d Hvi eq_refl).
    pose proof (up2_spec (Z.max b d) ltac:(lia)) as [Hu Hk]. unfold up2 in *.
    pose proof (lor_below_pow2 (ev E e1) (ev E e2) (Z.log2_up (Z.max b d + 1)) Hk ltac:(lia) ltac:(lia)). lia.
  - destruct (itv vi e1) as [[a b]|] eqn:E1; destruct (itv vi e2) as [[c d]|] eqn:E2; cbn in H; try discriminate.
    destruct (Z.leb_spec 0 a); destruct (Z.leb_spec 0 c); cbn in H; try discriminate.
    injection H as <- <-. specialize (IHe1 a b Hvi eq_refl). specialize (IHe2 c d Hvi eq_refl).
    pose proof (up2_spec (Z.max b d) ltac:(lia)) as [Hu Hk]. unfold up2 in *.
    pose proof (lxor_below_pow2 (ev E e1) (ev E e2) (Z.log2_up (Z.max b d + 1)) Hk ltac:(lia) ltac:(lia)). lia.
  - unfold itv_modp in H. destruct (Z.ltb_spec k 0); [discriminate|].
    pose proof (Z.mod_pos_bound (ev E e) (2 ^ k) ltac:(apply Z.pow_pos_nonneg; lia)) as Hm.
    destruct (itv vi e) as [[a b]|] eqn:E1.
    + destruct (Z.leb_spec 0 a); destruct (Z.ltb_spec b (2 ^ k)); cbn in H; injection H as <- <-; try lia.
      specialize (IHe a b Hvi eq_refl). rewrite Z.mod_small by lia. lia.
    + injection H as <- <-. lia.
  - unfold itv_divp in H. destruct (Z.ltb_spec k 0); [discriminate|].
    destruct (itv vi e) as [[a b]|] eqn:E1; [|discriminate]. injection H as <- <-.
    specialize (IHe a b Hvi eq_refl).
    assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    split; apply Z.div_le_mono; lia.
  - destruct (itv vi e1) as [[a b]|] eqn:E1; destruct (itv vi e2) as [[c d]|] eqn:E2; cbn in H; try discriminate.
    destruct (Z.leb_spec 0 a); destruct (Z.leb_spec 0 c); cbn in H; try discriminate.
    injection H as <- <-. specialize (IHe1 a b Hvi eq_refl). specialize (IHe2 c d Hvi eq_refl).
    assert (0 < 2 ^ c <= 2 ^ ev E e2) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    assert (2 ^ ev E e2 <= 2 ^ d) by (apply Z.pow_le_mono_r; lia). nia.
  - destruct (itv vi e1) as [[a b]|] eqn:E1; destruct (itv vi e2) as [[c d]|] eqn:E2; cbn in H; try discriminate.
    destruct (Z.leb_spec 0 a); destruct (Z.leb_spec 0 c); cbn in H; try discriminate.
    injection H as <- <-. specialize (IHe1 a b Hvi eq_refl). specialize (IHe2 c d Hvi eq_refl).
    assert (0 < 2 ^ c <= 2 ^ ev E e2) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    assert (2 ^ ev E e2 <= 2 ^ d) by (apply Z.pow_le_mono_r; lia).
    split.
    + apply Z.le_trans with (m := a / 2 ^ ev E e2); [apply Z.div_le_compat_l; lia | apply Z.div_le_mono; lia].
    + apply Z.le_trans with (m := ev E e1 / 2 ^ c); [apply Z.div_le_compat_l; lia | apply Z.div_le_mono; lia].
  - unfold itv_sw in H. destruct (Z.ltb_spec 0 (Z.of_N w)) as [Hw|Hw]; [|discriminate].
    pose proof (bv_swrap_range w (ev E e) Hw) as Hr.
    destruct (itv vi e) as [[a b]|] eqn:E1.
    + destruct (Z.leb_spec (- 2 ^ (Z.of_N w - 1)) a); destruct (Z.ltb_spec b (2 ^ (Z.of_N w - 1))); cbn in H;
        injection H as <- <-; try lia.
      specialize (IHe a b Hvi eq_refl). rewrite bv_swrap_id by lia. lia.
    + injection H as <- <-. lia.
  - injection H as <- <-. destruct (ev E e1 <? ev E e2); lia.
  - pose proof (Z.mod_pos_bound (ev E e1) M64 ltac:(lia)) as H1.
    pose proof (Z.mod_pos_bound (ev E e2) M64 ltac:(lia)) as H2.
    destruct op; try discriminate; injection H as <- <-; cbn [zalu].
    + destruct (_ <? _); lia.
    + destruct (_ <? _); lia.
    + pose proof (lxor_below_pow2 _ _ 64 ltac:(lia) ltac:(rewrite <- M64_eq; exact H1) ltac:(rewrite <- M64_eq; exact H2)). rewrite <- M64_eq in *. lia.
    + rewrite Z.shiftr_div_pow2 by (apply Z.mod_pos_bound; lia).
      assert (0 < 2 ^ ((ev E e2 mod M64) mod 64)) by (apply Z.pow_pos_nonneg; [lia|apply Z.mod_pos_bound; lia]).
      split; [apply Z.div_pos; lia|].
      apply Z.le_trans with (m := ev E e1 mod M64); [|lia]. apply Z.div_le_upper_bound; [lia|]. nia.
    + pose proof (lor_below_pow2 _ _ 64 ltac:(lia) ltac:(rewrite <- M64_eq; exact H1) ltac:(rewrite <- M64_eq; exact H2)). rewrite <- M64_eq in *. lia.
    + split; [apply Z.land_nonneg; lia|]. pose proof (land_upper _ _ (proj1 H1) (proj1 H2)). lia.
  - injection H as <- <-. 
    destruct op; cbn [zaluw]; try lia;
      match goal with
      | |- _ <= bv_swrap 32 ?x <= _ => pose proof (bv_swrap_range 32 x ltac:(cbn; lia)) as Hr; cbn [Z.of_N Z.sub Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul] in Hr; cbn; lia
      end.
Qed.

Lemma within_sound : forall E vi e lo hi, vi_ok E vi -> within vi e lo hi = true -> lo <= ev E e <= hi.
Proof.
  intros E vi e lo hi Hvi H. unfold within in H.
  destruct (itv vi e) as [[a b]|] eqn:Ei; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (itv_sound E vi e a b Hvi Ei). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zadd (a b : zx) : zx :=
  match a, b with
  | ZL x, ZL y => ZL (x + y)
  | ZAdd a' (ZL x), ZL y => if x + y =? 0 then a' else ZAdd a' (ZL (x + y))
  | _, ZL y => if y =? 0 then a else ZAdd a b
  | ZL x, ZAdd b' (ZL y) => if x + y =? 0 then b' else ZAdd b' (ZL (x + y))
  | ZL x, _ => if x =? 0 then b else ZAdd b (ZL x)
  | _, _ => ZAdd a b
  end.

Lemma zadd_ev : forall E a b, ev E (zadd a b) = ev E a + ev E b.
Proof.
  intros E a b. unfold zadd.
  destruct a as [x| |a1 a2| | | | | | | | | | | | |]; destruct b as [y| |b1 b2| | | | | | | | | | | | |];
    cbn [ev]; try lia;
    try (destruct a2 as [x2| | | | | | | | | | | | | | |]; cbn [ev]; try lia);
    try (destruct b2 as [y2| | | | | | | | | | | | | | |]; cbn [ev]; try lia);
    repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:?; cbn [ev] end;
    repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end; try lia.
Qed.

Definition zsub (a b : zx) : zx :=
  match b with
  | ZL y => zadd a (ZL (- y))
  | _ => ZSub a b
  end.

Lemma zsub_ev : forall E a b, ev E (zsub a b) = ev E a - ev E b.
Proof. intros E a b. unfold zsub. destruct b; cbn [ev]; try lia. rewrite zadd_ev. cbn [ev]. lia. Qed.

Definition zmul (a b : zx) : zx :=
  match a, b with
  | ZL x, ZL y => ZL (x * y)
  | _, ZL y => if y =? 1 then a else if y =? 0 then ZL 0 else ZMul a b
  | ZL x, _ => if x =? 1 then b else if x =? 0 then ZL 0 else ZMul b a
  | _, _ => ZMul a b
  end.

Lemma zmul_ev : forall E a b, ev E (zmul a b) = ev E a * ev E b.
Proof.
  intros E a b. unfold zmul.
  destruct a; destruct b; cbn [ev]; try lia;
    repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:?; cbn [ev] end;
    repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end; try lia.
Qed.

(* [comment removed for export] *)
Definition zlt (vi : vitab) (a b : zx) : zx :=
  match itv vi a, itv vi b with
  | Some (la, ha), Some (lb, hb) => if ha <? lb then ZL 1 else if hb <=? la then ZL 0 else ZLt a b
  | _, _ => ZLt a b
  end.

Lemma zlt_ev : forall E vi a b, vi_ok E vi -> ev E (zlt vi a b) = (if ev E a <? ev E b then 1 else 0).
Proof.
  intros E vi a b Hvi. unfold zlt.
  destruct (itv vi a) as [[la ha]|] eqn:Ea; destruct (itv vi b) as [[lb hb]|] eqn:Eb; cbn [ev]; try reflexivity.
  pose proof (itv_sound E vi a la ha Hvi Ea). pose proof (itv_sound E vi b lb hb Hvi Eb).
  destruct (Z.ltb_spec ha lb); [destruct (Z.ltb_spec (ev E a) (ev E b)); cbn [ev]; lia|].
  destruct (Z.leb_spec hb la); [destruct (Z.ltb_spec (ev E a) (ev E b)); cbn [ev]; lia|].
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition zmodp (a : zx) (k : Z) : zx := match a with ZL c => ZL (c mod 2 ^ k) | _ => ZModP a k end.
Definition zdivp (a : zx) (k : Z) : zx := match a with ZL c => ZL (c / 2 ^ k) | _ => ZDivP a k end.
Definition zsw (w : N) (a : zx) : zx := match a with ZL c => ZL (bv_swrap w c) | _ => ZSw w a end.

Lemma zmodp_ev : forall E a k, ev E (zmodp a k) = ev E a mod 2 ^ k.
Proof. intros E a k. destruct a; reflexivity. Qed.
Lemma zdivp_ev : forall E a k, ev E (zdivp a k) = ev E a / 2 ^ k.
Proof. intros E a k. destruct a; reflexivity. Qed.
Lemma zsw_ev : forall E w a, ev E (zsw w a) = bv_swrap w (ev E a).
Proof. intros E w a. destruct a; reflexivity. Qed.

Ltac zev := cbn [ev]; rewrite ?zmodp_ev, ?zdivp_ev, ?zsw_ev; cbn [ev].

(* [comment removed for export] *)
Definition nU (vi : vitab) (a : zx) : zx := if inU vi a then a else zmodp a 64.
Definition nS (vi : vitab) (a : zx) : zx := if inS vi a then a else zsw 64 a.
Definition nU32 (vi : vitab) (a : zx) : zx := if within vi a 0 (M32 - 1) then a else zmodp a 32.
Definition nS32 (vi : vitab) (a : zx) : zx := if inS32 vi a then a else zsw 32 a.

Lemma nU_ev : forall E vi a, vi_ok E vi -> ev E (nU vi a) = ev E a mod M64.
Proof.
  intros E vi a Hvi. unfold nU. destruct (inU vi a) eqn:Hu; zev; [|rewrite M64_eq; reflexivity].
  pose proof (within_sound E vi a _ _ Hvi Hu). rewrite Z.mod_small; lia.
Qed.

Lemma nS_ev : forall E vi a, vi_ok E vi -> ev E (nS vi a) = bv_swrap 64 (ev E a).
Proof.
  intros E vi a Hvi. unfold nS. destruct (inS vi a) eqn:Hu; zev; [|reflexivity].
  pose proof (within_sound E vi a _ _ Hvi Hu). rewrite bv_swrap_id; cbn; lia.
Qed.

Lemma nU32_ev : forall E vi a, vi_ok E vi -> ev E (nU32 vi a) = ev E a mod M32.
Proof.
  intros E vi a Hvi. unfold nU32. destruct (within vi a 0 (M32 - 1)) eqn:Hu; zev; [|rewrite M32_eq; reflexivity].
  pose proof (within_sound E vi a _ _ Hvi Hu). rewrite Z.mod_small; lia.
Qed.

Lemma nS32_ev : forall E vi a, vi_ok E vi -> ev E (nS32 vi a) = bv_swrap 32 (ev E a).
Proof.
  intros E vi a Hvi. unfold nS32. destruct (inS32 vi a) eqn:Hu; zev; [|reflexivity].
  pose proof (within_sound E vi a _ _ Hvi Hu). rewrite bv_swrap_id; cbn; lia.
Qed.

(* [comment removed for export] *)
Definition as_mask (b : zx) : option Z :=
  match b with
  | ZL m => if (0 <? m) && (m <? M64) && (Z.land m (m + 1) =? 0) && (2 ^ Z.log2 (m + 1) =? m + 1)
            then Some (Z.log2 (m + 1)) else None
  | _ => None
  end.

Lemma as_mask_spec : forall b k, as_mask b = Some k -> b = ZL (2 ^ k - 1) /\ 1 <= k <= 64.
Proof.
  intros b k H. destruct b; cbn in H; try discriminate.
  destruct (0 <? z) eqn:E1; [|discriminate]. destruct (z <? M64) eqn:E2; [|discriminate].
  destruct (Z.land z (z + 1) =? 0) eqn:E3; [|discriminate]. destruct (2 ^ Z.log2 (z + 1) =? z + 1) eqn:E4; [|discriminate].
  cbn in H. injection H as <-.
  apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. apply Z.eqb_eq in E4.
  split; [f_equal; lia|].
  split.
  - destruct (Z.le_gt_cases 1 (Z.log2 (z + 1))); [assumption|].
    pose proof (Z.log2_nonneg (z + 1)). assert (Z.log2 (z + 1) = 0) by lia. rewrite H1 in E4. cbn in E4. lia.
  - destruct (Z.le_gt_cases (Z.log2 (z + 1)) 64); [assumption|].
    assert (2 ^ 65 <= 2 ^ Z.log2 (z + 1)) by (apply Z.pow_le_mono_r; lia).
    rewrite E4 in H0. change (2 ^ 65) with 36893488147419103232 in H0. lia.
Qed.

(* [comment removed for export] *)
Definition as_pow2mul (a : zx) : option (zx * Z) :=
  match a with
  | ZMul x (ZL c) => if (0 <? c) && (2 ^ Z.log2 c =? c) then Some (x, Z.log2 c) else None
  | _ => None
  end.

Lemma as_pow2mul_spec : forall a x j, as_pow2mul a = Some (x, j) -> a = ZMul x (ZL (2 ^ j)) /\ 0 <= j.
Proof.
  intros a x j H. destruct a; cbn in H; try discriminate. destruct a2; try discriminate.
  destruct (0 <? z) eqn:E1; [|discriminate]. destruct (2 ^ Z.log2 z =? z) eqn:E2; [|discriminate].
  cbn in H. injection H as <- <-. apply Z.eqb_eq in E2. rewrite E2. split; [reflexivity | apply Z.log2_nonneg].
Qed.

Lemma shl_mod_shr : forall x j s, 0 <= j <= s -> s < 64 ->
  ((x * 2 ^ j) mod M64) / 2 ^ s = (x mod 2 ^ (64 - j)) / 2 ^ (s - j).
Proof.
  intros x j s Hj Hs.
  assert (HM : M64 = 2 ^ (64 - j) * 2 ^ j) by (rewrite <- Z.pow_add_r by lia; rewrite M64_eq; f_equal; lia).
  assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (Hq : 0 < 2 ^ (64 - j)) by (apply Z.pow_pos_nonneg; lia).
  rewrite HM, Z.mul_mod_distr_r by lia.
  replace (2 ^ s) with (2 ^ j * 2 ^ (s - j)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite <- Z.div_div by (try apply Z.pow_pos_nonneg; lia). rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma swrap_as_mod : forall n z, 0 < Z.of_N n ->
  bv_swrap n z = (z + 2 ^ (Z.of_N n - 1)) mod 2 ^ Z.of_N n - 2 ^ (Z.of_N n - 1).
Proof.
  intros n z Hn. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N n `div` 2) with (2 ^ (Z.of_N n - 1)); [reflexivity|].
  replace (2 ^ Z.of_N n) with (2 ^ (Z.of_N n - 1) * 2) by (rewrite (Z.mul_comm _ 2), <- Z.pow_succ_r by lia; f_equal; lia).
  rewrite Z.div_mul by lia. reflexivity.
Qed.

Lemma swrap_shl_shr : forall x s, 0 <= s < 64 ->
  bv_swrap 64 (x * 2 ^ s) / 2 ^ s = bv_swrap (Z.to_N (64 - s)) x.
Proof.
  intros x s Hs. rewrite !swrap_as_mod by lia. rewrite Z2N.id by lia.
  change (Z.of_N 64) with 64.
  assert (Hp : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  assert (E63 : 2 ^ (64 - 1) = 2 ^ (64 - s - 1) * 2 ^ s) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (E64 : 2 ^ 64 = 2 ^ (64 - s) * 2 ^ s) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite E63, E64. rewrite <- Z.mul_add_distr_r, Z.mul_mod_distr_r by (try apply Z.pow_nonzero; lia).
  rewrite <- Z.mul_sub_distr_r, Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint strip (k : Z) (e : zx) : zx :=
  match e with
  | ZAdd a b => zadd (strip k a) (strip k b)
  | ZSub a b => zsub (strip k a) (strip k b)
  | ZMul a b => zmul (strip k a) (strip k b)
  | ZSw w a => if k <=? Z.of_N w then strip k a else e
  | ZModP a j => if k <=? j then strip k a else e
  | _ => e
  end.

Lemma eqmod_modp : forall j a k, 0 <= k <= j -> (a mod 2 ^ j) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros j a k Hk. apply Z.mod_mod_divide. exists (2 ^ (j - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma eqmod_swrap : forall w a k, 0 <= k <= Z.of_N w -> (bv_swrap w a) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros w a k Hk.
  destruct (Z.eq_dec (Z.of_N w) 0) as [Hw|Hw].
  { assert (k = 0) by lia. subst k. rewrite Z.pow_0_r, !Z.mod_1_r. reflexivity. }
  rewrite swrap_as_mod by lia.
  rewrite <- Zminus_mod_idemp_l, (eqmod_modp (Z.of_N w)) by lia. rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma strip_sound : forall E k e, 0 <= k -> ev E (strip k e) mod 2 ^ k = ev E e mod 2 ^ k.
Proof.
  intros E k e Hk. induction e; cbn [strip]; try reflexivity.
  - rewrite zadd_ev. cbn [ev]. rewrite Zplus_mod, IHe1, IHe2, <- Zplus_mod. reflexivity.
  - rewrite zsub_ev. cbn [ev]. rewrite Zminus_mod, IHe1, IHe2, <- Zminus_mod. reflexivity.
  - rewrite zmul_ev. cbn [ev]. rewrite Zmult_mod, IHe1, IHe2, <- Zmult_mod. reflexivity.
  - lazymatch goal with |- context [k <=? ?j] => destruct (Z.leb_spec k j); [|reflexivity] end. rewrite IHe. cbn [ev]. symmetry. apply eqmod_modp. lia.
  - lazymatch goal with |- context [k <=? ?j] => destruct (Z.leb_spec k j); [|reflexivity] end. rewrite IHe. cbn [ev]. symmetry. apply eqmod_swrap. lia.
Qed.

Definition shamt64 (s : Z) : Z := (s mod M64) mod 64.
Definition shamt32 (s : Z) : Z := (s mod M64) mod 32.

Definition wrap32 (vi : vitab) (r : zx) : zx := if inS32 vi r then r else zsw 32 r.

Lemma wrap32_ev : forall E vi r, vi_ok E vi -> ev E (wrap32 vi r) = bv_swrap 32 (ev E r).
Proof. intros. apply nS32_ev. assumption. Qed.

Definition is_m1 (b : zx) : bool := match b with ZL m => (m =? -1) || (m =? M64 - 1) | _ => false end.

Definition mk_alu (vi : vitab) (op : aluop) (a b : zx) : zx :=
  match op with
  | ALU_ADD => zadd a b
  | ALU_SUB => zsub a b
  | ALU_AND =>
      match as_mask b with
      | Some k => if within vi a 0 (2 ^ k - 1) then a else zmodp (strip k a) k
      | None =>
          match as_mask a with
          | Some k => if within vi b 0 (2 ^ k - 1) then b else zmodp (strip k b) k
          | None => if inU vi a && inU vi b then ZAnd a b else ZAlu ALU_AND a b
          end
      end
  | ALU_OR => if inU vi a && inU vi b then ZOr a b else ZAlu ALU_OR a b
  | ALU_XOR => if is_m1 b && inU vi a then zsub (ZL (M64 - 1)) a
               else if inU vi a && inU vi b then ZXor a b else ZAlu ALU_XOR a b
  | ALU_SLL =>
      match b with
      | ZL s => zmul a (ZL (2 ^ shamt64 s))
      | _ => if within vi b 0 63 then ZShlv a b else ZAlu ALU_SLL a b
      end
  | ALU_SRL =>
      match b with
      | ZL s => let s' := shamt64 s in
          match (match as_pow2mul a with Some (x, j) => if j <=? s' then Some (x, j) else None | None => None end) with
          | Some (x, j) => (* [comment removed for export] *)
              let x' := if within vi x 0 (2 ^ (64 - j) - 1) then x else zmodp (strip (64 - j) x) (64 - j) in
              if s' =? j then x' else zdivp x' (s' - j)
          | None => if s' =? 0 then nU vi a else zdivp (nU vi a) s'
          end
      | _ => if within vi b 0 63 then ZShrv (nU vi a) b else ZAlu ALU_SRL a b
      end
  | ALU_SRA =>
      match b with
      | ZL s => let s' := shamt64 s in
          match (match as_pow2mul a with Some (x, j) => if j =? s' then Some x else None | None => None end) with
          | Some x => (* [comment removed for export] *)
              if within vi x (- 2 ^ (63 - s')) (2 ^ (63 - s') - 1) then x else zsw (Z.to_N (64 - s')) x
          | None => if s' =? 0 then nS vi a else zdivp (nS vi a) s'
          end
      | _ => ZAlu ALU_SRA a b
      end
  | ALU_SLT => zlt vi (nS vi a) (nS vi b)
  | ALU_SLTU => zlt vi (nU vi a) (nU vi b)
  end.

Definition mk_aluw (vi : vitab) (op : aluop) (a b : zx) : zx :=
  match op with
  | ALU_ADD => wrap32 vi (zadd a b)
  | ALU_SUB => wrap32 vi (zsub a b)
  | ALU_SLL =>
      match b with
      | ZL s => wrap32 vi (zmul a (ZL (2 ^ shamt32 s)))
      | _ => if within vi b 0 31 then wrap32 vi (ZShlv a b) else ZAluw ALU_SLL a b
      end
  | ALU_SRL =>
      match b with
      | ZL s => let s' := shamt32 s in wrap32 vi (if s' =? 0 then nU32 vi a else zdivp (nU32 vi a) s')
      | _ => if within vi b 0 31 then wrap32 vi (ZShrv (nU32 vi a) b) else ZAluw ALU_SRL a b
      end
  | ALU_SRA =>
      match b with
      | ZL s => let s' := shamt32 s in wrap32 vi (if s' =? 0 then nS32 vi a else zdivp (nS32 vi a) s')
      | _ => ZAluw ALU_SRA a b
      end
  | _ => ZAluw op a b
  end.

(* [comment removed for export] *)

Lemma mod_mod_pow2 : forall a k, 0 <= k <= 64 -> (a mod M64) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros a k Hk. rewrite M64_eq. apply Z.mod_mod_divide.
  exists (2 ^ (64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma land_mask : forall a k, 0 <= k -> Z.land a (2 ^ k - 1) = a mod 2 ^ k.
Proof. intros. rewrite <- Z.land_ones by lia. unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity. Qed.

Lemma lxor_ones64 : forall x, 0 <= x < M64 -> Z.lxor x (M64 - 1) = M64 - 1 - x.
Proof.
  intros x Hx.
  assert (Hl : Z.land (Z.lxor x (M64 - 1)) x = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    change (M64 - 1) with (Z.ones 64). 
    destruct (Z.lt_ge_cases i 64).
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x i); reflexivity.
    - rewrite (Z_testbit_high 64 x i) by (lia). rewrite andb_false_r. reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ Hl) as Ha.
  rewrite Z.lxor_assoc, (Z.lxor_comm (M64 - 1) x), <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in Ha. lia.
Qed.

Lemma swrap32_congr : forall x y, x mod M32 = y mod M32 -> bv_swrap 32 x = bv_swrap 32 y.
Proof.
  intros x y H. rewrite <- (bv_swrap_wrap 32 x), <- (bv_swrap_wrap 32 y). unfold bv_wrap.
  change (bv_modulus 32) with M32. rewrite H. reflexivity.
Qed.

Lemma mod64_mod32 : forall a, (a mod M64) mod M32 = a mod M32.
Proof. intros. rewrite M32_eq. apply mod_mod_pow2. lia. Qed.

Lemma shamt64_range : forall s, 0 <= shamt64 s < 64.
Proof. intros. unfold shamt64. apply Z.mod_pos_bound. lia. Qed.
Lemma shamt32_range : forall s, 0 <= shamt32 s < 32.
Proof. intros. unfold shamt32. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Definition eqm (x y : Z) : Prop := Z_to_bv 64 x = Z_to_bv 64 y.

Lemma eqm_of_eq : forall x y, x = y -> eqm x y. Proof. intros; subst; reflexivity. Qed.
Lemma eqm_mod : forall x y, x mod M64 = y mod M64 -> eqm x y. Proof. exact Z2bv_eqm. Qed.

Lemma mk_alu_sound : forall E vi op a b, vi_ok E vi ->
  eqm (ev E (mk_alu vi op a b)) (zalu op (ev E a) (ev E b)).
Proof.
  intros E vi op a b Hvi.
  pose proof (Z.mod_pos_bound (ev E a) M64 ltac:(lia)) as Hua.
  pose proof (Z.mod_pos_bound (ev E b) M64 ltac:(lia)) as Hub.
  destruct op; cbn [mk_alu zalu].
  - apply eqm_mod. rewrite zadd_ev. rewrite M64_eq, <- Zplus_mod. reflexivity.
  - apply eqm_mod. rewrite zsub_ev. rewrite M64_eq, <- Zminus_mod. reflexivity.
  - (* [comment removed for export] *)
    assert (Hvar : within vi b 0 63 = true -> eqm (ev E (ZShlv a b)) (Z.shiftl (ev E a mod M64) ((ev E b mod M64) mod 64))).
    { intros Hw. apply eqm_mod. zev. pose proof (within_sound E vi b _ _ Hvi Hw) as Hb.
      rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
      rewrite (Z.mod_small (ev E b) M64) by (lia). rewrite (Z.mod_small (ev E b) 64) by lia.
      rewrite M64_eq, <- Zmult_mod_idemp_l. reflexivity. }
    destruct b as [s| | | | | | | | | | | | | | |];
      [ apply eqm_mod; rewrite zmul_ev; zev; rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia);
        unfold shamt64; rewrite M64_eq, <- Zmult_mod_idemp_l; reflexivity | ..];
      (destruct (within vi _ 0 63) eqn:Hw; [apply Hvar; reflexivity|apply eqm_of_eq; reflexivity]).
  - (* [comment removed for export] *) apply eqm_of_eq. rewrite zlt_ev by assumption. rewrite !nS_ev by assumption.
    rewrite <- (bv_swrap_wrap 64 (ev E a)), <- (bv_swrap_wrap 64 (ev E b)). reflexivity.
  - (* [comment removed for export] *) apply eqm_of_eq. rewrite zlt_ev by assumption. rewrite !nU_ev by assumption. reflexivity.
  - (* [comment removed for export] *)
    destruct (is_m1 b && inU vi a) eqn:Hm.
    + apply andb_prop in Hm as [Hm Hu]. pose proof (within_sound E vi a _ _ Hvi Hu) as Ha.
      apply eqm_of_eq. rewrite zsub_ev. zev.
      assert (Hb : ev E b mod M64 = M64 - 1).
      { destruct b; cbn in Hm; try discriminate. zev. apply orb_prop in Hm as [Hm|Hm]; apply Z.eqb_eq in Hm; subst; reflexivity. }
      rewrite Hb, (Z.mod_small (ev E a)) by (lia). symmetry. apply lxor_ones64. lia.
    + destruct (inU vi a && inU vi b) eqn:Hu; [|apply eqm_of_eq; reflexivity].
      apply andb_prop in Hu as [H1 H2]. pose proof (within_sound E vi a _ _ Hvi H1). pose proof (within_sound E vi b _ _ Hvi H2).
      apply eqm_of_eq. zev. rewrite !Z.mod_small by (lia). reflexivity.
  - (* [comment removed for export] *)
    assert (Hvar : within vi b 0 63 = true -> eqm (ev E (ZShrv (nU vi a) b)) (Z.shiftr (ev E a mod M64) ((ev E b mod M64) mod 64))).
    { intros Hw. apply eqm_of_eq. zev. rewrite nU_ev by assumption. pose proof (within_sound E vi b _ _ Hvi Hw) as Hb.
      rewrite (Z.mod_small (ev E b) M64) by (lia). rewrite (Z.mod_small (ev E b) 64) by lia.
      rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
    destruct b as [s| | | | | | | | | | | | | | |].
    1:{ apply eqm_of_eq. pose proof (shamt64_range s) as Hs.
        destruct (match as_pow2mul a with Some (x, j) => if j <=? shamt64 s then Some (x, j) else None | None => None end)
          as [[x j]|] eqn:Hpm.
        - destruct (as_pow2mul a) as [[x0 j0]|] eqn:Hpm0; [|discriminate].
          destruct (Z.leb_spec j0 (shamt64 s)); [|discriminate]. injection Hpm as <- <-.
          apply as_pow2mul_spec in Hpm0 as [-> Hj]. zev. unfold shamt64 in *.
          rewrite Z.shiftr_div_pow2 by lia. rewrite shl_mod_shr by lia.
          assert (Hx' : ev E (if within vi x0 0 (2 ^ (64 - j0) - 1) then x0 else zmodp (strip (64 - j0) x0) (64 - j0)) = ev E x0 mod 2 ^ (64 - j0)).
          { destruct (within vi x0 0 _) eqn:Hw; zev; [|apply strip_sound; lia].
            pose proof (within_sound E vi x0 _ _ Hvi Hw). rewrite Z.mod_small; [reflexivity|lia]. }
          destruct (Z.eqb_spec ((s mod M64) mod 64) j0) as [Hsj|Hsj].
          + rewrite Hx', Hsj, Z.sub_diag, Z.pow_0_r, Z.div_1_r. reflexivity.
          + zev. rewrite Hx'. reflexivity.
        - destruct (Z.eqb_spec (shamt64 s) 0) as [Hz|Hz]; unfold shamt64 in *.
          * rewrite nU_ev by assumption. zev. rewrite Hz, Z.shiftr_0_r. reflexivity.
          * zev. rewrite nU_ev by assumption. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
    all: destruct (within vi _ 0 63) eqn:Hw; [apply Hvar; reflexivity|apply eqm_of_eq; reflexivity].
  - (* [comment removed for export] *)
    destruct b as [s| | | | | | | | | | | | | | |]; [|apply eqm_of_eq; reflexivity..].
    apply eqm_of_eq. pose proof (shamt64_range s) as Hs.
    replace (bv_swrap 64 (ev E a mod M64)) with (bv_swrap 64 (ev E a)) by (symmetry; apply (bv_swrap_wrap 64)).
    destruct (match as_pow2mul a with Some (x, j) => if j =? shamt64 s then Some x else None | None => None end)
      as [x|] eqn:Hpm.
    { destruct (as_pow2mul a) as [[x0 j0]|] eqn:Hpm0; [|discriminate].
      destruct (Z.eqb_spec j0 (shamt64 s)); [|discriminate]. injection Hpm as <-.
      apply as_pow2mul_spec in Hpm0 as [-> Hj]. zev. subst j0. unfold shamt64 in *.
      rewrite Z.shiftr_div_pow2 by lia. rewrite swrap_shl_shr by lia.
      destruct (within vi x0 _ _) eqn:Hw; zev; [|reflexivity].
      pose proof (within_sound E vi x0 _ _ Hvi Hw). symmetry. apply bv_swrap_id; rewrite Z2N.id by lia; [lia|].
      replace (64 - (s mod M64) mod 64 - 1) with (63 - (s mod M64) mod 64) by lia. lia. }
    destruct (Z.eqb_spec (shamt64 s) 0) as [Hz|Hz]; unfold shamt64 in *.
    + rewrite nS_ev by assumption. zev. rewrite Hz, Z.shiftr_0_r. reflexivity.
    + zev. rewrite nS_ev by assumption. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
  - (* [comment removed for export] *)
    destruct (inU vi a && inU vi b) eqn:Hu; [|apply eqm_of_eq; reflexivity].
    apply andb_prop in Hu as [H1 H2]. pose proof (within_sound E vi a _ _ Hvi H1). pose proof (within_sound E vi b _ _ Hvi H2).
    apply eqm_of_eq. zev. rewrite !Z.mod_small by (lia). reflexivity.
  - (* [comment removed for export] *)
    destruct (as_mask b) as [k|] eqn:Hmb.
    + apply as_mask_spec in Hmb as [-> Hk]. zev.
      rewrite (Z.mod_small (2 ^ k - 1) M64).
      2:{ split; [pose proof (Z.pow_pos_nonneg 2 k); lia|]. apply Z.lt_le_trans with (m := 2 ^ k); [lia|].
          rewrite M64_eq. apply Z.pow_le_mono_r; lia. }
      rewrite land_mask, mod_mod_pow2 by lia.
      destruct (within vi a 0 (2 ^ k - 1)) eqn:Hw.
      * pose proof (within_sound E vi a _ _ Hvi Hw). apply eqm_of_eq. rewrite Z.mod_small by lia. reflexivity.
      * apply eqm_of_eq. zev. apply strip_sound. lia.
    + destruct (as_mask a) as [k|] eqn:Hma.
      * apply as_mask_spec in Hma as [-> Hk]. zev. rewrite Z.land_comm.
        rewrite (Z.mod_small (2 ^ k - 1) M64).
        2:{ split; [pose proof (Z.pow_pos_nonneg 2 k); lia|]. apply Z.lt_le_trans with (m := 2 ^ k); [lia|].
            rewrite M64_eq. apply Z.pow_le_mono_r; lia. }
        rewrite land_mask, mod_mod_pow2 by lia.
        destruct (within vi b 0 (2 ^ k - 1)) eqn:Hw.
        -- pose proof (within_sound E vi b _ _ Hvi Hw). apply eqm_of_eq. rewrite Z.mod_small by lia. reflexivity.
        -- apply eqm_of_eq. zev. apply strip_sound. lia.
      * destruct (inU vi a && inU vi b) eqn:Hu; [|apply eqm_of_eq; reflexivity].
        apply andb_prop in Hu as [H1 H2]. pose proof (within_sound E vi a _ _ Hvi H1). pose proof (within_sound E vi b _ _ Hvi H2).
        apply eqm_of_eq. zev. rewrite !Z.mod_small by (lia). reflexivity.
Qed.

Lemma mk_aluw_sound : forall E vi op a b, vi_ok E vi -> op32_ok op = true ->
  ev E (mk_aluw vi op a b) = zaluw op (ev E a) (ev E b).
Proof.
  intros E vi op a b Hvi Hop.
  pose proof (Z.mod_pos_bound (ev E a) M64 ltac:(lia)) as Hua.
  pose proof (Z.mod_pos_bound (ev E b) M64 ltac:(lia)) as Hub.
  destruct op; cbn [mk_aluw zaluw]; try discriminate.
  - rewrite wrap32_ev, zadd_ev by assumption. apply swrap32_congr.
    rewrite <- (mod64_mod32 (ev E a mod M64 + ev E b mod M64)). rewrite M64_eq, <- Zplus_mod, <- M64_eq. symmetry. apply mod64_mod32.
  - rewrite wrap32_ev, zsub_ev by assumption. apply swrap32_congr.
    rewrite <- (mod64_mod32 (ev E a mod M64 - ev E b mod M64)). rewrite M64_eq, <- Zminus_mod, <- M64_eq. symmetry. apply mod64_mod32.
  - (* [comment removed for export] *)
    assert (Hvar : within vi b 0 31 = true -> ev E (wrap32 vi (ZShlv a b)) = bv_swrap 32 (Z.shiftl (ev E a mod M64) ((ev E b mod M64) mod 32))).
    { intros Hw. rewrite wrap32_ev by assumption. zev. pose proof (within_sound E vi b _ _ Hvi Hw) as Hb. apply swrap32_congr.
      rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia).
      rewrite (Z.mod_small (ev E b) M64) by (lia). rewrite (Z.mod_small (ev E b) 32) by lia.
      rewrite <- (mod64_mod32 (ev E a mod M64 * _)), M64_eq, Zmult_mod_idemp_l, <- M64_eq. symmetry. apply mod64_mod32. }
    destruct b as [s| | | | | | | | | | | | | | |].
    1:{ rewrite wrap32_ev, zmul_ev by assumption. zev. apply swrap32_congr.
        rewrite Z.shiftl_mul_pow2 by (apply Z.mod_pos_bound; lia). unfold shamt32.
        rewrite <- (mod64_mod32 (ev E a mod M64 * _)), M64_eq, Zmult_mod_idemp_l, <- M64_eq. symmetry. apply mod64_mod32. }
    all: destruct (within vi _ 0 31) eqn:Hw; [apply Hvar; reflexivity|reflexivity].
  - (* [comment removed for export] *)
    assert (Hvar : within vi b 0 31 = true -> ev E (wrap32 vi (ZShrv (nU32 vi a) b)) = bv_swrap 32 (Z.shiftr (bv_wrap 32 (ev E a mod M64)) ((ev E b mod M64) mod 32))).
    { intros Hw. rewrite wrap32_ev by assumption. zev. rewrite nU32_ev by assumption.
      pose proof (within_sound E vi b _ _ Hvi Hw) as Hb. f_equal.
      change (bv_wrap 32 (ev E a mod M64)) with ((ev E a mod M64) mod M32). rewrite mod64_mod32.
      rewrite (Z.mod_small (ev E b) M64) by (lia). rewrite (Z.mod_small (ev E b) 32) by lia.
      rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
    destruct b as [s| | | | | | | | | | | | | | |].
    1:{ rewrite wrap32_ev by assumption. f_equal. pose proof (shamt32_range s) as Hs.
        change (bv_wrap 32 (ev E a mod M64)) with ((ev E a mod M64) mod M32). rewrite mod64_mod32.
        destruct (Z.eqb_spec (shamt32 s) 0) as [Hz|Hz]; unfold shamt32 in *.
        * rewrite nU32_ev by assumption. zev. rewrite Hz, Z.shiftr_0_r. reflexivity.
        * zev. rewrite nU32_ev by assumption. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
    all: destruct (within vi _ 0 31) eqn:Hw; [apply Hvar; reflexivity|reflexivity].
  - (* [comment removed for export] *)
    destruct b as [s| | | | | | | | | | | | | | |]; [|reflexivity..].
    rewrite wrap32_ev by assumption. f_equal. pose proof (shamt32_range s) as Hs.
    rewrite (swrap32_congr (ev E a mod M64) (ev E a)) by apply mod64_mod32.
    destruct (Z.eqb_spec (shamt32 s) 0) as [Hz|Hz]; unfold shamt32 in *.
    + rewrite nS32_ev by assumption. zev. rewrite Hz, Z.shiftr_0_r. reflexivity.
    + zev. rewrite nS32_ev by assumption. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition aluop_eqb (a b : aluop) : bool :=
  match a, b with
  | ALU_ADD, ALU_ADD | ALU_SUB, ALU_SUB | ALU_SLL, ALU_SLL | ALU_SLT, ALU_SLT
  | ALU_SLTU, ALU_SLTU | ALU_XOR, ALU_XOR | ALU_SRL, ALU_SRL | ALU_SRA, ALU_SRA
  | ALU_OR, ALU_OR | ALU_AND, ALU_AND => true
  | _, _ => false
  end.

Lemma aluop_eqb_eq : forall a b, aluop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; try reflexivity; discriminate. Qed.

Fixpoint zx_eqb (x y : zx) : bool :=
  match x, y with
  | ZL a, ZL b => Z.eqb a b
  | ZV a, ZV b => Nat.eqb a b
  | ZAdd a b, ZAdd a' b' | ZSub a b, ZSub a' b' | ZMul a b, ZMul a' b'
  | ZAnd a b, ZAnd a' b' | ZOr a b, ZOr a' b' | ZXor a b, ZXor a' b'
  | ZShlv a b, ZShlv a' b' | ZShrv a b, ZShrv a' b' | ZLt a b, ZLt a' b' => zx_eqb a a' && zx_eqb b b'
  | ZModP a k, ZModP a' k' | ZDivP a k, ZDivP a' k' => zx_eqb a a' && Z.eqb k k'
  | ZSw w a, ZSw w' a' => N.eqb w w' && zx_eqb a a'
  | ZAlu o a b, ZAlu o' a' b' | ZAluw o a b, ZAluw o' a' b' => aluop_eqb o o' && zx_eqb a a' && zx_eqb b b'
  | _, _ => false
  end.

Lemma zx_eqb_eq : forall x y, zx_eqb x y = true -> x = y.
Proof.
  induction x; destruct y; cbn; intros H; try discriminate;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    repeat match goal with
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : N.eqb _ _ = true |- _ => apply N.eqb_eq in H
      | H : aluop_eqb _ _ = true |- _ => apply aluop_eqb_eq in H
      | H : zx_eqb ?a _ = true, IH : forall y, zx_eqb ?a y = true -> _ |- _ => apply IH in H
      end; subst; reflexivity.
Qed.

(* [comment removed for export] *)

Definition ridx (r : reg) : nat := Z.to_nat (bv_unsigned r).

Lemma ridx_inj : forall r r' : reg, ridx r = ridx r' -> r = r'.
Proof. intros r r' H. apply bv_eq. unfold ridx in H. pose proof (u5_range r). pose proof (u5_range r'). lia. Qed.

Definition sr_get (sr : list zx) (r : reg) : zx :=
  if bv_eqb r 0 then ZL 0 else nth (ridx r) sr (ZL 0).

Fixpoint sr_upd (sr : list zx) (n : nat) (e : zx) : list zx :=
  match n with
  | O => match sr with [] => [e] | _ :: t => e :: t end
  | S n' => match sr with
            | [] => ZL 0 :: sr_upd [] n' e
            | h :: t => h :: sr_upd t n' e
            end
  end.

Lemma nth_sr_upd : forall n sr e i,
  nth i (sr_upd sr n e) (ZL 0) = if Nat.eqb i n then e else nth i sr (ZL 0).
Proof.
  induction n as [|n IH]; intros sr e i.
  - destruct sr; destruct i; cbn; try reflexivity; destruct i; reflexivity.
  - destruct sr as [|h t]; destruct i as [|i]; cbn; try reflexivity.
    + rewrite IH. destruct (Nat.eqb i n); [reflexivity|]. destruct i; reflexivity.
    + apply IH.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Record sentry : Type := SE { se_base : zx; se_off : Z; se_n : nat; se_val : zx }.
(* [comment removed for export] *)
Record kcell : Type := KC { kc_base : zx; kc_off : Z; kc_n : nat; kc_val : zx }.
(* [comment removed for export] *)
Record kwin : Type := KW { kw_base : zx; kw_lo : Z; kw_hi : Z }.

Record ctx : Type := CTX { c_vi : vitab; c_kn : list kcell; c_kw : list kwin }.

Inductive zcond : Type :=
| CEq (a b : zx) | CNe (a b : zx) | CLt (a b : zx) | CGe (a b : zx).

Inductive zsc : Type :=
| SCBr (c : zcond)
| SCFlat (b : zx) (k : Z) (n : nat)
| SCDisj (b1 : zx) (k1 : Z) (n1 : nat) (b2 : zx) (k2 : Z) (n2 : nat)
| SCStore (b : zx) (k : Z) (n : nat)
| SCRead (b : zx) (k : Z) (n : nat) (v : zx).

Record zst : Type := ZS { z_pc : Z; z_rs : list zx; z_log : list sentry }.

Record script : Type := SCR { sc_dirs : list bool; sc_reads : list zx }.

Definition addr (E : env) (b : zx) (k : Z) : word := Z_to_bv 64 (ev E b + k).

Definition cond_ok (E : env) (c : zcond) : Prop :=
  match c with
  | CEq a b => ev E a = ev E b
  | CNe a b => ev E a <> ev E b
  | CLt a b => ev E a < ev E b
  | CGe a b => ev E b <= ev E a
  end.

Definition flat (E : env) (b : zx) (k : Z) (n : nat) : Prop :=
  0 <= ev E b + k /\ ev E b + k < M64 /\ ev E b + k + Z.of_nat n <= M64.

Section WithSegs.
Variable segs : list Segment.

Definition sc_ok (E : env) (m : word -> option byte) (c : zsc) : Prop :=
  match c with
  | SCBr c => cond_ok E c
  | SCFlat b k n => flat E b k n
  | SCDisj b1 k1 n1 b2 k2 n2 =>
      flat E b1 k1 n1 /\ flat E b2 k2 n2 /\
      (ev E b1 + k1 + Z.of_nat n1 <= ev E b2 + k2 \/ ev E b2 + k2 + Z.of_nat n2 <= ev E b1 + k1)
  | SCStore b k n => RiscvSemantics.store_ok segs m (addr E b k) n = true
  | SCRead b k n v => exists bs, rdn segs m (addr E b k) n = Some bs /\ bytes_le_to_Z bs = ev E v
  end.

Definition scs_ok (E : env) (m : word -> option byte) (l : list zsc) : Prop := Forall (sc_ok E m) l.

Definition kn_ok (E : env) (m : word -> option byte) (kn : list kcell) : Prop :=
  Forall (fun c => flat E (kc_base c) (kc_off c) (kc_n c) /\
                   exists bs, rdn segs m (addr E (kc_base c) (kc_off c)) (kc_n c) = Some bs
                              /\ bytes_le_to_Z bs = ev E (kc_val c)) kn.

Definition kw_ok (E : env) (m : word -> option byte) (kw : list kwin) : Prop :=
  Forall (fun w => 0 <= ev E (kw_base w) + kw_lo w /\ ev E (kw_base w) + kw_hi w <= M64 /\
                   forall k n, kw_lo w <= k -> k + Z.of_nat n <= kw_hi w ->
                               RiscvSemantics.store_ok segs m (addr E (kw_base w) k) n = true) kw.

Definition ctx_ok (E : env) (m : word -> option byte) (C : ctx) : Prop :=
  vi_ok E (c_vi C) /\ kn_ok E m (c_kn C) /\ kw_ok E m (c_kw C).

(* [comment removed for export] *)

Fixpoint mem_denot (E : env) (m : word -> option byte) (log : list sentry) : word -> option byte :=
  match log with
  | [] => m
  | SE b k n v :: rest => wbytes (mem_denot E m rest) (addr E b k) (word_to_le_bytes n (wd E v))
  end.

Fixpoint log_flat (E : env) (log : list sentry) : Prop :=
  match log with
  | [] => True
  | SE b k n _ :: rest => flat E b k n /\ log_flat E rest
  end.

Lemma mem_denot_grows : forall E m log, mem_grows m (mem_denot E m log).
Proof.
  intros E m log. induction log as [|[b k n v] rest IH]; cbn [mem_denot].
  - apply mem_grows_refl.
  - eapply mem_grows_trans; [exact IH | apply wbytes_grows].
Qed.

Section WithFP.
Context {fx : FPState}.

Definition regs_ok (E : env) (sr : list zx) (regs : bvmap 5 word) : Prop :=
  forall r : reg, getr regs r = wd E (sr_get sr r).

Definition st_ok (E : env) (m rom : word -> option byte) (st : zst) (ms : machine_state) : Prop :=
  exists regs, ms = mkst regs (Z_to_bv 64 (z_pc st)) (mem_denot E m (z_log st)) rom
          /\ regs_ok E (z_rs st) regs /\ log_flat E (z_log st).

Lemma regs_ok_upd : forall E sr regs (rd : reg) v e,
  regs_ok E sr regs -> wd E e = v ->
  regs_ok E (if bv_eqb rd 0 then sr else sr_upd sr (ridx rd) e)
            (if bv_eqb rd 0 then regs else regupd regs rd v).
Proof.
  intros E sr regs rd v e Hr Hv.
  destruct (bv_eqb rd 0) eqn:Hrd; [exact Hr|].
  assert (Hne : rd <> 0%bv).
  { intro Hc. subst rd. rewrite bv_eqb_refl in Hrd. discriminate. }
  intro r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia).
    subst r. unfold getr. rewrite Hr0. reflexivity.
  - rewrite nth_sr_upd.
    destruct (Nat.eqb (ridx r) (ridx rd)) eqn:Hi.
    + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r.
      rewrite getr_same by exact Hne. exact (eq_sym Hv).
    + assert (Hrr : r <> rd).
      { intro Hc. subst r. rewrite Nat.eqb_refl in Hi. discriminate. }
      rewrite getr_other by exact Hrr.
      specialize (Hr r). unfold sr_get in Hr. rewrite Hr0 in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition split_addr (e : zx) (imm : Z) : zx * Z :=
  match zadd e (ZL imm) with
  | ZL k => (ZL 0, k)
  | ZAdd b (ZL k) => (b, k)
  | e' => (e', 0)
  end.

Lemma split_addr_ev : forall E e imm b k, split_addr e imm = (b, k) -> ev E b + k = ev E e + imm.
Proof.
  intros E e imm b k H. unfold split_addr in H.
  pose proof (zadd_ev E e (ZL imm)) as Hz. cbn [ev] in Hz.
  destruct (zadd e (ZL imm)) as [z| |a c| | | | | | | | | | | | |] eqn:Ez;
    try (injection H as <- <-; cbn [ev] in *; lia).
  destruct c as [z| | | | | | | | | | | | | | |]; injection H as <- <-; cbn [ev] in *; lia.
Qed.

(* [comment removed for export] *)
Definition flat_auto (vi : vitab) (b : zx) (k : Z) (n : nat) : bool :=
  match itv vi b with
  | Some (lo, hi) => (0 <=? lo + k) && (hi + k <? M64) && (hi + k + Z.of_nat n <=? M64)
  | None => false
  end.

Definition flat_sc (vi : vitab) (b : zx) (k : Z) (n : nat) : list zsc :=
  if flat_auto vi b k n then [] else [SCFlat b k n].

(* [comment removed for export] *)
Definition disj_auto (vi : vitab) (b1 : zx) (k1 : Z) (n1 : nat) (b2 : zx) (k2 : Z) (n2 : nat) : bool :=
  match itv vi b1, itv vi b2 with
  | Some (l1, h1), Some (l2, h2) => (h1 + k1 + Z.of_nat n1 <=? l2 + k2) || (h2 + k2 + Z.of_nat n2 <=? l1 + k1)
  | _, _ => false
  end.

Inductive lres : Type :=
| LHit (v : zx) (scs : list zsc)      (* [comment removed for export] *)
| LMiss (scs : list zsc)              (* [comment removed for export] *)
| LStuck.

Fixpoint log_lookup (vi : vitab) (log : list sentry) (b : zx) (k : Z) (n : nat) : lres :=
  match log with
  | [] => LMiss []
  | SE b' k' n' v :: rest =>
      if zx_eqb b b' then
        if (k =? k') && Nat.eqb n n' then LHit v []
        else if (k + Z.of_nat n <=? k') || (k' + Z.of_nat n' <=? k) then log_lookup vi rest b k n
        else LStuck
      else if disj_auto vi b k n b' k' n' then log_lookup vi rest b k n
      else match log_lookup vi rest b k n with
           | LHit v scs => LHit v (SCDisj b k n b' k' n' :: scs)
           | LMiss scs => LMiss (SCDisj b k n b' k' n' :: scs)
           | LStuck => LStuck
           end
  end.

Fixpoint kn_lookup (kn : list kcell) (b : zx) (k : Z) (n : nat) : option zx :=
  match kn with
  | [] => None
  | KC b' k' n' v :: rest =>
      if zx_eqb b b' && (k =? k') && Nat.eqb n n' then Some v else kn_lookup rest b k n
  end.

Fixpoint kw_lookup (kw : list kwin) (b : zx) (k : Z) (n : nat) : bool :=
  match kw with
  | [] => false
  | KW b' lo hi :: rest =>
      if zx_eqb b b' && (lo <=? k) && (k <? hi) && (k + Z.of_nat n <=? hi) then true else kw_lookup rest b k n
  end.

(* [comment removed for export] *)
Definition sx_wrap (vi : vitab) (w : N) (hmax : Z) (v : zx) : zx :=
  if within vi v 0 hmax then v else zsw w v.

Definition load_val (vi : vitab) (n : nat) (sx : bool) (v : zx) : zx :=
  if sx then
    match n with
    | 1%nat => sx_wrap vi 8 127 v
    | 2%nat => sx_wrap vi 16 32767 v
    | 4%nat => sx_wrap vi 32 2147483647 v
    | _ => v
    end
  else v.

(* [comment removed for export] *)
Definition stored_val (vi : vitab) (n : nat) (e : zx) : zx :=
  if within vi e 0 (2 ^ (8 * Z.of_nat n) - 1) then e else zmodp e (8 * Z.of_nat n).

Definition msz (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end%nat.

(* [comment removed for export] *)
Definition load_ok (sz : msize) (sx : bool) : bool :=
  match sz, sx with SZ8, false => false | _, _ => true end.

(* [comment removed for export] *)
Definition br_operands (vi : vitab) (c : branch_cond) (a b : zx) : zx * zx :=
  match c with
  | BC_LT | BC_GE => (nS vi a, nS vi b)
  | BC_LTU | BC_GEU => (nU vi a, nU vi b)
  | BC_EQ | BC_NE => if inS vi a && inS vi b then (a, b) else (nU vi a, nU vi b)
  end.

(* [comment removed for export] *)
Definition br_cond (c : branch_cond) (taken : bool) (x y : zx) : zcond :=
  match c, taken with
  | BC_EQ, true => CEq x y | BC_EQ, false => CNe x y
  | BC_NE, true => CNe x y | BC_NE, false => CEq x y
  | BC_LT, true => CLt x y | BC_LT, false => CGe x y
  | BC_GE, true => CGe x y | BC_GE, false => CLt x y
  | BC_LTU, true => CLt x y | BC_LTU, false => CGe x y
  | BC_GEU, true => CGe x y | BC_GEU, false => CLt x y
  end.

Definition decide_cond (vi : vitab) (c : zcond) : option bool :=
  match c with
  | CLt x y => match itv vi x, itv vi y with
               | Some (lx, hx), Some (ly, hy) => if hx <? ly then Some true else if hy <=? lx then Some false else None
               | _, _ => None end
  | CGe x y => match itv vi x, itv vi y with
               | Some (lx, hx), Some (ly, hy) => if hy <=? lx then Some true else if hx <? ly then Some false else None
               | _, _ => None end
  | CEq x y => if zx_eqb x y then Some true else
               match itv vi x, itv vi y with
               | Some (lx, hx), Some (ly, hy) =>
                   if (hx <? ly) || (hy <? lx) then Some false
                   else if (lx =? hx) && (ly =? hy) && (lx =? ly) then Some true else None
               | _, _ => None end
  | CNe x y => if zx_eqb x y then Some false else
               match itv vi x, itv vi y with
               | Some (lx, hx), Some (ly, hy) =>
                   if (hx <? ly) || (hy <? lx) then Some true
                   else if (lx =? hx) && (ly =? hy) && (lx =? ly) then Some false else None
               | _, _ => None end
  end.

(* [comment removed for export] *)
Definition normlit (e : zx) : zx :=
  match e with
  | ZL c => if (0 <=? c) && (c <? M64) then e else ZL (c mod M64)
  | _ => e
  end.

Lemma wd_normlit : forall E e, wd E (normlit e) = wd E e.
Proof.
  intros E e. destruct e; cbn [normlit]; try reflexivity.
  destruct ((0 <=? z) && (z <? M64)); [reflexivity|]. unfold wd. cbn [ev]. apply Z2bv_mod.
Qed.

Inductive stepres : Type :=
| SOk (st : zst) (scs : list zsc) (scr : script)
| SStop.

Definition sset (st : zst) (rd : reg) (e : zx) (npc : Z) : zst :=
  ZS npc (if bv_eqb rd 0 then z_rs st else sr_upd (z_rs st) (ridx rd) e) (z_log st).

Definition zstep (C : ctx) (i : instr) (st : zst) (scr : script) : stepres :=
  let vi := c_vi C in
  let g r := sr_get (z_rs st) r in
  let p := z_pc st in
  match i with
  | OpImm op rd rs imm => SOk (sset st rd (normlit (mk_alu vi op (g rs) (ZL (bv_signed imm)))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset st rd (normlit (mk_alu vi op (g rs) (ZL (bv_unsigned sh)))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset st rd (normlit (mk_alu vi op (g rs1) (g rs2))) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset st rd (normlit (mk_aluw vi ALU_ADD (g rs) (ZL (bv_signed imm)))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh =>
      if op32_ok op then SOk (sset st rd (normlit (mk_aluw vi op (g rs) (ZL (bv_unsigned sh)))) (p + 4)) [] scr else SStop
  | Op32 op rd rs1 rs2 =>
      if op32_ok op then SOk (sset st rd (normlit (mk_aluw vi op (g rs1) (g rs2))) (p + 4)) [] scr else SStop
  | Mul M_MUL rd rs1 rs2 => SOk (sset st rd (normlit (zmul (g rs1) (g rs2))) (p + 4)) [] scr
  | Lui rd imm => SOk (sset st rd (ZL (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset st rd (ZL (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset st rd (ZL (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match g rs1 with
      | ZL z => SOk (sset st rd (ZL (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2 ^ 64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let (x, y) := br_operands vi c (g rs1) (g rs2) in
      match decide_cond vi (br_cond c true x y) with
      | Some t => SOk (ZS (if t then tk else p + 4) (z_rs st) (z_log st)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' => SOk (ZS (if t then tk else p + 4) (z_rs st) (z_log st))
                              [SCBr (br_cond c t x y)] (SCR dirs' (sc_reads scr))
          end
      end
  | Load sz sx rd rs imm =>
      if negb (load_ok sz sx) then SStop else
      let n := msz sz in
      let (b, k) := split_addr (g rs) (bv_signed imm) in
      let fsc := flat_sc vi b k n in
      match log_lookup vi (z_log st) b k n with
      | LStuck => SStop
      | LHit e scs => SOk (sset st rd (load_val vi n sx (stored_val vi n e)) (p + 4)) (fsc ++ scs) scr
      | LMiss scs =>
          match kn_lookup (c_kn C) b k n with
          | Some v => SOk (sset st rd (load_val vi n sx v) (p + 4)) (fsc ++ scs) scr
          | None =>
              match sc_reads scr with
              | [] => SStop
              | v :: reads' => SOk (sset st rd (load_val vi n sx v) (p + 4))
                                   (fsc ++ SCRead b k n v :: scs) (SCR (sc_dirs scr) reads')
              end
          end
      end
  | Store sz rs1 rs2 imm =>
      let n := msz sz in
      let (b, k) := split_addr (g rs1) (bv_signed imm) in
      let fsc := flat_sc vi b k n in
      let ssc := if kw_lookup (c_kw C) b k n then [] else [SCStore b k n] in
      SOk (ZS (p + 4) (z_rs st) (SE b k n (g rs2) :: z_log st)) (fsc ++ ssc) scr
  | Fence _ _ _ _ _ | FenceI _ _ _ => SOk (ZS (p + 4) (z_rs st) (z_log st)) [] scr   (* [comment removed for export] *)
  | _ => SStop
  end.

(* [comment removed for export] *)
Fixpoint zrun (C : ctx) (fuel : nat) (first : bool) (stops : list Z) (scr : script) (st : zst) (acc : list zsc)
  : zst * list zsc :=
  match fuel with
  | O => (st, acc)
  | S f =>
      if negb first && existsb (Z.eqb (z_pc st)) stops then (st, acc) else
      match fetch_word segs (Z_to_bv 64 (z_pc st)) with
      | None => (st, acc)
      | Some w =>
          if is_ecall w then (st, acc) else
          match decode_any w with
          | None => (st, acc)
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (st, acc) else
              match zstep C i st scr with
              | SOk st' scs scr' => zrun C f false stops scr' st' (scs ++ acc)
              | SStop => (st, acc)
              end
          end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma scs_ok_cons : forall E m c l, scs_ok E m (c :: l) <-> sc_ok E m c /\ scs_ok E m l.
Proof. intros. unfold scs_ok. split; [intros H; inversion H; auto | intros [? ?]; constructor; auto]. Qed.

Lemma scs_ok_app : forall E m l1 l2, scs_ok E m (l1 ++ l2) <-> scs_ok E m l1 /\ scs_ok E m l2.
Proof. intros. unfold scs_ok. apply Forall_app. Qed.

Lemma flat_auto_sound : forall E vi b k n, vi_ok E vi -> flat_auto vi b k n = true -> flat E b k n.
Proof.
  intros E vi b k n Hvi H. unfold flat_auto in H. destruct (itv vi b) as [[lo hi]|] eqn:Ei; [|discriminate].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  pose proof (itv_sound E vi b lo hi Hvi Ei). unfold flat. lia.
Qed.

Lemma flat_sc_sound : forall E m vi b k n, vi_ok E vi -> scs_ok E m (flat_sc vi b k n) -> flat E b k n.
Proof.
  intros E m vi b k n Hvi H. unfold flat_sc in H. destruct (flat_auto vi b k n) eqn:Ha.
  - eapply flat_auto_sound; eauto.
  - apply scs_ok_cons in H as [H _]. exact H.
Qed.

Lemma disj_auto_sound : forall E vi b1 k1 n1 b2 k2 n2, vi_ok E vi -> disj_auto vi b1 k1 n1 b2 k2 n2 = true ->
  ev E b1 + k1 + Z.of_nat n1 <= ev E b2 + k2 \/ ev E b2 + k2 + Z.of_nat n2 <= ev E b1 + k1.
Proof.
  intros E vi b1 k1 n1 b2 k2 n2 Hvi H. unfold disj_auto in H.
  destruct (itv vi b1) as [[l1 h1]|] eqn:E1; [|discriminate]. destruct (itv vi b2) as [[l2 h2]|] eqn:E2; [|discriminate].
  pose proof (itv_sound E vi b1 l1 h1 Hvi E1). pose proof (itv_sound E vi b2 l2 h2 Hvi E2).
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma addr_u : forall E b k n, flat E b k n -> bv_unsigned (addr E b k) = ev E b + k.
Proof.
  intros E b k n (H1 & H2 & H3). unfold addr. rewrite u_Z2bv64. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_le_word_to_le : forall n (w : word), (n <= 8)%nat ->
  bytes_le_to_Z (word_to_le_bytes n w) = bv_unsigned w mod 2 ^ (8 * Z.of_nat n).
Proof. intros. apply bytes_le_N. Qed.

Lemma log_lookup_sound : forall E m vi log b k n r,
  vi_ok E vi ->
  log_lookup vi log b k n = r ->
  match r with LHit _ scs | LMiss scs => scs_ok E m scs | LStuck => False end ->
  log_flat E log -> flat E b k n -> (n <= 8)%nat ->
  match r with
  | LMiss _ => rdn segs (mem_denot E m log) (addr E b k) n = rdn segs m (addr E b k) n
  | LHit v _ => exists bs, rdn segs (mem_denot E m log) (addr E b k) n = Some bs
                           /\ bytes_le_to_Z bs = ev E v mod 2 ^ (8 * Z.of_nat n)
  | LStuck => True
  end.
Proof.
  intros E m vi log. induction log as [|[b' k' n' v'] rest IH]; intros b k n r Hvi Hl Hsc Hlf Hfl Hn8.
  { cbn in Hl. subst r. reflexivity. }
  cbn [log_flat] in Hlf. destruct Hlf as [Hf' Hlf].
  pose proof (addr_u E b k n Hfl) as Hu. pose proof (addr_u E b' k' n' Hf') as Hu'.
  cbn [log_lookup] in Hl. cbn [mem_denot].
  assert (SKIP : (ev E b + k + Z.of_nat n <= ev E b' + k' \/ ev E b' + k' + Z.of_nat n' <= ev E b + k) ->
      rdn segs (wbytes (mem_denot E m rest) (addr E b' k') (word_to_le_bytes n' (wd E v'))) (addr E b k) n
      = rdn segs (mem_denot E m rest) (addr E b k) n).
  { intros Hd. destruct Hfl as [F1 F2]. destruct Hf' as [F3 F4]. destruct Hd as [Hd|Hd].
    - apply rdn_wbytes_below; [lia | rewrite length_N_to_le_bytes; lia].
    - apply rdn_wbytes_disjoint; [rewrite length_N_to_le_bytes; lia | lia]. }
  destruct (zx_eqb b b') eqn:Hbb.
  - apply zx_eqb_eq in Hbb. subst b'.
    destruct ((k =? k') && Nat.eqb n n') eqn:Hhit.
    + subst r. apply andb_prop in Hhit as [Hk Hn]. apply Z.eqb_eq in Hk. apply Nat.eqb_eq in Hn. subst k' n'.
      exists (word_to_le_bytes n (wd E v')). split.
      * pose proof (rdn_wbytes_hit segs (word_to_le_bytes n (wd E v')) (mem_denot E m rest) (addr E b k)) as Hh.
        rewrite length_N_to_le_bytes in Hh. apply Hh. destruct Hfl. lia.
      * rewrite bytes_le_word_to_le by assumption. unfold wd. rewrite u_Z2bv64.
        rewrite <- (mod_mod_pow2 (ev E v')) by lia. reflexivity.
    + destruct ((k + Z.of_nat n <=? k') || (k' + Z.of_nat n' <=? k)) eqn:Hdis; [|subst r; exact I].
      assert (Hd : ev E b + k + Z.of_nat n <= ev E b + k' \/ ev E b + k' + Z.of_nat n' <= ev E b + k).
      { apply orb_prop in Hdis as [Hdis|Hdis]; apply Z.leb_le in Hdis; lia. }
      specialize (IH b k n r Hvi Hl Hsc Hlf Hfl Hn8).
      destruct r as [v scs|scs|]; [| |exact I]; rewrite (SKIP Hd); exact IH.
  - destruct (disj_auto vi b k n b' k' n') eqn:Hda.
    + pose proof (disj_auto_sound E vi b k n b' k' n' Hvi Hda) as Hd.
      specialize (IH b k n r Hvi Hl Hsc Hlf Hfl Hn8).
      destruct r as [v scs|scs|]; [| |exact I]; rewrite (SKIP Hd); exact IH.
    + destruct (log_lookup vi rest b k n) as [v scs|scs|] eqn:Hr; subst r; [| |exact I];
        apply scs_ok_cons in Hsc as [Hd Hsc]; cbn [sc_ok] in Hd; destruct Hd as (_ & _ & Hd);
        specialize (IH b k n _ Hvi Hr Hsc Hlf Hfl Hn8); cbn in IH; rewrite (SKIP Hd); exact IH.
Qed.

Lemma kn_lookup_sound : forall E m kn b k n v,
  kn_ok E m kn -> kn_lookup kn b k n = Some v ->
  exists bs, rdn segs m (addr E b k) n = Some bs /\ bytes_le_to_Z bs = ev E v.
Proof.
  intros E m kn. induction kn as [|[b' k' n' v'] rest IH]; intros b k n v Hkn H; [discriminate|].
  apply Forall_cons_iff in Hkn as [Hc Hrest]. cbn [kn_lookup] in H.
  destruct (zx_eqb b b' && (k =? k') && Nat.eqb n n') eqn:Hm.
  - injection H as <-. apply andb_prop in Hm as [Hm Hn]. apply andb_prop in Hm as [Hb Hk].
    apply zx_eqb_eq in Hb. apply Z.eqb_eq in Hk. apply Nat.eqb_eq in Hn. subst. cbn in Hc. destruct Hc as [_ Hc]. exact Hc.
  - eapply IH; eauto.
Qed.

Lemma kw_lookup_sound : forall E m kw b k n,
  kw_ok E m kw -> kw_lookup kw b k n = true ->
  RiscvSemantics.store_ok segs m (addr E b k) n = true /\ flat E b k n.
Proof.
  intros E m kw. induction kw as [|[b' lo hi] rest IH]; intros b k n Hkw H; [discriminate|].
  apply Forall_cons_iff in Hkw as [Hc Hrest]. cbn [kw_lookup] in H.
  destruct (zx_eqb b b' && (lo <=? k) && (k <? hi) && (k + Z.of_nat n <=? hi)) eqn:Hm.
  - apply andb_prop in Hm as [Hm H2]. apply andb_prop in Hm as [Hm H3]. apply andb_prop in Hm as [Hb H1].
    apply zx_eqb_eq in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. subst b'.
    cbn in Hc. destruct Hc as (Hlo & Hhi & Hst). split; [apply Hst; lia|]. unfold flat. lia.
  - eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Lemma rdn_val_range : forall m a n bs, rdn segs m a n = Some bs -> 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat n).
Proof.
  intros m a n bs H. pose proof (rdn_length segs m n a bs H) as Hlen. subst n.
  split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound].
Qed.

(* [comment removed for export] *)
Lemma load_val_sound : forall E vi n sx v (u : Z),
  vi_ok E vi -> ev E v = u -> 0 <= u < 2 ^ (8 * Z.of_nat n) -> (n = 1 \/ n = 2 \/ n = 4 \/ n = 8)%nat ->
  wd E (load_val vi n sx v) =
    (if sx then match n with
                | 1%nat => Z_to_bv 64 (bv_swrap 8 u)
                | 2%nat => v_lh (Z_to_bv 64 u)
                | 4%nat => v_lw (Z_to_bv 64 u)
                | _ => Z_to_bv 64 u
                end
     else Z_to_bv 64 u).
Proof.
  intros E vi n sx v u Hvi Hv Hu Hn. unfold load_val, wd.
  destruct sx; [|rewrite Hv; reflexivity].
  assert (GEN : forall (w : N) hmax, hmax + 1 = 2 ^ (Z.of_N w - 1) -> 8 * Z.of_nat n = Z.of_N w ->
    ev E (sx_wrap vi w hmax v) = bv_swrap w u).
  { intros w hmax Hh Hwn. unfold sx_wrap. destruct (within vi v 0 _) eqn:Hin; zev; rewrite Hv; [|reflexivity].
    pose proof (within_sound E vi v _ _ Hvi Hin) as Hr. rewrite Hv in Hr.
    symmetry. apply bv_swrap_id; lia. }
  destruct Hn as [->|[->|[->| ->]]].
  - rewrite (GEN 8%N 127); reflexivity.
  - rewrite (GEN 16%N 32767) by reflexivity. unfold v_lh. rewrite u_Z2bv64, Z.mod_small by (cbn in Hu; lia). reflexivity.
  - rewrite (GEN 32%N 2147483647) by reflexivity. unfold v_lw. rewrite u_Z2bv64, Z.mod_small by (cbn in Hu; lia). reflexivity.
  - rewrite Hv. reflexivity.
Qed.

Lemma stored_val_ev : forall E vi n e, vi_ok E vi -> ev E (stored_val vi n e) = ev E e mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros E vi n e Hvi. unfold stored_val. destruct (within vi e 0 _) eqn:Hin; zev; [|reflexivity].
  pose proof (within_sound E vi e _ _ Hvi Hin). rewrite Z.mod_small; [reflexivity|].
  pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_nat n)). lia.
Qed.

(* [comment removed for export] *)
Lemma v_lb_swrap : forall b : byte, v_lb b = Z_to_bv 64 (bv_swrap 8 (bv_unsigned b)).
Proof. intros b. unfold v_lb, bv_signed. reflexivity. Qed.

(* [comment removed for export] *)
Lemma step_lw : forall regs pc mem rom w rd rs (imm : bv 12) bs v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_lw v)) (v_addi pc 4) mem rom).
Proof.
  intros regs pc mem rom w rd rs imm bs v Hfetch Hecall Hdecode Hread Hv.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hread; rewrite ?bv_eqb0_is_x0 in Hread.
  rewrite ov_rdn, b_addsext, Hread; cbv beta iota.
  rewrite (le_word_v _ _ Hv), b_lw_val, b_npc4.
  destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_fence : forall regs pc mem rom w fm pr sc (rd rs1 : reg),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fence fm pr sc rd rs1, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros regs pc mem rom w fm pr sc rd rs1 Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

Lemma step_fencei : forall regs pc mem rom w (rd rs1 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (FenceI rd rs1 imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof.
  intros regs pc mem rom w rd rs1 imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode. rewrite b_npc4. reflexivity.
Qed.

Lemma v_addi_lit : forall p i, v_addi (Z_to_bv 64 p) i = Z_to_bv 64 (p + i).
Proof. intros. unfold v_addi. rewrite u_Z2bv64. apply Z2bv_eqm. rewrite M64_eq. apply Zplus_mod_idemp_l. Qed.

Lemma br_operands_sound : forall E vi c a b x y,
  vi_ok E vi -> br_operands vi c a b = (x, y) ->
  forall t, cond_ok E (br_cond c t x y) -> branch_taken c (wd E a) (wd E b) = t.
Proof.
  intros E vi c a b x y Hvi Hop t Hc.
  assert (HU : forall e, bv_unsigned (wd E e) = ev E (nU vi e)).
  { intros e. unfold wd. rewrite u_Z2bv64. symmetry. apply nU_ev. exact Hvi. }
  assert (HS : forall e, bv_signed (wd E e) = ev E (nS vi e)).
  { intros e. unfold wd. rewrite Z_to_bv_signed. symmetry. apply nS_ev. exact Hvi. }
  assert (HEQ : (inS vi a && inS vi b) = true -> (bv_unsigned (wd E a) =? bv_unsigned (wd E b)) = (ev E a =? ev E b)).
  { intros Hin. apply andb_prop in Hin as [Ha Hb].
    pose proof (within_sound E vi a _ _ Hvi Ha). pose proof (within_sound E vi b _ _ Hvi Hb).
    unfold wd. rewrite !u_Z2bv64. 
    destruct (Z.eqb_spec (ev E a) (ev E b)) as [->|Hne]; [apply Z.eqb_refl|].
    apply Z.eqb_neq. intros Hm. apply Hne.
    (* [comment removed for export] *)
    assert (Hd : (ev E a - ev E b) mod 18446744073709551616 = 0).
    { rewrite Zminus_mod, Hm, Z.sub_diag. reflexivity. }
    apply Z.mod_divide in Hd; [|lia]. destruct Hd as [q Hq]. assert (q = 0) by lia. subst q. lia. }
  destruct c; cbn [br_operands] in Hop; unfold branch_taken, bv_eqb, bv_lts, bv_ltu;
    try (injection Hop as <- <-); cbn [br_cond cond_ok] in Hc.
  - destruct (inS vi a && inS vi b) eqn:Hin.
    + injection Hop as <- <-. rewrite (HEQ eq_refl). destruct t; cbn [br_cond cond_ok] in Hc; [apply Z.eqb_eq; exact Hc | apply Z.eqb_neq; exact Hc].
    + injection Hop as <- <-. rewrite !HU. destruct t; cbn [br_cond cond_ok] in Hc; [apply Z.eqb_eq; exact Hc | apply Z.eqb_neq; exact Hc].
  - destruct (inS vi a && inS vi b) eqn:Hin.
    + injection Hop as <- <-. rewrite (HEQ eq_refl). destruct t; cbn [br_cond cond_ok negb] in Hc.
      * destruct (Z.eqb_spec (ev E a) (ev E b)); [contradiction|reflexivity].
      * rewrite (proj2 (Z.eqb_eq _ _) Hc). reflexivity.
    + injection Hop as <- <-. rewrite !HU. destruct t; cbn [br_cond cond_ok negb] in Hc.
      * destruct (Z.eqb_spec (ev E (nU vi a)) (ev E (nU vi b))); [contradiction|reflexivity].
      * rewrite (proj2 (Z.eqb_eq _ _) Hc). reflexivity.
  - rewrite !HS. destruct t; cbn [br_cond cond_ok] in Hc; [apply Z.ltb_lt; exact Hc | apply Z.ltb_ge; lia].
  - rewrite !HS. destruct t; cbn [br_cond cond_ok negb] in Hc.
    + destruct (Z.ltb_spec (ev E (nS vi a)) (ev E (nS vi b))); [lia|reflexivity].
    + destruct (Z.ltb_spec (ev E (nS vi a)) (ev E (nS vi b))); [reflexivity|lia].
  - rewrite !HU. destruct t; cbn [br_cond cond_ok] in Hc; [apply Z.ltb_lt; exact Hc | apply Z.ltb_ge; lia].
  - rewrite !HU. destruct t; cbn [br_cond cond_ok negb] in Hc.
    + destruct (Z.ltb_spec (ev E (nU vi a)) (ev E (nU vi b))); [lia|reflexivity].
    + destruct (Z.ltb_spec (ev E (nU vi a)) (ev E (nU vi b))); [reflexivity|lia].
Qed.

Lemma decide_cond_sound : forall E vi c t, vi_ok E vi -> decide_cond vi c = Some t ->
  if t then cond_ok E c else cond_ok E (match c with CEq x y => CNe x y | CNe x y => CEq x y | CLt x y => CGe x y | CGe x y => CLt x y end).
Proof.
  intros E vi c t Hvi H.
  assert (IT : forall x lx hx, itv vi x = Some (lx, hx) -> lx <= ev E x <= hx) by (intros; eapply itv_sound; eauto).
  destruct c as [x y|x y|x y|x y]; cbn [decide_cond] in H.
  - destruct (zx_eqb x y) eqn:Exy.
    + injection H as <-. apply zx_eqb_eq in Exy. subst. cbn. reflexivity.
    + destruct (itv vi x) as [[lx hx]|] eqn:Ex; [|discriminate]. destruct (itv vi y) as [[ly hy]|] eqn:Ey; [|discriminate].
      pose proof (IT _ _ _ Ex). pose proof (IT _ _ _ Ey).
      destruct ((hx <? ly) || (hy <? lx)) eqn:Hc.
      * injection H as <-. cbn. apply orb_prop in Hc as [Hc|Hc]; apply Z.ltb_lt in Hc; lia.
      * destruct ((lx =? hx) && (ly =? hy) && (lx =? ly)) eqn:Hs; [|discriminate]. injection H as <-. cbn.
        apply andb_prop in Hs as [Hs Q3]. apply andb_prop in Hs as [Q1 Q2].
        apply Z.eqb_eq in Q1. apply Z.eqb_eq in Q2. apply Z.eqb_eq in Q3. lia.
  - destruct (zx_eqb x y) eqn:Exy.
    + injection H as <-. apply zx_eqb_eq in Exy. subst. cbn. reflexivity.
    + destruct (itv vi x) as [[lx hx]|] eqn:Ex; [|discriminate]. destruct (itv vi y) as [[ly hy]|] eqn:Ey; [|discriminate].
      pose proof (IT _ _ _ Ex). pose proof (IT _ _ _ Ey).
      destruct ((hx <? ly) || (hy <? lx)) eqn:Hc.
      * injection H as <-. cbn. apply orb_prop in Hc as [Hc|Hc]; apply Z.ltb_lt in Hc; lia.
      * destruct ((lx =? hx) && (ly =? hy) && (lx =? ly)) eqn:Hs; [|discriminate]. injection H as <-. cbn.
        apply andb_prop in Hs as [Hs Q3]. apply andb_prop in Hs as [Q1 Q2].
        apply Z.eqb_eq in Q1. apply Z.eqb_eq in Q2. apply Z.eqb_eq in Q3. lia.
  - destruct (itv vi x) as [[lx hx]|] eqn:Ex; [|discriminate]. destruct (itv vi y) as [[ly hy]|] eqn:Ey; [|discriminate].
    pose proof (IT _ _ _ Ex). pose proof (IT _ _ _ Ey).
    destruct (Z.ltb_spec hx ly); [injection H as <-; cbn; lia|].
    destruct (Z.leb_spec hy lx); [injection H as <-; cbn; lia|discriminate].
  - destruct (itv vi x) as [[lx hx]|] eqn:Ex; [|discriminate]. destruct (itv vi y) as [[ly hy]|] eqn:Ey; [|discriminate].
    pose proof (IT _ _ _ Ex). pose proof (IT _ _ _ Ey).
    destruct (Z.leb_spec hy lx); [injection H as <-; cbn; lia|].
    destruct (Z.ltb_spec hx ly); [injection H as <-; cbn; lia|discriminate].
Qed.

Lemma br_cond_negate : forall c t x y,
  match br_cond c t x y with CEq a b => CNe a b | CNe a b => CEq a b | CLt a b => CGe a b | CGe a b => CLt a b end
  = br_cond c (negb t) x y.
Proof. intros [] [] x y; reflexivity. Qed.


(* [comment removed for export] *)

Lemma sext64_lit : forall {n} (b : bv n), sext 64 b = Z_to_bv 64 (bv_signed b).
Proof. reflexivity. Qed.
Lemma zext64_lit : forall {n} (b : bv n), zext 64 b = Z_to_bv 64 (bv_unsigned b).
Proof. reflexivity. Qed.
Lemma low32_lit : forall z, low32 (Z_to_bv 64 z) = Z_to_bv 32 z.
Proof.
  intro z. unfold low32. apply bv_eq.
  rewrite bv_extract_unsigned, Z.shiftr_0_r, !Z_to_bv_unsigned.
  rewrite bv_wrap32_mod, !bv_wrap64_mod, bv_wrap32_mod. rewrite <- M64_eq, <- M32_eq. apply mod64_mod32.
Qed.
Lemma sext32_low32 : forall {n} (b : bv n), sext 32 b = low32 (Z_to_bv 64 (bv_signed b)).
Proof. intros n b. rewrite low32_lit. reflexivity. Qed.
Lemma zext32_low32 : forall {n} (b : bv n), zext 32 b = low32 (Z_to_bv 64 (bv_unsigned b)).
Proof. intros n b. rewrite low32_lit. reflexivity. Qed.

Lemma wd_mk_alu : forall E vi op a b, vi_ok E vi -> wd E (mk_alu vi op a b) = alu64 op (wd E a) (wd E b).
Proof. intros. unfold wd. rewrite zalu_ok. apply mk_alu_sound. assumption. Qed.

Lemma wd_mk_aluw : forall E vi op a b, vi_ok E vi -> op32_ok op = true ->
  wd E (mk_aluw vi op a b) = sext 64 (alu32 op (low32 (wd E a)) (low32 (wd E b))).
Proof. intros. unfold wd. rewrite zaluw_ok by assumption. f_equal. apply mk_aluw_sound; assumption. Qed.

Lemma wd_zmul : forall E a b, wd E (zmul a b) = mul_div M_MUL (wd E a) (wd E b).
Proof. intros. unfold wd. rewrite zmul_ok, zmul_ev. reflexivity. Qed.

Lemma wd_lit : forall E z, wd E (ZL z) = Z_to_bv 64 z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Lemma st_ok_intro : forall E m rom regs sr p p' log,
  regs_ok E sr regs -> log_flat E log -> Z_to_bv 64 p' = p ->
  st_ok E m rom (ZS p' sr log) (mkst regs p (mem_denot E m log) rom).
Proof. intros E m rom regs sr p p' log Hr Hl <-. exists regs. repeat split; auto. Qed.

Lemma zstep_sound : forall C E m rom st ms i st' scs (scr scr' : script) w,
  ctx_ok E m C ->
  fetch_word segs (Z_to_bv 64 (z_pc st)) = Some w -> is_ecall w = false ->
  decode_any w = Some (i, 4%Z) ->
  zstep C i st scr = SOk st' scs scr' ->
  scs_ok E m scs ->
  st_ok E m rom st ms ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_ok E m rom st' ms'.
Proof.
  intros C E m rom st ms i st' scs scr scr' w (Hvi & Hkn & Hkw) Hf He Hd Hs Hsc (regs & -> & Hregs & Hlf).
  set (mem := mem_denot E m (z_log st)) in *.
  assert (ALU : forall rd (e : zx) (v : word),
    wd E e = v ->
    RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (z_pc st)) mem rom)
      = MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd v) (v_addi (Z_to_bv 64 (z_pc st)) 4) mem rom) ->
    SOk (sset st rd e (z_pc st + 4)) [] scr = SOk st' scs scr' ->
    exists ms', RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (z_pc st)) mem rom) = MachineOk ms' /\ st_ok E m rom st' ms').
  { intros rd e v Hv Hstep HS. injection HS as <- <- <-.
    eexists. split; [exact Hstep|]. unfold sset. apply st_ok_intro; [|exact Hlf|symmetry; apply v_addi_lit].
    apply regs_ok_upd; [exact Hregs | exact Hv]. }
  destruct i; cbn [zstep] in Hs; try discriminate.
  - (* [comment removed for export] *) eapply ALU; [|exact (step_lui segs regs _ mem rom w rd imm Hf He Hd)|exact Hs].
    rewrite wd_lit. unfold v_lui. rewrite u_Z2bv64. apply Z2bv_mod.
  - (* [comment removed for export] *) eapply ALU; [|exact (step_auipc segs regs _ mem rom w rd imm Hf He Hd)|exact Hs].
    rewrite wd_lit. unfold v_auipc. rewrite !u_Z2bv64. rewrite Z2bv_mod. apply Z2bv_eqm.
    rewrite M64_eq, Zplus_mod_idemp_r. reflexivity.
  - (* [comment removed for export] *) injection Hs as <- <- <-.
    eexists; split; [ exact (step_jal_link segs regs _ mem rom w rd imm Hf He Hd) |].
    unfold sset. apply st_ok_intro; [|exact Hlf|].
    + apply regs_ok_upd; [exact Hregs|]. rewrite wd_lit. symmetry. apply v_addi_lit.
    + unfold btgt. rewrite v_addi_lit, u_Z2bv64. apply Z2bv_mod.
  - (* [comment removed for export] *)
    destruct (sr_get (z_rs st) rs1) as [z| | | | | | | | | | | | | | |] eqn:Hg; try discriminate.
    injection Hs as <- <- <-.
    eexists; split; [ exact (step_jalr_gen segs regs _ mem rom w rd rs1 imm Hf He Hd) |].
    unfold sset. apply st_ok_intro; [|exact Hlf|].
    + apply regs_ok_upd; [exact Hregs|]. rewrite wd_lit. symmetry. apply v_addi_lit.
    + unfold jalr_tgt, jalr_tgtZ. rewrite (Hregs rs1), Hg. unfold wd. cbn [ev]. rewrite u_Z2bv64.
      rewrite <- M64_eq. rewrite Z2bv_mod. reflexivity.
  - (* [comment removed for export] *)
    destruct (br_operands (c_vi C) c (sr_get (z_rs st) rs1) (sr_get (z_rs st) rs2)) as [x y] eqn:Hop.
    pose proof (br_operands_sound E (c_vi C) c _ _ x y Hvi Hop) as BR.
    assert (TK : forall t : bool, branch_taken c (wd E (sr_get (z_rs st) rs1)) (wd E (sr_get (z_rs st) rs2)) = t ->
      exists ms', RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (z_pc st)) mem rom) = MachineOk ms'
        /\ st_ok E m rom (ZS (if t then bv_unsigned (Z_to_bv 64 (z_pc st + bv_signed imm)) else z_pc st + 4) (z_rs st) (z_log st)) ms').
    { intros t Ht. rewrite <- !Hregs in Ht. destruct t.
      - eexists; split; [exact (step_branch_tk_gen segs regs _ mem rom w c rs1 rs2 imm Hf He Hd Ht)|].
        apply st_ok_intro; [exact Hregs|exact Hlf|]. unfold btgt. rewrite v_addi_lit, u_Z2bv64. apply Z2bv_mod.
      - eexists; split; [exact (step_branch_ft_gen segs regs _ mem rom w c rs1 rs2 imm Hf He Hd Ht)|].
        apply st_ok_intro; [exact Hregs|exact Hlf|]. symmetry. apply v_addi_lit. }
    destruct (decide_cond (c_vi C) (br_cond c true x y)) as [t|] eqn:Hdec.
    + injection Hs as <- <- <-. apply TK. apply BR.
      pose proof (decide_cond_sound E (c_vi C) _ t Hvi Hdec) as Hc.
      destruct t; [exact Hc|]. rewrite br_cond_negate in Hc. exact Hc.
    + destruct (sc_dirs scr) as [|t dirs']; [discriminate|]. injection Hs as <- <- <-.
      apply TK. apply BR. apply scs_ok_cons in Hsc as [Hc _]. exact Hc.
  - (* [comment removed for export] *)
    destruct (load_ok sz signed) eqn:Hok; cbn [negb] in Hs; [|discriminate].
    destruct (split_addr (sr_get (z_rs st) rs1) (bv_signed imm)) as [b k] eqn:Hsa.
    pose proof (split_addr_ev E _ _ _ _ Hsa) as Hbk.
    assert (Hadr : addr E b k = v_addi (getr regs rs1) (bv_signed imm)).
    { unfold addr. rewrite Hbk, (Hregs rs1). unfold wd. symmetry. apply v_addi_lit. }
    assert (Hn : (msz sz = 1 \/ msz sz = 2 \/ msz sz = 4 \/ msz sz = 8)%nat) by (destruct sz; cbn; tauto).
    assert (Hn8 : (msz sz <= 8)%nat) by (destruct sz; cbn; lia).
    (* [comment removed for export] *)
    assert (FIN : forall (v : zx) bs scs0 scr0,
      rdn segs mem (addr E b k) (msz sz) = Some bs -> bytes_le_to_Z bs = ev E v ->
      SOk (sset st rd (load_val (c_vi C) (msz sz) signed v) (z_pc st + 4)) scs0 scr0 = SOk st' scs scr' ->
      exists ms', RiscvSemantics.step segs (mkst regs (Z_to_bv 64 (z_pc st)) mem rom) = MachineOk ms' /\ st_ok E m rom st' ms').
    { intros v bs scs0 scr0 Hrd Hbs HS. injection HS as <- <- <-.
      pose proof (rdn_val_range mem _ _ _ Hrd) as Hrange. rewrite Hbs in Hrange.
      pose proof (load_val_sound E (c_vi C) (msz sz) signed v (ev E v) Hvi eq_refl Hrange Hn) as Hval.
      rewrite Hadr in Hrd.
      assert (Hbs' : bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (ev E v))).
      { rewrite u_Z2bv64, Z.mod_small; [exact Hbs|].
        assert (2 ^ (8 * Z.of_nat (msz sz)) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia. }
      eexists. split.
      2:{ unfold sset. apply st_ok_intro; [|exact Hlf|symmetry; apply v_addi_lit]. apply regs_ok_upd; [exact Hregs|exact Hval]. }
      destruct sz; destruct signed; cbn [msz] in *.
      - destruct bs as [|b0 [|]]; try (pose proof (rdn_length segs mem _ _ _ Hrd) as HL; cbn in HL; discriminate).
        rewrite bytes_le_single in Hbs. rewrite <- Hbs, <- v_lb_swrap.
        exact (step_lb segs regs _ mem rom w rd rs1 imm b0 Hf He Hd Hrd).
      - destruct bs as [|b0 [|]]; try (pose proof (rdn_length segs mem _ _ _ Hrd) as HL; cbn in HL; discriminate).
        rewrite bytes_le_single in Hbs. rewrite <- Hbs.
        exact (step_lbu segs regs _ mem rom w rd rs1 imm b0 Hf He Hd Hrd).
      - exact (step_lh segs regs _ mem rom w rd rs1 imm bs _ Hf He Hd Hrd Hbs').
      - exact (step_lhu segs regs _ mem rom w rd rs1 imm bs _ Hf He Hd Hrd Hbs').
      - exact (step_lw regs _ mem rom w rd rs1 imm bs _ Hf He Hd Hrd Hbs').
      - exact (step_lwu segs regs _ mem rom w rd rs1 imm bs _ Hf He Hd Hrd Hbs').
      - exact (step_ld segs regs _ mem rom w rd rs1 imm bs _ Hf He Hd Hrd Hbs').
      - discriminate Hok. }
    (* [comment removed for export] *)
    assert (SPLIT : forall scs0 scr0 e0, SOk (sset st rd e0 (z_pc st + 4)) (flat_sc (c_vi C) b k (msz sz) ++ scs0) scr0 = SOk st' scs scr' ->
                    flat E b k (msz sz) /\ scs_ok E m scs0).
    { intros scs0 scr0 e0 HS. injection HS as E1 E2 E3. subst scs. apply scs_ok_app in Hsc as [H1 H2].
      split; [eapply flat_sc_sound; eauto | exact H2]. }
    destruct (log_lookup (c_vi C) (z_log st) b k (msz sz)) as [e scs1|scs1|] eqn:Hlk; [| |discriminate].
    + (* [comment removed for export] *)
      destruct (SPLIT _ _ _ Hs) as [Hfl Hsc1].
      pose proof (log_lookup_sound E m (c_vi C) (z_log st) b k (msz sz) _ Hvi Hlk Hsc1 Hlf Hfl Hn8) as HL.
      cbn in HL. destruct HL as (bs & Hrd & Hbs).
      eapply (FIN (stored_val (c_vi C) (msz sz) e) bs); [exact Hrd | | exact Hs].
      rewrite stored_val_ev by assumption. exact Hbs.
    + destruct (kn_lookup (c_kn C) b k (msz sz)) as [v|] eqn:Hkl.
      * (* [comment removed for export] *)
        destruct (SPLIT _ _ _ Hs) as [Hfl Hsc1].
        pose proof (log_lookup_sound E m (c_vi C) (z_log st) b k (msz sz) _ Hvi Hlk Hsc1 Hlf Hfl Hn8) as HL. cbn in HL.
        destruct (kn_lookup_sound E m (c_kn C) b k (msz sz) v Hkn Hkl) as (bs & Hrd & Hbs).
        eapply (FIN v bs); [ | exact Hbs | exact Hs]. unfold mem. rewrite HL. exact Hrd.
      * (* [comment removed for export] *)
        destruct (sc_reads scr) as [|v reads']; [discriminate|].
        assert (Hs' : SOk (sset st rd (load_val (c_vi C) (msz sz) signed v) (z_pc st + 4))
                          (flat_sc (c_vi C) b k (msz sz) ++ SCRead b k (msz sz) v :: scs1) (SCR (sc_dirs scr) reads') = SOk st' scs scr') by exact Hs.
        pose proof (SPLIT _ _ _ Hs') as [Hfl Hsc1]. apply scs_ok_cons in Hsc1 as [Hrd0 Hsc1].
        cbn [sc_ok] in Hrd0. destruct Hrd0 as (bs & Hrd & Hbs).
        pose proof (log_lookup_sound E m (c_vi C) (z_log st) b k (msz sz) _ Hvi Hlk Hsc1 Hlf Hfl Hn8) as HL2. cbn in HL2.
        eapply (FIN v bs); [ | exact Hbs | exact Hs']. unfold mem. rewrite HL2. exact Hrd.
  - (* [comment removed for export] *)
    destruct (split_addr (sr_get (z_rs st) rs1) (bv_signed imm)) as [b k] eqn:Hsa.
    pose proof (split_addr_ev E _ _ _ _ Hsa) as Hbk.
    assert (Hadr : addr E b k = v_addi (getr regs rs1) (bv_signed imm)).
    { unfold addr. rewrite Hbk, (Hregs rs1). unfold wd. symmetry. apply v_addi_lit. }
    injection Hs as <- <- <-. apply scs_ok_app in Hsc as [Hsc1 Hsc2].
    assert (Hfl : flat E b k (msz sz)) by (eapply flat_sc_sound; eauto).
    assert (Hok0 : RiscvSemantics.store_ok segs m (addr E b k) (msz sz) = true).
    { destruct (kw_lookup (c_kw C) b k (msz sz)) eqn:Hkwl.
      - apply (proj1 (kw_lookup_sound E m (c_kw C) b k (msz sz) Hkw Hkwl)).
      - apply scs_ok_cons in Hsc2 as [H _]. exact H. }
    assert (Hok' : RiscvSemantics.store_ok segs mem (v_addi (getr regs rs1) (bv_signed imm)) (msz sz) = true).
    { rewrite <- Hadr. eapply store_ok_mono; [apply mem_denot_grows | exact Hok0]. }
    eexists. split.
    2:{ apply (st_ok_intro E m rom regs (z_rs st) (v_addi (Z_to_bv 64 (z_pc st)) 4) (z_pc st + 4) (SE b k (msz sz) (sr_get (z_rs st) rs2) :: z_log st));
          [exact Hregs | cbn [log_flat]; split; [exact Hfl | exact Hlf] | symmetry; apply v_addi_lit]. }
    cbn [mem_denot]. fold mem. rewrite Hadr, <- (Hregs rs2).
    destruct sz; cbn [msz] in *.
    + exact (step_sb segs regs _ mem rom w rs1 rs2 imm Hf He Hd Hok').
    + exact (step_sh_val segs regs _ mem rom w rs1 rs2 imm Hf He Hd Hok').
    + exact (step_sw_val segs regs _ mem rom w rs1 rs2 imm Hf He Hd Hok').
    + exact (step_sd_val segs regs _ mem rom w rs1 rs2 imm Hf He Hd Hok').
  - (* [comment removed for export] *) eapply ALU; [|exact (step_opimm_gen segs regs _ mem rom w op rd rs1 imm Hf He Hd)|exact Hs].
    rewrite wd_normlit, wd_mk_alu by assumption. rewrite (Hregs rs1), sext64_lit. reflexivity.
  - (* [comment removed for export] *) eapply ALU; [|exact (step_shiftimm_gen segs regs _ mem rom w op rd rs1 shamt Hf He Hd)|exact Hs].
    rewrite wd_normlit, wd_mk_alu by assumption. rewrite (Hregs rs1), zext64_lit. reflexivity.
  - (* [comment removed for export] *) eapply ALU; [|exact (step_op_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd)|exact Hs].
    rewrite wd_normlit, wd_mk_alu by assumption. rewrite (Hregs rs1), (Hregs rs2). reflexivity.
  - (* [comment removed for export] *) eapply ALU; [|exact (step_opimm32_gen segs regs _ mem rom w rd rs1 imm Hf He Hd)|exact Hs].
    rewrite wd_normlit, wd_mk_aluw by (try assumption; reflexivity). rewrite (Hregs rs1), (sext32_low32 imm). reflexivity.
  - (* [comment removed for export] *) destruct (op32_ok op) eqn:Hop; [|discriminate].
    eapply ALU; [|exact (step_shiftimm32_gen segs regs _ mem rom w op rd rs1 shamt Hf He Hd)|exact Hs].
    rewrite wd_normlit, wd_mk_aluw by assumption. rewrite (Hregs rs1), (zext32_low32 shamt). reflexivity.
  - (* [comment removed for export] *) destruct (op32_ok op) eqn:Hop; [|discriminate].
    eapply ALU; [|exact (step_op32_gen segs regs _ mem rom w op rd rs1 rs2 Hf He Hd)|exact Hs].
    rewrite wd_normlit, wd_mk_aluw by assumption. rewrite (Hregs rs1), (Hregs rs2). reflexivity.
  - (* [comment removed for export] *) injection Hs as <- <- <-.
    eexists; split; [exact (step_fence regs _ mem rom w fm pred succ rd rs1 Hf He Hd)|].
    apply st_ok_intro; [exact Hregs|exact Hlf|symmetry; apply v_addi_lit].
  - (* [comment removed for export] *) injection Hs as <- <- <-.
    eexists; split; [exact (step_fencei regs _ mem rom w rd rs1 imm Hf He Hd)|].
    apply st_ok_intro; [exact Hregs|exact Hlf|symmetry; apply v_addi_lit].
  - (* [comment removed for export] *) destruct op; try discriminate.
    eapply ALU; [|exact (step_mul_gen segs regs _ mem rom w M_MUL rd rs1 rs2 Hf He Hd)|exact Hs].
    rewrite wd_normlit, wd_zmul. rewrite (Hregs rs1), (Hregs rs2). reflexivity.
Qed.


(* [comment removed for export] *)

Lemma zrun_acc : forall C fuel first stops scr st acc,
  exists pre, snd (zrun C fuel first stops scr st acc) = pre ++ acc.
Proof.
  intros C fuel. induction fuel as [|f IH]; intros first stops scr st acc; [exists []; reflexivity|].
  cbn [zrun].
  destruct (negb first && existsb (Z.eqb (z_pc st)) stops); [exists []; reflexivity|].
  destruct (fetch_word segs (Z_to_bv 64 (z_pc st))) as [w|]; [|exists []; reflexivity].
  destruct (is_ecall w); [exists []; reflexivity|].
  destruct (decode_any w) as [[i sz]|]; [|exists []; reflexivity].
  destruct (Z.eqb sz 4); cbn [negb]; [|exists []; reflexivity].
  destruct (zstep C i st scr) as [st' scs scr'|]; [|exists []; reflexivity].
  destruct (IH false stops scr' st' (scs ++ acc)) as [pre Hpre].
  exists (pre ++ scs). rewrite <- app_assoc. exact Hpre.
Qed.

Theorem zrun_sound : forall C fuel first stops scr st acc st' scs E m rom ms,
  zrun C fuel first stops scr st acc = (st', scs) ->
  ctx_ok E m C ->
  scs_ok E m scs ->
  st_ok E m rom st ms ->
  exists ms', msteps segs ms ms' /\ st_ok E m rom st' ms'.
Proof.
  intros C fuel. induction fuel as [|f IH]; intros first stops scr st acc st' scs E m rom ms Hex HC Hsc Hst.
  { cbn in Hex. injection Hex as <- <-. exists ms. split; [apply mst_refl|exact Hst]. }
  assert (Hstop : (st, acc) = (st', scs) -> exists ms', msteps segs ms ms' /\ st_ok E m rom st' ms').
  { intro HX. injection HX as <- <-. exists ms. split; [apply mst_refl|exact Hst]. }
  cbn [zrun] in Hex.
  destruct (negb first && existsb (Z.eqb (z_pc st)) stops); [exact (Hstop Hex)|].
  destruct (fetch_word segs (Z_to_bv 64 (z_pc st))) as [w|] eqn:Hf; [|exact (Hstop Hex)].
  destruct (is_ecall w) eqn:He; [exact (Hstop Hex)|].
  destruct (decode_any w) as [[i sz]|] eqn:Hd; [|exact (Hstop Hex)].
  destruct (Z.eqb sz 4) eqn:Hsz; cbn [negb] in Hex; [|exact (Hstop Hex)].
  apply Z.eqb_eq in Hsz. subst sz.
  destruct (zstep C i st scr) as [st2 scs2 scr2|] eqn:Hstep; [|exact (Hstop Hex)].
  destruct (zrun_acc C f false stops scr2 st2 (scs2 ++ acc)) as [pre Hpre].
  rewrite Hex in Hpre. cbn [snd] in Hpre. subst scs.
  assert (Hsc2 : scs_ok E m scs2).
  { apply scs_ok_app in Hsc as [_ Hsc]. apply scs_ok_app in Hsc as [Hsc _]. exact Hsc. }
  destruct (zstep_sound C E m rom st ms i st2 scs2 scr scr2 w HC Hf He Hd Hstep Hsc2 Hst) as (msA & HstepA & HstA).
  destruct (IH false stops scr2 st2 (scs2 ++ acc) st' _ E m rom msA Hex HC Hsc HstA) as (msB & HmsB & HstB).
  exists msB. split; [|exact HstB].
  eapply mst_step; [destruct Hst as (rr & -> & _); reflexivity | exact HstepA | exact HmsB].
Qed.

(* [comment removed for export] *)
Theorem zrun_block : forall C fuel stops scr sr p st' scs E m rom regs,
  zrun C fuel true stops scr (ZS p sr []) [] = (st', scs) ->
  ctx_ok E m C ->
  regs_ok E sr regs ->
  scs_ok E m scs ->
  exists regs', regs_ok E (z_rs st') regs' /\ log_flat E (z_log st') /\
    msteps segs (mkst regs (Z_to_bv 64 p) m rom)
                (mkst regs' (Z_to_bv 64 (z_pc st')) (mem_denot E m (z_log st')) rom).
Proof.
  intros C fuel stops scr sr p st' scs E m rom regs Hex HC Hregs Hsc.
  assert (Hst : st_ok E m rom (ZS p sr []) (mkst regs (Z_to_bv 64 p) m rom)).
  { exists regs. repeat split; auto. }
  destruct (zrun_sound C fuel true stops scr _ [] st' scs E m rom _ Hex HC Hsc Hst) as (ms' & Hms & (regs' & -> & Hr' & Hlf')).
  exists regs'. repeat split; auto.
Qed.

End WithFP.
End WithSegs.
End ZXA.
