(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigModel BigFactsBase BigFactsDigits.
Import ListNotations.
Import AX2.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Open Scope Z_scope.

Module BL.

Definition MM : Z := 2 ^ 64.
Lemma MM_WM : MM = W.M. Proof. rewrite M_val. reflexivity. Qed.
Lemma MM_val : MM = 18446744073709551616. Proof. reflexivity. Qed.

Definition zalu (op : aluop) (a b : Z) : option Z :=
  match op with
  | ALU_ADD => Some ((a + b) mod MM)
  | ALU_SUB => Some ((a - b) mod MM)
  | ALU_SLL => Some ((a * 2 ^ (b mod 64)) mod MM)
  | ALU_SRL => Some (a / 2 ^ (b mod 64))
  | ALU_SLTU => Some (if a <? b then 1 else 0)
  | ALU_AND => Some (Z.land a b)
  | ALU_OR => Some (Z.lor a b)
  | ALU_XOR => Some (Z.lxor a b)
  | ALU_SLT | ALU_SRA => None
  end.

Definition zmd (op : mulop) (a b : Z) : option Z :=
  match op with
  | M_MUL => Some ((a * b) mod MM)
  | M_MULHU => Some ((a * b) / MM)
  | M_DIVU => Some (if b =? 0 then MM - 1 else a / b)
  | M_REMU => Some (if b =? 0 then a else a mod b)
  | _ => None
  end.

Fixpoint zeval (V : nat -> Z) (e : expr) : option Z :=
  match e with
  | ELit z => Some (z mod MM)
  | EVar n => Some (V n)
  | EAlu op a b => match zeval V a, zeval V b with Some x, Some y => zalu op x y | _, _ => None end
  | EMd op a b => match zeval V a, zeval V b with Some x, Some y => zmd op x y | _, _ => None end
  | _ => None
  end.

Definition uv (E : env) (n : nat) : Z := bv_unsigned (ev E n).

Definition inrange (z : Z) : Prop := 0 <= z < MM.

Lemma bvu_range (w : word) : inrange (bv_unsigned w).
Proof. unfold inrange, MM. pose proof (bv_unsigned_in_range 64 w). unfold bv_modulus in H. exact H. Qed.

Lemma zalu_sound op (a b : word) z : zalu op (bv_unsigned a) (bv_unsigned b) = Some z -> bv_unsigned (alu64 op a b) = z.
Proof.
  pose proof (bvu_range a) as Ra. pose proof (bvu_range b) as Rb. unfold inrange in *.
  unfold alu64, alu, zalu. destruct op; intros H; inversion H; subst; clear H.
  - rewrite bv_add_unsigned. reflexivity.
  - rewrite bv_sub_unsigned. reflexivity.
  - rewrite bv_shiftl_unsigned. unfold bv_wrap. rewrite bv_and_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with MM. rewrite (Z.mod_small 63) by (unfold MM; lia).
    rewrite Z.shiftl_mul_pow2. 2: apply Z.land_nonneg; lia. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity.
  - unfold bv_ltu. destruct (Z.ltb _ _); rewrite Z_to_bv_unsigned; reflexivity.
  - rewrite bv_xor_unsigned. reflexivity.
  - rewrite bv_shiftr_unsigned, bv_and_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with MM.
    rewrite (Z.mod_small 63) by (unfold MM; lia). rewrite Z.shiftr_div_pow2. 2: apply Z.land_nonneg; lia.
    change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity.
  - rewrite bv_or_unsigned. reflexivity.
  - rewrite bv_and_unsigned. reflexivity.
Qed.

Lemma zmd_sound op (a b : word) z : zmd op (bv_unsigned a) (bv_unsigned b) = Some z -> bv_unsigned (mul_div op a b) = z.
Proof.
  pose proof (bvu_range a) as Ra. pose proof (bvu_range b) as Rb. unfold inrange in *.
  unfold mul_div, zmd. destruct op; intros H; inversion H; subst; clear H.
  - rewrite bv_mul_unsigned. reflexivity.
  - unfold bv_mulhuu. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with MM.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ Z.of_N 64) with MM. apply Z.mod_small. split.
    apply Z.div_pos; unfold MM; lia. apply Z.div_lt_upper_bound. unfold MM; lia. unfold MM in *; nia.
  - destruct (Z.eqb_spec (bv_unsigned b) 0). rewrite Z_to_bv_unsigned. reflexivity. rewrite bv_divu_unsigned. reflexivity.
  - destruct (Z.eqb_spec (bv_unsigned b) 0). reflexivity. rewrite bv_modu_unsigned. reflexivity.
Qed.

Theorem zeval_sound E e : forall z, zeval (uv E) e = Some z -> bv_unsigned (edenot E e) = z.
Proof.
  induction e; intros zz H; cbn [zeval edenot] in H; try discriminate.
  - inversion H. cbn [edenot]. rewrite Z_to_bv_unsigned. reflexivity.
  - inversion H. cbn [edenot]. reflexivity.
  - destruct (zeval (uv E) e1) as [x|] eqn:E1; try discriminate. destruct (zeval (uv E) e2) as [y|] eqn:E2; try discriminate.
    cbn [edenot]. rewrite <- (IHe1 x eq_refl), <- (IHe2 y eq_refl) in H. apply zalu_sound; auto.
  - destruct (zeval (uv E) e1) as [x|] eqn:E1; try discriminate. destruct (zeval (uv E) e2) as [y|] eqn:E2; try discriminate.
    cbn [edenot]. rewrite <- (IHe1 x eq_refl), <- (IHe2 y eq_refl) in H. apply zmd_sound; auto.
Qed.

Corollary zeval_word E e z : zeval (uv E) e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros H. apply bv_eq. rewrite (zeval_sound E e z H). rewrite Z_to_bv_unsigned.
  pose proof (bvu_range (edenot E e)) as R. rewrite (zeval_sound E e z H) in R. unfold inrange in R.
  unfold bv_wrap. change (bv_modulus 64) with MM. rewrite Z.mod_small; auto.
Qed.

Inductive za : Type :=
| ZV (n : nat) | ZL (z : Z)
| ZAddM (a b : za) | ZSubM (a b : za) | ZMulM (a b : za) | ZMulHU (a b : za)
| ZDivC (a : za) (c : Z)
| ZShlC (a : za) (c : Z)
| ZSrl (a b : za) | ZSll (a b : za)
| ZLtu (a b : za) | ZAnd (a b : za) | ZOr (a b : za) | ZXor (a b : za)
| ZDivU (a b : za) | ZRemU (a b : za).

Fixpoint zden (V : nat -> Z) (t : za) : Z :=
  match t with
  | ZV n => V n
  | ZL z => z
  | ZAddM a b => (zden V a + zden V b) mod MM
  | ZSubM a b => (zden V a - zden V b) mod MM
  | ZMulM a b => (zden V a * zden V b) mod MM
  | ZMulHU a b => (zden V a * zden V b) / MM
  | ZDivC a c => zden V a / c
  | ZShlC a c => (zden V a * c) mod MM
  | ZSrl a b => zden V a / 2 ^ (zden V b mod 64)
  | ZSll a b => (zden V a * 2 ^ (zden V b mod 64)) mod MM
  | ZLtu a b => (if zden V a <? zden V b then 1 else 0)
  | ZAnd a b => Z.land (zden V a) (zden V b)
  | ZOr a b => Z.lor (zden V a) (zden V b)
  | ZXor a b => Z.lxor (zden V a) (zden V b)
  | ZDivU a b => (if zden V b =? 0 then MM - 1 else zden V a / zden V b)
  | ZRemU a b => (if zden V b =? 0 then zden V a else zden V a mod zden V b)
  end.

Fixpoint zcomp (e : expr) : option za :=
  match e with
  | ELit z => Some (ZL (z mod MM))
  | EVar n => Some (ZV n)
  | EAlu op a b =>
      match zcomp a, zcomp b with
      | Some x, Some y =>
          match op with
          | ALU_ADD => Some (ZAddM x y)
          | ALU_SUB => Some (ZSubM x y)
          | ALU_SLL => Some (match y with ZL k => ZShlC x (2 ^ (k mod 64)) | _ => ZSll x y end)
          | ALU_SRL => Some (match y with ZL k => ZDivC x (2 ^ (k mod 64)) | _ => ZSrl x y end)
          | ALU_SLTU => Some (ZLtu x y)
          | ALU_AND => Some (ZAnd x y)
          | ALU_OR => Some (ZOr x y)
          | ALU_XOR => Some (ZXor x y)
          | _ => None
          end
      | _, _ => None
      end
  | EMd op a b =>
      match zcomp a, zcomp b with
      | Some x, Some y =>
          match op with
          | M_MUL => Some (ZMulM x y)
          | M_MULHU => Some (ZMulHU x y)
          | M_DIVU => Some (ZDivU x y)
          | M_REMU => Some (ZRemU x y)
          | _ => None
          end
      | _, _ => None
      end
  | _ => None
  end.

Definition zc (e : expr) : za := match zcomp e with Some t => t | None => ZL 0 end.

Lemma zcomp_zeval V e : forall t, zcomp e = Some t -> zeval V e = Some (zden V t).
Proof.
  induction e; intros t H; cbn [zcomp] in H; try discriminate.
  - inversion H. reflexivity.
  - inversion H. reflexivity.
  - destruct (zcomp e1) as [x|] eqn:E1; try discriminate. destruct (zcomp e2) as [y|] eqn:E2; try discriminate.
    cbn [zeval]. rewrite (IHe1 x eq_refl), (IHe2 y eq_refl).
    destruct op; inversion H; subst; cbn [zalu zden]; try reflexivity.
    + destruct y; reflexivity.
    + destruct y; reflexivity.
  - destruct (zcomp e1) as [x|] eqn:E1; try discriminate. destruct (zcomp e2) as [y|] eqn:E2; try discriminate.
    cbn [zeval]. rewrite (IHe1 x eq_refl), (IHe2 y eq_refl).
    destruct op; inversion H; subst; cbn [zmd zden]; reflexivity.
Qed.

Theorem zcomp_sound E e t : zcomp e = Some t -> bv_unsigned (edenot E e) = zden (uv E) t.
Proof. intros H. apply zeval_sound. apply zcomp_zeval; auto. Qed.

Lemma zden_agree b V V' e t : (forall n, (n < b)%nat -> V n = V' n) -> evars_lt b e = true -> zcomp e = Some t ->
  zden V t = zden V' t.
Proof.
  intros HV Hv Ht. pose proof (zcomp_zeval V e t Ht) as A. pose proof (zcomp_zeval V' e t Ht) as B.
  assert (zeval V e = zeval V' e).
  { clear A B t Ht. induction e; cbn [evars_lt zeval] in *; auto;
      repeat match goal with | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
      try (rewrite IHe1, IHe2 by assumption; reflexivity).
    apply Nat.ltb_lt in Hv. rewrite HV; auto. }
  rewrite H in A. rewrite A in B. inversion B. reflexivity.
Qed.

Lemma zeval_agree b V V' e : (forall n, (n < b)%nat -> V n = V' n) -> evars_lt b e = true -> zeval V e = zeval V' e.
Proof.
  intros HV. induction e; cbn [evars_lt zeval]; intros H; auto;
    repeat match goal with | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end;
    try (rewrite IHe1, IHe2 by assumption; reflexivity).
  apply Nat.ltb_lt in H. rewrite HV; auto.
Qed.

Definition zb (b : bool) : Z := if b then 1 else 0.

Lemma carry_ltu_l a b : inrange a -> inrange b -> zb ((a + b) mod MM <? a) = (a + b) / MM.
Proof.
  unfold inrange, zb, MM. intros Ha Hb.
  destruct (Z_lt_le_dec (a + b) (2^64)).
  - rewrite Z.mod_small, Z.div_small by lia. destruct (Z.ltb_spec (a + b) a); lia.
  - replace ((a + b) mod 2^64) with (a + b - 2^64). 2:{ apply Z.mod_unique with 1; lia. }
    replace ((a + b) / 2^64) with 1. 2:{ apply Z.div_unique with (a + b - 2^64); lia. }
    destruct (Z.ltb_spec (a + b - 2^64) a); lia.
Qed.

Lemma carry_ltu_r a b : inrange a -> inrange b -> zb ((a + b) mod MM <? b) = (a + b) / MM.
Proof. intros. rewrite Z.add_comm. apply carry_ltu_l; auto. Qed.

Lemma mod_inrange a : inrange (a mod MM).
Proof. unfold inrange. apply Z.mod_pos_bound. reflexivity. Qed.

Lemma esub_val a b : 0 < a <= b -> b < MM -> (((MM - 1) * a) mod MM + b) mod MM = b - a.
Proof.
  intros Ha Hb. unfold MM in *.
  replace ((2 ^ 64 - 1) * a) with ((2^64 - a) + (a - 1) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. rewrite (Z.mod_small (2^64 - a)) by lia.
  replace (2 ^ 64 - a + b) with ((b - a) + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma esub_val' a b : 0 < a <= b -> b < MM -> (b + ((MM - 1) * a) mod MM) mod MM = b - a.
Proof. intros. rewrite Z.add_comm. apply esub_val; auto. Qed.

Lemma W_add_eq a b : W.add a b = (a + b) mod MM. Proof. unfold W.add, W.wrap. rewrite MM_WM. reflexivity. Qed.
Lemma W_mul_eq a b : W.mul a b = (a * b) mod MM. Proof. unfold W.mul, W.wrap. rewrite MM_WM. reflexivity. Qed.
Lemma W_b2z_ltu a b : W.b2z (W.ltu a b) = zb (a <? b). Proof. reflexivity. Qed.
Lemma wordZ_inrange a : wordZ a <-> inrange a. Proof. unfold wordZ, inrange. rewrite MM_WM. tauto. Qed.

Lemma DDproduct_closed A B : inrange A -> inrange B ->
  fst (DDproduct A B) = (A * B) / MM /\ snd (DDproduct A B) = (A * B) mod MM.
Proof.
  intros HA HB. apply wordZ_inrange in HA. apply wordZ_inrange in HB.
  pose proof (DDproduct_correct A B HA HB) as H. destruct (DDproduct A B) as [hi lo]. cbn [fst snd] in *.
  destruct H as (Wh & Wl & E). unfold wordZ, inrange in *. rewrite MM_val. rewrite M_val in *. split.
  - apply Z.div_unique with lo; lia.
  - apply Z.mod_unique with hi; lia.
Qed.

End BL.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.
