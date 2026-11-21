(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Inductive expr : Type :=
| ELit  (z : Z)
| EVar  (n : nat)
| EAdd  (a b : expr)
| ESub  (a b : expr)
| EMul  (a b : expr)
| EAnd  (a b : expr)
| EOr   (a b : expr)
| EXor  (a b : expr)
| EShl  (a : expr) (k : Z)
| EShr  (a : expr) (k : Z)
| EZx   (k : Z) (a : expr)
| ESx   (k : Z) (a : expr)
| ELtb  (a b : expr)
| EApp1 (f : nat) (a : expr)
| EApp2 (f : nat) (a b : expr)
| EOpq  (op : aluop) (a b : expr)
| EOpqw (op : aluop) (a b : expr)
| EMdq  (op : mulop) (a b : expr)
| EMdqw (op : mulop) (a b : expr).

Record venv : Type := VEnv {
  vv  : nat -> Z;
  vf1 : nat -> Z -> Z;
  vf2 : nat -> Z -> Z -> Z
}.

Definition szwrap (k a : Z) : Z := (a + 2 ^ (k - 1)) mod 2 ^ k - 2 ^ (k - 1).

Definition zw (a : Z) : word := Z_to_bv 64 a.

Definition zalu (op : aluop) (a b : Z) : Z := bv_unsigned (alu64 op (zw a) (zw b)).
Definition zaluw (op : aluop) (a b : Z) : Z :=
  bv_unsigned (sext 64 (alu32 op (low32 (zw a)) (low32 (zw b)))).
Definition zmd (op : mulop) (a b : Z) : Z := bv_unsigned (mul_div op (zw a) (zw b)).
Definition zmdw (op : mulop) (a b : Z) : Z :=
  bv_unsigned (sext 64 (mul_div op (low32 (zw a)) (low32 (zw b)))).

Fixpoint ed (E : venv) (e : expr) : Z :=
  match e with
  | ELit z => z
  | EVar n => vv E n
  | EAdd a b => ed E a + ed E b
  | ESub a b => ed E a - ed E b
  | EMul a b => ed E a * ed E b
  | EAnd a b => Z.land (ed E a) (ed E b)
  | EOr a b => Z.lor (ed E a) (ed E b)
  | EXor a b => Z.lxor (ed E a) (ed E b)
  | EShl a k => ed E a * 2 ^ k
  | EShr a k => ed E a / 2 ^ k
  | EZx k a => (ed E a) mod 2 ^ k
  | ESx k a => szwrap k (ed E a)
  | ELtb a b => if ed E a <? ed E b then 1 else 0
  | EApp1 f a => vf1 E f (ed E a)
  | EApp2 f a b => vf2 E f (ed E a) (ed E b)
  | EOpq op a b => zalu op (ed E a) (ed E b)
  | EOpqw op a b => zaluw op (ed E a) (ed E b)
  | EMdq op a b => zmd op (ed E a) (ed E b)
  | EMdqw op a b => zmdw op (ed E a) (ed E b)
  end.

Definition aluop_eqb (a b : aluop) : bool :=
  match a, b with
  | ALU_ADD, ALU_ADD | ALU_SUB, ALU_SUB | ALU_SLL, ALU_SLL | ALU_SLT, ALU_SLT
  | ALU_SLTU, ALU_SLTU | ALU_XOR, ALU_XOR | ALU_SRL, ALU_SRL | ALU_SRA, ALU_SRA
  | ALU_OR, ALU_OR | ALU_AND, ALU_AND => true
  | _, _ => false
  end.

Definition mulop_eqb (a b : mulop) : bool :=
  match a, b with
  | M_MUL, M_MUL | M_MULH, M_MULH | M_MULHSU, M_MULHSU | M_MULHU, M_MULHU
  | M_DIV, M_DIV | M_DIVU, M_DIVU | M_REM, M_REM | M_REMU, M_REMU => true
  | _, _ => false
  end.

Fixpoint expr_eqb (x y : expr) {struct x} : bool :=
  match x, y with
  | ELit a, ELit b => Z.eqb a b
  | EVar a, EVar b => Nat.eqb a b
  | EAdd a1 a2, EAdd b1 b2 => expr_eqb a1 b1 && expr_eqb a2 b2
  | ESub a1 a2, ESub b1 b2 => expr_eqb a1 b1 && expr_eqb a2 b2
  | EMul a1 a2, EMul b1 b2 => expr_eqb a1 b1 && expr_eqb a2 b2
  | EAnd a1 a2, EAnd b1 b2 => expr_eqb a1 b1 && expr_eqb a2 b2
  | EOr a1 a2, EOr b1 b2 => expr_eqb a1 b1 && expr_eqb a2 b2
  | EXor a1 a2, EXor b1 b2 => expr_eqb a1 b1 && expr_eqb a2 b2
  | EShl a k, EShl b j => expr_eqb a b && Z.eqb k j
  | EShr a k, EShr b j => expr_eqb a b && Z.eqb k j
  | EZx k a, EZx j b => Z.eqb k j && expr_eqb a b
  | ESx k a, ESx j b => Z.eqb k j && expr_eqb a b
  | ELtb a1 a2, ELtb b1 b2 => expr_eqb a1 b1 && expr_eqb a2 b2
  | EApp1 f a, EApp1 g b => Nat.eqb f g && expr_eqb a b
  | EApp2 f a1 a2, EApp2 g b1 b2 => Nat.eqb f g && expr_eqb a1 b1 && expr_eqb a2 b2
  | EOpq o a1 a2, EOpq p b1 b2 => aluop_eqb o p && expr_eqb a1 b1 && expr_eqb a2 b2
  | EOpqw o a1 a2, EOpqw p b1 b2 => aluop_eqb o p && expr_eqb a1 b1 && expr_eqb a2 b2
  | EMdq o a1 a2, EMdq p b1 b2 => mulop_eqb o p && expr_eqb a1 b1 && expr_eqb a2 b2
  | EMdqw o a1 a2, EMdqw p b1 b2 => mulop_eqb o p && expr_eqb a1 b1 && expr_eqb a2 b2
  | _, _ => false
  end.

Lemma aluop_eqb_eq : forall a b, aluop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; congruence. Qed.

Lemma mulop_eqb_eq : forall a b, mulop_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros; congruence. Qed.

Lemma expr_eqb_eq : forall x y, expr_eqb x y = true -> x = y.
Proof.
  induction x; intros y H; destruct y; cbn [expr_eqb] in H; try discriminate;
    repeat match goal with
    | H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?]
    | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
    | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
    | H : aluop_eqb _ _ = true |- _ => apply aluop_eqb_eq in H
    | H : mulop_eqb _ _ = true |- _ => apply mulop_eqb_eq in H
    end; subst; f_equal; auto.
Qed.

Lemma ed_eqb : forall E x y, expr_eqb x y = true -> ed E x = ed E y.
Proof. intros E x y H. apply expr_eqb_eq in H. subst. reflexivity. Qed.


Definition bounds : Type := list (nat * Z).

Fixpoint blookup (l : bounds) (n : nat) : option Z :=
  match l with
  | [] => None
  | (m, b) :: rest => if Nat.eqb m n then Some b else blookup rest n
  end.

Definition vars_ok (E : venv) (vb : bounds) : Prop :=
  forall n b, blookup vb n = Some b -> 0 <= vv E n < b.

Definition funs_ok (E : venv) (fb : bounds) : Prop :=
  forall f b x, blookup fb f = Some b -> 0 <= vf1 E f x < b.

Definition pow2_above (b : Z) : Z := 2 ^ (Z.log2_up b).

Lemma pow2_above_ge : forall b, 1 <= b -> b <= pow2_above b.
Proof.
  intros b Hb. unfold pow2_above.
  destruct (Z.eq_dec b 1) as [->|Hne]; [cbn; lia|].
  apply Z.log2_up_spec. lia.
Qed.

Definition omin (x y : option Z) : option Z :=
  match x, y with
  | Some a, Some b => Some (Z.min a b)
  | Some a, None => Some a
  | None, Some b => Some b
  | None, None => None
  end.

Fixpoint ebound (vb fb : bounds) (e : expr) : option Z :=
  match e with
  | ELit z => if 0 <=? z then Some (z + 1) else None
  | EVar n => blookup vb n
  | EAdd a b => match ebound vb fb a, ebound vb fb b with
                | Some x, Some y => Some (x + y - 1) | _, _ => None end
  | ESub _ _ => None
  | EMul a b => match ebound vb fb a, ebound vb fb b with
                | Some x, Some y => Some ((x - 1) * (y - 1) + 1) | _, _ => None end
  | EAnd a b => omin (ebound vb fb a) (ebound vb fb b)
  | EOr a b | EXor a b =>
      match ebound vb fb a, ebound vb fb b with
      | Some x, Some y => Some (pow2_above (Z.max x y)) | _, _ => None end
  | EShl a k => if 0 <=? k then
                  match ebound vb fb a with
                  | Some x => Some ((x - 1) * 2 ^ k + 1) | None => None end
                else None
  | EShr a k => if 0 <=? k then
                  match ebound vb fb a with
                  | Some x => Some ((x - 1) / 2 ^ k + 1) | None => None end
                else None
  | EZx k a => if 0 <=? k then
                 match ebound vb fb a with
                 | Some x => Some (Z.min x (2 ^ k)) | None => Some (2 ^ k) end
               else None
  | ESx _ _ => None
  | ELtb _ _ => Some 2
  | EApp1 f _ => blookup fb f
  | EApp2 _ _ _ => None
  | EOpq _ _ _ | EOpqw _ _ _ | EMdq _ _ _ | EMdqw _ _ _ => Some (2 ^ 64)
  end.

Lemma land_upper : forall a b, 0 <= a -> 0 <= Z.land a b <= a.
Proof.
  intros a b Ha.
  assert (H0 : 0 <= Z.land a b) by (apply Z.land_nonneg; left; exact Ha).
  split; [exact H0|].
  assert (E : a = Z.lor (Z.land a b) (Z.ldiff a b)).
  { apply Z.bits_inj'. intros i Hi.
    rewrite Z.lor_spec, Z.land_spec, Z.ldiff_spec.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  assert (Hd : 0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; left; exact Ha).
  assert (Hdis : Z.land (Z.land a b) (Z.ldiff a b) = 0).
  { apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.land_spec, Z.ldiff_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ Hdis) as Hx.
  rewrite Z.lxor_lor in Hx by exact Hdis.
  lia.
Qed.

Lemma lor_lxor_bound : forall a b n, 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= n ->
  0 <= Z.lor a b < 2 ^ n /\ 0 <= Z.lxor a b < 2 ^ n.
Proof.
  intros a b n Ha Hb Hn.
  assert (Hta : forall k, n <= k -> Z.testbit a k = false).
  { intros k Hk. destruct (Z.eq_dec a 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    apply Z.lt_le_trans with n; [|lia]. apply Z.log2_lt_pow2; lia. }
  assert (Htb : forall k, n <= k -> Z.testbit b k = false).
  { intros k Hk. destruct (Z.eq_dec b 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    apply Z.lt_le_trans with n; [|lia]. apply Z.log2_lt_pow2; lia. }
  assert (Hor0 : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  assert (Hxor0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; split; try assumption.
  - destruct (Z.eq_dec (Z.lor a b) 0) as [->|Hnz]; [lia|].
    destruct (Z_lt_le_dec (Z.lor a b) (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
    assert (Ht : Z.testbit (Z.lor a b) (Z.log2 (Z.lor a b)) = true)
      by (apply Z.bit_log2; lia).
    assert (Hl : n <= Z.log2 (Z.lor a b)).
    { apply Z.log2_le_pow2 in Hge; lia. }
    rewrite Z.lor_spec, Hta, Htb in Ht by lia. discriminate.
  - destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
    destruct (Z_lt_le_dec (Z.lxor a b) (2 ^ n)) as [|Hge]; [assumption|]. exfalso.
    assert (Ht : Z.testbit (Z.lxor a b) (Z.log2 (Z.lxor a b)) = true)
      by (apply Z.bit_log2; lia).
    assert (Hl : n <= Z.log2 (Z.lxor a b)).
    { apply Z.log2_le_pow2 in Hge; lia. }
    rewrite Z.lxor_spec, Hta, Htb in Ht by lia. discriminate.
Qed.

Lemma ebound_sound : forall E vb fb e b,
  vars_ok E vb -> funs_ok E fb ->
  ebound vb fb e = Some b -> 0 <= ed E e < b.
Proof.
  intros E vb fb e. induction e; intros bb Hv Hf Hb; cbn [ebound ed] in Hb |- *.
  - destruct (Z.leb_spec 0 z); [|discriminate]. injection Hb as <-. lia.
  - exact (Hv _ _ Hb).
  - destruct (ebound vb fb e1) as [x|] eqn:E1; [|discriminate].
    destruct (ebound vb fb e2) as [y|] eqn:E2; [|discriminate].
    injection Hb as <-.
    specialize (IHe1 x Hv Hf eq_refl). specialize (IHe2 y Hv Hf eq_refl). lia.
  - discriminate.
  - destruct (ebound vb fb e1) as [x|] eqn:E1; [|discriminate].
    destruct (ebound vb fb e2) as [y|] eqn:E2; [|discriminate].
    injection Hb as <-.
    specialize (IHe1 x Hv Hf eq_refl). specialize (IHe2 y Hv Hf eq_refl).
    split; [apply Z.mul_nonneg_nonneg; lia|].
    assert (ed E e1 * ed E e2 <= (x - 1) * (y - 1)) by (apply Z.mul_le_mono_nonneg; lia).
    lia.
  - destruct (ebound vb fb e1) as [x|] eqn:E1; destruct (ebound vb fb e2) as [y|] eqn:E2;
      cbn [omin] in Hb; try discriminate; injection Hb as <-.
    + specialize (IHe1 x Hv Hf eq_refl). specialize (IHe2 y Hv Hf eq_refl).
      pose proof (land_upper (ed E e1) (ed E e2) ltac:(lia)).
      pose proof (land_upper (ed E e2) (ed E e1) ltac:(lia)).
      rewrite Z.land_comm in H0. lia.
    + specialize (IHe1 x Hv Hf eq_refl).
      pose proof (land_upper (ed E e1) (ed E e2) ltac:(lia)). lia.
    + specialize (IHe2 y Hv Hf eq_refl).
      pose proof (land_upper (ed E e2) (ed E e1) ltac:(lia)).
      rewrite Z.land_comm in H. lia.
  - destruct (ebound vb fb e1) as [x|] eqn:E1; [|discriminate].
    destruct (ebound vb fb e2) as [y|] eqn:E2; [|discriminate].
    injection Hb as <-.
    specialize (IHe1 x Hv Hf eq_refl). specialize (IHe2 y Hv Hf eq_refl).
    pose proof (pow2_above_ge (Z.max x y) ltac:(lia)) as Hp.
    assert (Hn : 0 <= Z.log2_up (Z.max x y)) by apply Z.log2_up_nonneg.
    destruct (lor_lxor_bound (ed E e1) (ed E e2) (Z.log2_up (Z.max x y))) as [H1 H2];
      unfold pow2_above in *; try lia.
  - destruct (ebound vb fb e1) as [x|] eqn:E1; [|discriminate].
    destruct (ebound vb fb e2) as [y|] eqn:E2; [|discriminate].
    injection Hb as <-.
    specialize (IHe1 x Hv Hf eq_refl). specialize (IHe2 y Hv Hf eq_refl).
    pose proof (pow2_above_ge (Z.max x y) ltac:(lia)) as Hp.
    assert (Hn : 0 <= Z.log2_up (Z.max x y)) by apply Z.log2_up_nonneg.
    destruct (lor_lxor_bound (ed E e1) (ed E e2) (Z.log2_up (Z.max x y))) as [H1 H2];
      unfold pow2_above in *; try lia.
  - destruct (Z.leb_spec 0 k); [|discriminate].
    destruct (ebound vb fb e) as [x|] eqn:E1; [|discriminate].
    injection Hb as <-. specialize (IHe x Hv Hf eq_refl).
    assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    split; [apply Z.mul_nonneg_nonneg; lia|].
    assert (ed E e * 2 ^ k <= (x - 1) * 2 ^ k) by (apply Z.mul_le_mono_nonneg_r; lia).
    lia.
  - destruct (Z.leb_spec 0 k); [|discriminate].
    destruct (ebound vb fb e) as [x|] eqn:E1; [|discriminate].
    injection Hb as <-. specialize (IHe x Hv Hf eq_refl).
    assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    split; [apply Z.div_pos; lia|].
    assert (ed E e / 2 ^ k <= (x - 1) / 2 ^ k) by (apply Z.div_le_mono; lia).
    lia.
  - destruct (Z.leb_spec 0 k); [|discriminate].
    assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    pose proof (Z.mod_pos_bound (ed E e) (2 ^ k) ltac:(lia)).
    destruct (ebound vb fb e) as [x|] eqn:E1; injection Hb as <-; [|lia].
    specialize (IHe x Hv Hf eq_refl).
    destruct (Z_lt_le_dec (ed E e) (2 ^ k)).
    + rewrite Z.mod_small by lia. lia.
    + lia.
  - discriminate.
  - injection Hb as <-. destruct (ed E e1 <? ed E e2); lia.
  - exact (Hf _ _ _ Hb).
  - discriminate.
  - injection Hb as <-. unfold zalu. apply u64_range.
  - injection Hb as <-. unfold zaluw. apply u64_range.
  - injection Hb as <-. unfold zmd. apply u64_range.
  - injection Hb as <-. unfold zmdw. apply u64_range.
Qed.

Definition ebelow (vb fb : bounds) (e : expr) (B : Z) : bool :=
  match ebound vb fb e with Some x => x <=? B | None => false end.

Lemma ebelow_sound : forall E vb fb e B,
  vars_ok E vb -> funs_ok E fb -> ebelow vb fb e B = true -> 0 <= ed E e < B.
Proof.
  intros E vb fb e B Hv Hf H. unfold ebelow in H.
  destruct (ebound vb fb e) as [x|] eqn:Eb; [|discriminate].
  apply Z.leb_le in H. pose proof (ebound_sound E vb fb e x Hv Hf Eb). lia.
Qed.


Lemma two64 : bv_modulus 64 = 2 ^ 64.
Proof. reflexivity. Qed.

Lemma u_zw : forall a, bv_unsigned (zw a) = a mod 2 ^ 64.
Proof. intro a. unfold zw. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma u_zw_small : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (zw a) = a.
Proof. intros a H. rewrite u_zw. apply Z.mod_small. exact H. Qed.

Lemma zw_mod : forall a, zw (a mod 2 ^ 64) = zw a.
Proof.
  intro a. unfold zw. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite two64. apply Z.mod_mod. lia.
Qed.

Lemma zw_eq_iff : forall a b, zw a = zw b <-> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof.
  intros a b. split.
  - intro H. rewrite <- !u_zw, H. reflexivity.
  - intro H. rewrite <- (zw_mod a), <- (zw_mod b), H. reflexivity.
Qed.

Lemma zw_eqm : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> zw a = zw b.
Proof. intros a b H. apply zw_eq_iff. exact H. Qed.

Lemma zw_u : forall w : word, zw (bv_unsigned w) = w.
Proof. intro w. unfold zw. apply Z_to_bv_bv_unsigned. Qed.

Lemma szwrap_bv : forall (n : N), (0 < n)%N -> forall a,
  szwrap (Z.of_N n) a = bv_swrap n a.
Proof.
  intros n Hn a. unfold szwrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  assert (Hh : 2 ^ Z.of_N n `div` 2 = 2 ^ (Z.of_N n - 1)).
  { replace (Z.of_N n) with (Z.of_N n - 1 + 1) at 1 by lia.
    rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite Hh. reflexivity.
Qed.

Lemma szwrap64 : forall a, szwrap 64 a = bv_swrap 64 a.
Proof. intro a. exact (szwrap_bv 64 ltac:(lia) a). Qed.
Lemma szwrap32 : forall a, szwrap 32 a = bv_swrap 32 a.
Proof. intro a. exact (szwrap_bv 32 ltac:(lia) a). Qed.
Lemma szwrap16 : forall a, szwrap 16 a = bv_swrap 16 a.
Proof. intro a. exact (szwrap_bv 16 ltac:(lia) a). Qed.
Lemma szwrap8 : forall a, szwrap 8 a = bv_swrap 8 a.
Proof. intro a. exact (szwrap_bv 8 ltac:(lia) a). Qed.

Lemma s_zw : forall a, bv_signed (zw a) = szwrap 64 a.
Proof.
  intro a. unfold zw. rewrite Z_to_bv_signed, szwrap64. reflexivity.
Qed.


Lemma szwrap_small : forall k a, 0 < k -> - 2 ^ (k - 1) <= a < 2 ^ (k - 1) -> szwrap k a = a.
Proof.
  intros k a Hk Ha. unfold szwrap.
  assert (2 ^ k = 2 * 2 ^ (k - 1)).
  { replace k with (k - 1 + 1) at 1 by lia. rewrite Z.pow_add_r by lia. lia. }
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma szwrap_mod : forall k a, 0 < k -> szwrap k (a mod 2 ^ k) = szwrap k a.
Proof.
  intros k a Hk. unfold szwrap.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma szwrap_eqm : forall k a, 0 < k -> (szwrap k a) mod 2 ^ k = a mod 2 ^ k.
Proof.
  intros k a Hk. unfold szwrap.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Zminus_mod_idemp_l.
  replace (a + 2 ^ (k - 1) - 2 ^ (k - 1)) with a by lia. reflexivity.
Qed.


Lemma mod_mod_le : forall a j k, 0 <= j <= k -> (a mod 2 ^ k) mod 2 ^ j = a mod 2 ^ j.
Proof.
  intros a j k Hjk. apply Z.mod_mod_divide.
  exists (2 ^ (k - j)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.


Lemma testbit_mod_pow2 : forall a n i, 0 <= n -> 0 <= i ->
  Z.testbit (a mod 2 ^ n) i = if i <? n then Z.testbit a i else false.
Proof.
  intros a n i Hn Hi. destruct (Z.ltb_spec i n).
  - apply Z.mod_pow2_bits_low. lia.
  - apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma land_mod : forall a b n, 0 <= n ->
  (Z.land a b) mod 2 ^ n = Z.land (a mod 2 ^ n) (b mod 2 ^ n).
Proof.
  intros a b n Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !testbit_mod_pow2, Z.land_spec by lia.
  destruct (i <? n); reflexivity.
Qed.

Lemma lor_mod : forall a b n, 0 <= n ->
  (Z.lor a b) mod 2 ^ n = Z.lor (a mod 2 ^ n) (b mod 2 ^ n).
Proof.
  intros a b n Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lor_spec, !testbit_mod_pow2, Z.lor_spec by lia.
  destruct (i <? n); reflexivity.
Qed.

Lemma lxor_mod : forall a b n, 0 <= n ->
  (Z.lxor a b) mod 2 ^ n = Z.lxor (a mod 2 ^ n) (b mod 2 ^ n).
Proof.
  intros a b n Hn. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec, !testbit_mod_pow2, Z.lxor_spec by lia.
  destruct (i <? n); reflexivity.
Qed.


Lemma zw_add : forall a b, alu64 ALU_ADD (zw a) (zw b) = zw (a + b).
Proof.
  intros a b. rewrite alu_add. unfold v_add. rewrite !u_zw. apply zw_eqm.
  rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma zw_sub : forall a b, alu64 ALU_SUB (zw a) (zw b) = zw (a - b).
Proof.
  intros a b. rewrite alu_sub. unfold v_sub. rewrite !u_zw. apply zw_eqm.
  rewrite <- Zminus_mod. reflexivity.
Qed.

Lemma zw_and : forall a b, alu64 ALU_AND (zw a) (zw b) = zw (Z.land a b).
Proof.
  intros a b. rewrite alu_and. unfold v_and. rewrite !u_zw. apply zw_eqm.
  rewrite <- land_mod by lia. apply Z.mod_mod. lia.
Qed.

Lemma zw_or : forall a b, alu64 ALU_OR (zw a) (zw b) = zw (Z.lor a b).
Proof.
  intros a b. rewrite alu_or. unfold v_or. rewrite !u_zw. apply zw_eqm.
  rewrite <- lor_mod by lia. apply Z.mod_mod. lia.
Qed.

Lemma zw_xor : forall a b, alu64 ALU_XOR (zw a) (zw b) = zw (Z.lxor a b).
Proof.
  intros a b. rewrite alu_xor. unfold v_xor. rewrite !u_zw. apply zw_eqm.
  rewrite <- lxor_mod by lia. apply Z.mod_mod. lia.
Qed.

Lemma mod64_mod64_64 : forall b, (b mod 2 ^ 64) mod 64 = b mod 64.
Proof.
  intro b. apply (Z.mod_mod_divide b (2 ^ 64) 64). exists (2 ^ 58). reflexivity.
Qed.

Lemma zw_sll : forall a b, alu64 ALU_SLL (zw a) (zw b) = zw (a * 2 ^ (b mod 64)).
Proof.
  intros a b. rewrite alu_sll. unfold v_sll. rewrite !u_zw, mod64_mod64_64.
  pose proof (Z.mod_pos_bound b 64 ltac:(lia)).
  rewrite Z.shiftl_mul_pow2 by lia. apply zw_eqm.
  apply Z.mul_mod_idemp_l. lia.
Qed.

Lemma zw_srl : forall a b, alu64 ALU_SRL (zw a) (zw b) = zw ((a mod 2 ^ 64) / 2 ^ (b mod 64)).
Proof.
  intros a b. rewrite alu_srl. unfold v_srl. rewrite !u_zw, mod64_mod64_64.
  pose proof (Z.mod_pos_bound b 64 ltac:(lia)).
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma zw_sra : forall a b, alu64 ALU_SRA (zw a) (zw b) = zw (szwrap 64 a / 2 ^ (b mod 64)).
Proof.
  intros a b. rewrite alu_sra. unfold v_sra. rewrite s_zw, u_zw, mod64_mod64_64.
  pose proof (Z.mod_pos_bound b 64 ltac:(lia)).
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma zw_slt : forall a b,
  alu64 ALU_SLT (zw a) (zw b) = zw (if szwrap 64 a <? szwrap 64 b then 1 else 0).
Proof.
  intros a b. rewrite alu_slt. unfold v_slt, c_lts, bv_lts. rewrite !s_zw.
  destruct (szwrap 64 a <? szwrap 64 b); reflexivity.
Qed.

Lemma zw_sltu : forall a b,
  alu64 ALU_SLTU (zw a) (zw b) = zw (if a mod 2 ^ 64 <? b mod 2 ^ 64 then 1 else 0).
Proof.
  intros a b. rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite !u_zw.
  destruct (a mod 2 ^ 64 <? b mod 2 ^ 64); reflexivity.
Qed.

Lemma wrap32_u_zw : forall a, bv_wrap 32 (bv_unsigned (zw a)) = a mod 2 ^ 32.
Proof.
  intro a. rewrite u_zw. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  apply mod_mod_le. lia.
Qed.

Lemma swrap32_of_mod64 : forall a, bv_swrap 32 (a mod 2 ^ 64) = bv_swrap 32 a.
Proof.
  intro a. apply bv_swrap_congr. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  apply mod_mod_le. lia.
Qed.

Lemma mod32_mod64_32 : forall b, (b mod 2 ^ 64) mod 32 = b mod 32.
Proof.
  intro b. apply (Z.mod_mod_divide b (2 ^ 64) 32). exists (2 ^ 59). reflexivity.
Qed.

Lemma zw_addw : forall a b,
  sext 64 (alu32 ALU_ADD (low32 (zw a)) (low32 (zw b))) = zw (szwrap 32 (a + b)).
Proof.
  intros a b. rewrite w_addw. unfold v_addw. rewrite !u_zw, szwrap32. unfold zw. f_equal.
  rewrite <- (swrap32_of_mod64 (a + b)), Zplus_mod, swrap32_of_mod64. reflexivity.
Qed.

Lemma zw_subw : forall a b,
  sext 64 (alu32 ALU_SUB (low32 (zw a)) (low32 (zw b))) = zw (szwrap 32 (a - b)).
Proof.
  intros a b. rewrite w_subw. unfold v_subw. rewrite !u_zw, szwrap32. unfold zw. f_equal.
  rewrite <- (swrap32_of_mod64 (a - b)), Zminus_mod, swrap32_of_mod64. reflexivity.
Qed.

Lemma zw_sllw : forall a b,
  sext 64 (alu32 ALU_SLL (low32 (zw a)) (low32 (zw b))) = zw (szwrap 32 (a * 2 ^ (b mod 32))).
Proof.
  intros a b. rewrite w_sllw. unfold v_sllw. rewrite !u_zw, mod32_mod64_32, szwrap32.
  pose proof (Z.mod_pos_bound b 32 ltac:(lia)).
  rewrite Z.shiftl_mul_pow2 by lia. unfold zw. f_equal.
  rewrite <- (swrap32_of_mod64 (a mod 2 ^ 64 * _)), Z.mul_mod_idemp_l, swrap32_of_mod64 by lia.
  reflexivity.
Qed.

Lemma zw_srlw : forall a b,
  sext 64 (alu32 ALU_SRL (low32 (zw a)) (low32 (zw b)))
  = zw (szwrap 32 ((a mod 2 ^ 32) / 2 ^ (b mod 32))).
Proof.
  intros a b. rewrite w_srlw. unfold v_srlw. rewrite wrap32_u_zw, u_zw, mod32_mod64_32, szwrap32.
  pose proof (Z.mod_pos_bound b 32 ltac:(lia)).
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma zw_sraw : forall a b,
  sext 64 (alu32 ALU_SRA (low32 (zw a)) (low32 (zw b)))
  = zw (szwrap 32 (szwrap 32 a / 2 ^ (b mod 32))).
Proof.
  intros a b. rewrite w_sraw. unfold v_sraw. rewrite !u_zw, mod32_mod64_32, !szwrap32.
  pose proof (Z.mod_pos_bound b 32 ltac:(lia)).
  rewrite Z.shiftr_div_pow2 by lia. rewrite swrap32_of_mod64. reflexivity.
Qed.

Lemma zw_mul : forall a b, mul_div M_MUL (zw a) (zw b) = zw (a * b).
Proof.
  intros a b. rewrite m_mul. unfold v_mul. rewrite !u_zw. apply zw_eqm.
  rewrite <- Zmult_mod. reflexivity.
Qed.

Lemma zw_mulhu : forall a b,
  mul_div M_MULHU (zw a) (zw b) = zw ((a mod 2 ^ 64) * (b mod 2 ^ 64) / 2 ^ 64).
Proof.
  intros a b. rewrite m_mulhu. unfold v_mulhu. rewrite !u_zw.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma zw_mulh : forall a b,
  mul_div M_MULH (zw a) (zw b) = zw (szwrap 64 a * szwrap 64 b / 2 ^ 64).
Proof.
  intros a b. rewrite m_mulh. unfold v_mulh. rewrite !s_zw.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma zw_mulhsu : forall a b,
  mul_div M_MULHSU (zw a) (zw b) = zw (szwrap 64 a * (b mod 2 ^ 64) / 2 ^ 64).
Proof.
  intros a b. rewrite m_mulhsu. unfold v_mulhsu. rewrite s_zw, u_zw.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma zw_mulw : forall a b,
  sext 64 (mul_div M_MUL (low32 (zw a)) (low32 (zw b))) = zw (szwrap 32 (a * b)).
Proof.
  intros a b. rewrite w_mulw. unfold v_mulw. rewrite !u_zw, szwrap32. unfold zw. f_equal.
  rewrite <- (swrap32_of_mod64 (a * b)), Zmult_mod, swrap32_of_mod64. reflexivity.
Qed.

Lemma zw_opq : forall op a b, alu64 op (zw a) (zw b) = zw (zalu op a b).
Proof. intros. unfold zalu. symmetry. apply zw_u. Qed.
Lemma zw_opqw : forall op a b,
  sext 64 (alu32 op (low32 (zw a)) (low32 (zw b))) = zw (zaluw op a b).
Proof. intros. unfold zaluw. symmetry. apply zw_u. Qed.
Lemma zw_mdq : forall op a b, mul_div op (zw a) (zw b) = zw (zmd op a b).
Proof. intros. unfold zmd. symmetry. apply zw_u. Qed.
Lemma zw_mdqw : forall op a b,
  sext 64 (mul_div op (low32 (zw a)) (low32 (zw b))) = zw (zmdw op a b).
Proof. intros. unfold zmdw. symmetry. apply zw_u. Qed.



Section Smart.
Variables (vb fb : bounds).

Definition lin (e : expr) : expr * Z :=
  match e with
  | ELit k => (ELit 0, k)
  | EAdd a (ELit k) => (a, k)
  | _ => (e, 0)
  end.

Definition is_lit0 (e : expr) : bool := match e with ELit Z0 => true | _ => false end.

Definition relin (c : expr) (k : Z) : expr :=
  if is_lit0 c then ELit k else if Z.eqb k 0 then c else EAdd c (ELit k).

Definition mkAdd (a b : expr) : expr :=
  let (ca, x) := lin a in
  let (cb, y) := lin b in
  let c := if is_lit0 ca then cb else if is_lit0 cb then ca else EAdd ca cb in
  relin c (x + y).

Definition mkSub (a b : expr) : expr :=
  let (ca, x) := lin a in
  let (cb, y) := lin b in
  let c := if is_lit0 cb then ca
           else if expr_eqb ca cb then ELit 0
           else match ca with
                | EAdd ca1 ca2 =>
                    if expr_eqb ca1 cb then ca2
                    else if expr_eqb ca2 cb then ca1 else ESub ca cb
                | _ => ESub ca cb
                end in
  relin c (x - y).

Definition shl1 (a : expr) (k : Z) : expr :=
  match a with
  | EShl a' j => if 0 <=? j then EShl a' (j + k) else EShl a k
  | _ => EShl a k
  end.

Definition mkShl (a : expr) (k : Z) : expr :=
  if Z.eqb k 0 then a else
  match a with
  | ELit z => ELit (z * 2 ^ k)
  | EAdd a' (ELit x) => EAdd (shl1 a' k) (ELit (x * 2 ^ k))
  | _ => shl1 a k
  end.

Definition mkMul (a b : expr) : expr :=
  match a, b with
  | ELit x, ELit y => ELit (x * y)
  | _, ELit y => if Z.eqb y 0 then ELit 0 else if Z.eqb y 1 then a
                 else match lin a with
                      | (c, x) => if Z.eqb x 0 then EMul a b
                                  else EAdd (EMul c b) (ELit (x * y)) end
  | ELit x, _ => if Z.eqb x 0 then ELit 0 else if Z.eqb x 1 then b else EMul a b
  | _, _ => EMul a b
  end.

Fixpoint stripw (k : Z) (e : expr) {struct e} : expr :=
  match e with
  | EZx j a => if k <=? j then stripw k a else e
  | ESx j a => if k <=? j then stripw k a else e
  | EAdd a b => mkAdd (stripw k a) (stripw k b)
  | ESub a b => mkSub (stripw k a) (stripw k b)
  | EMul a b => mkMul (stripw k a) (stripw k b)
  | EShl a j => if 0 <=? j then mkShl (stripw k a) j else e
  | _ => e
  end.

Definition mkZx (k : Z) (a : expr) : expr :=
  if 0 <? k then
    let a' := stripw k a in
    if ebelow vb fb a' (2 ^ k) then a'
    else match a' with
         | ELit z => ELit (z mod 2 ^ k)
         | _ => EZx k a'
         end
  else EZx k a.

Definition mkSx (k : Z) (a : expr) : expr :=
  if 0 <? k then
    let a' := stripw k a in
    if ebelow vb fb a' (2 ^ (k - 1)) then a'
    else match a' with
         | ELit z => ELit (szwrap k z)
         | _ => ESx k a'
         end
  else ESx k a.

Definition mask_width (m : Z) : option Z :=
  if (0 <=? m) && (Z.eqb (2 ^ (Z.log2 (m + 1))) (m + 1)) then Some (Z.log2 (m + 1)) else None.

Definition mkAnd (a b : expr) : expr :=
  match a, b with
  | ELit x, ELit y => ELit (Z.land x y)
  | _, ELit y => match mask_width y with Some k => mkZx k a | None => EAnd a b end
  | ELit x, _ => match mask_width x with Some k => mkZx k b | None => EAnd a b end
  | _, _ => EAnd a b
  end.

Definition mkOr (a b : expr) : expr :=
  match a, b with
  | ELit x, ELit y => ELit (Z.lor x y)
  | _, ELit Z0 => a
  | ELit Z0, _ => b
  | _, _ => EOr a b
  end.

Definition mkXor (a b : expr) : expr :=
  match a, b with
  | ELit x, ELit y => ELit (Z.lxor x y)
  | _, ELit Z0 => a
  | ELit Z0, _ => b
  | _, _ => EXor a b
  end.

Definition mkShr (a : expr) (k : Z) : expr :=
  if Z.eqb k 0 then a else
  match a with
  | ELit z => ELit (z / 2 ^ k)
  | EShr a' j => if 0 <=? j then EShr a' (j + k) else EShr a k
  | EShl a' j => if (0 <=? j) && (j <=? k) then (if Z.eqb j k then a' else EShr a' (k - j))
                 else if (0 <=? k) && (k <=? j) then mkShl a' (j - k)
                 else EShr a k
  | EZx 64 (EShl a' j) =>
      if (0 <=? j) && (j <=? k) && (k <=? 64) then
        let a2 := mkZx (64 - j) a' in
        if Z.eqb j k then a2 else EShr a2 (k - j)
      else EShr a k
  | EZx 64 (EAdd (EShl a' j) (ELit c)) =>
      if (0 <=? j) && (j <=? k) && (k <=? 64) && (Z.eqb (c mod 2 ^ j) 0) then
        let a2 := mkZx (64 - j) (mkAdd a' (ELit (c / 2 ^ j))) in
        if Z.eqb j k then a2 else EShr a2 (k - j)
      else EShr a k
  | EAdd (EShl a' j) (ELit c) =>
      if (0 <=? j) && (j <=? k) && (Z.eqb (c mod 2 ^ j) 0) then
        let a2 := mkAdd a' (ELit (c / 2 ^ j)) in
        if Z.eqb j k then a2 else EShr a2 (k - j)
      else EShr a k
  | _ => EShr a k
  end.

Definition mkLtb (a b : expr) : expr :=
  match a, b with
  | ELit x, ELit y => ELit (if x <? y then 1 else 0)
  | _, _ => ELtb a b
  end.


Context (E : venv) (Hv : vars_ok E vb) (Hf : funs_ok E fb).

Lemma lin_ed : forall e, ed E e = ed E (fst (lin e)) + snd (lin e).
Proof.
  intro e. destruct e; cbn [lin fst snd ed]; try lia.
  destruct e2; cbn [fst snd ed]; lia.
Qed.

Lemma is_lit0_ed : forall e, is_lit0 e = true -> ed E e = 0.
Proof. intros e H. destruct e; cbn in H; try discriminate. destruct z; try discriminate. reflexivity. Qed.

Lemma relin_ed : forall c k, ed E (relin c k) = ed E c + k.
Proof.
  intros c k. unfold relin. destruct (is_lit0 c) eqn:H0.
  - rewrite (is_lit0_ed c H0). cbn. lia.
  - destruct (Z.eqb_spec k 0); [subst; lia|]. cbn [ed]. lia.
Qed.

Lemma mkAdd_ed : forall a b, ed E (mkAdd a b) = ed E a + ed E b.
Proof.
  intros a b. unfold mkAdd.
  destruct (lin a) as [ca x] eqn:La. destruct (lin b) as [cb y] eqn:Lb.
  rewrite relin_ed.
  rewrite (lin_ed a), (lin_ed b), La, Lb. cbn [fst snd].
  destruct (is_lit0 ca) eqn:Ha; [rewrite (is_lit0_ed ca Ha); lia|].
  destruct (is_lit0 cb) eqn:Hb; [rewrite (is_lit0_ed cb Hb); lia|].
  cbn [ed]. lia.
Qed.

Lemma mkSub_ed : forall a b, ed E (mkSub a b) = ed E a - ed E b.
Proof.
  intros a b. unfold mkSub.
  destruct (lin a) as [ca x] eqn:La. destruct (lin b) as [cb y] eqn:Lb.
  rewrite relin_ed.
  rewrite (lin_ed a), (lin_ed b), La, Lb. cbn [fst snd].
  destruct (is_lit0 cb) eqn:Hb; [rewrite (is_lit0_ed cb Hb); lia|].
  destruct (expr_eqb ca cb) eqn:Heq.
  - rewrite (ed_eqb E ca cb Heq). cbn [ed]. lia.
  - destruct ca; cbn [ed]; try lia.
    destruct (expr_eqb ca1 cb) eqn:H1; [rewrite <- (ed_eqb E ca1 cb H1); lia|].
    destruct (expr_eqb ca2 cb) eqn:H2; [rewrite <- (ed_eqb E ca2 cb H2); lia|].
    cbn [ed]. lia.
Qed.

Lemma shl1_ed : forall a k, 0 <= k -> ed E (shl1 a k) = ed E a * 2 ^ k.
Proof.
  intros a k Hk. unfold shl1. destruct a; cbn [ed]; try lia.
  destruct (Z.leb_spec 0 k0); cbn [ed]; [|lia].
  rewrite Z.pow_add_r by lia. lia.
Qed.

Lemma mkShl_ed : forall a k, 0 <= k -> ed E (mkShl a k) = ed E a * 2 ^ k.
Proof.
  intros a k Hk. unfold mkShl.
  destruct (Z.eqb_spec k 0) as [->|Hk0]; [rewrite Z.pow_0_r; lia|].
  destruct a; try (apply shl1_ed; exact Hk).
  - reflexivity.
  - destruct a2; try (apply shl1_ed; exact Hk).
    cbn [ed]. rewrite shl1_ed by exact Hk. lia.
Qed.

Lemma mkMul_ed : forall a b, ed E (mkMul a b) = ed E a * ed E b.
Proof.
  intros a b. unfold mkMul.
  destruct a; destruct b;
    try reflexivity;
    try (match goal with
         | |- ed E (if Z.eqb ?y 0 then _ else _) = _ =>
             destruct (Z.eqb_spec y 0) as [->|]; [cbn [ed]; lia|];
             destruct (Z.eqb_spec y 1) as [->|]; [cbn [ed]; lia|]
         end);
    try reflexivity;
    try (match goal with
         | |- ed E (let (c, x) := lin ?a in _) = _ =>
             pose proof (lin_ed a) as HL;
             destruct (lin a) as [c x]; cbn [fst snd] in HL;
             destruct (Z.eqb_spec x 0); [reflexivity|]; cbn [ed]; cbn [ed] in HL; rewrite HL; lia
         end).
Qed.

Lemma eqmod_le : forall x y j k, 0 <= k <= j ->
  x mod 2 ^ j = y mod 2 ^ j -> x mod 2 ^ k = y mod 2 ^ k.
Proof.
  intros x y j k Hk H.
  rewrite <- (mod_mod_le x k j), <- (mod_mod_le y k j) by lia. rewrite H. reflexivity.
Qed.

Lemma stripw_eqm : forall k e, 0 < k -> (ed E (stripw k e)) mod 2 ^ k = (ed E e) mod 2 ^ k.
Proof.
  intros k e Hk. induction e; cbn [stripw]; try reflexivity.
  - rewrite mkAdd_ed. cbn [ed]. rewrite Zplus_mod, IHe1, IHe2, <- Zplus_mod. reflexivity.
  - rewrite mkSub_ed. cbn [ed]. rewrite Zminus_mod, IHe1, IHe2, <- Zminus_mod. reflexivity.
  - rewrite mkMul_ed. cbn [ed]. rewrite Zmult_mod, IHe1, IHe2, <- Zmult_mod. reflexivity.
  - destruct (Z.leb_spec 0 k0); [|reflexivity].
    rewrite mkShl_ed by lia. cbn [ed]. rewrite Zmult_mod, IHe, <- Zmult_mod. reflexivity.
  - destruct (Z.leb_spec k k0); [|reflexivity]. rewrite IHe. cbn [ed].
    symmetry. apply mod_mod_le. lia.
  - destruct (Z.leb_spec k k0); [|reflexivity]. rewrite IHe. cbn [ed].
    apply (eqmod_le _ _ k0 k); [lia|]. symmetry. apply szwrap_eqm. lia.
Qed.

Lemma mkZx_ed : forall k a, ed E (mkZx k a) = (ed E a) mod 2 ^ k.
Proof.
  intros k a. unfold mkZx.
  destruct (Z.ltb_spec 0 k) as [Hk|Hk]; [|reflexivity].
  pose proof (stripw_eqm k a Hk) as Hs.
  destruct (ebelow vb fb (stripw k a) (2 ^ k)) eqn:Hb.
  { pose proof (ebelow_sound E vb fb _ _ Hv Hf Hb). rewrite <- Hs. symmetry. apply Z.mod_small. lia. }
  destruct (stripw k a); cbn [ed]; cbn [ed] in Hs; rewrite <- Hs; reflexivity.
Qed.

Lemma szwrap_of_mod : forall k a b, 0 < k -> a mod 2 ^ k = b mod 2 ^ k -> szwrap k a = szwrap k b.
Proof.
  intros k a b Hk H. rewrite <- (szwrap_mod k a), <- (szwrap_mod k b) by lia. rewrite H. reflexivity.
Qed.

Lemma mkSx_ed : forall k a, ed E (mkSx k a) = szwrap k (ed E a).
Proof.
  intros k a. unfold mkSx.
  destruct (Z.ltb_spec 0 k) as [Hk|Hk]; [|reflexivity].
  pose proof (stripw_eqm k a Hk) as Hs.
  rewrite <- (szwrap_of_mod k _ _ Hk Hs).
  destruct (ebelow vb fb (stripw k a) (2 ^ (k - 1))) eqn:Hb.
  { pose proof (ebelow_sound E vb fb _ _ Hv Hf Hb). symmetry. apply szwrap_small; lia. }
  destruct (stripw k a); cbn [ed]; reflexivity.
Qed.

Lemma mask_width_sound : forall m k, mask_width m = Some k -> 0 <= k /\ m = 2 ^ k - 1.
Proof.
  intros m k H. unfold mask_width in H.
  destruct (Z.leb_spec 0 m); cbn [andb] in H; [|discriminate].
  destruct (Z.eqb_spec (2 ^ Z.log2 (m + 1)) (m + 1)); [|discriminate].
  injection H as <-. split; [apply Z.log2_nonneg | lia].
Qed.

Lemma land_mask : forall a k, 0 <= k -> Z.land a (2 ^ k - 1) = a mod 2 ^ k.
Proof.
  intros a k Hk. replace (2 ^ k - 1) with (Z.ones k).
  - apply Z.land_ones. exact Hk.
  - unfold Z.ones. rewrite Z.shiftl_1_l. lia.
Qed.

Lemma mkAnd_ed : forall a b, ed E (mkAnd a b) = Z.land (ed E a) (ed E b).
Proof.
  intros a b. unfold mkAnd.
  destruct a; destruct b; try reflexivity.
  all: match goal with
       | |- ed E (match mask_width ?m with _ => _ end) = _ =>
           let kk := fresh "kk" in let Hm := fresh "Hm" in
           let Hkk := fresh "Hkk" in let Hm2 := fresh "Hm2" in
           destruct (mask_width m) as [kk|] eqn:Hm; [|reflexivity];
           apply mask_width_sound in Hm as [Hkk Hm2]; rewrite Hm2;
           rewrite mkZx_ed; cbn [ed];
           first [ rewrite land_mask by exact Hkk; reflexivity
                 | rewrite (Z.land_comm (2 ^ kk - 1)), land_mask by exact Hkk; reflexivity ]
       end.
Qed.


Lemma mkOr_ed : forall a b, ed E (mkOr a b) = Z.lor (ed E a) (ed E b).
Proof.
  intros a b. unfold mkOr.
  destruct a; destruct b; try reflexivity;
    try (destruct z; try reflexivity; cbn [ed]; rewrite ?Z.lor_0_r, ?Z.lor_0_l; reflexivity);
    try (destruct z0; try reflexivity; cbn [ed]; rewrite ?Z.lor_0_r, ?Z.lor_0_l; reflexivity).
Qed.

Lemma mkXor_ed : forall a b, ed E (mkXor a b) = Z.lxor (ed E a) (ed E b).
Proof.
  intros a b. unfold mkXor.
  destruct a; destruct b; try reflexivity;
    try (destruct z; try reflexivity; cbn [ed]; rewrite ?Z.lxor_0_r, ?Z.lxor_0_l; reflexivity);
    try (destruct z0; try reflexivity; cbn [ed]; rewrite ?Z.lxor_0_r, ?Z.lxor_0_l; reflexivity).
Qed.

Lemma shl_mod_shr : forall a j k, 0 <= j <= k -> k <= 64 ->
  (a * 2 ^ j) mod 2 ^ 64 / 2 ^ k = (a mod 2 ^ (64 - j)) / 2 ^ (k - j).
Proof.
  intros a j k Hjk Hk.
  replace (2 ^ 64) with (2 ^ (64 - j) * 2 ^ j)
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_mod_distr_r by (try apply Z.pow_nonzero; lia).
  replace (2 ^ k) with (2 ^ j * 2 ^ (k - j))
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite <- Z.div_div by (try apply Z.pow_pos_nonneg; try apply Z.pow_nonneg; lia).
  rewrite Z.div_mul by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma shl_lit_div : forall x z j k, 0 <= j <= k -> z mod 2 ^ j = 0 ->
  (x * 2 ^ j + z) / 2 ^ k = (x + z / 2 ^ j) / 2 ^ (k - j).
Proof.
  intros x z j k Hjk Hz.
  assert (Hc : z = z / 2 ^ j * 2 ^ j).
  { pose proof (Z.div_mod z (2 ^ j) ltac:(apply Z.pow_nonzero; lia)). lia. }
  rewrite Hc at 1. rewrite <- Z.mul_add_distr_r.
  replace (2 ^ k) with (2 ^ j * 2 ^ (k - j)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite <- Z.div_div by (try apply Z.pow_pos_nonneg; try apply Z.pow_nonzero; lia).
  rewrite Z.div_mul by (apply Z.pow_nonzero; lia). reflexivity.
Qed.

Lemma shl_lit_mod_shr : forall x z j k, 0 <= j <= k -> k <= 64 -> z mod 2 ^ j = 0 ->
  (x * 2 ^ j + z) mod 2 ^ 64 / 2 ^ k = ((x + z / 2 ^ j) mod 2 ^ (64 - j)) / 2 ^ (k - j).
Proof.
  intros x z j k Hjk Hk Hz.
  assert (Hc : z = z / 2 ^ j * 2 ^ j).
  { pose proof (Z.div_mod z (2 ^ j) ltac:(apply Z.pow_nonzero; lia)). lia. }
  rewrite Hc at 1. rewrite <- Z.mul_add_distr_r. apply shl_mod_shr; lia.
Qed.

Lemma mkShr_ed : forall a k, 0 <= k -> ed E (mkShr a k) = ed E a / 2 ^ k.
Proof.
  intros a k Hk. unfold mkShr.
  destruct (Z.eqb_spec k 0) as [->|Hk0]; [rewrite Z.pow_0_r, Z.div_1_r; reflexivity|].
  destruct a as [z|n|a1 a2|a1 a2|a1 a2|a1 a2|a1 a2|a1 a2|a' j|a' j|j a'|j a'|a1 a2|f a1|f a1 a2|o a1 a2|o a1 a2|o a1 a2|o a1 a2];
    try reflexivity.
  -
    destruct a1 as [| |? ?|? ?|? ?|? ?|? ?|? ?|a'' j|? ?|? ?|? ?|? ?|? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?]; try reflexivity.
    destruct a2 as [c| |? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?]; try reflexivity.
    destruct (Z.leb_spec 0 j); cbn [andb]; [|reflexivity].
    destruct (Z.leb_spec j k); cbn [andb]; [|reflexivity].
    destruct (Z.eqb_spec (c mod 2 ^ j) 0) as [Hz|]; cbn [andb]; [|reflexivity].
    cbn [ed]. rewrite (shl_lit_div _ c j k) by lia.
    destruct (Z.eqb_spec j k) as [<-|].
    + rewrite mkAdd_ed. cbn [ed]. rewrite Z.sub_diag, Z.pow_0_r, Z.div_1_r. reflexivity.
    + cbn [ed]. rewrite mkAdd_ed. reflexivity.
  - cbn [ed].
    destruct (Z.leb_spec 0 j); cbn [andb].
    + destruct (Z.leb_spec j k); cbn [andb].
      * destruct (Z.eqb_spec j k) as [->|].
        -- rewrite Z.div_mul by (apply Z.pow_nonzero; lia). reflexivity.
        -- cbn [ed]. replace (2 ^ k) with (2 ^ j * 2 ^ (k - j))
             by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
           rewrite <- Z.div_div, Z.div_mul by (try apply Z.pow_pos_nonneg; try apply Z.pow_nonzero; lia).
           reflexivity.
      * destruct (Z.leb_spec 0 k); cbn [andb]; [|lia].
        destruct (Z.leb_spec k j); cbn [andb ed]; [|lia].
        rewrite mkShl_ed by lia.
        replace (2 ^ j) with (2 ^ (j - k) * 2 ^ k)
          by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        rewrite Z.mul_assoc, Z.div_mul by (apply Z.pow_nonzero; lia). reflexivity.
    + destruct (Z.leb_spec 0 k); cbn [andb]; [|lia].
      destruct (Z.leb_spec k j); cbn [andb ed]; [lia|reflexivity].
  - cbn [ed]. destruct (Z.leb_spec 0 j); cbn [ed]; [|reflexivity].
    rewrite Z.pow_add_r, Z.div_div by (try apply Z.pow_pos_nonneg; try apply Z.pow_nonzero; lia).
    reflexivity.
  - destruct j; try reflexivity. destruct p; try reflexivity.
    destruct p; try reflexivity. destruct p; try reflexivity. destruct p; try reflexivity.
    destruct p; try reflexivity. destruct p; try reflexivity. destruct p; try reflexivity.
    destruct a' as [| |a1 a2|? ?|? ?|? ?|? ?|? ?|a'' j|? ?|? ?|? ?|? ?|? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?];
      try reflexivity.
    +
      destruct a1 as [| |? ?|? ?|? ?|? ?|? ?|? ?|a'' j|? ?|? ?|? ?|? ?|? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?]; try reflexivity.
      destruct a2 as [c| |? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?]; try reflexivity.
      destruct (Z.leb_spec 0 j); cbn [andb]; [|reflexivity].
      destruct (Z.leb_spec j k); cbn [andb]; [|reflexivity].
      destruct (Z.leb_spec k 64); cbn [andb]; [|reflexivity].
      destruct (Z.eqb_spec (c mod 2 ^ j) 0) as [Hz|]; cbn [andb]; [|reflexivity].
      cbn [ed]. rewrite (shl_lit_mod_shr _ c j k) by lia.
      destruct (Z.eqb_spec j k) as [<-|].
      * rewrite mkZx_ed, mkAdd_ed. cbn [ed]. rewrite Z.sub_diag, Z.pow_0_r, Z.div_1_r. reflexivity.
      * cbn [ed]. rewrite mkZx_ed, mkAdd_ed. reflexivity.
    + destruct (Z.leb_spec 0 j); cbn [andb]; [|reflexivity].
      destruct (Z.leb_spec j k); cbn [andb]; [|reflexivity].
      destruct (Z.leb_spec k 64); cbn [andb]; [|reflexivity].
      cbn [ed]. rewrite shl_mod_shr by lia.
      destruct (Z.eqb_spec j k) as [<-|].
      * rewrite mkZx_ed. rewrite Z.sub_diag, Z.pow_0_r, Z.div_1_r. reflexivity.
      * cbn [ed]. rewrite mkZx_ed. reflexivity.
Qed.

Lemma mkLtb_ed : forall a b, ed E (mkLtb a b) = (if ed E a <? ed E b then 1 else 0).
Proof. intros a b. unfold mkLtb. destruct a; destruct b; reflexivity. Qed.

End Smart.


Section Sem.
Variables (vb fb : bounds).

Definition sem_alu (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD => mkAdd a b
  | ALU_SUB => mkSub a b
  | ALU_AND => mkAnd vb fb a b
  | ALU_OR => mkOr a b
  | ALU_XOR => mkXor a b
  | ALU_SLL => match b with
               | ELit k => mkShl a (k mod 64)
               | _ => EOpq ALU_SLL a b end
  | ALU_SRL => match b with
               | ELit k => mkShr vb fb (mkZx vb fb 64 a) (k mod 64)
               | _ => EOpq ALU_SRL a b end
  | ALU_SRA => match b with
               | ELit k => mkShr vb fb (mkSx vb fb 64 a) (k mod 64)
               | _ => EOpq ALU_SRA a b end
  | ALU_SLT => mkLtb (mkSx vb fb 64 a) (mkSx vb fb 64 b)
  | ALU_SLTU => mkLtb (mkZx vb fb 64 a) (mkZx vb fb 64 b)
  end.

Definition sem_aluw (op : aluop) (a b : expr) : expr :=
  match op with
  | ALU_ADD => mkSx vb fb 32 (mkAdd a b)
  | ALU_SUB => mkSx vb fb 32 (mkSub a b)
  | ALU_SLL => match b with
               | ELit k => mkSx vb fb 32 (mkShl a (k mod 32))
               | _ => EOpqw ALU_SLL a b end
  | ALU_SRL => match b with
               | ELit k => mkSx vb fb 32 (mkShr vb fb (mkZx vb fb 32 a) (k mod 32))
               | _ => EOpqw ALU_SRL a b end
  | ALU_SRA => match b with
               | ELit k => mkSx vb fb 32 (mkShr vb fb (mkSx vb fb 32 a) (k mod 32))
               | _ => EOpqw ALU_SRA a b end
  | _ => EOpqw op a b
  end.

Definition sem_md (op : mulop) (a b : expr) : expr :=
  match op with
  | M_MUL => mkMul a b
  | M_MULHU => mkShr vb fb (mkMul (mkZx vb fb 64 a) (mkZx vb fb 64 b)) 64
  | M_MULH => mkShr vb fb (mkMul (mkSx vb fb 64 a) (mkSx vb fb 64 b)) 64
  | M_MULHSU => mkShr vb fb (mkMul (mkSx vb fb 64 a) (mkZx vb fb 64 b)) 64
  | _ => EMdq op a b
  end.

Definition sem_mdw (op : mulop) (a b : expr) : expr :=
  match op with
  | M_MUL => mkSx vb fb 32 (mkMul a b)
  | _ => EMdqw op a b
  end.

Context (E : venv) (Hv : vars_ok E vb) (Hf : funs_ok E fb).

Local Ltac smart :=
  repeat first [ rewrite (mkAdd_ed E) | rewrite (mkSub_ed E) | rewrite (mkMul_ed E)
               | rewrite (mkLtb_ed E) | rewrite (mkOr_ed E) | rewrite (mkXor_ed E)
               | rewrite (mkAnd_ed vb fb E Hv Hf) | rewrite (mkZx_ed vb fb E Hv Hf)
               | rewrite (mkSx_ed vb fb E Hv Hf) ].

Lemma sem_alu_sound : forall op a b,
  zw (ed E (sem_alu op a b)) = alu64 op (zw (ed E a)) (zw (ed E b)).
Proof.
  intros op a b. destruct op; cbn [sem_alu].
  - smart. symmetry. apply zw_add.
  - smart. symmetry. apply zw_sub.
  - destruct b; try (symmetry; apply zw_opq).
    pose proof (Z.mod_pos_bound z 64 ltac:(lia)).
    rewrite (mkShl_ed E) by lia. cbn [ed]. symmetry. apply zw_sll.
  - smart. symmetry. apply zw_slt.
  - smart. symmetry. apply zw_sltu.
  - smart. symmetry. apply zw_xor.
  - destruct b; try (symmetry; apply zw_opq).
    pose proof (Z.mod_pos_bound z 64 ltac:(lia)).
    rewrite (mkShr_ed vb fb E Hv Hf) by lia. smart. cbn [ed]. symmetry. apply zw_srl.
  - destruct b; try (symmetry; apply zw_opq).
    pose proof (Z.mod_pos_bound z 64 ltac:(lia)).
    rewrite (mkShr_ed vb fb E Hv Hf) by lia. smart. cbn [ed]. symmetry. apply zw_sra.
  - smart. symmetry. apply zw_or.
  - smart. symmetry. apply zw_and.
Qed.

Lemma sem_aluw_sound : forall op a b,
  zw (ed E (sem_aluw op a b)) = sext 64 (alu32 op (low32 (zw (ed E a))) (low32 (zw (ed E b)))).
Proof.
  intros op a b. destruct op; cbn [sem_aluw]; try (symmetry; apply zw_opqw).
  - smart. symmetry. apply zw_addw.
  - smart. symmetry. apply zw_subw.
  - destruct b; try (symmetry; apply zw_opqw).
    pose proof (Z.mod_pos_bound z 32 ltac:(lia)).
    smart. rewrite (mkShl_ed E) by lia. cbn [ed]. symmetry. apply zw_sllw.
  - destruct b; try (symmetry; apply zw_opqw).
    pose proof (Z.mod_pos_bound z 32 ltac:(lia)).
    smart. rewrite (mkShr_ed vb fb E Hv Hf) by lia. smart. cbn [ed]. symmetry. apply zw_srlw.
  - destruct b; try (symmetry; apply zw_opqw).
    pose proof (Z.mod_pos_bound z 32 ltac:(lia)).
    smart. rewrite (mkShr_ed vb fb E Hv Hf) by lia. smart. cbn [ed]. symmetry. apply zw_sraw.
Qed.

Lemma sem_md_sound : forall op a b,
  zw (ed E (sem_md op a b)) = mul_div op (zw (ed E a)) (zw (ed E b)).
Proof.
  intros op a b. destruct op; cbn [sem_md]; try (symmetry; apply zw_mdq).
  - smart. symmetry. apply zw_mul.
  - rewrite (mkShr_ed vb fb E Hv Hf) by lia. smart. symmetry. apply zw_mulh.
  - rewrite (mkShr_ed vb fb E Hv Hf) by lia. smart. symmetry. apply zw_mulhsu.
  - rewrite (mkShr_ed vb fb E Hv Hf) by lia. smart. symmetry. apply zw_mulhu.
Qed.

Lemma sem_mdw_sound : forall op a b,
  zw (ed E (sem_mdw op a b)) = sext 64 (mul_div op (low32 (zw (ed E a))) (low32 (zw (ed E b)))).
Proof.
  intros op a b. destruct op; cbn [sem_mdw]; try (symmetry; apply zw_mdqw).
  smart. symmetry. apply zw_mulw.
Qed.

End Sem.
End FXG.
