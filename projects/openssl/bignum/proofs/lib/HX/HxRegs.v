(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Inductive rix : Set := X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9 | X10 | X11 | X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19 | X20 | X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29 | X30 | X31.

Definition rix_Z (i : rix) : Z := match i with X0 => 0 | X1 => 1 | X2 => 2 | X3 => 3 | X4 => 4 | X5 => 5 | X6 => 6 | X7 => 7 | X8 => 8 | X9 => 9 | X10 => 10 | X11 => 11 | X12 => 12 | X13 => 13 | X14 => 14 | X15 => 15 | X16 => 16 | X17 => 17 | X18 => 18 | X19 => 19 | X20 => 20 | X21 => 21 | X22 => 22 | X23 => 23 | X24 => 24 | X25 => 25 | X26 => 26 | X27 => 27 | X28 => 28 | X29 => 29 | X30 => 30 | X31 => 31 end.

Definition rix_of_Z (z : Z) : rix := match z with 1 => X1 | 2 => X2 | 3 => X3 | 4 => X4 | 5 => X5 | 6 => X6 | 7 => X7 | 8 => X8 | 9 => X9 | 10 => X10 | 11 => X11 | 12 => X12 | 13 => X13 | 14 => X14 | 15 => X15 | 16 => X16 | 17 => X17 | 18 => X18 | 19 => X19 | 20 => X20 | 21 => X21 | 22 => X22 | 23 => X23 | 24 => X24 | 25 => X25 | 26 => X26 | 27 => X27 | 28 => X28 | 29 => X29 | 30 => X30 | 31 => X31 | _ => X0 end.

Lemma rix_of_Z_Z (z : Z) : 0 <= z < 32 -> rix_Z (rix_of_Z z) = z.
Proof.
  intros H. assert (E : z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9 \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29 \/ z = 30 \/ z = 31) by lia.
  repeat (destruct E as [E|E]; [subst z; reflexivity|]). subst z; reflexivity.
Qed.

Lemma rix_Z_inj (i j : rix) : rix_Z i = rix_Z j -> i = j.
Proof. destruct i, j; cbn; intros H; try reflexivity; discriminate H. Qed.

Definition rix_of_reg (r : reg) : rix := rix_of_Z (bv_unsigned r).

Lemma rix_of_reg_Z (r : reg) : rix_Z (rix_of_reg r) = bv_unsigned r.
Proof.
  unfold rix_of_reg. apply rix_of_Z_Z. pose proof (bv_unsigned_in_range 5 r) as H.
  change (bv_modulus 5) with 32 in H. exact H.
Qed.

Definition rix_eqb (i j : rix) : bool := (rix_Z i =? rix_Z j).

Section Regs.
Context {V : Type}.
Variable zero : V.

Record regfile : Type := RF { r1 : V; r2 : V; r3 : V; r4 : V; r5 : V; r6 : V; r7 : V; r8 : V; r9 : V; r10 : V; r11 : V; r12 : V; r13 : V; r14 : V; r15 : V; r16 : V; r17 : V; r18 : V; r19 : V; r20 : V; r21 : V; r22 : V; r23 : V; r24 : V; r25 : V; r26 : V; r27 : V; r28 : V; r29 : V; r30 : V; r31 : V }.

Definition rf_get (R : regfile) (i : rix) : V :=
  match i with X0 => zero | X1 => r1 R | X2 => r2 R | X3 => r3 R | X4 => r4 R | X5 => r5 R | X6 => r6 R | X7 => r7 R | X8 => r8 R | X9 => r9 R | X10 => r10 R | X11 => r11 R | X12 => r12 R | X13 => r13 R | X14 => r14 R | X15 => r15 R | X16 => r16 R | X17 => r17 R | X18 => r18 R | X19 => r19 R | X20 => r20 R | X21 => r21 R | X22 => r22 R | X23 => r23 R | X24 => r24 R | X25 => r25 R | X26 => r26 R | X27 => r27 R | X28 => r28 R | X29 => r29 R | X30 => r30 R | X31 => r31 R end.

Definition rf_set (R : regfile) (i : rix) (v : V) : regfile :=
  match i with X0 => R
  | X1 => RF v (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X2 => RF (r1 R) v (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X3 => RF (r1 R) (r2 R) v (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X4 => RF (r1 R) (r2 R) (r3 R) v (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X5 => RF (r1 R) (r2 R) (r3 R) (r4 R) v (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X6 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) v (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X7 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) v (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X8 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) v (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X9 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) v (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X10 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) v (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X11 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) v (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X12 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) v (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X13 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) v (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X14 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) v (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X15 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) v (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X16 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) v (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X17 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) v (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X18 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) v (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X19 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) v (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X20 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) v (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X21 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) v (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X22 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) v (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X23 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) v (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X24 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) v (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X25 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) v (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X26 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) v (r27 R) (r28 R) (r29 R) (r30 R) (r31 R)
  | X27 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) v (r28 R) (r29 R) (r30 R) (r31 R)
  | X28 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) v (r29 R) (r30 R) (r31 R)
  | X29 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) v (r30 R) (r31 R)
  | X30 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) v (r31 R)
  | X31 => RF (r1 R) (r2 R) (r3 R) (r4 R) (r5 R) (r6 R) (r7 R) (r8 R) (r9 R) (r10 R) (r11 R) (r12 R) (r13 R) (r14 R) (r15 R) (r16 R) (r17 R) (r18 R) (r19 R) (r20 R) (r21 R) (r22 R) (r23 R) (r24 R) (r25 R) (r26 R) (r27 R) (r28 R) (r29 R) (r30 R) v
  end.

Definition rf_const (v : V) : regfile := RF v v v v v v v v v v v v v v v v v v v v v v v v v v v v v v v.

Lemma rf_get_set_same (R : regfile) (i : rix) (v : V) : i <> X0 -> rf_get (rf_set R i v) i = v.
Proof. destruct i; intros H; try reflexivity. exfalso; apply H; reflexivity. Qed.

Lemma rf_get_set_other (R : regfile) (i j : rix) (v : V) : i <> j -> rf_get (rf_set R i v) j = rf_get R j.
Proof. destruct i, j; intros H; try reflexivity; exfalso; apply H; reflexivity. Qed.

End Regs.
Arguments regfile V : clear implicits.

