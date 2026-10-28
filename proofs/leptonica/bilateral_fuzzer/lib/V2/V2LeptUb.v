(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StartupTac WalkTac SumsLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptArith LeptArith2.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma al16_mod8 : forall p, p mod 16 = 0 -> p mod 8 = 0.
Proof. intros p H. lia. Qed.
Lemma al16_mod4 : forall p, p mod 16 = 0 -> p mod 4 = 0.
Proof. intros p H. lia. Qed.
Lemma al8_mod4 : forall p, p mod 8 = 0 -> p mod 4 = 0.
Proof. intros p H. lia. Qed.
Lemma al16_plus_mod8 : forall p k, p mod 16 = 0 -> k mod 8 = 0 -> (p + k) mod 8 = 0.
Proof. intros p k H1 H2. lia. Qed.
Lemma al16_plus_mod4 : forall p k, p mod 16 = 0 -> k mod 4 = 0 -> (p + k) mod 4 = 0.
Proof. intros p k H1 H2. lia. Qed.
Lemma al4_plus_mod4 : forall p k, p mod 4 = 0 -> k mod 4 = 0 -> (p + k) mod 4 = 0.
Proof. intros p k H1 H2. lia. Qed.
Lemma sp_slot_al8 : forall sp k, sp mod 16 = 0 -> k mod 8 = 0 -> (sp - k) mod 8 = 0.
Proof. intros sp k H1 H2. lia. Qed.
Lemma sp_slot_al4' : forall sp k, sp mod 16 = 0 -> k mod 4 = 0 -> (sp - k) mod 4 = 0.
Proof. intros sp k H1 H2. lia. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma zbv_or : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_or (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lor a b).
Proof. intros a b Ha Hb. unfold v_or. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma Z_lor_range64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64.
Proof.
  intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [->|NZ]; [lia|].
  apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg a b); lia|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia].
  - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia].
Qed.

Lemma lor_mod_pow2_0 : forall a b n, 0 <= a -> 0 <= b -> 0 <= n -> a mod 2 ^ n = 0 -> b mod 2 ^ n = 0 -> (Z.lor a b) mod 2 ^ n = 0.
Proof.
  intros a b n Ha Hb Hn Ma Mb.
  rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l. rewrite !Z.land_ones by lia. rewrite Ma, Mb. reflexivity.
Qed.
Lemma lor_mod4_0 : forall a b, 0 <= a -> 0 <= b -> a mod 4 = 0 -> b mod 4 = 0 -> (Z.lor a b) mod 4 = 0.
Proof. intros a b Ha Hb Ma Mb. change 4 with (2 ^ 2) in *. apply lor_mod_pow2_0; lia || assumption. Qed.
Lemma lor_mod8_0 : forall a b, 0 <= a -> 0 <= b -> a mod 8 = 0 -> b mod 8 = 0 -> (Z.lor a b) mod 8 = 0.
Proof. intros a b Ha Hb Ma Mb. change 8 with (2 ^ 3) in *. apply lor_mod_pow2_0; lia || assumption. Qed.

(* [comment removed for export] *)
Ltac guard4 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_3; unorm; rewrite EQ; reflexivity).
Ltac guard8 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite EQ; reflexivity).
(* [comment removed for export] *)
Ltac orv F D a b :=
  chain_step;
  [ reflexivity
  | eapply step_or_at with (v := Z_to_bv 64 (Z.lor a b)); [ exact F | reflexivity | exact D | reflexivity | gres; pin; apply zbv_or; lia ]
  | step_simpl ].
