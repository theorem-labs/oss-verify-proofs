(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition X2B_ENTRY : Z := 0x81e48.
Definition X2B_HELPER : Z := 0x8d25c.
Definition X2B_SUAR : Z := 0xba300.
Definition X2B_GOTPC : Z := 0xb2db8.
Definition X2B_MAGIC_LIVE : Z := 0x41b58ab3.
Definition X2B_MAGIC_DEAD : Z := 0x45e0360e.
Definition X2B_DESC : Z := 0x16e85.

Definition SPB (SPV : Z) : Z := (SPV - 512) - (SPV - 512) mod 32.
Lemma spb_props : forall SPV, SPV mod 16 = 0 -> SPV - 528 <= SPB SPV <= SPV - 512 /\ SPB SPV mod 32 = 0 /\ (SPV + -512) - (SPV + -512) mod 2^5 = SPB SPV.
Proof. intros SPV H. unfold SPB. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

Definition X2BSAVED (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition X2BSH : list cell :=
  [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 18446744073709551603)].

Definition X2BFRA (FF DT WK tl : Z) (jA jB jC jD jE : list byte) : list cell :=
  [CB 128 jA; C8 (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)); CB 32 jB; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF);
   CB 8 jC; C8 (Z_to_bv 64 (WK + 676)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 DT); CB 128 jD; C8 (Z_to_bv 64 WK); CB 40 jE; C8 (Z_to_bv 64 FF)].
Lemma X2BFRA_size : forall FF DT WK tl jA jB jC jD jE,
  length jA = 128%nat -> length jB = 32%nat -> length jC = 8%nat -> length jD = 128%nat -> length jE = 40%nat ->
  cells_size (X2BFRA FF DT WK tl jA jB jC jD jE) = 408%nat.
Proof. intros. reflexivity. Qed.
