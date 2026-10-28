(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition AGOT_X2PC : Z := 0xc7f98.      (* [comment removed for export] *)
Definition X2_MAGIC_LIVE : Z := 0x41b58ab3.
Definition X2_MAGIC_DEAD : Z := 0x45e0360e.
Definition X2_DESC : Z := 0x16f2f.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition SPA2 (SPV : Z) : Z := (SPV - 832) - (SPV - 832) mod 32.
Lemma spa2_props : forall SPV, SPV mod 16 = 0 -> SPV - 848 <= SPA2 SPV <= SPV - 832 /\ SPA2 SPV mod 32 = 0 /\ (SPV + -832) - (SPV + -832) mod 2^5 = SPA2 SPV.
Proof. intros SPV H. unfold SPA2. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition X2SAVED (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition X2SH : list cell :=
  [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
   C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 18446744073709551602); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 18446744073709551603)].

(* [comment removed for export] *)
Definition X2FRA (FF DT WK hdw : Z) (jA jB jC jD : list byte) : list cell :=
  [CB 56 jA; C8 (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)); C8 (Z_to_bv 64 hdw); CB 24 jB; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); CB 8 jC;
   C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 WK); CB 576 jD; C8 (Z_to_bv 64 FF)].
Lemma X2FRA_size : forall FF DT WK hdw jA jB jC jD,
  length jA = 56%nat -> length jB = 24%nat -> length jC = 8%nat -> length jD = 576%nat ->
  cells_size (X2FRA FF DT WK hdw jA jB jC jD) = 728%nat.
Proof. intros. reflexivity. Qed.
