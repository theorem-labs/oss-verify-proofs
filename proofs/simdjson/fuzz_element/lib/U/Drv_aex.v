(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Drv_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation usegs := Image.usegs.

Definition aex_addr (a : Z) : Prop :=
  (0x10f5d0 <= a < 0x10f5d1) \/ (0x10f5d4 <= a < 0x10f5dc) \/ (0x10f5e0 <= a < 0x10f5f8) \/ (0x10f6f0 <= a < 0x10f6f8)
  \/ (0xedaa0 <= a < 0xedaa1) \/ (0xedaa4 <= a < 0xedaa5).

Lemma aex_cells_agree : forall (P : Z -> Prop) m m' k,
  agree_on P m m' -> (forall a, aex_addr a -> P a) -> aex_cells m k -> aex_cells m' k.
Proof.
  intros P m m' k AG HP (A1 & A2 & A3 & A4 & A5 & A6). unfold aex_cells in *.
  split; [| split; [| split; [| split; [| split]]]];
    (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; apply HP; unfold aex_addr; cbn in Ha; lia]).
Qed.

Lemma aex_inv_agree : forall (P : Z -> Prop) m m',
  agree_on P m m' -> (forall a, aex_addr a -> P a) -> aex_inv m -> aex_inv m'.
Proof. intros P m m' AG HP (k & Hk & C). exists k. split; [exact Hk|]. eapply aex_cells_agree; [exact AG| exact HP| exact C]. Qed.
