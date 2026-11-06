(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Layout Exit Drv_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation psegs := Image.psegs.

Definition aex_addr (a : Z) : Prop :=
  (0xffab0 <= a < 0xffab1) \/ (0xffab4 <= a < 0xffabc) \/ (0xffac0 <= a < 0xffad8) \/ (0xffbd0 <= a < 0xffbd8)
  \/ (0xddf80 <= a < 0xddf81) \/ (0xddf84 <= a < 0xddf85).

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
