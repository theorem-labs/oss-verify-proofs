(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Exit Drv_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation usegs := Image.usegs.

Definition aex_addr (a : Z) : Prop :=
  (0x115590 <= a < 0x1156c8) \/ (0xf32a0 <= a < 0xf32a1) \/ (0xf32a4 <= a < 0xf32a5).

Lemma aex_tbl_agree_k : forall (P : Z -> Prop) m m' n,
  agree_on P m m' -> (forall a, aex_addr a -> P a) -> aex_tbl m n -> aex_tbl m' n.
Proof.
  intros P m m' n AG HP H. eapply aex_tbl_agree; [exact AG| | exact H].
  intros a Ha. apply HP. left. unfold aex_tbl_addr, AEX in Ha. exact Ha.
Qed.

Lemma aex_cells_agree : forall (P : Z -> Prop) m m' k,
  agree_on P m m' -> (forall a, aex_addr a -> P a) -> aex_cells m k -> aex_cells m' k.
Proof.
  intros P m m' k AG HP (A1 & A2 & A3). unfold aex_cells.
  split; [eapply aex_tbl_agree_k; [exact AG| exact HP| exact A1]|].
  unfold RLATCH, RINCB in *.
  split; (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; apply HP; unfold aex_addr; cbn in Ha; lia]).
Qed.

Lemma aex_inv_agree : forall (P : Z -> Prop) m m',
  agree_on P m m' -> (forall a, aex_addr a -> P a) -> aex_inv m -> aex_inv m'.
Proof. intros P m m' AG HP (k & Hk & C). exists k. split; [exact Hk|]. eapply aex_cells_agree; [exact AG| exact HP| exact C]. Qed.

Lemma aex_mid_agree : forall (P : Z -> Prop) m m',
  agree_on P m m' -> (forall a, aex_addr a -> P a) -> aex_mid m -> aex_mid m'.
Proof.
  intros P m m' AG HP (A1 & A2 & A3). unfold aex_mid.
  split; [eapply aex_tbl_agree_k; [exact AG| exact HP| exact A1]|].
  unfold RLATCH, RINCB in *.
  split; (eapply rw_cells_agree; [exact AG| eassumption| intros a Ha; apply HP; unfold aex_addr; cbn in Ha; lia]).
Qed.
