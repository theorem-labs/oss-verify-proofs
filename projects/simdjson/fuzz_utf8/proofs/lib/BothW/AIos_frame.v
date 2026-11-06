(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import F_syscalls StdioFiles Stdio_kit BImg MonadF AIos_iface AIos_dtor.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Lemma disjoint_from_Forall' : forall (P : Z * Z -> Prop) W A n,
  Forall P W -> (forall iv, P iv -> A + n <= fst iv \/ snd iv <= A) -> disjoint_from W A n.
Proof.
  intros P W A n HF HP. induction HF as [|[lo hi] W' Hx HF IH]; cbn; [exact I|].
  split; [exact (HP _ Hx) | exact IH].
Qed.

(* [comment removed for export] *)
Definition ios_wr_ok (iv : Z * Z) : Prop :=
  0x6afae0 <= fst iv \/ (RSTDERR <= fst iv /\ snd iv <= 0x6adba8) \/ (0x6afa60 <= fst iv /\ snd iv <= 0x6afad8).   (* [comment removed for export] *)

Lemma ios_cells_frame : forall W m m', ios_cells m -> munch W m m' -> wmono bsegs m m' -> Forall ios_wr_ok W -> ios_cells m'.
Proof.
  intros W m m' IOS MU WM HW.
  assert (T : forall A cs, rw_cells bsegs m A cs ->
                (forall iv, ios_wr_ok iv -> A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) -> rw_cells bsegs m' A cs).
  { intros A cs H HD. eapply rw_cells_transport; [exact H | exact MU | exact WM |]. eapply disjoint_from_Forall'; [exact HW | exact HD]. }
  unfold ios_cells, ios_char_shared, ios_cout, ios_clog, ios_wide_shared, ios_wcout, ios_wclog in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end;
    (eapply T; [eassumption | cbn [cells_size csize Nat.add]; unfold ios_wr_ok; intros iv [X|[[X Y]|[X Y]]]; lia]).
Qed.
End CANSEC1.
