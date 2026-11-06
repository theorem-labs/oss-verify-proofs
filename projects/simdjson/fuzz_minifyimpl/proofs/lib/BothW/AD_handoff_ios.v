(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import MainExport MainFactsBoth.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg ARepInit_kit F_syscalls StdioFiles Stdio_kit AExit F_module_dtor_pre AD_handoff_md AD_hokit AIos_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Handoff.
  Variables (V : nat -> Z) (m : word -> option byte).
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Ltac go := repeat match goal with |- _ /\ _ => split end; ho_cells V m HM.

  (* [comment removed for export] *)
  Lemma ios_char_shared_init : ios_char_shared m.  Proof. unfold ios_char_shared. go. Qed.
  Lemma ios_cout_init : ios_cout m.                Proof. unfold ios_cout. go. Qed.
  Lemma ios_clog_init : ios_clog m.                Proof. unfold ios_clog. go. Qed.
  Lemma ios_wide_shared_init : ios_wide_shared m.  Proof. unfold ios_wide_shared. go. Qed.
  Lemma ios_wcout_init : ios_wcout m.              Proof. unfold ios_wcout. go. Qed.
  Lemma ios_wclog_init : ios_wclog m.              Proof. unfold ios_wclog. go. Qed.

End Handoff.
End CANSEC1.
