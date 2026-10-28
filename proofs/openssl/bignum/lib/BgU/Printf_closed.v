(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats Stdio Driver.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Printf_lib F_printf_iface Printf_stdio_iface F_stdio_write F_stdout_write F_fwritex_stderr F_fwritex_stdout F_stdio_flush F_vfprintf_stdout F_fprintf.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Export Printf_stdio_iface F_vsnprintf F_vfprintf_stdout F_fprintf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma fwritex_stderr_ok : fwritex_stderr_stmt.
Proof. apply fwritex_stderr_proof. intros St. apply (@stdio_write_proof St). Qed.

Lemma stdio_write_flush_ok : stdio_write_flush_stmt.
Proof. apply stdio_write_flush_proof. intros St. apply (@stdio_write_proof St). Qed.

Lemma fwritex_stdout_ok : fwritex_stdout_stmt.
Proof. apply fwritex_stdout_proof. intros St get_so set_so GS SS. apply (stdout_writefn_proof get_so set_so GS SS). Qed.

Section Closed.
  Context {St : Type}.

  Context (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.

  End Closed.
