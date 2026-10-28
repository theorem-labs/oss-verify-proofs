(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats Stdio Driver.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Printf_lib F_printf_iface Printf_stdio_iface
     F_stdio_write F_stdout_write F_fwritex_stderr F_fwritex_stdout F_stdio_flush F_vfprintf_stdout F_fprintf.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Export Printf_stdio_iface F_vsnprintf F_vfprintf_stdout F_fprintf.
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

  Lemma vfprintf_stderr_ok : vfprintf_stderr_stmt (St:=St).
  Proof. exact (vfprintf_stderr_proof fwritex_stderr_ok stdio_write_flush_ok). Qed.

  Lemma fprintf_gen_ok : fprintf_gen_stmt (St:=St).
  Proof. exact (fprintf_gen_proof fwritex_stderr_ok stdio_write_flush_ok). Qed.

  (* [comment removed for export] *)
  Lemma fprintf_diag_ok :
    forall (d : diag_msg)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (lo : Z) (canary : word),
      stderr_wfile m ->
      a0 = Z_to_bv 64 RSTDERR -> diag_args d m a1 a2 lo (bv_unsigned sp) ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - FPRINTF_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      Monad.implM usegs (s_diag (St:=St) d) st
            (fprintf_diag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m st)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x2b4648) fc None m (seg_rom usegs)).
  Proof. intros. eapply (fprintf_diag_proof St); eauto using fwritex_stderr_ok, stdio_write_flush_ok. Qed.

  Context (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis GS : forall x so, get_so (set_so so x) = so.
  Hypothesis SS : forall x so so', set_so so' (set_so so x) = set_so so' x.

  Lemma vfprintf_stdout_ok : vfprintf_stdout_stmt get_so set_so.
  Proof. exact (vfprintf_stdout_proof get_so set_so GS SS fwritex_stdout_ok). Qed.

  Lemma emit_printf_ok :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : St) (lo : Z) (canary : word),
      stdout_file m (get_so st) ->
      bv_unsigned a1 mod 2^32 = 0 ->
      stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EMIT_DEPTH) -> (GLOBALS_TOP <= lo) ->
      (bv_unsigned sp < 2^63) ->
      ssp_cells m canary -> mem_inv usegs m -> frm0 fc ->
      Monad.implM usegs (stdout_vprintf get_so set_so pieces_emit_0) st
            (emit_printf_post get_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xe1a64) fc None m (seg_rom usegs)).
  Proof. intros. eapply (emit_printf_proof St get_so set_so); eauto using fwritex_stdout_ok. Qed.
End Closed.
