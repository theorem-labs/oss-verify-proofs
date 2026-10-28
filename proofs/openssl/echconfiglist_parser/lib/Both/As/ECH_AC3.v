(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_AStmt_C3
     ECH_AC3_ready ECH_AC3_newexW ECH_AC3_freeexW ECH_AC3_phase ECH_AC3_phase2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Theorem AC3_spec : asan_rt_hyps_x H -> getdefctx_fresh_stmt H -> C3_stmts H.
  Proof.
    intros HX GDF. unfold C3_stmts.
    split; [exact getdefctx_ready_spec|]. split; [exact (getdefctx_spec H HX GDF)|].
    split; [exact getglobal_ready_spec|]. split; [exact (getglobal_spec H HX GDF)|].
    split; [exact getandlock_spec|]. split; [exact (acnewex_ready_spec H HX)|].
    split; [exact (cnewex_spec H HX GDF)| exact (acfreeex_spec H HX)].
  Qed.
End W.
