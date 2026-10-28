(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_AStmt_C4
     ECH_AC4_egs ECH_AC4_seterr ECH_AC4_new ECH_AC4_debug ECH_AC4_debugW ECH_AC4_clear ECH_AC4_clearW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Theorem AC4_spec : asan_rt_hyps_x H -> egs_fresh_stmt H -> C4_stmts H.
  Proof.
    intros HX O3. pose proof (aegs_spec H HX O3) as EGS. unfold C4_stmts.
    split; [exact (aegs_ready_spec H HX)|]. split; [exact EGS|]. split; [exact (aerrnew_spec H HX EGS)|].
    split; [exact (aerrdebug_spec H HX)|]. split; [exact (aerrseterr_spec H HX)| exact (aerrclear_spec H HX EGS)].
  Qed.
End W.
