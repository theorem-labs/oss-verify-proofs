(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_AStmt_C4 ECH_AStmt_C11
     ECH_AC11_find ECH_AC11_fail ECH_AC11_suitebad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Theorem AC11_spec : asan_rt_hyps H -> araise_stmt H -> C11_stmts H.
  Proof.
    intros HH RAISE. unfold C11_stmts.
    split; [exact ahfind_found_kem|]. split; [exact (ahfind_fail_kem H HH RAISE)|].
    split; [exact ahfind_found_kdf|]. split; [exact (ahfind_fail_kdf H HH RAISE)|].
    split; [exact ahfind_found_aead|]. split; [exact (ahfind_fail_aead H HH RAISE)|].
    split; [exact asuiteok_spec| exact (asuitebad_spec H HH RAISE)].
  Qed.
End W.
