(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_ARep ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7
  ECH_AC7_rd ECH_AC7_read ECH_AC7_rd2 ECH_AC7_bioread ECH_AC7_newmembuf ECH_AC7_biofreeint ECH_AC7_biofree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Theorem AC7_spec : asan_rt_hyps_x H -> cnewex_stmt H -> cfreeex_stmt H -> C7_stmts H.
  Proof.
    intros HX CNX CFX. pose proof (proj1 HX) as HH. unfold C7_stmts.
    split; [exact (amemread_spec H HH)|]. split; [exact (amemctrl_spec H)|]. split; [exact (abioctrl_mem_spec H)|]. split; [exact (abioeof_mem_spec H)|].
    split; [exact (abreadconv_mem_spec H HH)|]. split; [exact (areadintern_mem_spec H HH)|]. split; [exact (abioreadex_mem_spec H HH)|].
    split; [exact (abioread_mem_spec H HX)|]. split; [exact (anewmembuf_spec H HH CNX)|]. split; [exact (abiofreeint_mem_spec H HH CFX)| exact (abiofree_spec H HH CFX)].
  Qed.
End W.
