(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_ARep ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9
  ECH_AC6_acc ECH_AC7_bioread ECH_AC8_small ECH_AC8_update ECH_AC8_final ECH_AC9_ctrl ECH_AC9_push ECH_AC9_read ECH_AC9_bionew ECH_AC9_bioread ECH_AC9_biofreeall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Theorem AC9_spec : asan_rt_hyps_x H -> cnewex_stmt H -> cfreeex_stmt H -> C9_stmts H.
  Proof.
    intros HX CNX CFX. pose proof (proj1 HX) as HH. unfold C9_stmts.
    pose proof (abioread_mem_spec H HX) as BRMS. pose proof (abiogetdata_spec H) as GDS. pose proof (abionext_spec H) as NXS.
    pose proof (abioclearflags_spec H) as CFS. pose proof (abiotestflags_spec H) as TFS.
    pose proof (adecupdate_spec H) as DUS. pose proof (adecfinal_spec H) as DFS. pose proof (adecinit_spec H) as DIS.
    split; [eapply abionew_b64_spec; assumption|].
    split; [eapply abiopush_spec; assumption|].
    split; [eapply abioread_b64_spec; assumption|].
    split; [eapply abiofreeall_spec; assumption| eapply ab64ctrl_spec; assumption].
  Qed.
End W.

(* [comment removed for export] *)
