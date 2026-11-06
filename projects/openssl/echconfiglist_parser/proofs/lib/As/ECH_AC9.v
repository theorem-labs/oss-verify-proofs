(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_ARep ECH_AStmt_C1 ECH_AStmt_C3 ECH_AStmt_C6 ECH_AStmt_C7 ECH_AStmt_C8 ECH_AStmt_C9
  ECH_AC6_acc ECH_AC7_bioread ECH_AC8_small ECH_AC8_update ECH_AC8_final ECH_AC9_ctrl ECH_AC9_push ECH_AC9_read ECH_AC9_bionew ECH_AC9_bioread ECH_AC9_biofreeall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Theorem AC9_spec : asan_rt_hyps_x H -> cnewex_stmt H -> cfreeex_stmt H -> C9_stmts H.
  Proof.
    intros HX CNX CFX. pose proof (proj1 HX) as HH. unfold C9_stmts.
    split; [exact (abionew_b64_spec H HX CNX)|].
    split; [exact (abiopush_spec H)|].
    split; [exact (abioread_b64_spec H HX (abioread_mem_spec H HX) (abiogetdata_spec H) (abionext_spec H) (abioclearflags_spec H) (abiotestflags_spec H)
                                    (adecupdate_spec H) (adecfinal_spec H) (adecinit_spec H))|].
    split; [exact (abiofreeall_spec H HH CFX)| exact (ab64ctrl_spec H)].
  Qed.
End W.

(* [comment removed for export] *)
