(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_C3_stmt ECH_C7_stmt
     ECH_C7_read ECH_C7_rd ECH_C7_rd2 ECH_C7_newmembuf ECH_C7_biofree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.

  Theorem C7_spec : heap_sr_hyps_x H -> getdefctx_fresh_stmt H -> C7_stmts H.
  Proof.
    intros HX CERTA. unfold C7_stmts.
    split; [exact memread_spec|]. split; [exact memctrl_spec|]. split; [exact bioctrl_mem_spec|]. split; [exact bioeof_mem_spec|].
    split; [exact breadconv_mem_spec|]. split; [exact readintern_mem_spec|]. split; [exact bioreadex_mem_spec|]. split; [exact bioread_mem_spec|].
    split; [exact (newmembuf_spec H HX CERTA)| exact (biofree_spec H (proj1 HX))].
  Qed.
End W.
