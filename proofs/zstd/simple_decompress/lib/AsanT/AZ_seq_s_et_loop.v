(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_xat AZ_seq_s_a2_at AZ_seq_s_et_at AZ_seq_s_et_exlit AZ_seq_s_et_exmat AZ_seq_s_et_exclose AZ_seq_s_et_exloop AZ_seq_s_et_slow AZ_seq_s_et_tail.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac kxa_norm ::= unfold shspan in *.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac kxl_hyp ::= lazymatch goal with |- ?G => first [ match goal with H : G |- _ => exact H end | match goal with H : rheld G |- _ => exact H end ] end.
Ltac kxa_rng ::= first [ kxl_hyp | kxa_rng0 ].
Ltac kxl_rng ::=
  first [ kxl_hyp
        | lazymatch goal with |- rng ?RNG ?A ?N => match goal with H : rng RNG ?A0 ?N0 |- _ => apply (rng_sub' RNG A0 N0 A N H); solve [kxl_lia_small] end end
        | kx_rng ].

Section CANSEC1. Context {rc : runConstT}.

Lemma et_run : forall P OEND LLO LEND LOCV K,
  sqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P -> LLO = v_DCTX P + 30372 -> sqs_at_err P OEND LLO LEND LOCV -> sqs_at_err20 P OEND LLO LEND LOCV -> sqs_at_lexit P OEND LLO LEND LOCV ->
  (1 < K -> a2_head P OEND LLO LEND LOCV (K - 1)) -> et_execb P OEND LLO LEND LOCV K /\ et_slow P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK HLLO A_err A_err20 A_lexit IH1.
  pose proof (et_tail2_ok P OEND LLO LEND LOCV K ST HK HLLO IH1 A_lexit) as A_tail2.
  pose proof (et_tail_ok P OEND LLO LEND LOCV K ST HK HLLO A_err A_tail2) as A_tail.
  pose proof (et_ctail_ok P OEND LLO LEND LOCV K ST HK HLLO A_err A_tail2) as A_ctail.
  pose proof (et_closeloop_ok P OEND LLO LEND LOCV K ST HK HLLO A_ctail) as A_closeloop.
  pose proof (et_exec7 P OEND LLO LEND LOCV K ST HK HLLO A_ctail A_closeloop) as A_close8.
  pose proof (et_exec6 P OEND LLO LEND LOCV K ST HK HLLO A_close8) as A_close.
  pose proof (et_matloop_ok P OEND LLO LEND LOCV K ST HK HLLO A_tail) as A_matloop.
  pose proof (et_exec3 P OEND LLO LEND LOCV K ST HK HLLO A_err20 A_close A_tail A_matloop) as A_match.
  pose proof (et_litloop_ok P OEND LLO LEND LOCV K ST HK HLLO A_match) as A_litloop.
  pose proof (et_exec1 P OEND LLO LEND LOCV K ST HK HLLO A_match A_litloop) as A_lit1.
  pose proof (et_slow_ok P OEND LLO LEND LOCV K ST HK HLLO A_tail2 A_err) as A_slow.
  pose proof (et_exec0b P OEND LLO LEND LOCV K ST HK HLLO A_slow A_lit1) as A_execb.
  split; [exact A_execb | exact A_slow].
Qed.

End CANSEC1.
