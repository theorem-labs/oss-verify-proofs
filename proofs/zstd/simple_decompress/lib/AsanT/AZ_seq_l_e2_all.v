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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_xat AZ_seq_l_xat2 AZ_seq_l_e2_at AZ_seq_l_lm_at AZ_seq_l_lf_at AZ_seq_l_e2_exlit AZ_seq_l_e2_exmat AZ_seq_l_e2_excla AZ_seq_l_e2_exclb AZ_seq_l_e2_exclc AZ_seq_l_e2_exclose AZ_seq_l_e2_exloop AZ_seq_l_e2_slow AZ_seq_l_e2_tails.
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
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.

Lemma e2_exec_ok : forall P OEND LLO LEND LOCV K, sql_static P OEND LLO LEND LOCV -> 1 <= K <= l_nbSeq P ->
  sql_at_err P OEND LLO LEND LOCV -> sql_at_err20 P OEND LLO LEND LOCV -> lf_latch2 P OEND LLO LEND LOCV K -> e2_exec P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK A_err A_errx A_latch.
  pose proof (e2_tail_ok P OEND LLO LEND LOCV K ST HK A_err A_latch) as A_tail.
  pose proof (e2_ltail_ok P OEND LLO LEND LOCV K ST HK A_err A_latch) as A_ltail.
  pose proof (e2_stail_ok P OEND LLO LEND LOCV K ST HK A_err A_latch) as A_stail.
  pose proof (e2_closeloop_ok P OEND LLO LEND LOCV K ST HK A_ltail) as A_closeloop.
  pose proof (e2_exec7 P OEND LLO LEND LOCV K ST HK A_ltail A_closeloop) as A_close8.
  pose proof (e2_exec6 P OEND LLO LEND LOCV K ST HK A_close8) as A_close.
  pose proof (e2_matloop_ok P OEND LLO LEND LOCV K ST HK A_tail) as A_matloop.
  pose proof (e2_exec3 P OEND LLO LEND LOCV K ST HK A_errx A_close A_tail A_matloop) as A_match.
  pose proof (e2_litloop_ok P OEND LLO LEND LOCV K ST HK A_match) as A_litloop.
  pose proof (e2_exec1 P OEND LLO LEND LOCV K ST HK A_match A_litloop) as A_lit1.
  pose proof (e2_slow_ok P OEND LLO LEND LOCV K ST HK A_stail) as A_slow.
  pose proof (e2_exec0b P OEND LLO LEND LOCV K ST HK A_slow A_lit1) as A_execb.
  exact (e2_exec0 P OEND LLO LEND LOCV K ST HK A_slow A_execb).
Qed.

End CANSEC1.
