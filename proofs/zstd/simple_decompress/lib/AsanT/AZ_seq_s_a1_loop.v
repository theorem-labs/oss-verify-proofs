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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_xat AZ_seq_s_a1_at AZ_seq_s_a1_dec AZ_seq_s_a1_rl1 AZ_seq_s_a1_upd AZ_seq_s_a1_chk AZ_seq_s_a1_rl2 AZ_seq_s_a1_exlit AZ_seq_s_a1_exmat AZ_seq_s_a1_exclose AZ_seq_s_a1_exloop AZ_seq_s_a1_slow AZ_seq_s_a1_tail.
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

Lemma a1_loop_step : forall P OEND LLO LEND LOCV K,
  sqs_static P OEND LLO LEND LOCV -> 1 <= K <= v_nbSeq P -> wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 LEND -> LEND + 32 <= OEND -> sqs_at_err P OEND LLO LEND LOCV -> sqs_at_err19 P OEND LLO LEND LOCV -> sqs_at_err20 P OEND LLO LEND LOCV -> sqs_at_lexit P OEND LLO LEND LOCV -> a1_brk P OEND LLO LEND LOCV K ->
  (forall K', 1 <= K' < K -> a1_head P OEND LLO LEND LOCV K') -> a1_head P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK HLBE HL32 A_err A_err19 A_err20 A_lexit A_brk IH.
  assert (IH1 : 1 < K -> a1_head P OEND LLO LEND LOCV (K - 1)) by (intros H1; apply IH; lia).
  pose proof (a1_tail2_ok P OEND LLO LEND LOCV K ST HK HLBE HL32 IH1 A_lexit) as A_tail2.
  pose proof (a1_tail_ok P OEND LLO LEND LOCV K ST HK HLBE HL32 A_err19 A_tail2) as A_tail.
  pose proof (a1_ctail_ok P OEND LLO LEND LOCV K ST HK HLBE HL32 A_err19 A_tail2) as A_ctail.
  pose proof (a1_ltail_ok P OEND LLO LEND LOCV K ST HK HLBE HL32 A_err19 A_tail2) as A_ltail.
  pose proof (a1_closeloop_ok P OEND LLO LEND LOCV K ST HK HLBE HL32 A_ltail) as A_closeloop.
  pose proof (a1_exec7 P OEND LLO LEND LOCV K ST HK HLBE HL32 A_ctail A_closeloop) as A_close8.
  pose proof (a1_exec6 P OEND LLO LEND LOCV K ST HK HLBE HL32 A_close8) as A_close.
  pose proof (a1_matloop_ok P OEND LLO LEND LOCV K ST HK HLBE HL32 A_tail) as A_matloop.
  pose proof (a1_exec3 P OEND LLO LEND LOCV K ST HK HLBE HL32 A_err20 A_close A_tail A_matloop) as A_match.
  pose proof (a1_litloop_ok P OEND LLO LEND LOCV K ST HK HLBE HL32 A_match) as A_litloop.
  pose proof (a1_exec1 P OEND LLO LEND LOCV K ST HK HLBE HL32 A_match A_litloop) as A_lit1.
  pose proof (a1_slow_ok P OEND LLO LEND LOCV K ST HK HLBE HL32 A_tail2 A_err19) as A_slow.
  pose proof (a1_exec0b P OEND LLO LEND LOCV K ST HK HLBE HL32 A_slow A_lit1) as A_execb.
  pose proof (a1_exec0 P OEND LLO LEND LOCV K ST HK HLBE HL32 A_slow A_execb A_brk) as A_exec.
  pose proof (a1_chk_ok P OEND LLO LEND LOCV K ST HK HLBE HL32 A_exec) as A_chk.
  pose proof (a1_reload2 P OEND LLO LEND LOCV K ST HK HLBE HL32 A_chk A_exec) as A_upd.
  pose proof (a1_update P OEND LLO LEND LOCV K ST HK HLBE HL32 A_upd A_execb A_slow A_brk) as A_rl1.
  pose proof (a1_reload1 P OEND LLO LEND LOCV K ST HK HLBE HL32 A_rl1) as A_dec.
  exact (a1_decode P OEND LLO LEND LOCV K ST HK HLBE HL32 A_dec).
Qed.

Theorem a1_loop : forall P OEND LLO LEND LOCV,
  sqs_static P OEND LLO LEND LOCV -> wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 LEND -> LEND + 32 <= OEND -> sqs_at_err P OEND LLO LEND LOCV -> sqs_at_err19 P OEND LLO LEND LOCV -> sqs_at_err20 P OEND LLO LEND LOCV -> sqs_at_lexit P OEND LLO LEND LOCV -> (forall K, 1 <= K <= v_nbSeq P -> a1_brk P OEND LLO LEND LOCV K) ->
  forall K, 1 <= K <= v_nbSeq P -> a1_head P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV ST HLBE HL32 A_err A_err19 A_err20 A_lexit A_brk.
  assert (ALL : forall n : nat, forall K, 1 <= K <= v_nbSeq P -> K <= Z.of_nat n -> a1_head P OEND LLO LEND LOCV K).
  { induction n as [|n IHn]; intros K HK HN; [exfalso; lia|].
    apply (a1_loop_step P OEND LLO LEND LOCV K ST HK HLBE HL32 A_err A_err19 A_err20 A_lexit (A_brk K HK)). intros K' HK'. apply IHn; lia. }
  intros K HK. apply (ALL (Z.to_nat K) K HK). lia.
Qed.

End CANSEC1.
