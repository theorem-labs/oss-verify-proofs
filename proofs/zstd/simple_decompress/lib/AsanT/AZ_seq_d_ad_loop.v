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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_xat AZ_seq_d_ad_at AZ_seq_d_ad_dec AZ_seq_d_ad_rl1 AZ_seq_d_ad_upd AZ_seq_d_ad_rl2 AZ_seq_d_ad_exlit AZ_seq_d_ad_exmat AZ_seq_d_ad_exclose AZ_seq_d_ad_exloop AZ_seq_d_ad_slow AZ_seq_d_ad_tail.
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

Lemma ad_loop_step : forall P OEND LLO LEND LOCV K,
  sqd_static P OEND LLO LEND LOCV -> 1 <= K <= w_nbSeq P -> sqd_at_err P OEND LLO LEND LOCV -> sqd_at_err20 P OEND LLO LEND LOCV -> sqd_at_lexit P OEND LLO LEND LOCV ->
  (forall K', 1 <= K' < K -> ad_head P OEND LLO LEND LOCV K') -> ad_head P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV K ST HK A_err A_err20 A_lexit IH.
  assert (IH1 : 1 < K -> ad_head P OEND LLO LEND LOCV (K - 1)) by (intros H1; apply IH; lia).
  pose proof (ad_tail2_ok P OEND LLO LEND LOCV K ST HK IH1 A_lexit) as A_tail2.
  pose proof (ad_tail_ok P OEND LLO LEND LOCV K ST HK A_err A_tail2) as A_tail.
  pose proof (ad_ctail_ok P OEND LLO LEND LOCV K ST HK A_err A_tail2) as A_ctail.
  pose proof (ad_closeloop_ok P OEND LLO LEND LOCV K ST HK A_ctail) as A_closeloop.
  pose proof (ad_exec7 P OEND LLO LEND LOCV K ST HK A_ctail A_closeloop) as A_close8.
  pose proof (ad_exec6 P OEND LLO LEND LOCV K ST HK A_close8) as A_close.
  pose proof (ad_matloop_ok P OEND LLO LEND LOCV K ST HK A_tail) as A_matloop.
  pose proof (ad_exec3 P OEND LLO LEND LOCV K ST HK A_err20 A_close A_tail A_matloop) as A_match.
  pose proof (ad_litloop_ok P OEND LLO LEND LOCV K ST HK A_match) as A_litloop.
  pose proof (ad_exec1 P OEND LLO LEND LOCV K ST HK A_match A_litloop) as A_lit1.
  pose proof (ad_slow_ok P OEND LLO LEND LOCV K ST HK A_tail2 A_err) as A_slow.
  pose proof (ad_exec0b P OEND LLO LEND LOCV K ST HK A_slow A_lit1) as A_execb.
  pose proof (ad_exec0 P OEND LLO LEND LOCV K ST HK A_slow A_execb) as A_exec.
  pose proof (ad_reload2 P OEND LLO LEND LOCV K ST HK A_exec A_execb A_slow) as A_upd.
  pose proof (ad_update P OEND LLO LEND LOCV K ST HK A_upd A_exec) as A_rl1.
  pose proof (ad_reload1 P OEND LLO LEND LOCV K ST HK A_rl1) as A_dec.
  exact (ad_decode P OEND LLO LEND LOCV K ST HK A_dec).
Qed.

Theorem ad_loop : forall P OEND LLO LEND LOCV,
  sqd_static P OEND LLO LEND LOCV -> sqd_at_err P OEND LLO LEND LOCV -> sqd_at_err20 P OEND LLO LEND LOCV -> sqd_at_lexit P OEND LLO LEND LOCV ->
  forall K, 1 <= K <= w_nbSeq P -> ad_head P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV ST A_err A_err20 A_lexit.
  assert (ALL : forall n : nat, forall K, 1 <= K <= w_nbSeq P -> K <= Z.of_nat n -> ad_head P OEND LLO LEND LOCV K).
  { induction n as [|n IHn]; intros K HK HN; [exfalso; lia|].
    apply (ad_loop_step P OEND LLO LEND LOCV K ST HK A_err A_err20 A_lexit). intros K' HK'. apply IHn; lia. }
  intros K HK. apply (ALL (Z.to_nat K) K HK). lia.
Qed.

End CANSEC1.
