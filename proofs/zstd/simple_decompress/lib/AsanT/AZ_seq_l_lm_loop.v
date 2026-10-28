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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_tkit AZ_seq_l_xat AZ_seq_l_xat2 AZ_seq_l_md_at AZ_seq_l_lm_at AZ_seq_l_lm_at1 AZ_seq_l_n1_at AZ_seq_l_s1_at AZ_seq_l_e1_at AZ_seq_l_md_dtbl AZ_seq_l_md_dec AZ_seq_l_md_rl1 AZ_seq_l_md_upd AZ_seq_l_md_rl2 AZ_seq_l_lm_mode AZ_seq_l_lm_split AZ_seq_l_lm_latch AZ_seq_l_lm_latch1 AZ_seq_l_n1_all AZ_seq_l_s1_all AZ_seq_l_e1_all AZ_seq_l_t1_all.
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

Section MAINLOOP.
Variable P : slq.

(* [comment removed for export] *)
Lemma lm_step : forall OEND LLO LEND LOCV K, sql_static P OEND LLO LEND LOCV -> 1 <= K <= l_nbSeq P ->
  (LOCV = 2 -> wnth (l_ws P) H5_litBufferEnd = Z_to_bv 64 LEND) ->
  sql_at_err P OEND LLO LEND LOCV -> sql_at_err20 P OEND LLO LEND LOCV -> sql_at_err20d P OEND LLO LEND LOCV -> sql_at_e70 P OEND LLO LEND LOCV -> lm_done P OEND LLO LEND LOCV 1 ->
  sql_at_err P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 -> sql_at_err20 P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 -> sql_at_err20d P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 -> sql_at_e70 P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 -> lm_done P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 1 ->
  (1 < K -> md_head P OEND LLO LEND LOCV (K - 1)) -> (1 < K -> md_head P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 (K - 1)) ->
  md_head P OEND LLO LEND LOCV K.
Proof.
  intros OEND LLO LEND LOCV K ST HK HLBE ERR ERR20 ERR20D E70 DONE ERR2 ERR202 ERR202D E702 DONE2 IH IH2.
  pose proof (sql_static_switch P OEND LLO LEND LOCV ST) as ST2.
  pose proof (lm_latch_ok P OEND LLO LEND LOCV K ST HK IH DONE) as LATCH.
  pose proof (lm_latch1_ok P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 K ST2 HK IH2 DONE2) as LATCH1.
  pose proof (n1_exec_ok P OEND LLO LEND LOCV K ST HK ERR ERR20 LATCH) as XN1.
  pose proof (s1_exec_ok P OEND LLO LEND LOCV K ST HK ERR ERR20D LATCH) as XS1.
  pose proof (e1_exec_ok P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 K ST2 HK ERR2 ERR202 LATCH1) as XE1.
  pose proof (t1_brk_all P OEND LLO LEND LOCV K ST HK E70 XE1) as XT1.
  pose proof (lm_mnorm_ok P OEND LLO LEND LOCV K ST HK XN1) as MN.
  assert (MS : lm_msplit P OEND LLO LEND LOCV K).
  { destruct (Z.eq_dec LOCV 2) as [EL|NL].
    - exact (lm_msplit_ok P OEND LLO LEND LOCV K ST HK (HLBE EL) XS1 XT1).
    - unfold lm_msplit. intros. exfalso. apply NL. assumption. }
  pose proof (lm_mode_ok P OEND LLO LEND LOCV K ST HK MN MS) as MX.
  pose proof (md_reload2 P OEND LLO LEND LOCV K ST HK MX) as MU.
  pose proof (md_update P OEND LLO LEND LOCV K ST HK MU MX) as MR1.
  pose proof (md_reload1 P OEND LLO LEND LOCV K ST HK MR1) as MDEC.
  pose proof (md_decode P OEND LLO LEND LOCV K ST HK MDEC) as MTBL.
  exact (md_dtable P OEND LLO LEND LOCV K ST HK MTBL).
Qed.

Theorem lm_loop : forall OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV ->
  (LOCV = 2 -> wnth (l_ws P) H5_litBufferEnd = Z_to_bv 64 LEND) ->
  sql_at_err P OEND LLO LEND LOCV -> sql_at_err20 P OEND LLO LEND LOCV -> sql_at_err20d P OEND LLO LEND LOCV -> sql_at_e70 P OEND LLO LEND LOCV -> lm_done P OEND LLO LEND LOCV 1 ->
  sql_at_err P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 -> sql_at_err20 P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 -> sql_at_err20d P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 -> sql_at_e70 P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 -> lm_done P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0 1 ->
  forall K, 1 <= K <= l_nbSeq P -> md_head P OEND LLO LEND LOCV K.
Proof.
  intros OEND LLO LEND LOCV ST HLBE ERR ERR20 ERR20D E70 DONE ERR2 ERR202 ERR202D E702 DONE2 K HK.
  assert (MAIN : forall k OEND' LLO' LEND' LOCV', sql_static P OEND' LLO' LEND' LOCV' ->
    (LOCV' = 2 -> wnth (l_ws P) H5_litBufferEnd = Z_to_bv 64 LEND') ->
    sql_at_err P OEND' LLO' LEND' LOCV' -> sql_at_err20 P OEND' LLO' LEND' LOCV' -> sql_at_err20d P OEND' LLO' LEND' LOCV' -> sql_at_e70 P OEND' LLO' LEND' LOCV' -> lm_done P OEND' LLO' LEND' LOCV' 1 ->
    sql_at_err P OEND' (l_DCTX P + 30372) (l_DCTX P + 95908) 0 -> sql_at_err20 P OEND' (l_DCTX P + 30372) (l_DCTX P + 95908) 0 -> sql_at_err20d P OEND' (l_DCTX P + 30372) (l_DCTX P + 95908) 0 -> sql_at_e70 P OEND' (l_DCTX P + 30372) (l_DCTX P + 95908) 0 -> lm_done P OEND' (l_DCTX P + 30372) (l_DCTX P + 95908) 0 1 ->
    forall K', 1 <= K' <= l_nbSeq P -> K' <= Z.of_nat k -> md_head P OEND' LLO' LEND' LOCV' K').
  { induction k as [|k IHk]; intros OEND' LLO' LEND' LOCV' ST' HLBE' ERR' ERR20' ERR20D' E70' DONE' ERR2' ERR202' ERR202D' E702' DONE2' K' HK' HKk.
    - exfalso. clear - HK' HKk. lia.
    - apply (lm_step OEND' LLO' LEND' LOCV' K' ST' HK' HLBE' ERR' ERR20' ERR20D' E70' DONE' ERR2' ERR202' ERR202D' E702' DONE2').
      + intro HK1. apply (IHk OEND' LLO' LEND' LOCV' ST' HLBE' ERR' ERR20' ERR20D' E70' DONE' ERR2' ERR202' ERR202D' E702' DONE2'); clear - HK' HKk HK1; lia.
      + intro HK1. apply (IHk OEND' (l_DCTX P + 30372) (l_DCTX P + 95908) 0 (sql_static_switch P _ _ _ _ ST') ltac:(clear; intro E02; exfalso; lia) ERR2' ERR202' ERR202D' E702' DONE2' ERR2' ERR202' ERR202D' E702' DONE2'); clear - HK' HKk HK1; lia. }
  exact (MAIN (Z.to_nat K) OEND LLO LEND LOCV ST HLBE ERR ERR20 ERR20D E70 DONE ERR2 ERR202 ERR202D E702 DONE2 K HK ltac:(clear - HK; lia)).
Qed.

End MAINLOOP.

End CANSEC1.
