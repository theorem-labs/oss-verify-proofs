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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_xat AZ_seq_l_la_at AZ_seq_l_la_at2 AZ_seq_l_la_dtbl AZ_seq_l_la_dec AZ_seq_l_la_rl1 AZ_seq_l_la_upd AZ_seq_l_la_rl2 AZ_seq_l_la_store.
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

Theorem la_loop : forall P OEND LLO LEND LOCV, sql_static P OEND LLO LEND LOCV -> la_done P OEND LLO LEND LOCV ->
  forall K, 1 <= K <= l_nbSeq P -> la_head P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV ST DONE.
  assert (STEP : forall K, 1 <= K <= l_nbSeq P -> (forall K', 1 <= K' < K -> la_head P OEND LLO LEND LOCV K') -> la_head P OEND LLO LEND LOCV K).
  { intros K HK IH.
    apply (la_dtable P OEND LLO LEND LOCV K ST HK).
    apply (la_decode P OEND LLO LEND LOCV K ST HK).
    apply (la_reload1 P OEND LLO LEND LOCV K ST HK).
    apply (la_update P OEND LLO LEND LOCV K ST HK).
    - apply (la_reload2 P OEND LLO LEND LOCV K ST HK). apply (la_store_ok P OEND LLO LEND LOCV K ST HK IH DONE).
    - apply (la_store_ok P OEND LLO LEND LOCV K ST HK IH DONE). }
  intros K HK.
  assert (IND : forall n K, 1 <= K <= l_nbSeq P -> K - 1 <= Z.of_nat n -> la_head P OEND LLO LEND LOCV K).
  { induction n as [|n IHn]; intros K0 HK0 Hn.
    - apply STEP; [exact HK0|]. intros K' HK'. exfalso. clear - HK0 Hn HK'. lia.
    - apply STEP; [exact HK0|]. intros K' HK'. apply IHn; [clear - HK0 HK'; lia | clear - Hn HK'; lia]. }
  apply (IND (Z.to_nat K) K); [exact HK | clear - HK; lia].
Qed.

End CANSEC1.
