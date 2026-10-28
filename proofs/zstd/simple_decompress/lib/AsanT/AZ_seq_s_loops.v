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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_akit3 AZ_seq_s_xat AZ_seq_s_tkit AZ_seq_s_a1_at AZ_seq_s_a2_at AZ_seq_s_et_at AZ_seq_s_tr_at AZ_seq_s_a1_loop AZ_seq_s_a2_loop AZ_seq_s_et_loop AZ_seq_s_tr1 AZ_seq_s_sw.
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

Theorem sqs_loops : forall P OEND LLO LEND,
  sqs_static P OEND LLO LEND 2 -> wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 LEND -> LEND + 32 <= OEND ->
  sqs_at_err P OEND LLO LEND 2 -> sqs_at_err19 P OEND LLO LEND 2 -> sqs_at_err10 P OEND LLO LEND 2 -> sqs_at_err20 P OEND LLO LEND 2 -> sqs_at_lexit P OEND LLO LEND 2 ->
  sqs_at_err P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 -> sqs_at_err20 P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 -> sqs_at_lexit P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 ->
  forall K, 1 <= K <= v_nbSeq P -> a1_head P OEND LLO LEND 2 K.
Proof.
  intros P OEND LLO LEND ST HLBE HL32 A_err A_err19 A_err10 A_err20 A_lexit B_err B_err20 B_lexit.
  pose proof (sqs_static_switch P OEND LLO LEND ST) as ST2.
  pose proof (a2_loop P OEND _ _ 0 ST2 B_err B_err20 B_lexit) as HB.
  assert (HET : forall K, 1 <= K <= v_nbSeq P -> et_execb P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 K /\ et_slow P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 K).
  { intros K HK. apply (et_run P OEND _ _ 0 K ST2 HK eq_refl B_err B_err20 B_lexit). intros H1. apply HB. lia. }
  apply (a1_loop P OEND LLO LEND 2 ST HLBE HL32 A_err A_err19 A_err20 A_lexit).
  intros K HK. destruct (HET K HK) as (E1 & E2).
  exact (tr_brk_ok P OEND LLO LEND 2 K ST HK HLBE HL32 eq_refl A_err10 (tr_switch P OEND LLO LEND 2 K ST HK HLBE HL32 eq_refl E2 E1)).
Qed.

End CANSEC1.
