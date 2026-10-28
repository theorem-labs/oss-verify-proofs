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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_akit3 AZ_seq_s_lkit2 AZ_seq_s_tkit AZ_seq_s_fin AZ_seq_s_lastb AZ_seq_s_last AZ_seq_s_end AZ_seq_s_exit AZ_seq_s_xat AZ_seq_s_a1_at AZ_seq_s_loops.
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

(* [comment removed for export] *)
Lemma sqs_last_all : forall P, sqs_ranges P -> sqs_side P -> sqs_sep P -> sqs_astat P -> sqs_pro P -> v_LBE P - v_LITP P < 2^32 ->
  zd_memmoveZ_stmtA -> zd_memcpyZ_stmtA -> sqs_at_last P.
Proof.
  intros P RG SD SEP AS PRO HLSZ MMV MCP.
  pose proof (sqs_fin_ok P RG AS PRO) as FINK.
  exact (sqs_last_ok P RG SD SEP AS PRO HLSZ MMV FINK (sqs_lastb_ok P RG SD SEP AS PRO MCP FINK)).
Qed.

Theorem sqs_body_ok : forall P OEND LLO LEND,
  sqs_static P OEND LLO LEND 2 -> sqs_ranges P -> sqs_side P -> sqs_sep P ->
  wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 (v_LBE P) -> v_LBE P - v_LITP P < 2^32 ->
  zd_memmoveZ_stmtA -> zd_memcpyZ_stmtA ->
  forall K, 1 <= K <= v_nbSeq P -> a1_head P OEND LLO LEND 2 K.
Proof.
  intros P OEND LLO LEND ST RG SD SEP HLBE HLSZ MMV MCP.
  pose proof (st61 _ _ _ _ _ ST) as AS. pose proof (st63 _ _ _ _ _ ST) as PRO. pose proof (st71 _ _ _ _ _ ST) as PH1. pose proof (st42 _ _ _ _ _ ST) as W42.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_ws v_LBE v_LITP v_nbSeq v_DCTX] in *.
  destruct (PH1 eq_refl) as (ELLO & ELEND & _).
  assert (HL32 : LEND + 32 <= OEND) by (clear - W42; lia).
  rewrite <- ELEND in HLBE.
  set (P := mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) in *.
  pose proof (sqs_fin_ok P RG AS PRO) as FINK.
  pose proof (sqs_last_all P RG SD SEP AS PRO HLSZ MMV MCP) as LASTK.
  pose proof (sqs_static_switch P OEND LLO LEND ST) as ST2. cbn [v_DCTX P] in ST2.
  pose proof (sqs_err_ok P _ _ _ _ ST FINK) as ERR1.
  pose proof (sqs_err20_ok P _ _ _ _ ST FINK) as ERR201.
  pose proof (sqs_err19_ok P _ _ _ _ ST FINK) as ERR191.
  pose proof (sqs_err10_ok P _ _ _ _ ST FINK) as ERR101.
  pose proof (sqs_err4_ok P _ _ _ _ ST FINK) as ERR41.
  pose proof (sqs_lexit_ok P _ _ _ _ ST ERR1 ERR41 LASTK) as LEX1.
  pose proof (sqs_err_ok P _ _ _ _ ST2 FINK) as ERR2.
  pose proof (sqs_err20_ok P _ _ _ _ ST2 FINK) as ERR202.
  pose proof (sqs_err4_ok P _ _ _ _ ST2 FINK) as ERR42.
  pose proof (sqs_lexit_ok P _ _ _ _ ST2 ERR2 ERR42 LASTK) as LEX2.
  exact (sqs_loops P OEND LLO LEND ST HLBE HL32 ERR1 ERR191 ERR101 ERR201 LEX1 ERR2 ERR202 LEX2).
Qed.

End CANSEC1.
