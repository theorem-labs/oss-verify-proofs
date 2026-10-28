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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_lkit2 AZ_seq_d_xat AZ_seq_d_fin AZ_seq_d_exit AZ_seq_d_last AZ_seq_d_end AZ_seq_d_ad_at AZ_seq_d_ad_loop.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma sqd_last_all : forall P, sqd_ranges P -> sqd_side P -> sqd_sep P -> sqd_astat P -> sqd_pro P -> zd_memcpyZ_stmtA -> sqd_at_last P.
Proof. intros P RG SD SEP AS PRO MCP. exact (sqd_last_ok P RG SD SEP AS PRO MCP (sqd_fin_ok P RG AS PRO)). Qed.

Theorem sqd_body_ok : forall P OEND LLO LEND LOCV,
  sqd_static P OEND LLO LEND LOCV -> LOCV <> 2 -> sqd_ranges P -> sqd_side P -> sqd_sep P -> zd_memcpyZ_stmtA ->
  forall K, 1 <= K <= w_nbSeq P -> ad_head P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV ST HLOC RG SD SEP MCP.
  pose proof (st61 _ _ _ _ _ ST) as AS. pose proof (st63 _ _ _ _ _ ST) as PRO.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv beta iota in AS, PRO.
  set (P := mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) in *.
  pose proof (sqd_fin_ok P RG AS PRO) as FINK.
  pose proof (sqd_err_ok P _ _ _ _ ST FINK) as ERRK.
  apply (ad_loop P OEND LLO LEND LOCV ST ERRK (sqd_err20_ok P _ _ _ _ ST FINK)).
  apply (sqd_lexit_ok P _ _ _ _ ST HLOC ERRK). apply (sqd_last_all P RG SD SEP AS PRO MCP).
Qed.

End CANSEC1.
