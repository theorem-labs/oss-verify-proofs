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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_huf_iface AZ_seq_bit_iface AZ_seq_d_ibase AZ_seq_d_iat AZ_seq_d_ikit AZ_seq_d_ickit AZ_seq_d_fin AZ_seq_d_xat AZ_seq_d_ad_at
     AZ_seq_d_i0 AZ_seq_d_i1 AZ_seq_d_i3 AZ_seq_d_i5 AZ_seq_d_i7 AZ_seq_d_ierr AZ_seq_d_body.
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

Theorem sqd_init_ok : forall P OEND LLO LEND LOCV,
  sqd_static P OEND LLO LEND LOCV -> LOCV <> 2 -> sqd_ranges P -> sqd_side P -> sqd_sep P ->
  zd_memcpyZ_stmtA ->
  ai_I0 P OEND LLO LEND LOCV.
Proof.
  intros P OEND LLO LEND LOCV ST HLOC RG SD SEP MCP.
  pose proof (st61 _ _ _ _ _ ST) as AS. pose proof (st63 _ _ _ _ _ ST) as PRO. pose proof (st16 _ _ _ _ _ ST) as NB.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv beta iota in AS, PRO, NB.
  set (P := mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) in *.
  pose proof (sqd_fin_ok P RG AS PRO) as FINK.
  apply (sqd_i0_ok P _ _ _ _ ST (sqd_ierr_ok P _ _ _ _ ST FINK)).
  apply (sqd_i1_ok P _ _ _ _ ST). apply (sqd_i3_ok P _ _ _ _ ST). apply (sqd_i5_ok P _ _ _ _ ST). apply (sqd_i7_ok P _ _ _ _ ST).
  apply (sqd_body_ok P OEND LLO LEND LOCV ST HLOC RG SD SEP MCP).
  cbn [w_nbSeq P]. clear - NB. lia.
Qed.

End CANSEC1.
