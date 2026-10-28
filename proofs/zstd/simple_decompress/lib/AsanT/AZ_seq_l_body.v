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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_lkit2 AZ_seq_l_tkit AZ_seq_l_zkit AZ_seq_l_fin AZ_seq_l_xat AZ_seq_l_xat2 AZ_seq_l_exit
     AZ_seq_l_la_at AZ_seq_l_md_at AZ_seq_l_lm_at AZ_seq_l_lf_at AZ_seq_l_la_loop AZ_seq_l_lm_loop AZ_seq_l_lf_loop AZ_seq_l_lf_after AZ_seq_l_last2 AZ_seq_l_lastx AZ_seq_l_end.
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

Theorem sql_body_ok : forall P OEND LLO LEND LOCV,
  sql_static P OEND LLO LEND LOCV -> sql_ranges P -> sql_side P -> sql_sep P ->
  (LOCV = 2 -> wnth (l_ws P) H5_litBufferEnd = Z_to_bv 64 LEND) -> l_LBE P - l_LITP P < 2^32 -> zd_memmoveZ_stmtA ->
  forall K, 1 <= K <= l_nbSeq P -> la_head P OEND LLO LEND LOCV K.
Proof.
  intros P OEND LLO LEND LOCV ST RG SD SEP HLBE HLSZ MMV.
  pose proof (st61 _ _ _ _ _ ST) as AS. pose proof (st63 _ _ _ _ _ ST) as PRO. pose proof (st16 _ _ _ _ _ ST) as NB.
  pose proof (sql_static_switch P _ _ _ _ ST) as ST2.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbv beta iota in AS, PRO, NB.
  set (P := mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) in *.
  pose proof (sql_fin_ok P RG AS PRO) as FINK.
  pose proof (sql_last2_ok P RG SD SEP AS PRO MMV FINK) as L2K.
  pose proof (sql_lastx_ok P RG SD SEP AS PRO HLSZ MMV FINK L2K) as LXK.
  pose proof (sql_err_ok P _ _ _ _ ST FINK) as ERR. pose proof (sql_errq_ok P _ _ _ _ ST FINK) as ERRQ.
  pose proof (sql_err20_at P _ _ _ _ ST FINK) as E20. pose proof (sql_err20d_at P _ _ _ _ ST FINK) as E20D. pose proof (sql_e70_at P _ _ _ _ ST FINK) as E70. pose proof (sql_err20c_at P _ _ _ _ ST FINK) as E20C.
  pose proof (sql_err_ok P _ _ _ _ ST2 FINK) as ERR2. pose proof (sql_errq_ok P _ _ _ _ ST2 FINK) as ERRQ2.
  pose proof (sql_err20_at P _ _ _ _ ST2 FINK) as E202. pose proof (sql_err20d_at P _ _ _ _ ST2 FINK) as E20D2. pose proof (sql_e70_at P _ _ _ _ ST2 FINK) as E702. pose proof (sql_err20c_at P _ _ _ _ ST2 FINK) as E20C2.
  cbn [l_DCTX P] in ST2, ERR2, ERRQ2, E202, E20D2, E702, E20C2.
  pose proof (lf_end_ok P _ _ _ _ ST LXK) as END1. pose proof (lf_end_ok P _ _ _ _ ST2 LXK) as END2.
  assert (HLBE2 : 0 = 2 -> wnth (l_ws P) H5_litBufferEnd = Z_to_bv 64 (DCTX + 95908)) by (intros E; exfalso; clear - E; lia).
  pose proof (lf_loop P _ _ _ _ ST HLBE ERR ERRQ E20 E20D E70 END1 ERR2 ERRQ2 E202 E20D2 E702 END2) as LFH.
  pose proof (lf_loop P _ _ _ _ ST2 HLBE2 ERR2 ERRQ2 E202 E20D2 E702 END2 ERR2 ERRQ2 E202 E20D2 E702 END2) as LFH2.
  apply (la_loop P _ _ _ _ ST).
  apply (la_done_ok P _ _ _ _ ST E20C).
  - intros H8. cbn [l_nbSeq P] in H8 |- *.
    assert (LMD1 : lm_done P OEND LLO LEND LOCV 1) by (apply (lm_done_ok P _ _ _ _ ST H8 E20C); apply LFH; cbn [l_nbSeq P]; clear - H8; lia).
    assert (LMD2 : lm_done P OEND (DCTX + 30372) (DCTX + 95908) 0 1).
    { apply (lm_done_ok P _ _ _ _ ST2 H8 E20C2). apply LFH2. cbn [l_nbSeq P]. clear - H8; lia. }
    apply (lm_loop P _ _ _ _ ST HLBE ERR E20 E20D E70 LMD1 ERR2 E202 E20D2 E702 LMD2). cbn [l_nbSeq P]. clear - H8; lia.
  - intros HLE. apply LFH. cbn [l_nbSeq P]. clear - NB; lia.
Qed.


End CANSEC1.
