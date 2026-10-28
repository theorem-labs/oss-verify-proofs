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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit AZ_seq_l_lkit2 AZ_seq_l_tkit AZ_seq_l_zkit AZ_seq_l_fin AZ_seq_l_xat AZ_seq_l_xat2 AZ_seq_l_exit
     AZ_seq_l_la_at AZ_seq_l_md_at AZ_seq_l_lm_at AZ_seq_l_lf_at AZ_seq_l_ibase AZ_seq_l_iat AZ_seq_l_ierr AZ_seq_l_i0 AZ_seq_l_i1 AZ_seq_l_i3 AZ_seq_l_i5 AZ_seq_l_i7 AZ_seq_l_body.
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

Theorem sql_init_ok : forall P OEND,
  sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P) -> sql_ranges P -> sql_side P -> sql_sep P ->
  (l_LOC P = 2 -> wnth (l_ws P) H5_litBufferEnd = Z_to_bv 64 (l_LBE P)) -> l_LBE P - l_LITP P < 2^32 -> zd_memmoveZ_stmtA ->
  (l_LLT P + 4104 < 2^47 /\ l_OFT P + 2056 < 2^47 /\ l_MLT P + 4104 < 2^47) ->
  ai_I0 P OEND.
Proof.
  intros P OEND ST RG SD SEP HLBE HLSZ MMV TST.
  pose proof (st61 _ _ _ _ _ ST) as AS. pose proof (st63 _ _ _ _ _ ST) as PRO. pose proof (st16 _ _ _ _ _ ST) as NB.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbv beta iota in AS, PRO, NB.
  set (P := mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) in *.
  pose proof (sql_fin_ok P RG AS PRO) as FINK.
  apply (sql_i0_ok P _ ST (sql_ierr_ok P _ ST FINK)).
  apply (sql_i1_ok P _ ST TST). apply (sql_i3_ok P _ ST TST). apply (sql_i5_ok P _ ST TST).
  apply (sql_i7_ok P _ ST).
  apply (sql_body_ok P OEND _ _ _ ST RG SD SEP HLBE HLSZ MMV). cbn [l_nbSeq P]. clear - NB. lia.
Qed.

End CANSEC1.
