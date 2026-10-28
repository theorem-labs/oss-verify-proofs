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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_s_ibase AZ_seq_s_iat AZ_seq_s_ikit AZ_seq_s_ickit AZ_seq_s_fin AZ_seq_s_xat AZ_seq_s_a1_at
     AZ_seq_s_i0 AZ_seq_s_i1 AZ_seq_s_i3 AZ_seq_s_i5 AZ_seq_s_i7 AZ_seq_s_ierr AZ_seq_s_body.
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

Theorem sqs_init_ok : forall P OEND LLO LEND,
  sqs_static P OEND LLO LEND 2 -> sqs_ranges P -> sqs_side P -> sqs_sep P ->
  wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 (v_LBE P) -> v_LBE P - v_LITP P < 2^32 ->
  zd_memmoveZ_stmtA -> zd_memcpyZ_stmtA ->
  (v_LLT P + 4104 < 2^47 /\ v_OFT P + 2056 < 2^47 /\ v_MLT P + 4104 < 2^47) ->
  ai_I0 P OEND LLO LEND 2.
Proof.
  intros P OEND LLO LEND ST RG SD SEP HLBE HLSZ MMV MCP TST.
  pose proof (st61 _ _ _ _ _ ST) as AS. pose proof (st63 _ _ _ _ _ ST) as PRO. pose proof (st16 _ _ _ _ _ ST) as NB.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbv beta iota in AS, PRO, NB.
  set (P := mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) in *.
  pose proof (sqs_fin_ok P RG AS PRO) as FINK.
  apply (sqs_i0_ok P _ _ _ _ ST (sqs_ierr_ok P _ _ _ _ ST FINK)).
  apply (sqs_i1_ok P _ _ _ _ ST TST). apply (sqs_i3_ok P _ _ _ _ ST TST). apply (sqs_i5_ok P _ _ _ _ ST TST). apply (sqs_i7_ok P _ _ _ _ ST eq_refl).
  apply (sqs_body_ok P OEND LLO LEND ST RG SD SEP HLBE HLSZ MMV MCP).
  cbn [v_nbSeq P]. clear - NB. lia.
Qed.

End CANSEC1.
