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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

Lemma sqs_lbe_asan : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_static P OEND LLO LEND LOCV -> sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  v_DCTX P = 8 * v_D8 P /\ 512 <= v_D8 P /\ v_D8 P + 11999 < 2^44 /\
  rdn bsegs m1 (wa (2147450880 + v_D8 P + 3795)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\
  rng (v_RNG P) (2147450880 + v_D8 P + 3795) 1 /\ rng (v_RNG P) (v_DCTX P + 30360) 8 /\
  ((6443008 <= v_DCTX P /\ v_DCTX P + 95992 <= 2147446784) \/ (17594333495296 <= v_DCTX P /\ v_DCTX P + 95992 <= ATOP)).
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV.
  pose proof (sqs_asan_now P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV) as AS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_asan sqs_astat v_DCTX v_D8 v_RNG] in *. sd_static_open ST.
  destruct AS as (ARD & _).
  destruct S61 as (_ & _ & _ & _ & ED8 & _).
  unfold DCTX_SIZEOF in *.
  destruct (ARD ltac:(clear; lia)) as (BD & UD & RD1 & RD2). pose proof (ablk_lits _ _ BD) as BDL.
  assert (Z0 : m1 (wa (shad (DCTX + 30360))) = Some (Z_to_bv 8 0)) by (eapply (unp_shadow_zero m1 DCTX 95992); [exact UD | clear; lia | clear - ED8; Z.div_mod_to_equations; lia]).
  rewrite shad_div in Z0. unfold ASHOFF in Z0.
  replace ((DCTX + 30360) / 8) with (D8 + 3795) in Z0 by (clear - ED8; Z.div_mod_to_equations; lia).
  split; [exact ED8|]. split; [clear - ED8 S19; lia|]. split; [clear - ED8 S20; lia|].
  split; [cbn [rdn]; replace (2147450880 + D8 + 3795) with (2147450880 + (D8 + 3795)) by lia; rewrite Z0; reflexivity|].
  split; [eapply rng_sub'; [exact RD2 |]; unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - ED8; Z.div_mod_to_equations; lia|].
  split; [eapply rng_sub'; [exact RD1 | clear; lia]| exact BDL].
Qed.

(* [comment removed for export] *)
Lemma sqs_linv_h5 : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rw_cells bsegs m1 (v_DCTX P + 30096) (h5_vcells (v_ws P) (Z_to_bv 64 LOCV)).
Proof. intros until LP. intros (_ & _ & _ & _ & _ & _ & _ & (H5V & _) & _). exact H5V. Qed.

(* [comment removed for export] *)
Lemma sqs_linv_lbe : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP V,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP -> wnth (v_ws P) H5_litBufferEnd = Z_to_bv 64 V ->
  rdn bsegs m1 (wa (v_DCTX P + 30360)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 V)).
Proof.
  intros until V. intros (_ & _ & _ & _ & _ & _ & _ & H5 & _) E. exact (h5_lbe_know _ _ _ _ _ H5 E).
Qed.

End CANSEC1.
