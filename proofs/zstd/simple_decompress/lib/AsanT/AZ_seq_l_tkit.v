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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_hkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma sql_lit_k : forall P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  sql_static P OEND LLO LEND LOCV -> sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  forall Q : Prop,
  (unpoisoned m1 (l_LITP P) (l_LITP P + (l_LBE P + 32 - l_LITP P)) -> rng (l_RNG P) (l_LITP P) (l_LBE P + 32 - l_LITP P) ->
   rng (l_RNG P) (shad (l_LITP P)) (shspan (l_LITP P) (l_LBE P + 32 - l_LITP P)) ->
   (6443008 <= l_LITP P /\ l_LBE P + 32 <= 2147446784) \/ (17594333495296 <= l_LITP P /\ l_LBE P + 32 <= ATOP) -> Q) -> Q.
Proof.
  intros P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV Q KQ.
  pose proof (sql_asan_now P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as AS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_asan l_RNG l_LITP l_LBE] in *. unfold WILDCOPY_OVERLENGTH in AS.
  sd_static_open ST.
  destruct AS as (_ & _ & _ & _ & _ & _ & ARL & _).
  destruct (ARL ltac:(clear - S70; lia)) as (BL & U & R1 & R2).
  apply KQ; [exact U | exact R1 | exact R2 |].
  pose proof (ablk_lits _ _ BL) as BL2. clear - BL2. lia.
Qed.

(* [comment removed for export] *)
Lemma sql_static_switch : forall P OEND LLO LEND LOCV,
  sql_static P OEND LLO LEND LOCV -> sql_static P OEND (l_DCTX P + 30372) (l_DCTX P + 95908) 0.
Proof.
  intros P OEND LLO LEND LOCV ST.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [l_DCTX].
  sd_static_open ST. unfold held in *.
  constructor; cbv beta iota zeta; try assumption.
  all: try (clear - S19 S20; lia).
  all: try (clear - S19 S20 S32; lia).
  all: try (clear - S19 S20 S27 S18; lia).
  all: try (clear - S19 S20 S54; lia).
Qed.

(* [comment removed for export] *)
Lemma rd_at_rdbl : forall (m : amem) lo hi, rdbl bsegs m lo hi -> lo <= hi -> rd_at bsegs m lo (hi - lo).
Proof.
  intros m lo hi (H0 & H1 & H) Hle. split; [exact H0|]. split; [lia|].
  intros i Hi. destruct (H (lo + i) ltac:(lia)) as [b Hb]. unfold mrd in Hb |- *. rewrite Hb. discriminate.
Qed.

End CANSEC1.
