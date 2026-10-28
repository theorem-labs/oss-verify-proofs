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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_lkit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma sqs_static_switch : forall P OEND LLO LEND,
  sqs_static P OEND LLO LEND 2 -> sqs_static P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0.
Proof.
  intros P OEND LLO LEND ST.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  sd_static_open ST. unfold held in *.
  cbn [v_DCTX].
  constructor; cbv beta iota zeta; try assumption.
  all: try (clear - S19 S20; lia).
  all: try (clear - S19 S20 S32; lia).
  all: try (clear - S19 S20 S27 S18; lia).
  all: try (clear - S19 S20 S54; lia).
Qed.

(* [comment removed for export] *)
Lemma sqs_linv_switch : forall P OEND LLO LEND m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_static P OEND LLO LEND 2 -> sqs_linv P OEND LLO LEND 2 m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 c0' c8' c152' c160' c168' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq,
  munch [(v_DCTX P + 30368, v_DCTX P + 30368 + 4); (v_FRB P, v_FRB P + 280); (v_FF P, v_FF P + 256)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
  rw_cells bsegs m2 (v_FRB P) (sqs_frame P OEND c0' c8' c152' c160' c168' c200' c208' c216' LP' jseq) ->
  rw_cells bsegs m2 (v_FF P) (sqs_ffr P cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' jpad) ->
  rw_cells bsegs m2 (v_DCTX P + 30096) (h5_vcells (v_ws P) (Z_to_bv 64 0)) ->
  sqs_linv P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 m2 c0' c8' c152' c160' c168' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP'.
Proof.
  intros P OEND LLO LEND m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 c0' c8' c152' c160' c168' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq MUL WML MI2 FR FRF H5V2.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exists jpad, jseq; split; [exact FR | exact FRF]|]. clear FR FRF.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqs_xinv v_FRB v_FF v_LLT v_OFT v_MLT v_SEQ v_sq v_tLL v_tOF v_tML v_DCTX v_ws v_m] in *.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & SAV & GAP & SHS & MU & WM & MI1).
  (* [comment removed for export] *)
  assert (BDL : (6443008 <= DCTX /\ DCTX + 95992 <= 2147446784) \/ (17594333495296 <= DCTX /\ DCTX + 95992 <= ATOP)).
  { cbn [sqs_asan] in S62. destruct S62 as (ARD & _). destruct (ARD ltac:(unfold DCTX_SIZEOF; clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BL. unfold DCTX_SIZEOF in BL. exact BL. }
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, h5_vcells in *.
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S37 LLL; lia | split; [clear - S28 S18 S47 LLL; lia| split; [clear - S58 LLL; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S38 LOF; lia | split; [clear - S29 S18 S47 LOF; lia| split; [clear - S59 LOF; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S39 LML; lia | split; [clear - S30 S18 S47 LML; lia| split; [clear - S60 LML; lia|exact I]]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S40; lia | split; [clear - S25 S18 S47; lia| split; [clear - S56; lia|exact I]]]]|].
  assert (XL2 : rdbl bsegs m2 (DCTX + 30372) (DCTX + 95940)).
  { eapply rdbl_transport; [exact (XLIT eq_refl) | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - Hx; lia | split; [clear - S27 S18 S47 Hx; lia| split; [clear - S54 Hx; lia|exact I]]]]. }
  split; [replace (DCTX + 95908 + 32) with (DCTX + 95940) by lia; exact XL2|].
  split; [intros _; exact XL2|].
  split; [split; [exact H5V2 | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear; lia | split; [clear - S27 S18 S47; lia| split; [clear - S54; lia|exact I]]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear; lia | split; [clear - S27 S18 S47; lia| split; [clear - S54; lia|exact I]]]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S32; lia | split; [clear - S24 S18 S47; lia| split; [clear - S55; lia|exact I]]]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S27 S18 S47; lia | split; [clear; lia| split; [clear - S50 S18 S47; lia|exact I]]]]|].
  split; [eapply rw_cells_transport; [exact SAV | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S27 S18 S47; lia | split; [clear - S47; lia| split; [clear - S50 S18 S47; lia|exact I]]]]|].
  split; [eapply stk_transport_disjoint; [exact GAP | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S27 S18 S47; lia | split; [clear; lia| split; [clear - S50 S18 S47; lia|exact I]]]]|].
  split; [eapply rw_cells_transport; [exact SHS | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - BDL S52 S53; pose proof atop_range; lia | split; [clear - S53 S18 S47; lia| split; [clear - S49 S52 S53; lia|exact I]]]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp, sqs_Wb; cbn [outside]; unfold DCTX_litBufferLocation; intros x Hx; clear - Hx S47; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

(* [comment removed for export] *)
Lemma rd_at_rdbl : forall (m : amem) lo hi, rdbl bsegs m lo hi -> lo <= hi -> rd_at bsegs m lo (hi - lo).
Proof.
  intros m lo hi (H0 & H1 & H) Hle. split; [exact H0|]. split; [lia|].
  intros i Hi. destruct (H (lo + i) ltac:(lia)) as [b Hb]. unfold mrd in Hb |- *. rewrite Hb. discriminate.
Qed.

End CANSEC1.
