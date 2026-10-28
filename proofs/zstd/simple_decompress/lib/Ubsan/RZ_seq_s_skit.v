(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_lkit2.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition seqs_frame4 (P : ssp) (OEND : Z) (c0 c8 c40 lec c128 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (jpad : list byte) (llv mlv ofs : Z) : list cell := let '(mkSSP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws) := P in
  [C8 c0; C8 c8; C8 (Z_to_bv 64 (PFX + 8)); C8 (Z_to_bv 64 (- (SPV - 160) - 1)); C8 (Z_to_bv 64 DCTX); C8 c40; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 OEND); C8 (Z_to_bv 64 (DCTX + 26684)); C8 (Z_to_bv 64 0); C8 dend; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (DCTX + 29896)); C8 (Z_to_bv 64 (2^60)); C8 (Z_to_bv 64 PFX); C8 lec; C8 c128; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (MLT + 8)); C8 p0; C8 p1; C8 p2] ++ [C8 (Z_to_bv 64 LP)] ++ [C8 (Z_to_bv 64 llv); C8 (Z_to_bv 64 mlv); C8 (Z_to_bv 64 ofs)] ++ [CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)].

Lemma seqs_frame4_merge : forall P OEND (m1 : fmem) c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad llv mlv ofs,
  rw_cells usegs m1 (v_SPV P + -384) (seqs_frame4 P OEND c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad llv mlv ofs) ->
  exists jseq, rw_cells usegs m1 (v_SPV P + -384) (seqs_frame P OEND c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq).
Proof.
  intros P OEND m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad llv mlv ofs FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqs_frame4 seqs_frame v_SPV] in *.
  eexists.
  change (rw_cells usegs m1 (SPV + -384) (([C8 c0; C8 c8; C8 (Z_to_bv 64 (PFX + 8)); C8 (Z_to_bv 64 (- (SPV - 160) - 1)); C8 (Z_to_bv 64 DCTX); C8 c40; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 OEND); C8 (Z_to_bv 64 (DCTX + 26684)); C8 (Z_to_bv 64 0); C8 dend; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (DCTX + 29896)); C8 (Z_to_bv 64 (2^60)); C8 (Z_to_bv 64 PFX); C8 lec; C8 c128; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (MLT + 8)); C8 p0; C8 p1; C8 p2] ++ [C8 (Z_to_bv 64 LP)]) ++ [C8 (Z_to_bv 64 llv); C8 (Z_to_bv 64 mlv); C8 (Z_to_bv 64 ofs)] ++ [CB 104 (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra)])) in FR.
  apply rw_cells_merge in FR. cbn [cells_size csize Nat.add] in FR. exact FR.
Qed.

(* [comment removed for export] *)
Lemma seqs_linv_slow : forall P OEND LLO LEND LOCV m0 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqs_static P OEND LLO LEND LOCV -> seqs_linv P OEND LLO LEND LOCV m0 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall jpad llv mlv ofs OP m2 lp' CS,
  rw_cells usegs m0 (v_SPV P + -384) (seqs_frame4 P OEND c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP jpad llv mlv ofs) ->
  v_DST P <= OP <= OEND -> 0 <= CS <= 208 ->
  munch [(OP, OEND); (v_SPV P + -136, v_SPV P + -136 + 8); (v_SPV P + -384 - CS, v_SPV P + -384)] m0 m2 ->
  wmono usegs m0 m2 -> mem_inv usegs m2 ->
  stk usegs m2 (v_lo P) (v_SPV P + -384) -> stk usegs m2 (v_B0 P) (v_B1 P) ->
  rw_cells usegs m2 (v_SPV P + -128) [C8 (Z_to_bv 64 llv); C8 (Z_to_bv 64 mlv); C8 (Z_to_bv 64 ofs)] ->
  rw_cells usegs m2 (v_SPV P + -136) [C8 (Z_to_bv 64 lp')] ->
  seqs_linv P OEND LLO LEND LOCV m2 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 lp'.
Proof.
  intros P OEND LLO LEND LOCV m0 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV jpad llv mlv ofs OP m2 lp' CS FR HOP HCS MUL WML MI2 STK2 BUF2 SQC LPC.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  assert (FR2 : rw_cells usegs m2 (v_SPV P + -384) (seqs_frame4 P OEND c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 lp' jpad llv mlv ofs)).
  { clear TLL TOF TML SQB LIT XLIT H5V H5L XI.
    destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqs_static seqs_frame4 v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *. sd_static_open ST. unfold held in S24.
    apply rw_cells_app in FR. destruct FR as (PRE & REST). apply rw_cells_app in REST. destruct REST as (_ & REST).
    apply rw_cells_app in REST. destruct REST as (_ & SAV).
    cbn [cells_size csize Nat.add app] in PRE, SAV.
    apply rw_cells_app. split.
    - eapply rw_cells_transport; [exact PRE | exact MUL | exact WML |].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear - S24 S18 S1 S2 S3 S4 S5 S6 HOP; lia|]. split; [lia|]. split; [lia| exact I].
    - apply rw_cells_app. split; [cbn [cells_size csize Nat.add]; replace (SPV + -384 + Z.of_nat 248) with (SPV + -136) by lia; exact LPC|].
      apply rw_cells_app. split; [cbn [cells_size csize Nat.add]; replace (SPV + -384 + Z.of_nat 248 + Z.of_nat 8) with (SPV + -128) by lia; exact SQC|].
      eapply rw_cells_transport; [exact SAV | exact MUL | exact WML |].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear - S24 S18 S1 S2 S3 S4 S5 S6 HOP; lia|]. split; [lia|]. split; [lia| exact I]. }
  destruct (seqs_frame4_merge _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR2) as (jseq & FR3). clear FR FR2 SQC LPC.
  split; [exists jpad, jseq; exact FR3|]. clear FR3.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_xinv v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST. unfold held in S18, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  rename BUF2 into BUF2'. pose proof BUF2' as BUF2.
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S33 S1 S2 S3 S4 S5 S6 HOP LLL; lia| split; [clear - S28 S18 LLL; lia| split; [clear - S28 S18 HCS LLL; lia| exact I]]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S34 S1 S2 S3 S4 S5 S6 HOP LOF; lia| split; [clear - S29 S18 LOF; lia| split; [clear - S29 S18 HCS LOF; lia| exact I]]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S35 S1 S2 S3 S4 S5 S6 HOP LML; lia| split; [clear - S30 S18 LML; lia| split; [clear - S30 S18 HCS LML; lia| exact I]]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S31 S1 S2 S3 S4 S5 S6 HOP; lia| split; [clear - S25 S18; lia| split; [clear - S25 S18 HCS; lia| exact I]]]]|].
  split; [unfold held in S12; destruct S12 as [(A1 & A2)|A]; [eapply rdbl_sub; [eapply rdbl_of_stk; exact BUF2 | exact A1 | exact A2] | eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - A S1 S2 S3 S4 S5 S6 HOP Hx; lia| split; [clear - S26 S18 Hx; lia| split; [clear - S26 S18 Hx HCS; lia| exact I]]]]]|].
  split; [eapply rdbl_transport; [exact XLIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HOP Hx; lia| split; [clear - S27 S18 Hx; lia| split; [clear - S27 S18 Hx HCS; lia| exact I]]]]|].
  split; [split; [eapply rw_cells_transport; [exact H5V | exact MUL | exact WML | unfold h5_vcells; cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HOP; lia| split; [clear - S27 S18; lia| split; [clear - S27 S18 HCS; lia| exact I]]]] | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HOP; lia| split; [clear - S27 S18; lia| split; [clear - S27 S18 HCS; lia| exact I]]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HOP; lia| split; [clear - S27 S18; lia| split; [clear - S27 S18 HCS; lia| exact I]]]]|].
  split; [exact BUF2|]. split; [exact STK2|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx HOP HCS S5 S18; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.
