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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_xat.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition tr_sw (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 < llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 OP) x20 x21 x22 x23 (Z_to_bv 64 K) x25 x26 (Z_to_bv 64 llv) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1ba7c) (v_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition tr_w1 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c40 cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs lft : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 (Z_to_bv 64 LEND) (Z_to_bv 64 K) cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  lft = LEND - LP ->
  0 < lft < llv ->
  OP + lft <= OEND ->
  evt usegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -384)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 mlv) (Z_to_bv 64 ofs) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 lft) x21 x22 x23 (Z_to_bv 64 K) x25 (Z_to_bv 64 OP) (Z_to_bv 64 llv) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1ba50) (v_fc P) None m1 (seg_rom usegs)).


(* [comment removed for export] *)
Lemma seqs_linv_switch : forall P OEND LLO LEND m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqs_static P OEND LLO LEND 2 -> seqs_linv P OEND LLO LEND 2 m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq,
  munch [(v_DCTX P + 30368, v_DCTX P + 30368 + 4); (v_SPV P - 384, v_SPV P)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  rw_cells usegs m2 (v_SPV P + -384) (seqs_frame P OEND c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq) ->
  rw_cells usegs m2 (v_DCTX P + 30096) (h5_vcells (v_ws P) (Z_to_bv 64 0)) ->
  seqs_linv P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 m2 c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP'.
Proof.
  intros P OEND LLO LEND m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 c0' c8' c40' lec' c128' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq MUL WML MI2 FR H5V2.
  destruct INV as (_ & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exists jpad, jseq; exact FR|]. clear FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_xinv v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST. unfold held in S18, S24, S25, S26, S27, S28, S29, S30, S32, S37, S38, S39, S40.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S37 LLL; lia| split; [clear - S28 S18 LLL; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S38 LOF; lia| split; [clear - S29 S18 LOF; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S39 LML; lia| split; [clear - S30 S18 LML; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S40; lia| split; [clear - S25 S18; lia| exact I]]]|].
  assert (XL2 : rdbl usegs m2 (DCTX + 30372) (DCTX + 95940)).
  { eapply rdbl_transport; [exact XLIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - Hx; lia| split; [clear - S27 S18 Hx; lia| exact I]]]. }
  split; [replace (DCTX + 95908 + 32) with (DCTX + 95940) by lia; exact XL2|].
  split; [exact XL2|].
  split; [split; [exact H5V2 | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [lia| split; [clear - S27 S18; lia|exact I]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [lia| split; [clear - S27 S18; lia|exact I]]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S32; lia| split; [clear - S24 S18; lia|exact I]]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S27 S18; lia| split; [clear - S18; lia|exact I]]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

Lemma seqs_linv_call : forall P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqs_static P OEND LLO LEND LOCV -> seqs_linv P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 D1 D2 CS,
  munch [(D1, D2); (v_SPV P + -384 - CS, v_SPV P + -384)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  stk usegs m2 (v_lo P) (v_SPV P + -384) -> stk usegs m2 (v_B0 P) (v_B1 P) -> v_DST P <= D1 -> D2 <= OEND -> 0 <= CS <= 208 ->
  seqs_linv P OEND LLO LEND LOCV m2 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c40 lec c128 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 D1 D2 CS MUL WML MI2 STK2 BUF2 HD1 HD2 HCS.
  destruct INV as ((jpad & jseq & FR) & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI). unfold seqs_linv.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_xinv seqs_frame v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST. unfold held in S12, S18, S24, S25, S26, S27, S28, S29, S30, S31, S32, S33, S34, S35.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  split; [exists jpad, jseq; eapply rw_cells_transport; [exact FR | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add seqs_frame]; split; [clear - S24 S18 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S33 S1 S2 S3 S4 S5 S6 HD1 HD2 LLL; lia| split; [clear - S28 S18 HCS LLL; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S34 S1 S2 S3 S4 S5 S6 HD1 HD2 LOF; lia| split; [clear - S29 S18 HCS LOF; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S35 S1 S2 S3 S4 S5 S6 HD1 HD2 LML; lia| split; [clear - S30 S18 HCS LML; lia| exact I]]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S31 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S25 S18 HCS; lia| exact I]]]|].
  split; [destruct S12 as [(A1 & A2)|A]; [eapply rdbl_sub; [eapply rdbl_of_stk; exact BUF2 | exact A1 | exact A2] | eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - A S1 S2 S3 S4 S5 S6 HD1 HD2 Hx; lia| split; [clear - S26 S18 HCS Hx; lia| exact I]]]]|].
  split; [eapply rdbl_transport; [exact XLIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2 Hx; lia| split; [clear - S27 S18 HCS Hx; lia| exact I]]]|].
  split; [split; [eapply rw_cells_transport; [exact H5V | exact MUL | exact WML | unfold h5_vcells; cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18 HCS; lia| exact I]]] | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18 HCS; lia| exact I]]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S32 S1 S2 S3 S4 S5 S6 HD1 HD2; lia| split; [clear - S27 S18 HCS; lia| exact I]]]|].
  split; [exact BUF2|].
  split; [exact STK2|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx HD1 HD2 S5 HCS; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
