(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit RZ_seq_s_xat.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition tr_sw (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 lec cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs : Z) (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x26 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 < llv < 2^18 ->
  0 <= mlv < 2^18 ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 (Z_to_bv 64 OP) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) x21 (Z_to_bv 64 ofs) (Z_to_bv 64 OEND) (Z_to_bv 64 K) (Z_to_bv 64 llv) x26 x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a72c) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition tr_cpA (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 lec cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs lft en cur src : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  lft = LEND - LP ->
  0 < lft < llv ->
  en = OP + lft ->
  en <= OEND ->
  OP <= cur < en ->
  src = LP + (cur - OP) ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 src) (Z_to_bv 64 en) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) (Z_to_bv 64 lft) (Z_to_bv 64 ofs) (Z_to_bv 64 OEND) (Z_to_bv 64 K) (Z_to_bv 64 llv) (Z_to_bv 64 cur) x27 x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a6d8) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition tr_cpB (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 lec cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs lft en cur src rem : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x26 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  lft = LEND - LP ->
  0 < lft < llv ->
  en = OP + lft ->
  en <= OEND ->
  OP <= cur < en ->
  src = LP + (cur - OP) ->
  rem = en - cur ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 src) (Z_to_bv 64 en) (Z_to_bv 64 rem) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 mlv) (Z_to_bv 64 lft) (Z_to_bv 64 ofs) (Z_to_bv 64 OEND) (Z_to_bv 64 K) (Z_to_bv 64 llv) x26 (Z_to_bv 64 cur) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a70c) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition tr_w1 (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 lec cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs lft en wend wlen : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  lft = LEND - LP ->
  0 < lft < llv ->
  en = OP + lft ->
  en <= OEND ->
  wend = en - 32 ->
  OP <= wend ->
  wlen = wend - OP ->
  17 <= LP - OP ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 LP) (Z_to_bv 64 en) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) (Z_to_bv 64 wlen) (Z_to_bv 64 mlv) (Z_to_bv 64 lft) (Z_to_bv 64 ofs) x23 (Z_to_bv 64 K) (Z_to_bv 64 llv) (Z_to_bv 64 OP) (Z_to_bv 64 wend) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a688) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition tr_wl (P : ssp) (OEND LLO LEND LOCV K : Z) : Prop :=
  forall (m1 : fmem) (w0 lec cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (LP : Z) (OP : Z) (llv mlv ofs lft en wend cur srcp : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  seqs_linv P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  seqs_lfacts P OEND LLO LEND (100 + 100 * (v_nbSeq P - K) + 90) OP LP bc ptr sLL sOF sML ->
  0 <= ofs < 2^64 ->
  0 <= llv < 2^18 ->
  0 <= mlv < 2^18 ->
  lft = LEND - LP ->
  0 < lft < llv ->
  en = OP + lft ->
  en <= OEND ->
  wend = en - 32 ->
  lec = Z_to_bv 64 (wend - OP) ->
  17 <= wend - OP ->
  OP + 16 <= cur < wend ->
  srcp = LP + (cur - OP) + 16 ->
  17 <= LP - OP ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 LP) (Z_to_bv 64 en) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) (Z_to_bv 64 cur) (Z_to_bv 64 mlv) (Z_to_bv 64 lft) (Z_to_bv 64 ofs) (Z_to_bv 64 srcp) (Z_to_bv 64 K) (Z_to_bv 64 llv) (Z_to_bv 64 OP) (Z_to_bv 64 wend) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x1a69c) (v_fc P) None m1 (seg_rom psegs)).


(* [comment removed for export] *)
Lemma seqs_linv_switch : forall P OEND LLO LEND m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP,
  seqs_static P OEND LLO LEND 2 -> seqs_linv P OEND LLO LEND 2 m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall m2 w0' lec' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq,
  munch [(v_DCTX P + 30368, v_DCTX P + 30368 + 4); (v_SPV P - 336, v_SPV P)] m1 m2 -> wmono psegs m1 m2 -> mem_inv psegs m2 ->
  rw_cells psegs m2 (v_SPV P + -336) (seqs_frame P OEND w0' lec' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq) ->
  rw_cells psegs m2 (v_DCTX P + 30096) (h5_vcells (v_ws P) (Z_to_bv 64 0)) ->
  seqs_linv P OEND (v_DCTX P + 30372) (v_DCTX P + 95908) 0 m2 w0' lec' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP'.
Proof.
  intros P OEND LLO LEND m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 w0' lec' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq MUL WML MI2 FR H5V2.
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
  assert (XL2 : rdbl psegs m2 (DCTX + 30372) (DCTX + 95940)).
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
