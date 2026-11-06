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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_d_base RZ_seq_d_lbase RZ_seq_d_lkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition seqd_iinv (P : sdp) (LEND : Z) (m1 : fmem) (fr : list cell) : Prop :=
  rw_cells psegs m1 (q_SPV P + -304) fr /\
  dctx_ptrs psegs m1 (q_DCTX P) (Z_to_bv 64 (q_LLT P)) (Z_to_bv 64 (q_MLT P)) (Z_to_bv 64 (q_OFT P)) (q_huf P) /\
  bytes_at psegs m1 (q_LLT P) (map (Z_to_bv 8) (seq_table_bytes (q_tLL P))) /\
  bytes_at psegs m1 (q_OFT P) (map (Z_to_bv 8) (seq_table_bytes (q_tOF P))) /\
  bytes_at psegs m1 (q_MLT P) (map (Z_to_bv 8) (seq_table_bytes (q_tML P))) /\
  bytes_at psegs m1 (q_SEQ P) (map (Z_to_bv 8) (q_sq P)) /\
  rdbl psegs m1 (q_LITP P) (LEND + 32) /\
  seqd_xinv P m1 (seqd_fe P).

Lemma seqd_iinv_mi : forall P LEND m1 fr, seqd_iinv P LEND m1 fr -> mem_inv psegs m1.
Proof.
  intros P LEND m1 fr (_ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqd_xinv] in XI. destruct XI as (_ & _ & _ & _ & _ & _ & MI). exact MI.
Qed.

(* [comment removed for export] *)
Lemma seqd_iinv_frame : forall P OEND LEND m1 fr,
  seqd_static P OEND LEND -> seqd_iinv P LEND m1 fr ->
  forall m2 fr2,
  munch [(q_SPV P - 304, q_SPV P)] m1 m2 -> wmono psegs m1 m2 -> mem_inv psegs m2 ->
  rw_cells psegs m2 (q_SPV P + -304) fr2 -> seqd_iinv P LEND m2 fr2.
Proof.
  intros P OEND LEND m1 fr ST INV m2 fr2 MUL WML MI2 FR.
  destruct INV as (_ & PT & TLL & TOF & TML & SQB & LIT & XI).
  split; [exact FR|]. clear FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqd_static seqd_xinv q_ra q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_F q_fc q_m q_SPV q_lo q_DCTX q_DST q_CAP q_B0 q_B1 q_SEQ q_nbSeq q_LLT q_MLT q_OFT q_PFX q_LITP q_LITSZ q_LITB q_LOC q_sq q_tLL q_tOF q_tML q_huf q_r0 q_r1 q_r2 q_pde q_dend q_expd q_pcs q_dsz q_bt q_stg q_le q_fe q_ws] in *.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_ptrs, dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy in *.
  split; [eapply rw_cells_transport; [exact PT | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S28 S18 LLL; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S29 S18 LOF; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S30 S18 LML; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S25 S18; lia|exact I]]|].
  split; [eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S26 S18 Hx; lia|exact I]]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S24 S18; lia|exact I]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S18; lia|exact I]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

(* [comment removed for export] *)
Lemma seqd_iinv_linv : forall P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq,
  seqd_iinv P LEND m1 (seqd_frame P OEND LEND cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq) -> seqd_linv P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP.
Proof.
  intros P OEND LEND m1 cw bc ptr sLL sOF sML p0 p1 p2 LP j0 jpad jseq (FR & _ & TLL & TOF & TML & SQB & LIT & XI).
  split; [exists j0, jpad, jseq; exact FR|]. repeat (split; [assumption|]). exact XI.
Qed.

(* [comment removed for export] *)
Lemma iframe_bc_blob : forall (m : fmem) A cs v, nth_error cs 8 = Some (C4 v) ->
  rw_cells psegs m A cs -> rw_cells psegs m A (firstn 8 cs ++ CB 4 (le4 v) :: skipn 9 cs).
Proof.
  intros m A cs v HN RW.
  assert (E : cs = firstn 8 cs ++ C4 v :: skipn 9 cs).
  { rewrite <- (firstn_skipn 8 cs) at 1. f_equal.
    do 8 (destruct cs as [|? cs]; [discriminate HN|]). destruct cs as [|c9 cs]; [discriminate HN|]. cbn in HN. injection HN as ->. reflexivity. }
  remember (firstn 8 cs) as pre eqn:Epre. remember (skipn 9 cs) as post eqn:Epost. clear Epre Epost HN. subst cs.
  pose proof RW as [[WF _] _]. apply cells_wf_app in WF. destruct WF as (W1 & _ & W2).
  eapply rw_cells_recell; [exact RW | |].
  - apply cells_wf_app. split; [exact W1|]. split; [apply length_le4| exact W2].
  - rewrite !cells_bytes_app. reflexivity.
Qed.

(* [comment removed for export] *)
Definition seqd_ibits (P : sdp) (B bc ptr : Z) : Prop := 0 <= bc <= B /\ bit_ok (q_SEQ P) (zlen (q_sq P)) bc ptr.

(* [comment removed for export] *)
Definition ai_408 (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 : word) (j0 jpad jseq j_c16 j_c48 j_cbc j_c96 j_c104 j_c112 j_c120 j_c128 j_c136 : list byte) (cw : word) (bc ptr : Z) (d : Z) (x1 x5 x6 x7 x16 x17 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 [CB 8 j0; C8 (Z_to_bv 64 (q_DCTX P + 26684)); CB 8 j_c16; C8 (Z_to_bv 64 OEND); C8 (q_dend P); C8 (Z_to_bv 64 (q_PFX P)); CB 8 j_c48; C8 cw; CB 4 j_cbc; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (q_SEQ P)); C8 (Z_to_bv 64 (q_SEQ P + 8)); CB 8 j_c96; CB 8 j_c104; CB 8 j_c112; CB 8 j_c120; CB 8 j_c128; CB 8 j_c136; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (q_LITP P)); CB 24 jseq; CB 104 (le8 (q_s11 P) ++ le8 (q_s10 P) ++ le8 (q_s9 P) ++ le8 (q_s8 P) ++ le8 (q_s7 P) ++ le8 (q_s6 P) ++ le8 (q_s5 P) ++ le8 (q_s4 P) ++ le8 (q_s3 P) ++ le8 (q_s2 P) ++ le8 (q_s1 P) ++ le8 (q_s0 P) ++ le8 (q_ra P))] ->
  seqd_ibits P 64 bc ptr ->
  ptr = q_SEQ P + d ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_DST P)) (Z_to_bv 64 (q_PFX P)) (Z_to_bv 64 (q_DCTX P)) (Z_to_bv 64 (q_SEQ P + 8)) cw (Z_to_bv 64 (q_SEQ P)) (Z_to_bv 64 bc) (Z_to_bv 64 d) x16 x17 (Z_to_bv 64 (q_nbSeq P)) x19 x20 x21 x22 x23 (Z_to_bv 64 (q_DST P)) x25 x26 (Z_to_bv 64 LEND) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1b4d4) (q_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_43c (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 : word) (j0 jpad jseq j_c16 j_c48 j_cbc j_c104 j_c112 j_c120 j_c128 j_c136 : list byte) (cw : word) (bc ptr : Z) (d sLL : Z) (x1 x6 x7 x14 x19 x20 x21 x23 x25 x26 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 [CB 8 j0; C8 (Z_to_bv 64 (q_DCTX P + 26684)); CB 8 j_c16; C8 (Z_to_bv 64 OEND); C8 (q_dend P); C8 (Z_to_bv 64 (q_PFX P)); CB 8 j_c48; C8 cw; CB 4 j_cbc; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (q_SEQ P)); C8 (Z_to_bv 64 (q_SEQ P + 8)); C8 (Z_to_bv 64 sLL); CB 8 j_c104; CB 8 j_c112; CB 8 j_c120; CB 8 j_c128; CB 8 j_c136; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (q_LITP P)); CB 24 jseq; CB 104 (le8 (q_s11 P) ++ le8 (q_s10 P) ++ le8 (q_s9 P) ++ le8 (q_s8 P) ++ le8 (q_s7 P) ++ le8 (q_s6 P) ++ le8 (q_s5 P) ++ le8 (q_s4 P) ++ le8 (q_s3 P) ++ le8 (q_s2 P) ++ le8 (q_s1 P) ++ le8 (q_s0 P) ++ le8 (q_ra P))] ->
  seqd_ibits P 73 bc ptr ->
  ptr = q_SEQ P + d ->
  0 <= sLL < 2^(st_log (q_tLL P)) ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) (Z_to_bv 64 65) x6 x7 (Z_to_bv 64 (q_DST P)) (Z_to_bv 64 (q_PFX P)) (Z_to_bv 64 (q_DCTX P)) (Z_to_bv 64 (q_SEQ P + 8)) cw (Z_to_bv 64 (q_SEQ P)) x14 (Z_to_bv 64 d) (Z_to_bv 64 (q_LLT P)) (Z_to_bv 64 bc) (Z_to_bv 64 (q_nbSeq P)) x19 x20 x21 (Z_to_bv 64 BITMASK) x23 (Z_to_bv 64 (q_DST P)) x25 x26 (Z_to_bv 64 LEND) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1b508) (q_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_538 (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 : word) (j0 jpad jseq j_c16 j_c48 j_cbc j_c104 j_c112 j_c120 j_c128 j_c136 : list byte) (cw : word) (bc ptr : Z) (sLL : Z) (x1 x5 x6 x7 x15 x19 x20 x21 x23 x25 x26 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 [CB 8 j0; C8 (Z_to_bv 64 (q_DCTX P + 26684)); CB 8 j_c16; C8 (Z_to_bv 64 OEND); C8 (q_dend P); C8 (Z_to_bv 64 (q_PFX P)); CB 8 j_c48; C8 cw; CB 4 j_cbc; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (q_SEQ P)); C8 (Z_to_bv 64 (q_SEQ P + 8)); C8 (Z_to_bv 64 sLL); CB 8 j_c104; CB 8 j_c112; CB 8 j_c120; CB 8 j_c128; CB 8 j_c136; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (q_LITP P)); CB 24 jseq; CB 104 (le8 (q_s11 P) ++ le8 (q_s10 P) ++ le8 (q_s9 P) ++ le8 (q_s8 P) ++ le8 (q_s7 P) ++ le8 (q_s6 P) ++ le8 (q_s5 P) ++ le8 (q_s4 P) ++ le8 (q_s3 P) ++ le8 (q_s2 P) ++ le8 (q_s1 P) ++ le8 (q_s0 P) ++ le8 (q_ra P))] ->
  seqd_ibits P 73 bc ptr ->
  0 <= sLL < 2^(st_log (q_tLL P)) ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_DST P)) (Z_to_bv 64 (q_PFX P)) (Z_to_bv 64 (q_DCTX P)) (Z_to_bv 64 (q_SEQ P + 8)) cw (Z_to_bv 64 (q_SEQ P)) (Z_to_bv 64 ptr) x15 (Z_to_bv 64 (q_LLT P)) (Z_to_bv 64 bc) (Z_to_bv 64 (q_nbSeq P)) x19 x20 x21 (Z_to_bv 64 BITMASK) x23 (Z_to_bv 64 (q_DST P)) x25 x26 (Z_to_bv 64 LEND) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1b604) (q_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_56c (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 : word) (j0 jpad jseq j_c16 j_c48 j_cbc j_c120 j_c128 j_c136 : list byte) (cw : word) (bc ptr : Z) (sLL sOF : Z) (x1 x6 x7 x17 x19 x20 x21 x23 x25 x26 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 [CB 8 j0; C8 (Z_to_bv 64 (q_DCTX P + 26684)); CB 8 j_c16; C8 (Z_to_bv 64 OEND); C8 (q_dend P); C8 (Z_to_bv 64 (q_PFX P)); CB 8 j_c48; C8 cw; CB 4 j_cbc; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (q_SEQ P)); C8 (Z_to_bv 64 (q_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (q_LLT P + 8)); C8 (Z_to_bv 64 sOF); CB 8 j_c120; CB 8 j_c128; CB 8 j_c136; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (q_LITP P)); CB 24 jseq; CB 104 (le8 (q_s11 P) ++ le8 (q_s10 P) ++ le8 (q_s9 P) ++ le8 (q_s8 P) ++ le8 (q_s7 P) ++ le8 (q_s6 P) ++ le8 (q_s5 P) ++ le8 (q_s4 P) ++ le8 (q_s3 P) ++ le8 (q_s2 P) ++ le8 (q_s1 P) ++ le8 (q_s0 P) ++ le8 (q_ra P))] ->
  seqd_ibits P 82 bc ptr ->
  0 <= sLL < 2^(st_log (q_tLL P)) ->
  0 <= sOF < 2^(st_log (q_tOF P)) ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) (Z_to_bv 64 65) x6 x7 (Z_to_bv 64 (q_DST P)) (Z_to_bv 64 (q_PFX P)) (Z_to_bv 64 (q_DCTX P)) (Z_to_bv 64 (q_SEQ P + 8)) cw (Z_to_bv 64 (q_SEQ P)) (Z_to_bv 64 ptr) (Z_to_bv 64 (q_OFT P)) (Z_to_bv 64 bc) x17 (Z_to_bv 64 (q_nbSeq P)) x19 x20 x21 (Z_to_bv 64 BITMASK) x23 (Z_to_bv 64 (q_DST P)) x25 x26 (Z_to_bv 64 LEND) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1b638) (q_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_66c (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 : word) (j0 jpad jseq j_c16 j_c48 j_cbc j_c120 j_c128 j_c136 : list byte) (cw : word) (bc ptr : Z) (sLL sOF : Z) (x1 x5 x6 x7 x17 x19 x20 x21 x23 x25 x26 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 [CB 8 j0; C8 (Z_to_bv 64 (q_DCTX P + 26684)); CB 8 j_c16; C8 (Z_to_bv 64 OEND); C8 (q_dend P); C8 (Z_to_bv 64 (q_PFX P)); CB 8 j_c48; C8 cw; CB 4 j_cbc; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (q_SEQ P)); C8 (Z_to_bv 64 (q_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (q_LLT P + 8)); C8 (Z_to_bv 64 sOF); CB 8 j_c120; CB 8 j_c128; CB 8 j_c136; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (q_LITP P)); CB 24 jseq; CB 104 (le8 (q_s11 P) ++ le8 (q_s10 P) ++ le8 (q_s9 P) ++ le8 (q_s8 P) ++ le8 (q_s7 P) ++ le8 (q_s6 P) ++ le8 (q_s5 P) ++ le8 (q_s4 P) ++ le8 (q_s3 P) ++ le8 (q_s2 P) ++ le8 (q_s1 P) ++ le8 (q_s0 P) ++ le8 (q_ra P))] ->
  seqd_ibits P 82 bc ptr ->
  0 <= sLL < 2^(st_log (q_tLL P)) ->
  0 <= sOF < 2^(st_log (q_tOF P)) ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_DST P)) (Z_to_bv 64 (q_PFX P)) (Z_to_bv 64 (q_DCTX P)) (Z_to_bv 64 (q_SEQ P + 8)) cw (Z_to_bv 64 (q_SEQ P)) (Z_to_bv 64 ptr) (Z_to_bv 64 (q_OFT P)) (Z_to_bv 64 bc) x17 (Z_to_bv 64 (q_nbSeq P)) x19 x20 x21 (Z_to_bv 64 BITMASK) x23 (Z_to_bv 64 (q_DST P)) x25 x26 (Z_to_bv 64 LEND) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1b738) (q_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_6a8 (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 : word) (j0 jpad jseq j_c48 j_c136 : list byte) (cw : word) (bc ptr : Z) (sLL sOF sML : Z) (x1 x5 x6 x7 x12 x15 x19 x20 x21 x23 x25 x26 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 [CB 8 j0; C8 (Z_to_bv 64 (q_DCTX P + 26684)); C8 (Z_to_bv 64 (q_DST P)); C8 (Z_to_bv 64 OEND); C8 (q_dend P); C8 (Z_to_bv 64 (q_PFX P)); CB 8 j_c48; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (q_SEQ P)); C8 (Z_to_bv 64 (q_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (q_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (q_OFT P + 8)); C8 (Z_to_bv 64 sML); CB 8 j_c136; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (q_LITP P)); CB 24 jseq; CB 104 (le8 (q_s11 P) ++ le8 (q_s10 P) ++ le8 (q_s9 P) ++ le8 (q_s8 P) ++ le8 (q_s7 P) ++ le8 (q_s6 P) ++ le8 (q_s5 P) ++ le8 (q_s4 P) ++ le8 (q_s3 P) ++ le8 (q_s2 P) ++ le8 (q_s1 P) ++ le8 (q_s0 P) ++ le8 (q_ra P))] ->
  seqd_ibits P 91 bc ptr ->
  0 <= sLL < 2^(st_log (q_tLL P)) ->
  0 <= sOF < 2^(st_log (q_tOF P)) ->
  0 <= sML < 2^(st_log (q_tML P)) ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_DST P)) (Z_to_bv 64 (q_PFX P)) (Z_to_bv 64 (q_MLT P)) (Z_to_bv 64 (q_SEQ P + 8)) x12 (Z_to_bv 64 (q_SEQ P)) (Z_to_bv 64 ptr) x15 (Z_to_bv 64 bc) (Z_to_bv 64 65) (Z_to_bv 64 (q_nbSeq P)) x19 x20 x21 (Z_to_bv 64 BITMASK) x23 (Z_to_bv 64 (q_DST P)) x25 x26 (Z_to_bv 64 LEND) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1b774) (q_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_7ac (P : sdp) (OEND LEND : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 : word) (j0 jpad jseq j_c48 j_c136 : list byte) (cw : word) (bc ptr : Z) (sLL sOF sML : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x23 x25 x26 x28 x29 x30 x31 : word),
  seqd_iinv P LEND m1 [CB 8 j0; C8 (Z_to_bv 64 (q_DCTX P + 26684)); C8 (Z_to_bv 64 (q_DST P)); C8 (Z_to_bv 64 OEND); C8 (q_dend P); C8 (Z_to_bv 64 (q_PFX P)); CB 8 j_c48; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (q_SEQ P)); C8 (Z_to_bv 64 (q_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (q_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (q_OFT P + 8)); C8 (Z_to_bv 64 sML); CB 8 j_c136; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (q_LITP P)); CB 24 jseq; CB 104 (le8 (q_s11 P) ++ le8 (q_s10 P) ++ le8 (q_s9 P) ++ le8 (q_s8 P) ++ le8 (q_s7 P) ++ le8 (q_s6 P) ++ le8 (q_s5 P) ++ le8 (q_s4 P) ++ le8 (q_s3 P) ++ le8 (q_s2 P) ++ le8 (q_s1 P) ++ le8 (q_s0 P) ++ le8 (q_ra P))] ->
  seqd_ibits P 91 bc ptr ->
  0 <= sLL < 2^(st_log (q_tLL P)) ->
  0 <= sOF < 2^(st_log (q_tOF P)) ->
  0 <= sML < 2^(st_log (q_tML P)) ->
  evt psegs (seqd_post P) (MS (mkR x1 (Z_to_bv 64 (q_SPV P + -304)) (q_gp P) (q_tp P) x5 x6 x7 (Z_to_bv 64 (q_DST P)) (Z_to_bv 64 (q_PFX P)) (Z_to_bv 64 (q_MLT P)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (q_nbSeq P)) x19 x20 x21 (Z_to_bv 64 BITMASK) x23 (Z_to_bv 64 (q_DST P)) x25 x26 (Z_to_bv 64 LEND) x28 x29 x30 x31) (q_F P) (Z_to_bv 64 0x1b878) (q_fc P) None m1 (seg_rom psegs)).

