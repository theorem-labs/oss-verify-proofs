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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_s_base RZ_seq_s_lbase RZ_seq_s_lkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition seqs_iinv (P : ssp) (OEND LLO LEND LOCV : Z) (m1 : fmem) (fr : list cell) : Prop :=
  rw_cells psegs m1 (v_SPV P + -336) fr /\
  dctx_ptrs psegs m1 (v_DCTX P) (Z_to_bv 64 (v_LLT P)) (Z_to_bv 64 (v_MLT P)) (Z_to_bv 64 (v_OFT P)) (v_huf P) /\
  bytes_at psegs m1 (v_LLT P) (map (Z_to_bv 8) (seq_table_bytes (v_tLL P))) /\
  bytes_at psegs m1 (v_OFT P) (map (Z_to_bv 8) (seq_table_bytes (v_tOF P))) /\
  bytes_at psegs m1 (v_MLT P) (map (Z_to_bv 8) (seq_table_bytes (v_tML P))) /\
  bytes_at psegs m1 (v_SEQ P) (map (Z_to_bv 8) (v_sq P)) /\
  rdbl psegs m1 LLO (LEND + 32) /\
  rdbl psegs m1 (v_DCTX P + 30372) (v_DCTX P + 95940) /\
  h5_viewed m1 (v_DCTX P) (v_ws P) (Z_to_bv 64 LOCV) /\
  seqs_xinv P m1 (seqs_fe P).

Lemma seqs_iinv_mi : forall P OEND LLO LEND LOCV m1 fr, seqs_iinv P OEND LLO LEND LOCV m1 fr -> mem_inv psegs m1.
Proof.
  intros P OEND LLO LEND LOCV m1 fr (_ & _ & _ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seqs_xinv] in XI. destruct XI as (_ & _ & _ & _ & _ & _ & MI). exact MI.
Qed.

(* [comment removed for export] *)
Lemma seqs_iinv_frame : forall P OEND LLO LEND LOCV m1 fr,
  seqs_static P OEND LLO LEND LOCV -> seqs_iinv P OEND LLO LEND LOCV m1 fr ->
  forall m2 fr2,
  munch [(v_SPV P - 336, v_SPV P)] m1 m2 -> wmono psegs m1 m2 -> mem_inv psegs m2 ->
  rw_cells psegs m2 (v_SPV P + -336) fr2 -> seqs_iinv P OEND LLO LEND LOCV m2 fr2.
Proof.
  intros P OEND LLO LEND LOCV m1 fr ST INV m2 fr2 MUL WML MI2 FR.
  destruct INV as (_ & PT & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exact FR|]. clear FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seqs_static seqs_xinv v_ra v_gp v_tp v_s0 v_s1 v_s2 v_s3 v_s4 v_s5 v_s6 v_s7 v_s8 v_s9 v_s10 v_s11 v_F v_fc v_m v_SPV v_lo v_DCTX v_DST v_CAP v_B0 v_B1 v_SEQ v_nbSeq v_LLT v_MLT v_OFT v_PFX v_LITP v_LBE v_LITB v_LOC v_sq v_tLL v_tOF v_tML v_huf v_r0 v_r1 v_r2 v_pde v_dend v_expd v_pcs v_dsz v_bt v_stg v_le v_fe v_ws] in *.
  sd_static_open ST. unfold held in *.
  pose proof (tbl_len_LL _ OKLL) as LLL. pose proof (tbl_len_OF _ OKOF) as LOF. pose proof (tbl_len_ML _ OKML) as LML.
  destruct XI as ((r0' & r1' & r2' & REP) & HH3 & BUF & STK & MU & WM & MI1).
  unfold dctx_ptrs, dctx_h3, DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation in *.
  split; [eapply rw_cells_transport; [exact PT | exact MUL | exact WML | cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply bytes_at_transport; [exact TLL | exact MUL | cbn [disjoint_from]; split; [clear - S28 S18 LLL; lia| exact I]]|].
  split; [eapply bytes_at_transport; [exact TOF | exact MUL | cbn [disjoint_from]; split; [clear - S29 S18 LOF; lia| exact I]]|].
  split; [eapply bytes_at_transport; [exact TML | exact MUL | cbn [disjoint_from]; split; [clear - S30 S18 LML; lia| exact I]]|].
  split; [eapply bytes_at_transport; [exact SQB | exact MUL | cbn [disjoint_from]; rewrite length_map; split; [clear - S25 S18; lia| exact I]]|].
  split; [eapply rdbl_transport; [exact LIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S26 S18 Hx; lia|exact I]]|].
  split; [eapply rdbl_transport; [exact XLIT | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S27 S18 Hx; lia|exact I]]|].
  split; [split; [eapply rw_cells_transport; [exact H5V | exact MUL | exact WML | unfold h5_vcells; cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S27 S18; lia|exact I]] | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S24 S18; lia|exact I]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S18; lia|exact I]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

(* [comment removed for export] *)
Lemma seqs_iinv_linv : forall P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq,
  seqs_iinv P OEND LLO LEND LOCV m1 (seqs_frame P OEND w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq) -> seqs_linv P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP.
Proof.
  intros P OEND LLO LEND LOCV m1 w0 lec cw bc ptr sLL sOF sML p0 p1 p2 LP jpad jseq (FR & _ & TLL & TOF & TML & SQB & LIT & XLIT & H5V & XI).
  split; [exists jpad, jseq; exact FR|]. repeat (split; [assumption|]). exact XI.
Qed.

Lemma seqs_iinv_eq : forall P OEND LLO LEND LOCV m1 fr fr', seqs_iinv P OEND LLO LEND LOCV m1 fr -> fr = fr' -> seqs_iinv P OEND LLO LEND LOCV m1 fr'.
Proof. intros P OEND LLO LEND LOCV m1 fr fr' H E. subst fr'. exact H. Qed.

(* [comment removed for export] *)
Definition seqs_ibits (P : ssp) (B bc ptr : Z) : Prop := 0 <= bc <= B /\ bit_ok (v_SEQ P) (zlen (v_sq P)) bc ptr.

(* [comment removed for export] *)
Definition ai_i0 (P : ssp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c88 w_c96 w_c104 w_c112 w_c120 w_c128 w_c136 w_c144 w_c152 w_c160 w_c168 : word) (jpad jseq : list byte)  (x1 x5 x6 x7 x8 x9 x10 x11 x12 x15 x16 x17 x19 x21 x22 x27 x28 x29 x31 : word),
  seqs_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 LEND); C8 w_c88; C4 w_c96; CB 4 jpad; C8 w_c104; C8 w_c112; C8 w_c120; C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (v_LITP P)); CB 24 jseq; CB 104 (le8 (v_s11 P) ++ le8 (v_s10 P) ++ le8 (v_s9 P) ++ le8 (v_s8 P) ++ le8 (v_s7 P) ++ le8 (v_s6 P) ++ le8 (v_s5 P) ++ le8 (v_s4 P) ++ le8 (v_s3 P) ++ le8 (v_s2 P) ++ le8 (v_s1 P) ++ le8 (v_s0 P) ++ le8 (v_ra P))] ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 (zlen (v_sq P))) x15 x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 (Z_to_bv 64 18446744073709551596) x21 x22 (Z_to_bv 64 OEND) (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 (v_DST P)) x27 x28 x29 (Z_to_bv 64 (v_DCTX P + 26684)) x31) (v_F P) (Z_to_bv 64 0x19880) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i1 (P : ssp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c96 w_c128 w_c136 w_c144 w_c152 w_c160 w_c168 : word) (jpad jseq : list byte) (cw : word) (bc ptr : Z) (d : Z) (x1 x5 x6 x7 x8 x9 x14 x16 x17 x19 x20 x21 x22 x27 x28 x29 x31 : word),
  seqs_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 LEND); C8 cw; C4 w_c96; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (v_SEQ P)); C8 (Z_to_bv 64 (v_SEQ P + 8)); C8 w_c128; C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (v_LITP P)); CB 24 jseq; CB 104 (le8 (v_s11 P) ++ le8 (v_s10 P) ++ le8 (v_s9 P) ++ le8 (v_s8 P) ++ le8 (v_s7 P) ++ le8 (v_s6 P) ++ le8 (v_s5 P) ++ le8 (v_s4 P) ++ le8 (v_s3 P) ++ le8 (v_s2 P) ++ le8 (v_s1 P) ++ le8 (v_s0 P) ++ le8 (v_ra P))] ->
  seqs_ibits P 64 bc ptr ->
  ptr = v_SEQ P + d ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 (Z_to_bv 64 (v_SEQ P + 8)) cw (Z_to_bv 64 d) (Z_to_bv 64 (v_SEQ P)) x14 (Z_to_bv 64 bc) x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 x20 x21 x22 (Z_to_bv 64 OEND) (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 (v_DST P)) x27 x28 x29 (Z_to_bv 64 (v_DCTX P + 26684)) x31) (v_F P) (Z_to_bv 64 0x19afc) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i2 (P : ssp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c96 w_c136 w_c144 w_c152 w_c160 w_c168 : word) (jpad jseq : list byte) (cw : word) (bc ptr : Z) (d sLL : Z) (x1 x5 x6 x7 x8 x9 x16 x19 x20 x21 x22 x27 x28 x29 x31 : word),
  seqs_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 (Z_to_bv 64 BITMASK); C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 LEND); C8 cw; C4 w_c96; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (v_SEQ P)); C8 (Z_to_bv 64 (v_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (v_LITP P)); CB 24 jseq; CB 104 (le8 (v_s11 P) ++ le8 (v_s10 P) ++ le8 (v_s9 P) ++ le8 (v_s8 P) ++ le8 (v_s7 P) ++ le8 (v_s6 P) ++ le8 (v_s5 P) ++ le8 (v_s4 P) ++ le8 (v_s3 P) ++ le8 (v_s2 P) ++ le8 (v_s1 P) ++ le8 (v_s0 P) ++ le8 (v_ra P))] ->
  seqs_ibits P 73 bc ptr ->
  ptr = v_SEQ P + d ->
  0 <= sLL < 2^(st_log (v_tLL P)) ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 (Z_to_bv 64 (v_SEQ P + 8)) cw (Z_to_bv 64 d) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 (v_LLT P)) (Z_to_bv 64 bc) x16 (Z_to_bv 64 65) (Z_to_bv 64 (v_DCTX P + 29896)) x19 x20 x21 x22 (Z_to_bv 64 OEND) (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 (v_DST P)) x27 x28 x29 (Z_to_bv 64 (v_DCTX P + 26684)) x31) (v_F P) (Z_to_bv 64 0x19b34) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i3 (P : ssp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c96 w_c136 w_c144 w_c152 w_c160 w_c168 : word) (jpad jseq : list byte) (cw : word) (bc ptr : Z) (sLL : Z) (x1 x5 x6 x7 x8 x9 x16 x17 x19 x20 x21 x22 x27 x28 x29 x31 : word),
  seqs_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 (Z_to_bv 64 BITMASK); C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 LEND); C8 cw; C4 w_c96; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (v_SEQ P)); C8 (Z_to_bv 64 (v_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 w_c136; C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (v_LITP P)); CB 24 jseq; CB 104 (le8 (v_s11 P) ++ le8 (v_s10 P) ++ le8 (v_s9 P) ++ le8 (v_s8 P) ++ le8 (v_s7 P) ++ le8 (v_s6 P) ++ le8 (v_s5 P) ++ le8 (v_s4 P) ++ le8 (v_s3 P) ++ le8 (v_s2 P) ++ le8 (v_s1 P) ++ le8 (v_s0 P) ++ le8 (v_ra P))] ->
  seqs_ibits P 73 bc ptr ->
  0 <= sLL < 2^(st_log (v_tLL P)) ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 (Z_to_bv 64 (v_SEQ P + 8)) cw (Z_to_bv 64 ptr) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 (v_LLT P)) (Z_to_bv 64 bc) x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 x20 x21 x22 (Z_to_bv 64 OEND) (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 (v_DST P)) x27 x28 x29 (Z_to_bv 64 (v_DCTX P + 26684)) x31) (v_F P) (Z_to_bv 64 0x19c4c) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i4 (P : ssp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c16 w_c24 w_c32 w_c40 w_c96 w_c152 w_c160 w_c168 : word) (jpad jseq : list byte) (cw : word) (bc ptr : Z) (sLL sOF : Z) (x1 x5 x6 x7 x8 x9 x15 x19 x20 x21 x22 x27 x28 x29 x31 : word),
  seqs_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 (Z_to_bv 64 69664); C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 (Z_to_bv 64 BITMASK); C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 LEND); C8 cw; C4 w_c96; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (v_SEQ P)); C8 (Z_to_bv 64 (v_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (v_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 w_c152; C8 w_c160; C8 w_c168; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (v_LITP P)); CB 24 jseq; CB 104 (le8 (v_s11 P) ++ le8 (v_s10 P) ++ le8 (v_s9 P) ++ le8 (v_s8 P) ++ le8 (v_s7 P) ++ le8 (v_s6 P) ++ le8 (v_s5 P) ++ le8 (v_s4 P) ++ le8 (v_s3 P) ++ le8 (v_s2 P) ++ le8 (v_s1 P) ++ le8 (v_s0 P) ++ le8 (v_ra P))] ->
  seqs_ibits P 82 bc ptr ->
  0 <= sLL < 2^(st_log (v_tLL P)) ->
  0 <= sOF < 2^(st_log (v_tOF P)) ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 (Z_to_bv 64 (v_SEQ P + 8)) cw (Z_to_bv 64 ptr) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 bc) x15 (Z_to_bv 64 (v_OFT P)) (Z_to_bv 64 65) (Z_to_bv 64 (v_DCTX P + 29896)) x19 x20 x21 x22 (Z_to_bv 64 OEND) (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 (v_DST P)) x27 x28 x29 (Z_to_bv 64 (v_DCTX P + 26684)) x31) (v_F P) (Z_to_bv 64 0x19c90) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i5 (P : ssp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c16 w_c24 w_c32 w_c40 w_c96 w_c152 w_c160 w_c168 : word) (jpad jseq : list byte) (cw : word) (bc ptr : Z) (sLL sOF : Z) (x1 x5 x6 x7 x8 x9 x15 x17 x19 x20 x21 x22 x27 x28 x29 x31 : word),
  seqs_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 (Z_to_bv 64 69664); C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 (Z_to_bv 64 BITMASK); C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 LEND); C8 cw; C4 w_c96; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (v_SEQ P)); C8 (Z_to_bv 64 (v_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (v_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 w_c152; C8 w_c160; C8 w_c168; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (v_LITP P)); CB 24 jseq; CB 104 (le8 (v_s11 P) ++ le8 (v_s10 P) ++ le8 (v_s9 P) ++ le8 (v_s8 P) ++ le8 (v_s7 P) ++ le8 (v_s6 P) ++ le8 (v_s5 P) ++ le8 (v_s4 P) ++ le8 (v_s3 P) ++ le8 (v_s2 P) ++ le8 (v_s1 P) ++ le8 (v_s0 P) ++ le8 (v_ra P))] ->
  seqs_ibits P 82 bc ptr ->
  0 <= sLL < 2^(st_log (v_tLL P)) ->
  0 <= sOF < 2^(st_log (v_tOF P)) ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 (Z_to_bv 64 (v_SEQ P + 8)) cw (Z_to_bv 64 ptr) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 bc) x15 (Z_to_bv 64 (v_OFT P)) x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 x20 x21 x22 (Z_to_bv 64 OEND) (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 (v_DST P)) x27 x28 x29 (Z_to_bv 64 (v_DCTX P + 26684)) x31) (v_F P) (Z_to_bv 64 0x19d94) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i6 (P : ssp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c16 w_c24 w_c40 w_c168 : word) (jpad jseq : list byte) (cw : word) (bc ptr : Z) (sLL sOF sML : Z) (x1 x5 x6 x7 x8 x9 x11 x17 x19 x20 x21 x22 x27 x28 x29 x31 : word),
  seqs_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 (Z_to_bv 64 69664); C8 w_c16; C8 w_c24; C8 (Z_to_bv 64 OEND); C8 w_c40; C8 (Z_to_bv 64 BITMASK); C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 LEND); C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (v_SEQ P)); C8 (Z_to_bv 64 (v_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (v_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (v_OFT P + 8)); C8 (Z_to_bv 64 sML); C8 w_c168; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (v_LITP P)); CB 24 jseq; CB 104 (le8 (v_s11 P) ++ le8 (v_s10 P) ++ le8 (v_s9 P) ++ le8 (v_s8 P) ++ le8 (v_s7 P) ++ le8 (v_s6 P) ++ le8 (v_s5 P) ++ le8 (v_s4 P) ++ le8 (v_s3 P) ++ le8 (v_s2 P) ++ le8 (v_s1 P) ++ le8 (v_s0 P) ++ le8 (v_ra P))] ->
  seqs_ibits P 91 bc ptr ->
  0 <= sLL < 2^(st_log (v_tLL P)) ->
  0 <= sOF < 2^(st_log (v_tOF P)) ->
  0 <= sML < 2^(st_log (v_tML P)) ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 (Z_to_bv 64 (v_SEQ P + 8)) x11 (Z_to_bv 64 ptr) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 bc) (Z_to_bv 64 (v_MLT P)) (Z_to_bv 64 65) x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 x20 x21 x22 (Z_to_bv 64 OEND) (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 (v_DST P)) x27 x28 x29 (Z_to_bv 64 (v_DCTX P + 26684)) x31) (v_F P) (Z_to_bv 64 0x19dd4) (v_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i7 (P : ssp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c16 w_c24 w_c40 w_c168 : word) (jpad jseq : list byte) (cw : word) (bc ptr : Z) (sLL sOF sML : Z) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x19 x20 x21 x22 x27 x28 x29 x31 : word),
  seqs_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 (Z_to_bv 64 69664); C8 w_c16; C8 w_c24; C8 (Z_to_bv 64 OEND); C8 w_c40; C8 (Z_to_bv 64 BITMASK); C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 LEND); C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (v_SEQ P)); C8 (Z_to_bv 64 (v_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (v_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (v_OFT P + 8)); C8 (Z_to_bv 64 sML); C8 w_c168; C8 p0; C8 p1; C8 p2; C8 (Z_to_bv 64 (v_LITP P)); CB 24 jseq; CB 104 (le8 (v_s11 P) ++ le8 (v_s10 P) ++ le8 (v_s9 P) ++ le8 (v_s8 P) ++ le8 (v_s7 P) ++ le8 (v_s6 P) ++ le8 (v_s5 P) ++ le8 (v_s4 P) ++ le8 (v_s3 P) ++ le8 (v_s2 P) ++ le8 (v_s1 P) ++ le8 (v_s0 P) ++ le8 (v_ra P))] ->
  seqs_ibits P 91 bc ptr ->
  0 <= sLL < 2^(st_log (v_tLL P)) ->
  0 <= sOF < 2^(st_log (v_tOF P)) ->
  0 <= sML < 2^(st_log (v_tML P)) ->
  evt psegs (seqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_SPV P + -336)) (v_gp P) (v_tp P) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (v_MLT P)) x16 x17 (Z_to_bv 64 (v_DCTX P + 29896)) x19 x20 x21 x22 (Z_to_bv 64 OEND) (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_DCTX P)) (Z_to_bv 64 (v_DST P)) x27 x28 x29 (Z_to_bv 64 (v_DCTX P + 26684)) x31) (v_F P) (Z_to_bv 64 0x19e7c) (v_fc P) None m1 (seg_rom psegs)).

