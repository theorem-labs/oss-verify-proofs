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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition seql_iinv (P : slp) (OEND LLO LEND LOCV : Z) (m1 : fmem) (fr : list cell) : Prop :=
  rw_cells psegs m1 (y_SPV P + -608) fr /\
  dctx_ptrs psegs m1 (y_DCTX P) (Z_to_bv 64 (y_LLT P)) (Z_to_bv 64 (y_MLT P)) (Z_to_bv 64 (y_OFT P)) (y_huf P) /\
  bytes_at psegs m1 (y_LLT P) (map (Z_to_bv 8) (seq_table_bytes (y_tLL P))) /\
  bytes_at psegs m1 (y_OFT P) (map (Z_to_bv 8) (seq_table_bytes (y_tOF P))) /\
  bytes_at psegs m1 (y_MLT P) (map (Z_to_bv 8) (seq_table_bytes (y_tML P))) /\
  bytes_at psegs m1 (y_SEQ P) (map (Z_to_bv 8) (y_sq P)) /\
  rdbl psegs m1 LLO (LEND + 32) /\
  (LOCV = 2 -> rdbl psegs m1 (y_DCTX P + 30372) (y_DCTX P + 95940)) /\
  h5_viewed m1 (y_DCTX P) (y_ws P) (Z_to_bv 64 LOCV) /\
  seql_xinv P m1 (seql_fe P).

Lemma seql_iinv_mi : forall P OEND LLO LEND LOCV m1 fr, seql_iinv P OEND LLO LEND LOCV m1 fr -> mem_inv psegs m1.
Proof.
  intros P OEND LLO LEND LOCV m1 fr (_ & _ & _ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seql_xinv] in XI. destruct XI as (_ & _ & _ & _ & _ & _ & MI). exact MI.
Qed.

(* [comment removed for export] *)
Lemma seql_iinv_frame : forall P OEND LLO LEND LOCV m1 fr,
  seql_static P OEND LLO LEND LOCV -> seql_iinv P OEND LLO LEND LOCV m1 fr ->
  forall m2 fr2,
  munch [(y_SPV P - 608, y_SPV P)] m1 m2 -> wmono psegs m1 m2 -> mem_inv psegs m2 ->
  rw_cells psegs m2 (y_SPV P + -608) fr2 -> seql_iinv P OEND LLO LEND LOCV m2 fr2.
Proof.
  intros P OEND LLO LEND LOCV m1 fr ST INV m2 fr2 MUL WML MI2 FR.
  destruct INV as (_ & PT & TLL & TOF & TML & SQB & LIT & XLIT & (H5V & H5L) & XI).
  split; [exact FR|]. clear FR.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws].
  cbn [seql_static seql_xinv y_ra y_gp y_tp y_s0 y_s1 y_s2 y_s3 y_s4 y_s5 y_s6 y_s7 y_s8 y_s9 y_s10 y_s11 y_F y_fc y_m y_SPV y_lo y_DCTX y_DST y_CAP y_B0 y_B1 y_SEQ y_nbSeq y_LLT y_MLT y_OFT y_PFX y_LITP y_LBE y_LITB y_LOC y_sq y_tLL y_tOF y_tML y_huf y_r0 y_r1 y_r2 y_pde y_dend y_expd y_pcs y_dsz y_bt y_stg y_le y_fe y_ws] in *.
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
  split; [intros HL2; eapply rdbl_transport; [exact (XLIT HL2) | exact MUL | intros x Hx; left; cbn [outside]; split; [clear - S27 S18 Hx; lia|exact I]]|].
  split; [split; [eapply rw_cells_transport; [exact H5V | exact MUL | exact WML | unfold h5_vcells; cbn [disjoint_from cells_size csize Nat.add]; split; [clear - S27 S18; lia|exact I]] | exact H5L]|].
  split; [exists r0', r1', r2'; eapply rw_cells_transport; [exact REP | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply rw_cells_transport; [exact HH3 | exact MUL | exact WML | cbn [disjoint_from cells_size csize]; split; [clear - S27 S18; lia|exact I]]|].
  split; [eapply stk_transport_disjoint; [exact BUF | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S24 S18; lia|exact I]]|].
  split; [eapply stk_transport_disjoint; [exact STK | exact MUL | exact WML | cbn [disjoint_from]; split; [clear - S18; lia|exact I]]|].
  split; [eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MUL]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia]|].
  split; [eapply wmono_trans; [exact WM | exact WML] | exact MI2].
Qed.

(* [comment removed for export] *)
Lemma seql_iinv_linv : forall P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 c128 lec c144 c152 c160 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq,
  seql_iinv P OEND LLO LEND LOCV m1 (seql_frame P OEND w0 c8 c16 c48 c56 c128 lec c144 c152 c160 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq) -> seql_linv P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 c128 lec c144 c152 c160 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP.
Proof.
  intros P OEND LLO LEND LOCV m1 w0 c8 c16 c48 c56 c128 lec c144 c152 c160 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq (FR & _ & TLL & TOF & TML & SQB & LIT & XLIT & H5V & XI).
  split; [exists jpad, jseq; exact FR|]. repeat (split; [assumption|]). exact XI.
Qed.

Lemma seql_iinv_eq : forall P OEND LLO LEND LOCV m1 fr fr', seql_iinv P OEND LLO LEND LOCV m1 fr -> fr = fr' -> seql_iinv P OEND LLO LEND LOCV m1 fr'.
Proof. intros P OEND LLO LEND LOCV m1 fr fr' H E. subst fr'. exact H. Qed.

(* [comment removed for export] *)
Definition seql_ibits (P : slp) (B bc ptr : Z) : Prop := 0 <= bc <= B /\ bit_ok (y_SEQ P) (zlen (y_sq P)) bc ptr.

(* [comment removed for export] *)
Definition ai_i0 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c96 w_c104 w_c112 w_c128 w_c144 w_c152 w_c160 w_c168 w_c176 w_c184 w_c192 w_c200 w_c208 w_c216 w_c224 w_c232 w_c240 w_c248 : word) (jpad jseq : list byte) (rl rm ro : Z -> Z) (x1 x5 x6 x7 x12 x15 x16 x17 x21 x22 x23 x25 x27 x28 x29 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 (y_dend P); C8 (Z_to_bv 64 (y_PFX P)); C8 w_c96; C8 w_c104; C8 w_c112; C8 (Z_to_bv 64 (y_PFX P)); C8 w_c128; C8 (Z_to_bv 64 LEND); C8 w_c144; C8 w_c152; C8 w_c160; C8 w_c168; C4 w_c176; CB 4 jpad; C8 w_c184; C8 w_c192; C8 w_c200; C8 w_c208; C8 w_c216; C8 w_c224; C8 w_c232; C8 w_c240; C8 w_c248; C8 p0; C8 p1; C8 p2; CB 192 (seql_ring_bytes rl rm ro); C8 (Z_to_bv 64 (y_LITP P)); CB 24 jseq; CB 104 (le8 (y_s11 P) ++ le8 (y_s10 P) ++ le8 (y_s9 P) ++ le8 (y_s8 P) ++ le8 (y_s7 P) ++ le8 (y_s6 P) ++ le8 (y_s5 P) ++ le8 (y_s4 P) ++ le8 (y_s3 P) ++ le8 (y_s2 P) ++ le8 (y_s1 P) ++ le8 (y_s0 P) ++ le8 (y_ra P))] ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 (y_DCTX P + 26684)) (Z_to_bv 64 (y_DST P)) p0 p1 x12 (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 (zlen (y_sq P))) x15 x16 x17 (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (Z.min (y_nbSeq P) 8)) (Z_to_bv 64 OEND) x21 x22 x23 (Z_to_bv 64 (y_nbSeq P)) x25 (Z_to_bv 64 18446744073709551596) x27 x28 x29 (Z_to_bv 64 (y_DCTX P + 29896)) x31) (y_F P) (Z_to_bv 64 0x172b8) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i1 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c96 w_c104 w_c112 w_c144 w_c152 w_c160 w_c176 w_c208 w_c216 w_c224 w_c232 w_c240 w_c248 : word) (jpad jseq : list byte) (rl rm ro : Z -> Z) (cw : word) (bc ptr : Z) (d : Z) (x1 x6 x7 x15 x16 x17 x21 x22 x23 x25 x26 x27 x28 x29 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 (y_dend P); C8 (Z_to_bv 64 (y_PFX P)); C8 w_c96; C8 w_c104; C8 w_c112; C8 (Z_to_bv 64 (y_PFX P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 (Z_to_bv 64 LEND); C8 w_c144; C8 w_c152; C8 w_c160; C8 cw; C4 w_c176; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 w_c208; C8 w_c216; C8 w_c224; C8 w_c232; C8 w_c240; C8 w_c248; C8 p0; C8 p1; C8 p2; CB 192 (seql_ring_bytes rl rm ro); C8 (Z_to_bv 64 (y_LITP P)); CB 24 jseq; CB 104 (le8 (y_s11 P) ++ le8 (y_s10 P) ++ le8 (y_s9 P) ++ le8 (y_s8 P) ++ le8 (y_s7 P) ++ le8 (y_s6 P) ++ le8 (y_s5 P) ++ le8 (y_s4 P) ++ le8 (y_s3 P) ++ le8 (y_s2 P) ++ le8 (y_s1 P) ++ le8 (y_s0 P) ++ le8 (y_ra P))] ->
  seql_ibits P 64 bc ptr ->
  ptr = y_SEQ P + d ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) cw x6 x7 (Z_to_bv 64 (y_DCTX P + 26684)) (Z_to_bv 64 (y_DST P)) p0 p1 (Z_to_bv 64 d) (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 bc) x15 x16 x17 (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (Z.min (y_nbSeq P) 8)) (Z_to_bv 64 OEND) x21 x22 x23 (Z_to_bv 64 (y_nbSeq P)) x25 x26 x27 x28 x29 (Z_to_bv 64 (y_DCTX P + 29896)) x31) (y_F P) (Z_to_bv 64 0x17560) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i2 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c96 w_c104 w_c112 w_c152 w_c160 w_c176 w_c208 w_c216 w_c224 w_c232 w_c240 w_c248 : word) (jpad jseq : list byte) (rl rm ro : Z -> Z) (cw : word) (bc ptr : Z) (d sLL : Z) (x1 x6 x7 x14 x21 x22 x23 x25 x26 x27 x28 x29 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 (y_dend P); C8 (Z_to_bv 64 (y_PFX P)); C8 w_c96; C8 w_c104; C8 w_c112; C8 (Z_to_bv 64 (y_PFX P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 (Z_to_bv 64 LEND); C8 (Z_to_bv 64 BITMASK); C8 w_c152; C8 w_c160; C8 cw; C4 w_c176; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 w_c208; C8 w_c216; C8 w_c224; C8 w_c232; C8 w_c240; C8 w_c248; C8 p0; C8 p1; C8 p2; CB 192 (seql_ring_bytes rl rm ro); C8 (Z_to_bv 64 (y_LITP P)); CB 24 jseq; CB 104 (le8 (y_s11 P) ++ le8 (y_s10 P) ++ le8 (y_s9 P) ++ le8 (y_s8 P) ++ le8 (y_s7 P) ++ le8 (y_s6 P) ++ le8 (y_s5 P) ++ le8 (y_s4 P) ++ le8 (y_s3 P) ++ le8 (y_s2 P) ++ le8 (y_s1 P) ++ le8 (y_s0 P) ++ le8 (y_ra P))] ->
  seql_ibits P 73 bc ptr ->
  ptr = y_SEQ P + d ->
  0 <= sLL < 2^(st_log (y_tLL P)) ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) cw x6 x7 (Z_to_bv 64 (y_DCTX P + 26684)) (Z_to_bv 64 (y_DST P)) p0 p1 (Z_to_bv 64 d) (Z_to_bv 64 (y_SEQ P)) x14 (Z_to_bv 64 sLL) (Z_to_bv 64 (y_LLT P)) (Z_to_bv 64 bc) (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (Z.min (y_nbSeq P) 8)) (Z_to_bv 64 OEND) x21 x22 x23 (Z_to_bv 64 (y_nbSeq P)) x25 x26 x27 x28 x29 (Z_to_bv 64 (y_DCTX P + 29896)) x31) (y_F P) (Z_to_bv 64 0x17590) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i3 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c96 w_c104 w_c112 w_c152 w_c160 w_c176 w_c216 w_c224 w_c232 w_c240 w_c248 : word) (jpad jseq : list byte) (rl rm ro : Z -> Z) (cw : word) (bc ptr : Z) (sLL : Z) (x1 x6 x7 x12 x21 x22 x23 x25 x26 x27 x28 x29 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 (y_dend P); C8 (Z_to_bv 64 (y_PFX P)); C8 w_c96; C8 w_c104; C8 w_c112; C8 (Z_to_bv 64 (y_PFX P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 (Z_to_bv 64 LEND); C8 (Z_to_bv 64 BITMASK); C8 w_c152; C8 w_c160; C8 cw; C4 w_c176; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 w_c216; C8 w_c224; C8 w_c232; C8 w_c240; C8 w_c248; C8 p0; C8 p1; C8 p2; CB 192 (seql_ring_bytes rl rm ro); C8 (Z_to_bv 64 (y_LITP P)); CB 24 jseq; CB 104 (le8 (y_s11 P) ++ le8 (y_s10 P) ++ le8 (y_s9 P) ++ le8 (y_s8 P) ++ le8 (y_s7 P) ++ le8 (y_s6 P) ++ le8 (y_s5 P) ++ le8 (y_s4 P) ++ le8 (y_s3 P) ++ le8 (y_s2 P) ++ le8 (y_s1 P) ++ le8 (y_s0 P) ++ le8 (y_ra P))] ->
  seql_ibits P 73 bc ptr ->
  0 <= sLL < 2^(st_log (y_tLL P)) ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) cw x6 x7 (Z_to_bv 64 (y_DCTX P + 26684)) (Z_to_bv 64 (y_DST P)) p0 p1 x12 (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 ptr) (Z_to_bv 64 sLL) (Z_to_bv 64 (y_LLT P)) (Z_to_bv 64 bc) (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (Z.min (y_nbSeq P) 8)) (Z_to_bv 64 OEND) x21 x22 x23 (Z_to_bv 64 (y_nbSeq P)) x25 x26 x27 x28 x29 (Z_to_bv 64 (y_DCTX P + 29896)) x31) (y_F P) (Z_to_bv 64 0x176b8) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i4 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c96 w_c104 w_c112 w_c152 w_c176 w_c224 w_c232 w_c240 w_c248 : word) (jpad jseq : list byte) (rl rm ro : Z -> Z) (cw : word) (bc ptr : Z) (sLL sOF : Z) (x1 x6 x16 x21 x22 x23 x25 x26 x27 x28 x29 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 (y_dend P); C8 (Z_to_bv 64 (y_PFX P)); C8 w_c96; C8 w_c104; C8 w_c112; C8 (Z_to_bv 64 (y_PFX P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 (Z_to_bv 64 LEND); C8 (Z_to_bv 64 BITMASK); C8 w_c152; C8 (Z_to_bv 64 (y_LLT P + 8)); C8 cw; C4 w_c176; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 w_c224; C8 w_c232; C8 w_c240; C8 w_c248; C8 p0; C8 p1; C8 p2; CB 192 (seql_ring_bytes rl rm ro); C8 (Z_to_bv 64 (y_LITP P)); CB 24 jseq; CB 104 (le8 (y_s11 P) ++ le8 (y_s10 P) ++ le8 (y_s9 P) ++ le8 (y_s8 P) ++ le8 (y_s7 P) ++ le8 (y_s6 P) ++ le8 (y_s5 P) ++ le8 (y_s4 P) ++ le8 (y_s3 P) ++ le8 (y_s2 P) ++ le8 (y_s1 P) ++ le8 (y_s0 P) ++ le8 (y_ra P))] ->
  seql_ibits P 82 bc ptr ->
  0 <= sLL < 2^(st_log (y_tLL P)) ->
  0 <= sOF < 2^(st_log (y_tOF P)) ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) cw x6 (Z_to_bv 64 (y_OFT P)) (Z_to_bv 64 (y_DCTX P + 26684)) (Z_to_bv 64 (y_DST P)) p0 p1 (Z_to_bv 64 bc) (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 ptr) (Z_to_bv 64 sLL) x16 (Z_to_bv 64 sOF) (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (Z.min (y_nbSeq P) 8)) (Z_to_bv 64 OEND) x21 x22 x23 (Z_to_bv 64 (y_nbSeq P)) x25 x26 x27 x28 x29 (Z_to_bv 64 (y_DCTX P + 29896)) x31) (y_F P) (Z_to_bv 64 0x176ec) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i5 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c96 w_c104 w_c152 w_c176 w_c232 w_c240 w_c248 : word) (jpad jseq : list byte) (rl rm ro : Z -> Z) (cw : word) (bc ptr : Z) (sLL sOF : Z) (x1 x6 x16 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 (y_dend P); C8 (Z_to_bv 64 (y_PFX P)); C8 w_c96; C8 w_c104; C8 (Z_to_bv 64 (y_DCTX P + 29896)); C8 (Z_to_bv 64 (y_PFX P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 (Z_to_bv 64 LEND); C8 (Z_to_bv 64 BITMASK); C8 w_c152; C8 (Z_to_bv 64 (y_LLT P + 8)); C8 cw; C4 w_c176; CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 w_c232; C8 w_c240; C8 w_c248; C8 p0; C8 p1; C8 p2; CB 192 (seql_ring_bytes rl rm ro); C8 (Z_to_bv 64 (y_LITP P)); CB 24 jseq; CB 104 (le8 (y_s11 P) ++ le8 (y_s10 P) ++ le8 (y_s9 P) ++ le8 (y_s8 P) ++ le8 (y_s7 P) ++ le8 (y_s6 P) ++ le8 (y_s5 P) ++ le8 (y_s4 P) ++ le8 (y_s3 P) ++ le8 (y_s2 P) ++ le8 (y_s1 P) ++ le8 (y_s0 P) ++ le8 (y_ra P))] ->
  seql_ibits P 82 bc ptr ->
  0 <= sLL < 2^(st_log (y_tLL P)) ->
  0 <= sOF < 2^(st_log (y_tOF P)) ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) cw x6 (Z_to_bv 64 (y_OFT P)) (Z_to_bv 64 (y_DCTX P + 26684)) (Z_to_bv 64 (y_DST P)) p0 p1 (Z_to_bv 64 bc) (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 ptr) (Z_to_bv 64 sLL) x16 (Z_to_bv 64 sOF) (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (Z.min (y_nbSeq P) 8)) (Z_to_bv 64 OEND) x21 x22 x23 (Z_to_bv 64 (y_nbSeq P)) x25 x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x17800) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i6 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c8 w_c16 w_c24 w_c32 w_c40 w_c48 w_c56 w_c64 w_c72 w_c96 w_c104 w_c240 w_c248 : word) (jpad jseq : list byte) (rl rm ro : Z -> Z) (cw : word) (bc ptr : Z) (sLL sOF sML : Z) (x1 x7 x12 x16 x21 x22 x23 x25 x26 x27 x30 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 w_c8; C8 w_c16; C8 w_c24; C8 w_c32; C8 w_c40; C8 w_c48; C8 w_c56; C8 w_c64; C8 w_c72; C8 (y_dend P); C8 (Z_to_bv 64 (y_PFX P)); C8 w_c96; C8 w_c104; C8 (Z_to_bv 64 (y_DCTX P + 29896)); C8 (Z_to_bv 64 (y_PFX P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 (Z_to_bv 64 LEND); C8 (Z_to_bv 64 BITMASK); C8 (Z_to_bv 64 (y_OFT P + 8)); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (y_OFT P + 8)); C8 w_c240; C8 w_c248; C8 p0; C8 p1; C8 p2; CB 192 (seql_ring_bytes rl rm ro); C8 (Z_to_bv 64 (y_LITP P)); CB 24 jseq; CB 104 (le8 (y_s11 P) ++ le8 (y_s10 P) ++ le8 (y_s9 P) ++ le8 (y_s8 P) ++ le8 (y_s7 P) ++ le8 (y_s6 P) ++ le8 (y_s5 P) ++ le8 (y_s4 P) ++ le8 (y_s3 P) ++ le8 (y_s2 P) ++ le8 (y_s1 P) ++ le8 (y_s0 P) ++ le8 (y_ra P))] ->
  seql_ibits P 91 bc ptr ->
  0 <= sLL < 2^(st_log (y_tLL P)) ->
  0 <= sOF < 2^(st_log (y_tOF P)) ->
  0 <= sML < 2^(st_log (y_tML P)) ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) cw (Z_to_bv 64 bc) x7 (Z_to_bv 64 (y_DCTX P + 26684)) (Z_to_bv 64 (y_DST P)) p0 p1 x12 (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 ptr) (Z_to_bv 64 sLL) x16 (Z_to_bv 64 sOF) (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (Z.min (y_nbSeq P) 8)) (Z_to_bv 64 OEND) x21 x22 x23 (Z_to_bv 64 (y_nbSeq P)) x25 x26 x27 (Z_to_bv 64 sML) (Z_to_bv 64 (y_MLT P)) x30 x31) (y_F P) (Z_to_bv 64 0x17838) (y_fc P) None m1 (seg_rom psegs)).

(* [comment removed for export] *)
Definition ai_i7 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (p0 p1 p2 w_c0 w_c8 w_c16 w_c32 w_c48 w_c56 w_c72 w_c96 w_c104 w_c248 : word) (jpad jseq : list byte) (rl rm ro : Z -> Z) (cw : word) (bc ptr : Z) (sLL sOF sML : Z) (x1 x7 x8 x12 x16 x18 x19 x21 x22 x23 x25 x26 x27 x30 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 [C8 w_c0; C8 w_c8; C8 w_c16; C8 (Z_to_bv 64 (y_DCTX P + 26684)); C8 w_c32; C8 (Z_to_bv 64 (y_DCTX P)); C8 w_c48; C8 w_c56; C8 (Z_to_bv 64 (Z.min (y_nbSeq P) 8)); C8 w_c72; C8 (y_dend P); C8 (Z_to_bv 64 (y_PFX P)); C8 w_c96; C8 w_c104; C8 (Z_to_bv 64 (y_DCTX P + 29896)); C8 (Z_to_bv 64 (y_PFX P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 (Z_to_bv 64 LEND); C8 (Z_to_bv 64 BITMASK); C8 (Z_to_bv 64 (y_OFT P + 8)); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8)); C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (y_OFT P + 8)); C8 (Z_to_bv 64 sML); C8 w_c248; C8 p0; C8 p1; C8 p2; CB 192 (seql_ring_bytes rl rm ro); C8 (Z_to_bv 64 (y_LITP P)); CB 24 jseq; CB 104 (le8 (y_s11 P) ++ le8 (y_s10 P) ++ le8 (y_s9 P) ++ le8 (y_s8 P) ++ le8 (y_s7 P) ++ le8 (y_s6 P) ++ le8 (y_s5 P) ++ le8 (y_s4 P) ++ le8 (y_s3 P) ++ le8 (y_s2 P) ++ le8 (y_s1 P) ++ le8 (y_s0 P) ++ le8 (y_ra P))] ->
  seql_ibits P 91 bc ptr ->
  0 <= sLL < 2^(st_log (y_tLL P)) ->
  0 <= sOF < 2^(st_log (y_tOF P)) ->
  0 <= sML < 2^(st_log (y_tML P)) ->
  evt psegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -608)) (y_gp P) (y_tp P) cw (Z_to_bv 64 bc) x7 x8 (Z_to_bv 64 (y_DST P)) p0 p1 x12 (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 ptr) (Z_to_bv 64 sLL) x16 (Z_to_bv 64 sOF) x18 x19 (Z_to_bv 64 OEND) x21 x22 x23 (Z_to_bv 64 (y_nbSeq P)) x25 x26 x27 (Z_to_bv 64 sML) (Z_to_bv 64 (y_MLT P)) x30 x31) (y_F P) (Z_to_bv 64 0x178f8) (y_fc P) None m1 (seg_rom psegs)).

