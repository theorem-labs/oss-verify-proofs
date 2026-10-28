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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memcpy F_memmove RZ_seq_iface RZ_seq_kit RZ_seq_gkit RZ_seq_l_base RZ_seq_l_lbase RZ_seq_l_lkit.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition seql_iinv (P : slp) (OEND LLO LEND LOCV : Z) (m1 : fmem) (fr : list cell) : Prop :=
  rw_cells usegs m1 (y_SPV P + -688) fr /\
  dctx_ptrs usegs m1 (y_DCTX P) (Z_to_bv 64 (y_LLT P)) (Z_to_bv 64 (y_MLT P)) (Z_to_bv 64 (y_OFT P)) (y_huf P) /\
  bytes_at usegs m1 (y_LLT P) (map (Z_to_bv 8) (seq_table_bytes (y_tLL P))) /\
  bytes_at usegs m1 (y_OFT P) (map (Z_to_bv 8) (seq_table_bytes (y_tOF P))) /\
  bytes_at usegs m1 (y_MLT P) (map (Z_to_bv 8) (seq_table_bytes (y_tML P))) /\
  bytes_at usegs m1 (y_SEQ P) (map (Z_to_bv 8) (y_sq P)) /\
  rdbl usegs m1 LLO (LEND + 32) /\
  (LOCV = 2 -> rdbl usegs m1 (y_DCTX P + 30372) (y_DCTX P + 95940)) /\
  h5_viewed m1 (y_DCTX P) (y_ws P) (Z_to_bv 64 LOCV) /\
  seql_xinv P m1 (seql_fe P).

Lemma seql_iinv_mi : forall P OEND LLO LEND LOCV m1 fr, seql_iinv P OEND LLO LEND LOCV m1 fr -> mem_inv usegs m1.
Proof.
  intros P OEND LLO LEND LOCV m1 fr (_ & _ & _ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws]. cbn [seql_xinv] in XI. destruct XI as (_ & _ & _ & _ & _ & _ & MI). exact MI.
Qed.

(* [comment removed for export] *)
Lemma seql_iinv_frame : forall P OEND LLO LEND LOCV m1 fr,
  seql_static P OEND LLO LEND LOCV -> seql_iinv P OEND LLO LEND LOCV m1 fr ->
  forall m2 fr2,
  munch [(y_SPV P - 688, y_SPV P)] m1 m2 -> wmono usegs m1 m2 -> mem_inv usegs m2 ->
  rw_cells usegs m2 (y_SPV P + -688) fr2 -> seql_iinv P OEND LLO LEND LOCV m2 fr2.
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
Lemma seql_iinv_linv : forall P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq,
  seql_iinv P OEND LLO LEND LOCV m1 (seql_frame P OEND c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq) -> seql_linv P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP.
Proof.
  intros P OEND LLO LEND LOCV m1 c0 c8 c16 c24 c40 c48 c64 c72 c104 c128 c152 c168 c176 c184 c216 c224 c232 c240 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP jpad jseq (FR & _ & TLL & TOF & TML & SQB & LIT & XLIT & H5V & XI).
  split; [exists jpad, jseq; exact FR|]. repeat (split; [assumption|]). exact XI.
Qed.

Lemma seql_iinv_eq : forall P OEND LLO LEND LOCV m1 fr fr', seql_iinv P OEND LLO LEND LOCV m1 fr -> fr = fr' -> seql_iinv P OEND LLO LEND LOCV m1 fr'.
Proof. intros P OEND LLO LEND LOCV m1 fr fr' H E. subst fr'. exact H. Qed.

(* [comment removed for export] *)
Definition seql_ibits (P : slp) (B bc ptr : Z) : Prop := 0 <= bc <= B /\ bit_ok (y_SEQ P) (zlen (y_sq P)) bc ptr.

Definition seql_ifr (P : slp) (OEND LEND : Z) (c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 : word) (bd st : list cell) (p0 p1 p2 : word) (jring jseq : list byte) : list cell :=
  [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 (Z_to_bv 64 (y_DCTX P)); C8 c64; C8 c72; C8 (Z_to_bv 64 (Z.min (y_nbSeq P) 8)); C8 c88; C8 (Z_to_bv 64 (y_DST P)); C8 c104; C8 (y_dend P); C8 (Z_to_bv 64 (y_PFX P)); C8 c128; C8 (Z_to_bv 64 (y_DCTX P + 26684)); C8 c144; C8 c152; C8 (Z_to_bv 64 OEND); C8 c168; C8 c176; C8 c184; C8 (Z_to_bv 64 (y_nbSeq P)); C8 (Z_to_bv 64 (y_PFX P)); C8 (Z_to_bv 64 (y_DCTX P + 29896)); C8 c216; C8 c224; C8 c232; C8 (Z_to_bv 64 LEND)] ++ bd ++ st ++
  [C8 p0; C8 p1; C8 p2; CB 192 jring; C8 (Z_to_bv 64 (y_LITP P)); CB 24 jseq] ++ seql_saved P.

(* [comment removed for export] *)
Definition ai_i0 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 u288 u296 u304 u312 u320 u328 p0 p1 p2 : word) (jbd jring jseq : list byte) (x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 (seql_ifr P OEND LEND c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c168 c176 c184 c216 c224 c232 [CB 40 jbd] [C8 u288; C8 u296; C8 u304; C8 u312; C8 u320; C8 u328] p0 p1 p2 jring jseq) ->
  evt usegs (seql_post P) (MS (mkR (Z_to_bv 64 0x17be0) (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 x8 x9 (Z_to_bv 64 (y_SPV P + -440)) (Z_to_bv 64 (y_SEQ P)) (Z_to_bv 64 (zlen (y_sq P))) x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1d904) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_i1 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw u288 u296 u304 u312 u320 u328 p0 p1 p2 : word) (jpad jring jseq : list byte) (bc ptr : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 (seql_ifr P OEND LEND c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 (Z_to_bv 64 (2^60)) c176 c184 c216 c224 c232 [C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8))] [C8 u288; C8 u296; C8 u304; C8 u312; C8 u320; C8 u328] p0 p1 p2 jring jseq) ->
  seql_ibits P 64 bc ptr -> 1 <= zlen (y_sq P) ->
  evt usegs (seql_post P) (MS (mkR (Z_to_bv 64 0x17c20) (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (y_SPV P + -352)) (Z_to_bv 64 (y_SPV P + -400)) (Z_to_bv 64 (y_SPV P + -440)) (Z_to_bv 64 (y_LLT P)) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (y_DST P - y_PFX P)) x20 x21 x22 x23 x24 (Z_to_bv 64 (y_DST P)) x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1db98) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_i2 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw u304 u312 u320 u328 p0 p1 p2 : word) (jpad jring jseq : list byte) (bc ptr sLL : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 (seql_ifr P OEND LEND c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 (Z_to_bv 64 (2^60)) c176 c184 c216 c224 c232 [C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8))] [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 u304; C8 u312; C8 u320; C8 u328] p0 p1 p2 jring jseq) ->
  seql_ibits P 73 bc ptr -> 1 <= zlen (y_sq P) ->
  0 <= sLL < 2^(st_log (y_tLL P)) ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (y_SPV P + -352)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (y_DST P - y_PFX P)) x20 x21 x22 x23 x24 (Z_to_bv 64 (y_DST P)) x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x17c20) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_i3 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw u304 u312 u320 u328 p0 p1 p2 : word) (jpad jring jseq : list byte) (bc ptr sLL : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 (seql_ifr P OEND LEND c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 (Z_to_bv 64 (2^60)) c176 c184 c216 c224 c232 [C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8))] [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 u304; C8 u312; C8 u320; C8 u328] p0 p1 p2 jring jseq) ->
  seql_ibits P 73 bc ptr -> 1 <= zlen (y_sq P) ->
  0 <= sLL < 2^(st_log (y_tLL P)) ->
  evt usegs (seql_post P) (MS (mkR (Z_to_bv 64 0x17c30) (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (y_SPV P + -352)) (Z_to_bv 64 (y_SPV P + -384)) (Z_to_bv 64 (y_SPV P + -440)) (Z_to_bv 64 (y_OFT P)) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (y_DST P - y_PFX P)) x20 x21 x22 x23 x24 (Z_to_bv 64 (y_DST P)) x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1db98) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_i4 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw u320 u328 p0 p1 p2 : word) (jpad jring jseq : list byte) (bc ptr sLL sOF : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 (seql_ifr P OEND LEND c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 (Z_to_bv 64 (2^60)) c176 c184 c216 c224 c232 [C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8))] [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (y_OFT P + 8)); C8 u320; C8 u328] p0 p1 p2 jring jseq) ->
  seql_ibits P 82 bc ptr -> 1 <= zlen (y_sq P) ->
  0 <= sLL < 2^(st_log (y_tLL P)) ->
  0 <= sOF < 2^(st_log (y_tOF P)) ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (y_SPV P + -352)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (y_DST P - y_PFX P)) x20 x21 x22 x23 x24 (Z_to_bv 64 (y_DST P)) x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x17c30) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_i5 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw u320 u328 p0 p1 p2 : word) (jpad jring jseq : list byte) (bc ptr sLL sOF : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 (seql_ifr P OEND LEND c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 (Z_to_bv 64 (2^60)) c176 c184 c216 c224 c232 [C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8))] [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (y_OFT P + 8)); C8 u320; C8 u328] p0 p1 p2 jring jseq) ->
  seql_ibits P 82 bc ptr -> 1 <= zlen (y_sq P) ->
  0 <= sLL < 2^(st_log (y_tLL P)) ->
  0 <= sOF < 2^(st_log (y_tOF P)) ->
  evt usegs (seql_post P) (MS (mkR (Z_to_bv 64 0x17c40) (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (y_SPV P + -352)) (Z_to_bv 64 (y_SPV P + -368)) (Z_to_bv 64 (y_SPV P + -440)) (Z_to_bv 64 (y_MLT P)) x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (y_DST P - y_PFX P)) x20 x21 x22 x23 x24 (Z_to_bv 64 (y_DST P)) x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x1db98) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_i6 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw p0 p1 p2 : word) (jpad jring jseq : list byte) (bc ptr sLL sOF sML : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 (seql_ifr P OEND LEND c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 (Z_to_bv 64 (2^60)) c176 c184 c216 c224 c232 [C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8))] [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (y_OFT P + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (y_MLT P + 8))] p0 p1 p2 jring jseq) ->
  seql_ibits P 91 bc ptr -> 1 <= zlen (y_sq P) ->
  0 <= sLL < 2^(st_log (y_tLL P)) ->
  0 <= sOF < 2^(st_log (y_tOF P)) ->
  0 <= sML < 2^(st_log (y_tML P)) ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (y_SPV P + -352)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (y_DST P - y_PFX P)) x20 x21 x22 x23 x24 (Z_to_bv 64 (y_DST P)) x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x17c40) (y_fc P) None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition ai_i7 (P : slp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : fmem) (c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 c176 c184 c216 c224 c232 cw p0 p1 p2 : word) (jpad jring jseq : list byte) (bc ptr sLL sOF sML : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  seql_iinv P OEND LLO LEND LOCV m1 (seql_ifr P OEND LEND c0 c8 c16 c24 c32 c40 c48 c64 c72 c88 c104 c128 c144 c152 (Z_to_bv 64 (2^60)) c176 c184 c216 c224 c232 [C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (y_SEQ P)); C8 (Z_to_bv 64 (y_SEQ P + 8))] [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (y_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (y_OFT P + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (y_MLT P + 8))] p0 p1 p2 jring jseq) ->
  seql_ibits P 91 bc ptr -> 1 <= zlen (y_sq P) ->
  0 <= sLL < 2^(st_log (y_tLL P)) ->
  0 <= sOF < 2^(st_log (y_tOF P)) ->
  0 <= sML < 2^(st_log (y_tML P)) ->
  evt usegs (seql_post P) (MS (mkR x1 (Z_to_bv 64 (y_SPV P + -688)) (y_gp P) (y_tp P) x5 x6 x7 (Z_to_bv 64 (y_DCTX P)) (Z_to_bv 64 (y_SPV P + -352)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (y_DST P - y_PFX P)) x20 x21 x22 x23 x24 (Z_to_bv 64 (y_DST P)) x26 x27 x28 x29 x30 x31) (y_F P) (Z_to_bv 64 0x17c40) (y_fc P) None m1 (seg_rom usegs)).

