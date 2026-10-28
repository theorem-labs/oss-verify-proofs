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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Lemma length_le8' : forall w, length (le8 w) = 8%nat. Proof. intros w. reflexivity. Qed.

(* [comment removed for export] *)
Definition sql_fr_le_1 (P : slq) (c8 : word) : list cell :=
  let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [CB 8 j0; C8 c8].
Lemma sql_fr_le_1_len : forall P c8, (length (l_j0 P) = 8%nat /\ length (l_j384 P) = 24%nat) -> length (cells_bytes (sql_fr_le_1 P c8)) = 16%nat.
Proof. intros P c8 L16. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. unfold sql_fr_le_1. cbn [cells_bytes cbytes l_j0 l_j384] in *. destruct L16 as [L0 L384]. rewrite !length_app, ?length_le8', ?sql_ring_len, ?L0, ?L384. reflexivity. Qed.
Definition sql_fr_le_2 (P : slq) : list cell :=
  let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [C8 (Z_to_bv 64 (DCTX + 26688))].
Lemma sql_fr_le_2_len : forall P, length (cells_bytes (sql_fr_le_2 P)) = 8%nat.
Proof. intros P . destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. unfold sql_fr_le_2. cbn [cells_bytes cbytes l_j0 l_j384] in *. rewrite !length_app, ?length_le8', ?sql_ring_len. reflexivity. Qed.
Definition sql_fr_le_3 (P : slq) (c16 : word) : list cell :=
  let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [C8 (Z_to_bv 64 (DCTX + 26692)); C8 (Z_to_bv 64 (DCTX + 26684)); C8 (Z_to_bv 64 (2147450880 + D8 + 3336)); C8 (Z_to_bv 64 (2147450880 + D8 + 3336)); C8 (Z_to_bv 64 (2147450880 + D8 + 3335)); C8 c16].
Lemma sql_fr_le_3_len : forall P c16, length (cells_bytes (sql_fr_le_3 P c16)) = 48%nat.
Proof. intros P c16 . destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. unfold sql_fr_le_3. cbn [cells_bytes cbytes l_j0 l_j384] in *. rewrite !length_app, ?length_le8', ?sql_ring_len. reflexivity. Qed.
Definition sql_fr_le_4 (P : slq) : list cell :=
  let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [C8 dend; C8 (Z_to_bv 64 PFX)].
Lemma sql_fr_le_4_len : forall P, length (cells_bytes (sql_fr_le_4 P)) = 16%nat.
Proof. intros P . destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. unfold sql_fr_le_4. cbn [cells_bytes cbytes l_j0 l_j384] in *. rewrite !length_app, ?length_le8', ?sql_ring_len. reflexivity. Qed.
Definition sql_fr_le_5 (P : slq) : list cell :=
  let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [C8 (Z_to_bv 64 SHF); C8 (Z_to_bv 64 (2147450880 + D8 + 3795)); C8 (Z_to_bv 64 (DCTX + 30360))].
Lemma sql_fr_le_5_len : forall P, length (cells_bytes (sql_fr_le_5 P)) = 24%nat.
Proof. intros P . destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. unfold sql_fr_le_5. cbn [cells_bytes cbytes l_j0 l_j384] in *. rewrite !length_app, ?length_le8', ?sql_ring_len. reflexivity. Qed.
Definition sql_fr_le_6 (P : slq) : list cell :=
  let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [C8 (Z_to_bv 64 (DCTX + 30368))].
Lemma sql_fr_le_6_len : forall P, length (cells_bytes (sql_fr_le_6 P)) = 8%nat.
Proof. intros P . destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. unfold sql_fr_le_6. cbn [cells_bytes cbytes l_j0 l_j384] in *. rewrite !length_app, ?length_le8', ?sql_ring_len. reflexivity. Qed.
Definition sql_fr_le_7 (P : slq) : list cell :=
  let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [C8 (Z_to_bv 64 (FF + 120)); C8 (Z_to_bv 64 (2147450880 + D8 + 3796))].
Lemma sql_fr_le_7_len : forall P, length (cells_bytes (sql_fr_le_7 P)) = 16%nat.
Proof. intros P . destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. unfold sql_fr_le_7. cbn [cells_bytes cbytes l_j0 l_j384] in *. rewrite !length_app, ?length_le8', ?sql_ring_len. reflexivity. Qed.
Definition sql_fr_le_8 (P : slq) (c376 : word) (rl : Z -> Z) (rm : Z -> Z) (ro : Z -> Z) : list cell :=
  let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [C8 c376; CB 24 j384; CB 192 (sql_ring_bytes rl rm ro)].
Lemma sql_fr_le_8_len : forall P c376 rl rm ro, (length (l_j0 P) = 8%nat /\ length (l_j384 P) = 24%nat) -> length (cells_bytes (sql_fr_le_8 P c376 rl rm ro)) = 224%nat.
Proof. intros P c376 rl rm ro L16. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. unfold sql_fr_le_8. cbn [cells_bytes cbytes l_j0 l_j384] in *. destruct L16 as [L0 L384]. rewrite !length_app, ?length_le8', ?sql_ring_len, ?L0, ?L384. reflexivity. Qed.
Definition sql_fr_le_9 (P : slq) (jseq : list byte) : list cell :=
  let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [CB 24 jseq].
Lemma sql_fr_le_9_len : forall P jseq, length jseq = 24%nat -> length (cells_bytes (sql_fr_le_9 P jseq)) = 24%nat.
Proof. intros P jseq LJ. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. unfold sql_fr_le_9. cbn [cells_bytes cbytes l_j0 l_j384] in *. rewrite !length_app, ?length_le8', ?sql_ring_len, ?LJ. reflexivity. Qed.
Lemma sql_frame_split_le : forall P OEND c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 rl rm ro LP jseq,
  sql_frame P OEND c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 rl rm ro LP jseq = sql_fr_le_1 P c8 ++
  [C8 c24] ++
  [C8 c32] ++
  sql_fr_le_2 P ++
  [C8 c88] ++
  [C8 c120] ++
  sql_fr_le_3 P c16 ++
  [C8 (Z_to_bv 64 (Z.min (l_nbSeq P) 8))] ++
  [C8 c160] ++
  sql_fr_le_4 P ++
  [C8 c224] ++
  sql_fr_le_5 P ++
  [C8 (Z_to_bv 64 OEND)] ++
  [C8 (Z_to_bv 64 (l_nbSeq P))] ++
  sql_fr_le_6 P ++
  [C8 (Z_to_bv 64 (l_DCTX P))] ++
  [C8 (Z_to_bv 64 (l_FF P))] ++
  [C8 c248] ++
  [C8 c264] ++
  [C8 (Z_to_bv 64 (l_PFX P))] ++
  [C8 (Z_to_bv 64 (l_DST P))] ++
  [C8 c304] ++
  [C8 (Z_to_bv 64 (l_FF P))] ++
  sql_fr_le_7 P ++
  [C8 c312] ++
  [C8 c368] ++
  [C8 c328] ++
  [C8 c336] ++
  [C8 c96] ++
  sql_fr_le_8 P c376 rl rm ro ++
  [C8 (Z_to_bv 64 LP)] ++
  sql_fr_le_9 P jseq.
Proof. intros. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. reflexivity. Qed.
Lemma sql_fr_vle : forall (mm : amem) P OEND c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 rl rm ro LP jseq,
  rw_cells bsegs mm (l_FRB P) (sql_frame P OEND c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 rl rm ro LP jseq) ->
  rw_cells bsegs mm (l_FRB P)
  [CB 16 (cells_bytes (sql_fr_le_1 P c8));
   C8 c24;
   C8 c32;
   CB 8 (cells_bytes (sql_fr_le_2 P));
   C8 c88;
   C8 c120;
   CB 48 (cells_bytes (sql_fr_le_3 P c16));
   C8 (Z_to_bv 64 (Z.min (l_nbSeq P) 8));
   C8 c160;
   CB 16 (cells_bytes (sql_fr_le_4 P));
   C8 c224;
   CB 24 (cells_bytes (sql_fr_le_5 P));
   C8 (Z_to_bv 64 OEND);
   C8 (Z_to_bv 64 (l_nbSeq P));
   CB 8 (cells_bytes (sql_fr_le_6 P));
   C8 (Z_to_bv 64 (l_DCTX P));
   C8 (Z_to_bv 64 (l_FF P));
   C8 c248;
   C8 c264;
   C8 (Z_to_bv 64 (l_PFX P));
   C8 (Z_to_bv 64 (l_DST P));
   C8 c304;
   C8 (Z_to_bv 64 (l_FF P));
   CB 16 (cells_bytes (sql_fr_le_7 P));
   C8 c312;
   C8 c368;
   C8 c328;
   C8 c336;
   C8 c96;
   CB 224 (cells_bytes (sql_fr_le_8 P c376 rl rm ro));
   C8 (Z_to_bv 64 LP);
   CB 24 (cells_bytes (sql_fr_le_9 P jseq))].
Proof.
  intros mm P OEND c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 rl rm ro LP jseq H. destruct (sql_fr_wf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as (L0 & L384 & LJ). pose proof (conj L0 L384) as L16.
  rewrite sql_frame_split_le in H. eapply rw_cells_recell; [exact H| |].
  - cbn [cells_wf cell_wf]. rewrite (sql_fr_le_1_len _ _ L16), (sql_fr_le_2_len _), (sql_fr_le_3_len _ _), (sql_fr_le_4_len _), (sql_fr_le_5_len _), (sql_fr_le_6_len _), (sql_fr_le_7_len _), (sql_fr_le_8_len _ _ _ _ _ L16), (sql_fr_le_9_len _ _ LJ). repeat split; try exact L0; try exact L384; try exact LJ; try reflexivity; apply sql_ring_len.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
Lemma sql_fr_ule : forall (mm : amem) P OEND c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 rl rm ro LP jseq,
  rw_cells bsegs mm (l_FRB P)
  [CB 16 (cells_bytes (sql_fr_le_1 P c8));
   C8 c24;
   C8 c32;
   CB 8 (cells_bytes (sql_fr_le_2 P));
   C8 c88;
   C8 c120;
   CB 48 (cells_bytes (sql_fr_le_3 P c16));
   C8 (Z_to_bv 64 (Z.min (l_nbSeq P) 8));
   C8 c160;
   CB 16 (cells_bytes (sql_fr_le_4 P));
   C8 c224;
   CB 24 (cells_bytes (sql_fr_le_5 P));
   C8 (Z_to_bv 64 OEND);
   C8 (Z_to_bv 64 (l_nbSeq P));
   CB 8 (cells_bytes (sql_fr_le_6 P));
   C8 (Z_to_bv 64 (l_DCTX P));
   C8 (Z_to_bv 64 (l_FF P));
   C8 c248;
   C8 c264;
   C8 (Z_to_bv 64 (l_PFX P));
   C8 (Z_to_bv 64 (l_DST P));
   C8 c304;
   C8 (Z_to_bv 64 (l_FF P));
   CB 16 (cells_bytes (sql_fr_le_7 P));
   C8 c312;
   C8 c368;
   C8 c328;
   C8 c336;
   C8 c96;
   CB 224 (cells_bytes (sql_fr_le_8 P c376 rl rm ro));
   C8 (Z_to_bv 64 LP);
   CB 24 (cells_bytes (sql_fr_le_9 P jseq))] ->
  (length (l_j0 P) = 8%nat /\ length (l_j384 P) = 24%nat) -> length jseq = 24%nat ->
  rw_cells bsegs mm (l_FRB P) (sql_frame P OEND c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 rl rm ro LP jseq).
Proof.
  intros mm P OEND c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 rl rm ro LP jseq H L16 LJ. pose proof L16 as [L0 L384]. rewrite sql_frame_split_le. eapply rw_cells_recell; [exact H| |].
  - rewrite !cells_wf_app. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. cbn [sql_fr_le_1 sql_fr_le_2 sql_fr_le_3 sql_fr_le_4 sql_fr_le_5 sql_fr_le_6 sql_fr_le_7 sql_fr_le_8 sql_fr_le_9 cells_wf cell_wf app l_j0 l_j384] in *.
    repeat split; try exact L0; try exact L384; try exact LJ; try reflexivity; apply sql_ring_len.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.
End CANSEC1.
