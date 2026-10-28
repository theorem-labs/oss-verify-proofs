(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_lkit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma sqs_ediv8 : forall q r, 0 <= r <= 7 -> (8 * q + r) / 8 = q /\ (8 * q + r) mod 8 = r.
Proof. intros q r H. split; [symmetry; apply (Z.div_unique (8 * q + r) 8 q r); lia | symmetry; apply (Z.mod_unique (8 * q + r) 8 q r); lia]. Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqs_ffr_rest (P : ssq) (sLL sOF sML : Z) (p0 p1 p2 : word) : list cell :=
  [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (v_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (v_OFT P + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (v_MLT P + 8));
   C8 p0; C8 p1; C8 p2; CB 104 (v_j144 P); C8 (Z_to_bv 64 (v_fflag P (v_L P) 2 (v_FF P)))].
Lemma sqs_ffr_app : forall P cw bc ptr sLL sOF sML p0 p1 p2 jpad,
  sqs_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad = [CB 32 (v_jfh P)] ++ sbd_cells cw bc jpad ptr (v_SEQ P) ++ sqs_ffr_rest P sLL sOF sML p0 p1 p2.
Proof. intros. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sqs_fr0_rdn : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (v_FRB P + 16)) 8 = Some (word_to_le_bytes 8 c0).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_FRB sqs_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 16%nat (C8 c0) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 16) with (FRB + 16) in R by lia. exact R.
Qed.
Lemma sqs_fr8_rdn : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (v_FRB P + 200)) 8 = Some (word_to_le_bytes 8 c8).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_FRB sqs_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 200%nat (C8 c8) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 200) with (FRB + 200) in R by lia. exact R.
Qed.

(* [comment removed for export] *)
Lemma sqs_fr176_rdn : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (v_FRB P + 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 139648)).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_FRB sqs_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 152%nat (C8 (Z_to_bv 64 139648)) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 152) with (FRB + 152) in R by lia. exact R.
Qed.
Lemma sqs_fr208_rdn : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (v_FRB P + 208)) 8 = Some (word_to_le_bytes 8 c208).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_FRB sqs_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 208%nat (C8 c208) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 208) with (FRB + 208) in R by lia. exact R.
Qed.

(* [comment removed for export] *)
Lemma sqs_fr168_rdn : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (v_FRB P + 176)) 8 = Some (word_to_le_bytes 8 c168).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_FRB sqs_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 176%nat (C8 c168) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 176) with (FRB + 176) in R by lia. exact R.
Qed.

(* [comment removed for export] *)
Lemma sqs_fr152_rdn : forall P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqs_linv P OEND LLO LEND LOCV m1 c0 c8 c152 c160 c168 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (v_FRB P + 96)) 8 = Some (word_to_le_bytes 8 c152).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [v_FRB sqs_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 96%nat (C8 c152) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 96) with (FRB + 96) in R by lia. exact R.
Qed.

End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
