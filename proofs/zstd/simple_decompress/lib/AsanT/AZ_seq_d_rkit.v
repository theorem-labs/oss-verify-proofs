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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_lkit2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma sqd_ediv8 : forall q r, 0 <= r <= 7 -> (8 * q + r) / 8 = q /\ (8 * q + r) mod 8 = r.
Proof. intros q r H. split; [symmetry; apply (Z.div_unique (8 * q + r) 8 q r); lia | symmetry; apply (Z.mod_unique (8 * q + r) 8 q r); lia]. Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqd_ffr_rest (P : sqp) (sLL sOF sML : Z) (p0 p1 p2 : word) : list cell :=
  [C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (w_LLT P + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (w_OFT P + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (w_MLT P + 8));
   C8 p0; C8 p1; C8 p2; CB 104 (w_j144 P); C8 (Z_to_bv 64 (w_fflag P (w_L P) 2 (w_FF P)))].
Lemma sqd_ffr_app : forall P cw bc ptr sLL sOF sML p0 p1 p2 jpad,
  sqd_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad = [CB 32 (w_jfh P)] ++ sbd_cells cw bc jpad ptr (w_SEQ P) ++ sqd_ffr_rest P sLL sOF sML p0 p1 p2.
Proof. intros. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1]. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sqd_fr24_rdn : forall P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (w_FRB P + 136)) 8 = Some (word_to_le_bytes 8 c24).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [w_FRB sqd_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 136%nat (C8 c24) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 136) with (FRB + 136) in R by lia. exact R.
Qed.
Lemma sqd_fr208_rdn : forall P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  rdn bsegs m1 (wa (w_FRB P + 144)) 8 = Some (word_to_le_bytes 8 c208).
Proof.
  intros until LP. intros ((jpad & jseq & FR & _) & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [w_FRB sqd_frame] in *.
  pose proof (rw_cells_read bsegs m1 FRB _ 144%nat (C8 c208) FR eq_refl) as R.
  rewrite ov_rdn in R. cbn [csize cbytes] in R. replace (FRB + Z.of_nat 144) with (FRB + 144) in R by lia. exact R.
Qed.

End CANSEC1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
