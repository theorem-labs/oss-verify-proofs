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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma sqd_rg_k : forall P OEND LLO LEND LOCV, sqd_static P OEND LLO LEND LOCV -> forall Q : Prop,
  (4096 <= w_FRB P <= 2^47 -> 6443008 <= w_FF P <= 2^47 -> 0 <= w_SPV P < 2^64 -> w_SPV P mod 16 = 0 ->
  w_lo P <= w_FRB P -> w_FRB P + 216 <= w_SPV P - 104 -> 17594333495296 <= w_FRB P -> w_FF P + 256 <= w_FRB P ->
   (w_FF P + 256 <= 2147446784 \/ 17594333495296 <= w_FF P) ->
   rng (w_RNG P) (w_lo P) (w_SPV P - w_lo P) -> rng (w_RNG P) (w_FF P) 256 -> rng (w_RNG P) (w_SHF P) 32 ->
   w_SHF P = 2147450880 + w_FF P / 8 -> w_FF P mod 8 = 0 -> Q) -> Q.
Proof.
  intros P OEND LLO LEND LOCV ST Q K.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [w_FRB w_FF w_SPV w_lo w_RNG w_SHF] in *. sd_static_open ST. unfold held in *.
  cbn [sqd_astat] in S61. destruct S61 as ((_ & RSTK & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & ESHF & RFF & RSHF & _).
  apply K.
  - clear - S17 S18 S47 S53. lia.
  - clear - S49 S50 S18 S17. lia.
  - clear - S17. lia.
  - exact S43.
  - clear - S18 S47. lia.
  - clear - S47. lia.
  - clear - S53 S18 S47. lia.
  - clear - S50 S18 S47. lia.
  - clear - S49. lia.
  - exact RSTK.
  - exact RFF.
  - exact RSHF.
  - rewrite ESHF, shad_div. unfold ASHOFF. reflexivity.
  - clear - S51. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma sqd_lopen_k : forall P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqd_static P OEND LLO LEND LOCV -> sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall Q : Prop,
  (forall jpad jseq,
     rw_cells bsegs m1 (w_FRB P) (sqd_frame P OEND c24 c32 c40 c200 c208 c216 LP jseq) ->
     rw_cells bsegs m1 (w_FF P) (sqd_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad) ->
     length (w_j224 P) = 16%nat -> length jseq = 24%nat ->
     bytes_at bsegs m1 (w_SEQ P) (map (Z_to_bv 8) (w_sq P)) ->
     mem_inv bsegs m1 ->
     unpoisoned m1 (w_FF P + 32) (w_FF P + 32 + 112) ->
     unpoisoned m1 (w_SEQ P) (w_SEQ P + zlen (w_sq P)) ->
     rng (w_RNG P) (w_SEQ P) (zlen (w_sq P)) ->
     rng (w_RNG P) (shad (w_SEQ P)) (shspan (w_SEQ P) (zlen (w_sq P))) -> Q) -> Q.
Proof.
  intros P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV Q K.
  pose proof (sqd_linv_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ INV) as MI.
  pose proof (sqd_linv_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as UFL.
  pose proof (sqd_seq_asan _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as (USEQ & RSQ & RSQS).
  destruct INV as ((jpad & jseq & FR & FRF) & _ & _ & _ & SQB & _).
  destruct (sqd_fr_wf _ _ _ _ _ _ _ _ _ _ _ _ FR) as (L16F & LJF).
  exact (K jpad jseq FR FRF L16F LJF SQB MI UFL USEQ RSQ RSQS).
Qed.

(* [comment removed for export] *)
Lemma sqd_lf_k : forall P OEND LLO LEND BND OP LP bc ptr sLL sOF sML,
  sqd_lfacts P OEND LLO LEND BND OP LP bc ptr sLL sOF sML -> forall Q : Prop,
  (w_DST P <= OP <= OEND -> LLO <= LP <= LEND ->
   0 <= sLL < 2^(st_log (w_tLL P)) -> 0 <= sOF < 2^(st_log (w_tOF P)) -> 0 <= sML < 2^(st_log (w_tML P)) ->
   0 <= bc <= BND -> bit_ok (w_SEQ P) (zlen (w_sq P)) bc ptr -> Q) -> Q.
Proof. intros P OEND LLO LEND BND OP LP bc ptr sLL sOF sML (L1 & L2 & L3 & L4 & L5 & L6 & L7) Q K. exact (K L1 L2 L3 L4 L5 L6 L7). Qed.

(* [comment removed for export] *)
Definition sqd_ffr8 (P : sqp) (L8 O8 M8 : Z) (cw : word) (bc ptr sLL sOF sML : Z) (p0 p1 p2 : word) (jpad : list byte) : list cell :=
  [CB 32 (w_jfh P); C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (w_SEQ P)); C8 (Z_to_bv 64 (w_SEQ P + 8));
   C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (8 * L8 + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (8 * O8 + 8)); C8 (Z_to_bv 64 sML); C8 (Z_to_bv 64 (8 * M8 + 8));
   C8 p0; C8 p1; C8 p2; CB 104 (w_j144 P); C8 (Z_to_bv 64 (w_fflag P (w_L P) 2 (w_FF P)))].

Lemma sqd_ffr8_eq : forall P L8 O8 M8 cw bc ptr sLL sOF sML p0 p1 p2 jpad,
  w_LLT P = 8 * L8 -> w_OFT P = 8 * O8 -> w_MLT P = 8 * M8 ->
  sqd_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad = sqd_ffr8 P L8 O8 M8 cw bc ptr sLL sOF sML p0 p1 p2 jpad.
Proof.
  intros P L8 O8 M8 cw bc ptr sLL sOF sML p0 p1 p2 jpad E1 E2 E3.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [w_LLT w_OFT w_MLT sqd_ffr sqd_ffr8 w_jfh w_SEQ w_j144 w_fflag w_L w_FF] in *. rewrite E1, E2, E3. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sqd_linv_frame8 : forall P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP L8 O8 M8,
  sqd_static P OEND LLO LEND LOCV -> sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  w_LLT P = 8 * L8 -> w_OFT P = 8 * O8 -> w_MLT P = 8 * M8 ->
  forall m2 c24' c32' c40' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq,
  munch [(w_FRB P, w_FRB P + 216); (w_FF P, w_FF P + 256)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
  rw_cells bsegs m2 (w_FRB P) (sqd_frame P OEND c24' c32' c40' c200' c208' c216' LP' jseq) ->
  rw_cells bsegs m2 (w_FF P) (sqd_ffr8 P L8 O8 M8 cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' jpad) ->
  sqd_linv P OEND LLO LEND LOCV m2 c24' c32' c40' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP'.
Proof.
  intros P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP L8 O8 M8 ST INV E1 E2 E3
         m2 c24' c32' c40' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq MU WM MI FR FRF.
  rewrite <- (sqd_ffr8_eq P L8 O8 M8 cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' jpad E1 E2 E3) in FRF.
  exact (sqd_linv_frame P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV m2 c24' c32' c40' c200' c208' c216' cw' bc' ptr' sLL' sOF' sML' p0' p1' p2' LP' jpad jseq MU WM MI FR FRF).
Qed.

Lemma sqd_dec_k : forall P OEND LLO LEND LOCV K BND m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP jpad,
  sqd_static P OEND LLO LEND LOCV -> sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  sqd_lfacts P OEND LLO LEND BND OP LP bc ptr sLL sOF sML -> BND <= 100 + 100 * (w_nbSeq P - K) + 47 -> 1 <= K <= w_nbSeq P ->
  rw_cells bsegs m1 (w_FF P) (sqd_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad) ->
  forall Q : Prop,
  (forall L8 O8 M8 nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML,
     w_LLT P = 8 * L8 -> w_OFT P = 8 * O8 -> w_MLT P = 8 * M8 ->
     512 <= L8 < 2^44 -> 512 <= O8 < 2^44 -> 512 <= M8 < 2^44 ->
     rdn bsegs m1 (wa (8 * L8 + 8 * sLL + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nLL)) ->
     rdn bsegs m1 (wa (8 * L8 + 8 * sLL + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aLL)) ->
     rdn bsegs m1 (wa (8 * L8 + 8 * sLL + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bLL)) ->
     rdn bsegs m1 (wa (8 * L8 + 8 * sLL + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vLL)) ->
     rdn bsegs m1 (wa (8 * O8 + 8 * sOF + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nOF)) ->
     rdn bsegs m1 (wa (8 * O8 + 8 * sOF + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aOF)) ->
     rdn bsegs m1 (wa (8 * O8 + 8 * sOF + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bOF)) ->
     rdn bsegs m1 (wa (8 * O8 + 8 * sOF + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vOF)) ->
     rdn bsegs m1 (wa (8 * M8 + 8 * sML + 8)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 nML)) ->
     rdn bsegs m1 (wa (8 * M8 + 8 * sML + 10)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 aML)) ->
     rdn bsegs m1 (wa (8 * M8 + 8 * sML + 11)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 bML)) ->
     rdn bsegs m1 (wa (8 * M8 + 8 * sML + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 vML)) ->
     rdn bsegs m1 (wa (2147450880 + L8 + sLL + 1)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
     rdn bsegs m1 (wa (2147450880 + O8 + sOF + 1)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
     rdn bsegs m1 (wa (2147450880 + M8 + sML + 1)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
     rng (w_RNG P) (8 * L8 + 8 * sLL + 8) 8 -> rng (w_RNG P) (8 * O8 + 8 * sOF + 8) 8 -> rng (w_RNG P) (8 * M8 + 8 * sML + 8) 8 ->
     rng (w_RNG P) (2147450880 + L8 + sLL + 1) 1 -> rng (w_RNG P) (2147450880 + O8 + sOF + 1) 1 -> rng (w_RNG P) (2147450880 + M8 + sML + 1) 1 ->
     rw_cells bsegs m1 (w_FF P) (sqd_ffr8 P L8 O8 M8 cw bc ptr sLL sOF sML p0 p1 p2 jpad) ->
     sqd_next P nLL bLL nOF bOF nML bML ->
     0 <= nLL + 2^bLL <= 2^(st_log (w_tLL P)) -> 0 <= nOF + 2^bOF <= 2^(st_log (w_tOF P)) -> 0 <= nML + 2^bML <= 2^(st_log (w_tML P)) ->
     0 <= nLL <= 511 -> 0 <= nOF <= 511 -> 0 <= nML <= 511 -> 0 <= bLL <= 9 -> 0 <= bOF <= 9 -> 0 <= bML <= 9 ->
     0 <= aLL <= 16 -> 0 <= aOF <= 31 -> 0 <= aML <= 16 ->
     0 <= vLL <= 131072 -> 0 <= vML <= 131075 -> 0 <= vOF <= 4294967294 -> 0 <= vLL < 2^17 -> 0 <= vML + 2^aML < 2^18 -> 0 < 2^aML ->
     (aOF = 0 -> vOF = 0) -> (aOF = 1 -> vOF = 1) ->
     1 <= 2^(st_log (w_tLL P)) <= 512 -> 1 <= 2^(st_log (w_tOF P)) <= 512 -> 1 <= 2^(st_log (w_tML P)) <= 512 ->
     0 <= sLL <= 511 -> 0 <= sOF <= 511 -> 0 <= sML <= 511 -> 0 <= bc <= 9900000 -> Q) -> Q.
Proof.
  intros P OEND LLO LEND LOCV K BND m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP jpad ST INV LF HBND HK FRF Q KQ.
  destruct (sqd_dec_asan P OEND LLO LEND LOCV _ m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ST INV LF)
    as (L8 & O8 & M8 & E1 & E2 & E3 & Z1 & Z2 & Z3 & R1 & R2 & R3 & R4 & R5 & R6).
  destruct (sqd_linv_cells P OEND LLO LEND LOCV _ m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP OP ST INV LF)
    as (nLL & aLL & bLL & vLL & nOF & aOF & bOF & vOF & nML & aML & bML & vML & (W1 & W2 & W3 & W4) & (W5 & W6 & W7 & W8) & (W9 & W10 & W11 & W12) & CF).
  rewrite E1 in W1, W2, W3, W4. rewrite E2 in W5, W6, W7, W8. rewrite E3 in W9, W10, W11, W12.
  destruct CF as (NX & N1 & N2 & N3 & A1 & A2 & A3 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
  pose proof NX as (NX1 & NX2 & NX3 & NX4 & NX5 & NX6 & NX7 & NX8 & NX9).
  destruct LF as (_ & _ & L3 & L4 & L5 & L6 & _).
  assert (OK3 : seq_table_ok K_LL (w_tLL P) /\ seq_table_ok K_OF (w_tOF P) /\ seq_table_ok K_ML (w_tML P) /\ 1 <= w_nbSeq P <= 98047 /\
                512 <= L8 < 2^44 /\ 512 <= O8 < 2^44 /\ 512 <= M8 < 2^44).
  { clear - ST E1 E2 E3. destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
    cbn [w_tLL w_tOF w_tML w_nbSeq w_LLT w_OFT w_MLT] in *. sd_static_open ST. split; [exact OKLL|]. split; [exact OKOF|]. split; [exact OKML|]. split; [exact S16|].
    clear - S21 S22 S23 E1 E2 E3. lia. }
  destruct OK3 as (OKLL & OKOF & OKML & S16 & G1 & G2 & G3).
  pose proof (seq_pow_le _ _ OKLL) as PLL. pose proof (seq_pow_le _ _ OKOF) as POF. pose proof (seq_pow_le _ _ OKML) as PML.
  pose proof (Z.pow_pos_nonneg 2 aLL ltac:(lia) ltac:(lia)) as QA. pose proof (Z.pow_pos_nonneg 2 aML ltac:(lia) ltac:(lia)) as QM. pose proof (Z.pow_pos_nonneg 2 aOF ltac:(lia) ltac:(lia)) as QO.
  pose proof (Z.pow_nonneg 2 bLL ltac:(lia)) as QB1. pose proof (Z.pow_nonneg 2 bOF ltac:(lia)) as QB2. pose proof (Z.pow_nonneg 2 bML ltac:(lia)) as QB3.
  assert (FRF8 : rw_cells bsegs m1 (w_FF P) (sqd_ffr8 P L8 O8 M8 cw bc ptr sLL sOF sML p0 p1 p2 jpad)).
  { rewrite <- (sqd_ffr8_eq P L8 O8 M8 cw bc ptr sLL sOF sML p0 p1 p2 jpad E1 E2 E3). exact FRF. }
  apply (KQ L8 O8 M8 nLL aLL bLL vLL nOF aOF bOF vOF nML aML bML vML E1 E2 E3 G1 G2 G3 W1 W2 W3 W4 W5 W6 W7 W8 W9 W10 W11 W12 Z1 Z2 Z3 R1 R2 R3 R4 R5 R6 FRF8 NX);
    first [assumption | (clear - NX1 NX2 NX3 NX4 NX5 NX6 NX7 NX8 NX9 N1 N2 N3 A1 A2 A3 V1 V2 V3 V4 V5 V6 L3 L4 L5 L6 HK HBND S16 PLL POF PML QA QM QO QB1 QB2 QB3; lia)].
Qed.


(* [comment removed for export] *)
Lemma shptr_eq : forall a i, (a - 8 * i) / 8 + i = a / 8.
Proof. intros a i. Z.div_mod_to_equations. lia. Qed.

Lemma sqd_buf_k : forall P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP,
  sqd_static P OEND LLO LEND LOCV -> sqd_linv P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ->
  forall Q : Prop,
  (stk bsegs m1 (w_B0 P) (w_B1 P) ->
   unpoisoned m1 (w_B0 P) (w_B0 P + (w_B1 P - w_B0 P)) -> rng (w_RNG P) (w_B0 P) (w_B1 P - w_B0 P) ->
   rng (w_RNG P) (shad (w_B0 P)) (shspan (w_B0 P) (w_B1 P - w_B0 P)) ->
   (forall X, w_B0 P <= X -> X - X mod 8 + 8 <= w_B1 P ->
      rdn bsegs m1 (wa (2147450880 + X / 8)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\ rng (w_RNG P) (2147450880 + X / 8) 1) ->
   unpoisoned m1 0x22240 (0x22240 + 32) -> rng (w_RNG P) 0x22240 32 -> rng (w_RNG P) (shad 0x22240) (shspan 0x22240 32) ->
   unpoisoned m1 0x22280 (0x22280 + 32) -> rng (w_RNG P) 0x22280 32 -> rng (w_RNG P) (shad 0x22280) (shspan 0x22280 32) ->
   (forall g, (17480 <= g < 17484 \/ 17488 <= g < 17492) ->
      rdn bsegs m1 (wa (2147450880 + g)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\ rng (w_RNG P) (2147450880 + g) 1) -> Q) -> Q.
Proof.
  intros P OEND LLO LEND LOCV m1 c24 c32 c40 c200 c208 c216 cw bc ptr sLL sOF sML p0 p1 p2 LP ST INV Q K.
  pose proof (sqd_asan_now _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST INV) as AS.
  destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1].
  cbn [sqd_xinv sqd_asan w_B0 w_B1 w_RNG] in *. sd_static_open ST.
  destruct XI as (_ & _ & BUF & _). destruct AS as (_ & _ & _ & _ & ACL & AOUT & _).
  destruct (AOUT S68) as (AB & _). destruct (AB ltac:(clear - S68; lia)) as (BB & UB & RB1 & RB2).
  assert (A32 : aro RNG m1 0x22240 32) by aro_cl ACL. assert (A64 : aro RNG m1 0x22280 32) by aro_cl ACL.
  destruct A32 as (U32 & R32 & RS32). destruct A64 as (U64 & R64 & RS64).
  apply K; try assumption.
  - intros X H1 H2.
    assert (Z0 : m1 (wa (shad X)) = Some (Z_to_bv 8 0)) by (eapply (unp_shadow_zero m1 B0 (B1 - B0) X); [exact UB | exact H1 | clear - H2; lia]).
    rewrite shad_div in Z0. unfold ASHOFF in Z0. split.
    + cbn [rdn]. rewrite Z0. reflexivity.
    + eapply rng_sub'; [exact RB2 |]. unfold shspan. rewrite !shad_div. unfold ASHOFF. clear - H1 H2 S1 S7. Z.div_mod_to_equations. lia.
  - intros g Hg.
    assert (Z0 : m1 (wa (shad (8 * g))) = Some (Z_to_bv 8 0)).
    { destruct Hg as [Hg|Hg].
      - eapply (unp_shadow_zero m1 0x22240 32); [exact U32 | clear - Hg; lia | clear - Hg; Z.div_mod_to_equations; lia].
      - eapply (unp_shadow_zero m1 0x22280 32); [exact U64 | clear - Hg; lia | clear - Hg; Z.div_mod_to_equations; lia]. }
    rewrite shad_div in Z0. unfold ASHOFF in Z0. replace (8 * g / 8) with g in Z0 by (clear; Z.div_mod_to_equations; lia). split.
    + cbn [rdn]. rewrite Z0. reflexivity.
    + destruct Hg as [Hg|Hg].
      * eapply rng_sub'; [exact RS32 |]. unfold shspan. rewrite !shad_div. unfold ASHOFF. clear - Hg. Z.div_mod_to_equations. lia.
      * eapply rng_sub'; [exact RS64 |]. unfold shspan. rewrite !shad_div. unfold ASHOFF. clear - Hg. Z.div_mod_to_equations. lia.
Qed.

End CANSEC1.
