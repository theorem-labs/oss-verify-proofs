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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_ibase.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma sqs_zbv_eqm : forall a b, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. rewrite <- (Z_to_bv_mod64 a), <- (Z_to_bv_mod64 b), H. reflexivity. Qed.
Ltac sqs_cells_eq :=
  let rec go := lazymatch goal with
    | |- @nil _ = _ => reflexivity
    | |- (_ :: _) = _ => apply f_equal2; [ first [reflexivity | do 2 apply f_equal; lia | apply f_equal; apply sqs_zbv_eqm; Z.div_mod_to_equations; lia] | go ] end in go.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqs_ifrI (P : ssq) (OEND LEND LP : Z) (mid : list cell) (T40 T48 T56 T64 T120 T160 T168 T192 : Z) (ja j128 j152 j176 jd jseq : list byte) : list cell :=
  let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  CB 24 ja :: mid ++
  [C8 (Z_to_bv 64 T40); C8 (Z_to_bv 64 T48); C8 (Z_to_bv 64 T56); C8 (Z_to_bv 64 T64); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 OEND); C8 (Z_to_bv 64 SHF);
   C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DCTX); C8 (Z_to_bv 64 T120); CB 8 j128; C8 dend; C8 (Z_to_bv 64 PFX); CB 8 j152;
   C8 (Z_to_bv 64 T160); C8 (Z_to_bv 64 T168); CB 8 j176; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 T192); C8 (Z_to_bv 64 LEND); CB 16 jd; CB 16 j224;
   C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 LP); CB 24 jseq].
(* [comment removed for export] *)
Definition sqs_imidA (jb : list byte) : list cell := [CB 16 jb].
Definition sqs_imidB (P : ssq) (jb : list byte) : list cell := [CB 8 jb; C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3336))].
Definition sqs_imidC (P : ssq) : list cell := [C8 (Z_to_bv 64 (v_DCTX P + 26692)); C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3336))].
(* [comment removed for export] *)
Definition sqs_ifrN (P : ssq) (OEND LEND LP : Z) (mid : list cell) (ja j128 j152 j176 jd jseq : list byte) : list cell :=
  sqs_ifrI P OEND LEND LP mid (2147450880 + v_D8 P + 3336) (2147450880 + v_D8 P + 3335) (v_DCTX P + 26688) (v_DCTX P + 29896) (v_DCTX P + 26684)
           (2147450880 + v_D8 P + 3795) (v_DCTX P + 30360) (v_FF P + 120) ja j128 j152 j176 jd jseq.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sqs_iffA (P : ssq) (jbd j72 : list byte) (p0 p1 p2 : word) : list cell := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  [CB 32 jfh; CB 40 jbd; CB 48 j72; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))].
(* [comment removed for export] *)
Definition sqs_iffB (P : ssq) (cw : word) (bc : Z) (jpad : list byte) (ptr : Z) (j72 : list byte) (p0 p1 p2 : word) : list cell := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8));
   CB 48 j72; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))].
(* [comment removed for export] *)
Definition sqs_iffC (P : ssq) (cw : word) (bc : Z) (jpad : list byte) (ptr sLL : Z) (j88 : list byte) (p0 p1 p2 : word) : list cell := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8));
   C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); CB 32 j88; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))].
(* [comment removed for export] *)
Definition sqs_iffD (P : ssq) (cw : word) (bc : Z) (jpad : list byte) (ptr sLL sOF : Z) (j104 : list byte) (p0 p1 p2 : word) : list cell := let '(mkSSQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8));
   C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8)); CB 16 j104; C8 p0; C8 p1; C8 p2; CB 104 j144;
   C8 (Z_to_bv 64 (fflag L 2 FF))].
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sqs_iregs (P : ssq) (A6 T32 : Z) (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s2 s9 s11 t3 t4 t5 t6 : word) : bvmap 5 word :=
  mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P))
      a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (zlen (v_sq P))) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 A6) (Z_to_bv 64 T32)
      (Z_to_bv 64 (v_nbSeq P)) s9 (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Definition sqs_at_ierr (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (ja jb jc jf : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  sqs_iinv P OEND LLO LEND LOCV m1 [CB 104 ja; C8 (Z_to_bv 64 (-20)); CB 24 jb; C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 (v_FF P)); CB 128 jc]
                               [CB 248 jf; C8 (Z_to_bv 64 (v_fflag P (v_L P) 2 (v_FF P)))] ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x91fa0) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I0 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (ja jb jc jd je jseq jbd j72 : list byte) (p0 p1 p2 : word) (T48 T56 T64 T128 T176 T184 A2 A4 A5 : Z)
         (x5 x6 x7 x10 x11 x22 x26 x28 x29 x30 : word),
  sqs_iinv P OEND LLO LEND LOCV m1
    [CB 16 (v_j0 P); CB 32 ja; C8 (Z_to_bv 64 T48); C8 (Z_to_bv 64 T56); C8 (Z_to_bv 64 T64); CB 16 jb; C8 (Z_to_bv 64 OEND); CB 8 jc;
     C8 (Z_to_bv 64 (-20)); C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 T128); C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 (v_FF P)); CB 24 jd;
     C8 (Z_to_bv 64 T176); C8 (Z_to_bv 64 T184); C8 (Z_to_bv 64 LEND); CB 24 je; CB 16 (v_j224 P); C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 LLO); CB 24 jseq]
    (sqs_iffA P jbd j72 p0 p1 p2) ->
  T48 = 2147450880 + v_D8 P + 3336 -> T56 = 2147450880 + v_D8 P + 3336 -> T64 = 2147450880 + v_D8 P + 3335 -> T128 = v_FF P + 120 ->
  T176 = 2147450880 + v_D8 P + 3795 -> T184 = v_DCTX P + 30360 -> A2 = v_DCTX P + 26688 -> A4 = v_DCTX P + 26684 -> A5 = v_DCTX P + 26692 ->
  1 <= zlen (v_sq P) ->
  evtF bsegs (v_RNG P) (sqs_post P)
    (MS (mkR (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P))
             x10 x11 (Z_to_bv 64 A2) (Z_to_bv 64 (v_PFX P)) (Z_to_bv 64 A4) (Z_to_bv 64 A5) (Z_to_bv 64 (v_FF P)) (Z_to_bv 64 T128)
             (Z_to_bv 64 28672) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) x22 (Z_to_bv 64 (zlen (v_sq P)))
             (Z_to_bv 64 (v_DST P)) (Z_to_bv 64 (v_DCTX P)) x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 (Z_to_bv 64 (v_DCTX P + 29896)))
        (v_F P) (Z_to_bv 64 0x8f4f8) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I1 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (jseq jpad j72 : list byte) (w16 w72 w80 w96 w152 w160 w200 w208 w216 p0 p1 p2 cw : word) (bc ptr : Z)
         (x5 x6 x7 x12 x14 x15 x16 x17 x18 x22 x23 x26 x28 x29 x30 : word),
  sqs_iinv P OEND LLO LEND LOCV m1
    [CB 16 (v_j0 P); C8 w16; C8 (Z_to_bv 64 (v_DCTX P + 26692)); C8 (Z_to_bv 64 (v_DCTX P + 26688)); C8 (Z_to_bv 64 (v_DCTX P + 26684));
     C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3335));
     C8 w72; C8 w80; C8 (Z_to_bv 64 OEND); C8 w96; C8 (Z_to_bv 64 (-20));
     C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (v_FF P + 120)); C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 (v_FF P));
     C8 w152; C8 w160; C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3795)); C8 (Z_to_bv 64 (v_DCTX P + 30360)); C8 (Z_to_bv 64 LEND);
     C8 w200; C8 w208; C8 w216; CB 16 (v_j224 P); C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 LLO); CB 24 jseq]
    (sqs_iffB P cw bc jpad ptr j72 p0 p1 p2) ->
  1 <= bc <= 64 -> bit_ok (v_SEQ P) (zlen (v_sq P)) bc ptr ->
  evtF bsegs (v_RNG P) (sqs_post P)
    (MS (mkR (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P))
             (Z_to_bv 64 (v_LLT P + 4)) (Z_to_bv 64 (v_SEQ P + 8)) x12 (Z_to_bv 64 (v_LLT P)) x14 x15 x16 x17
             x18 (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) x22 x23
             (Z_to_bv 64 (v_DST P)) (Z_to_bv 64 (v_DCTX P)) x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 (Z_to_bv 64 (v_DCTX P + 29896)))
        (v_F P) (Z_to_bv 64 0x8f994) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I3 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (jseq jpad j88 : list byte) (w16 w72 w80 w96 w152 w160 w200 w208 w216 p0 p1 p2 cw : word) (bc ptr sLL : Z)
         (x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 : word),
  sqs_iinv P OEND LLO LEND LOCV m1
    [CB 16 (v_j0 P); C8 w16; C8 (Z_to_bv 64 (v_DCTX P + 26692)); C8 (Z_to_bv 64 (v_DCTX P + 26688)); C8 (Z_to_bv 64 (v_DCTX P + 26684));
     C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3335));
     C8 w72; C8 w80; C8 (Z_to_bv 64 OEND); C8 w96; C8 (Z_to_bv 64 (-20));
     C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (v_FF P + 120)); C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 (v_FF P));
     C8 w152; C8 w160; C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3795)); C8 (Z_to_bv 64 (v_DCTX P + 30360)); C8 (Z_to_bv 64 LEND);
     C8 w200; C8 w208; C8 w216; CB 16 (v_j224 P); C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 LLO); CB 24 jseq]
    (sqs_iffC P cw bc jpad ptr sLL j88 p0 p1 p2) ->
  0 <= bc <= 73 -> bit_ok (v_SEQ P) (zlen (v_sq P)) bc ptr -> 0 <= sLL < 2^(st_log (v_tLL P)) ->
  evtF bsegs (v_RNG P) (sqs_post P)
    (MS (mkR (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P))
             (Z_to_bv 64 (v_OFT P + 4)) (Z_to_bv 64 (v_SEQ P + 8)) x12 (Z_to_bv 64 (v_OFT P)) x14 x15 x16 x17
             (Z_to_bv 64 0x22180) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) x22 x23
             (Z_to_bv 64 (v_DST P)) (Z_to_bv 64 (v_DCTX P)) x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 (Z_to_bv 64 (v_DCTX P + 29896)))
        (v_F P) (Z_to_bv 64 0x8fb54) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I5 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (jseq jpad j104 : list byte) (w16 w72 w80 w96 w152 w160 w200 w208 w216 p0 p1 p2 cw : word) (bc ptr sLL sOF : Z)
         (x5 x6 x7 x12 x14 x15 x16 x17 x22 x23 x26 x28 x29 x30 : word),
  sqs_iinv P OEND LLO LEND LOCV m1
    [CB 16 (v_j0 P); C8 w16; C8 (Z_to_bv 64 (v_DCTX P + 26692)); C8 (Z_to_bv 64 (v_DCTX P + 26688)); C8 (Z_to_bv 64 (v_DCTX P + 26684));
     C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3335));
     C8 w72; C8 w80; C8 (Z_to_bv 64 OEND); C8 w96; C8 (Z_to_bv 64 (-20));
     C8 (v_dend P); C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (v_FF P + 120)); C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 (v_FF P));
     C8 w152; C8 w160; C8 (Z_to_bv 64 (v_PFX P)); C8 (Z_to_bv 64 (2147450880 + v_D8 P + 3795)); C8 (Z_to_bv 64 (v_DCTX P + 30360)); C8 (Z_to_bv 64 LEND);
     C8 w200; C8 w208; C8 w216; CB 16 (v_j224 P); C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 LLO); CB 24 jseq]
    (sqs_iffD P cw bc jpad ptr sLL sOF j104 p0 p1 p2) ->
  0 <= bc <= 82 -> bit_ok (v_SEQ P) (zlen (v_sq P)) bc ptr -> 0 <= sLL < 2^(st_log (v_tLL P)) -> 0 <= sOF < 2^(st_log (v_tOF P)) ->
  evtF bsegs (v_RNG P) (sqs_post P)
    (MS (mkR (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P))
             (Z_to_bv 64 (v_MLT P + 4)) (Z_to_bv 64 (v_SEQ P + 8)) x12 (Z_to_bv 64 (v_MLT P)) x14 x15 x16 x17
             (Z_to_bv 64 0x22180) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) x22 x23
             (Z_to_bv 64 (v_DST P)) (Z_to_bv 64 (v_DCTX P)) x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 (Z_to_bv 64 (v_DCTX P + 29896)))
        (v_F P) (Z_to_bv 64 0x8fcf0) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I7 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (jseq jpad : list byte) (c0 c8 c208 c216 p0 p1 p2 cw : word) (bc ptr sLL sOF sML : Z)
         (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x24 x25 x26 x28 x29 x30 : word),
  sqs_iinv P OEND LLO LEND LOCV m1
    (sqs_frame P OEND c0 c8 (Z_to_bv 64 2147450880) (Z_to_bv 64 (v_DCTX P + 30360)) (Z_to_bv 64 (2147450880 + v_D8 P + 3795)) (Z_to_bv 64 LEND) c208 c216 LLO jseq)
    (sqs_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad) ->
  0 <= bc <= 91 -> bit_ok (v_SEQ P) (zlen (v_sq P)) bc ptr ->
  0 <= sLL < 2^(st_log (v_tLL P)) -> 0 <= sOF < 2^(st_log (v_tOF P)) -> 0 <= sML < 2^(st_log (v_tML P)) ->
  evtF bsegs (v_RNG P) (sqs_post P)
    (MS (mkR (Z_to_bv 64 (v_nbSeq P)) (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P))
             x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0x22180) x19 (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 2147450880) x22
             (Z_to_bv 64 (v_DST P)) x24 x25 x26 (Z_to_bv 64 (v_SHF P)) x28 x29 x30 (Z_to_bv 64 (v_DCTX P + 29896)))
        (v_F P) (Z_to_bv 64 0x8fe70) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma sqs_iinv_eq2 : forall P OEND LLO LEND LOCV m1 fr ff fr' ff',
  sqs_iinv P OEND LLO LEND LOCV m1 fr ff -> fr = fr' -> ff = ff' -> sqs_iinv P OEND LLO LEND LOCV m1 fr' ff'.
Proof. intros P OEND LLO LEND LOCV m1 fr ff fr' ff' H <- <-. exact H. Qed.

End CANSEC1.
