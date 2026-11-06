(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_s_base AZ_seq_s_lbase AZ_seq_s_lkit AZ_seq_s_akit AZ_seq_s_okit AZ_seq_s_ibase.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
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
  forall (m1 : amem) (ja jc jf : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word),
  sqs_iinv P OEND LLO LEND LOCV m1 [CB 88 ja; C8 (Z_to_bv 64 (v_SHF P)); C8 (Z_to_bv 64 (v_FF P)); C8 (Z_to_bv 64 (v_FF P)); CB 168 jc]
                               [CB 248 jf; C8 (Z_to_bv 64 (v_fflag P (v_L P) 2 (v_FF P)))] ->
  evtF bsegs (v_RNG P) (sqs_post P) (MS (mkR x1 (Z_to_bv 64 (v_FRB P)) (v_gp P) (v_tp P) x5 x6 x7 (Z_to_bv 64 (v_SPV P)) (Z_to_bv 64 (v_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 18446744073709551596) x28 x29 x30 x31) (v_F P) (Z_to_bv 64 0x92f8c) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I0 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (ja jb j128 j152 j176 jd jseq jbd j72 : list byte) (p0 p1 p2 : word) (T40 T48 T56 T64 T120 T160 T168 T192 A6 T32 : Z)
         (x5 x6 x7 x13 x14 x15 x16 x17 x18 x25 x27 x28 x29 x30 x31 : word),
  sqs_iinv P OEND LLO LEND LOCV m1 (sqs_ifrI P OEND LEND LLO (sqs_imidA jb) T40 T48 T56 T64 T120 T160 T168 T192 ja j128 j152 j176 jd jseq) (sqs_iffA P jbd j72 p0 p1 p2) ->
  T40 = 2147450880 + v_D8 P + 3336 -> T48 = 2147450880 + v_D8 P + 3335 -> T56 = v_DCTX P + 26688 -> T64 = v_DCTX P + 29896 -> T120 = v_DCTX P + 26684 ->
  T160 = 2147450880 + v_D8 P + 3795 -> T168 = v_DCTX P + 30360 -> T192 = v_FF P + 120 -> A6 = v_DCTX P + 26692 -> T32 = 2147450880 + v_D8 P + 3336 ->
  evtF bsegs (v_RNG P) (sqs_post P)
    (MS (sqs_iregs P A6 T32 (Z_to_bv 64 0x90618) x5 x6 x7 (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 (v_SEQ P)) (Z_to_bv 64 (zlen (v_sq P))) x13 x14 x15 x16 x17 x18 x25 x27 x28 x29 x30 x31)
        (v_F P) (Z_to_bv 64 0x95b74) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I1 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (ja jb j128 j152 j176 jd jseq jpad j72 : list byte) (p0 p1 p2 cw : word) (A0 : Z) (bc ptr : Z)
         (x5 x6 x7 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
  sqs_iinv P OEND LLO LEND LOCV m1 (sqs_ifrN P OEND LEND LLO (sqs_imidA jb) ja j128 j152 j176 jd jseq) (sqs_iffB P cw bc jpad ptr j72 p0 p1 p2) ->
  A0 = v_FF P + 72 ->
  1 <= bc <= 64 -> bit_ok (v_SEQ P) (zlen (v_sq P)) bc ptr ->
  evtF bsegs (v_RNG P) (sqs_post P)
    (MS (sqs_iregs P (v_DCTX P + 26692) (2147450880 + v_D8 P + 3336) (Z_to_bv 64 0x90650) x5 x6 x7 (Z_to_bv 64 A0) (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 (v_LLT P)) x13 x14 x15 x16 x17
                   (Z_to_bv 64 (v_DCTX P)) x25 (Z_to_bv 64 18446744073709551596) x28 x29 x30 x31)
        (v_F P) (Z_to_bv 64 0x96148) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I3 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (ja jb j128 j152 j176 jd jseq jpad j88 : list byte) (p0 p1 p2 cw : word) (A0 : Z) (bc ptr sLL : Z)
         (x5 x6 x7 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
  sqs_iinv P OEND LLO LEND LOCV m1 (sqs_ifrN P OEND LEND LLO (sqs_imidB P jb) ja j128 j152 j176 jd jseq) (sqs_iffC P cw bc jpad ptr sLL j88 p0 p1 p2) ->
  A0 = v_FF P + 88 ->
  0 <= bc <= 73 -> bit_ok (v_SEQ P) (zlen (v_sq P)) bc ptr -> 0 <= sLL < 2^(st_log (v_tLL P)) ->
  evtF bsegs (v_RNG P) (sqs_post P)
    (MS (sqs_iregs P (v_DCTX P + 26692) (2147450880 + v_D8 P + 3336) (Z_to_bv 64 0x9067c) x5 x6 x7 (Z_to_bv 64 A0) (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 (v_OFT P)) x13 x14 x15 x16 x17
                   (Z_to_bv 64 (v_DCTX P)) x25 (Z_to_bv 64 18446744073709551596) x28 x29 x30 x31)
        (v_F P) (Z_to_bv 64 0x96148) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I5 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (ja j128 j152 j176 jd jseq jpad j104 : list byte) (p0 p1 p2 cw : word) (A0 : Z) (bc ptr sLL sOF : Z)
         (x5 x6 x7 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
  sqs_iinv P OEND LLO LEND LOCV m1 (sqs_ifrN P OEND LEND LLO (sqs_imidC P) ja j128 j152 j176 jd jseq) (sqs_iffD P cw bc jpad ptr sLL sOF j104 p0 p1 p2) ->
  A0 = v_FF P + 104 ->
  0 <= bc <= 82 -> bit_ok (v_SEQ P) (zlen (v_sq P)) bc ptr -> 0 <= sLL < 2^(st_log (v_tLL P)) -> 0 <= sOF < 2^(st_log (v_tOF P)) ->
  evtF bsegs (v_RNG P) (sqs_post P)
    (MS (sqs_iregs P (v_DCTX P + 26692) (2147450880 + v_D8 P + 3336) (Z_to_bv 64 0x906b0) x5 x6 x7 (Z_to_bv 64 A0) (Z_to_bv 64 (v_FF P + 32)) (Z_to_bv 64 (v_MLT P)) x13 x14 x15 x16 x17
                   (Z_to_bv 64 1152921504606846976) x25 (Z_to_bv 64 18446744073709551596) x28 x29 x30 x31)
        (v_F P) (Z_to_bv 64 0x96148) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I7 (P : ssq) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (ja j128 j152 j176 jd jseq jpad : list byte) (p0 p1 p2 cw : word) (bc ptr sLL sOF sML : Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
  sqs_iinv P OEND LLO LEND LOCV m1 (sqs_ifrN P OEND LEND LLO (sqs_imidC P) ja j128 j152 j176 jd jseq) (sqs_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad) ->
  0 <= bc <= 91 -> bit_ok (v_SEQ P) (zlen (v_sq P)) bc ptr ->
  0 <= sLL < 2^(st_log (v_tLL P)) -> 0 <= sOF < 2^(st_log (v_tOF P)) -> 0 <= sML < 2^(st_log (v_tML P)) ->
  evtF bsegs (v_RNG P) (sqs_post P)
    (MS (sqs_iregs P (v_DCTX P + 26692) (2147450880 + v_D8 P + 3336) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 1152921504606846976) x25 (Z_to_bv 64 18446744073709551596) x28 x29 x30 x31)
        (v_F P) (Z_to_bv 64 0x906b0) (v_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma sqs_iinv_eq2 : forall P OEND LLO LEND LOCV m1 fr ff fr' ff',
  sqs_iinv P OEND LLO LEND LOCV m1 fr ff -> fr = fr' -> ff = ff' -> sqs_iinv P OEND LLO LEND LOCV m1 fr' ff'.
Proof. intros P OEND LLO LEND LOCV m1 fr ff fr' ff' H <- <-. exact H. Qed.

End CANSEC1.
