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
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_seq_kit AZ_seq_gkit AZ_seq_d_base AZ_seq_d_lbase AZ_seq_d_lkit AZ_seq_d_akit AZ_seq_d_okit AZ_seq_d_ibase.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma sqd_zbv_eqm : forall a b, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. rewrite <- (Z_to_bv_mod64 a), <- (Z_to_bv_mod64 b), H. reflexivity. Qed.
Ltac sqd_cells_eq :=
  let rec go := lazymatch goal with
    | |- @nil _ = _ => reflexivity
    | |- (_ :: _) = _ => apply f_equal2; [ first [reflexivity | do 2 apply f_equal; lia | apply f_equal; apply sqd_zbv_eqm; Z.div_mod_to_equations; lia] | go ] end in go.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sqd_ifrI (P : sqp) (OEND LEND LP : Z) (mid : list cell) (c176 : cell) (T72 T80 T88 T104 T192 : Z) (jb j48 jc144 jc168 jd jseq : list byte) : list cell :=
  let '(mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  [CB 24 j0; CB 24 jb; CB 8 j48] ++ mid ++
  [C8 (Z_to_bv 64 T72); C8 (Z_to_bv 64 T80); C8 (Z_to_bv 64 T88); C8 (Z_to_bv 64 OEND); C8 (Z_to_bv 64 T104); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF);
   C8 (Z_to_bv 64 SHF); C8 (Z_to_bv 64 DST); CB 8 jc144; C8 dend; C8 (Z_to_bv 64 PFX); CB 8 jc168; c176; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 T192);
   C8 (Z_to_bv 64 LEND); CB 16 jd; CB 16 j224; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 LP); CB 24 jseq].
(* [comment removed for export] *)
Definition sqd_imidA (jm : list byte) : list cell := [CB 16 jm].
Definition sqd_imidC (P : sqp) : list cell := [C8 (Z_to_bv 64 (2147450880 + w_D8 P + 3336)); C8 (Z_to_bv 64 (w_DCTX P + 26692))].
Definition sqd_ic176A (j176 : list byte) : cell := CB 8 j176.
Definition sqd_ic176C : cell := C8 (Z_to_bv 64 1152921504606846976).
(* [comment removed for export] *)
Definition sqd_ifrN (P : sqp) (OEND LEND LP : Z) (mid : list cell) (c176 : cell) (jb j48 jc144 jc168 jd jseq : list byte) : list cell :=
  sqd_ifrI P OEND LEND LP mid c176 (2147450880 + w_D8 P + 3336) (2147450880 + w_D8 P + 3335) (w_DCTX P + 26688) (w_DCTX P + 26684) (w_FF P + 120) jb j48 jc144 jc168 jd jseq.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sqd_iffA (P : sqp) (jbd j72 : list byte) (p0 p1 p2 : word) : list cell := let '(mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  [CB 32 jfh; CB 40 jbd; CB 48 j72; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))].
(* [comment removed for export] *)
Definition sqd_iffB (P : sqp) (cw : word) (bc : Z) (jpad : list byte) (ptr : Z) (j72 : list byte) (p0 p1 p2 : word) : list cell := let '(mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8));
   CB 48 j72; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))].
(* [comment removed for export] *)
Definition sqd_iffC (P : sqp) (cw : word) (bc : Z) (jpad : list byte) (ptr sLL : Z) (j88 : list byte) (p0 p1 p2 : word) : list cell := let '(mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8));
   C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); CB 32 j88; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))].
(* [comment removed for export] *)
Definition sqd_iffD (P : sqp) (cw : word) (bc : Z) (jpad : list byte) (ptr sLL sOF : Z) (j104 : list byte) (p0 p1 p2 : word) : list cell := let '(mkSQP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LITSZ LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j224 jfh j144 jsh0 jsh1) := P in
  [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8));
   C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8)); CB 16 j104; C8 p0; C8 p1; C8 p2; CB 104 j144;
   C8 (Z_to_bv 64 (fflag L 2 FF))].
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sqd_iregs (P : sqp) (A4 T8 : Z) (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word) : bvmap 5 word :=
  mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P))
      a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (w_DCTX P)) (Z_to_bv 64 (zlen (w_sq P))) (Z_to_bv 64 A4) (Z_to_bv 64 (w_SEQ P)) (Z_to_bv 64 (w_nbSeq P)) (Z_to_bv 64 (w_FF P + 32))
      (Z_to_bv 64 T8) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Definition sqd_at_ierr (P : sqp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (ja jc jf : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
  sqd_iinv P OEND LLO LEND LOCV m1 [CB 112 ja; C8 (Z_to_bv 64 (w_FF P)); C8 (Z_to_bv 64 (w_FF P)); C8 (Z_to_bv 64 (w_SHF P)); CB 144 jc]
                               [CB 248 jf; C8 (Z_to_bv 64 (w_fflag P (w_L P) 2 (w_FF P)))] ->
  evtF bsegs (w_RNG P) (sqd_post P) (MS (mkR x1 (Z_to_bv 64 (w_FRB P)) (w_gp P) (w_tp P) x5 x6 x7 (Z_to_bv 64 (w_SPV P)) (Z_to_bv 64 (w_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 18446744073709551596) x27 x28 x29 x30 x31) (w_F P) (Z_to_bv 64 0x9542c) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I0 (P : sqp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (jb j48 jm jc144 jc168 j176 jd jseq jbd j72 : list byte) (p0 p1 p2 : word) (T72 T80 T88 T104 T192 A4 T8 : Z)
         (x5 x6 x7 x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31 : word),
  sqd_iinv P OEND LLO LEND LOCV m1 (sqd_ifrI P OEND LEND LLO (sqd_imidA jm) (sqd_ic176A j176) T72 T80 T88 T104 T192 jb j48 jc144 jc168 jd jseq) (sqd_iffA P jbd j72 p0 p1 p2) ->
  T72 = 2147450880 + w_D8 P + 3336 -> T80 = 2147450880 + w_D8 P + 3335 -> T88 = w_DCTX P + 26688 -> T104 = w_DCTX P + 26684 -> T192 = w_FF P + 120 ->
  A4 = w_DCTX P + 26692 -> T8 = 2147450880 + w_D8 P + 3336 ->
  evtF bsegs (w_RNG P) (sqd_post P)
    (MS (sqd_iregs P A4 T8 (Z_to_bv 64 0x940ec) x5 x6 x7 (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 (w_SEQ P)) (Z_to_bv 64 (zlen (w_sq P))) x13 x14 x15 x16 x17 x26 x27 x28 x29 x30 x31)
        (w_F P) (Z_to_bv 64 0x95b74) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I1 (P : sqp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (jb j48 jm jc144 jc168 j176 jd jseq jpad j72 : list byte) (p0 p1 p2 cw : word) (A0 : Z) (bc ptr : Z)
         (x5 x6 x7 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
  sqd_iinv P OEND LLO LEND LOCV m1 (sqd_ifrN P OEND LEND LLO (sqd_imidA jm) (sqd_ic176A j176) jb j48 jc144 jc168 jd jseq) (sqd_iffB P cw bc jpad ptr j72 p0 p1 p2) ->
  A0 = w_FF P + 72 ->
  1 <= bc <= 64 -> bit_ok (w_SEQ P) (zlen (w_sq P)) bc ptr ->
  evtF bsegs (w_RNG P) (sqd_post P)
    (MS (sqd_iregs P (w_DCTX P + 26692) (2147450880 + w_D8 P + 3336) (Z_to_bv 64 0x94120) x5 x6 x7 (Z_to_bv 64 A0) (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 (w_LLT P)) x13 x14 x15 x16 x17
                   (Z_to_bv 64 18446744073709551596) x27 x28 x29 x30 x31)
        (w_F P) (Z_to_bv 64 0x96148) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I3 (P : sqp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (jb j48 jc144 jc168 j176 jd jseq jpad j88 : list byte) (p0 p1 p2 cw : word) (A0 : Z) (bc ptr sLL : Z)
         (x5 x6 x7 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
  sqd_iinv P OEND LLO LEND LOCV m1 (sqd_ifrN P OEND LEND LLO (sqd_imidC P) (sqd_ic176A j176) jb j48 jc144 jc168 jd jseq) (sqd_iffC P cw bc jpad ptr sLL j88 p0 p1 p2) ->
  A0 = w_FF P + 88 ->
  0 <= bc <= 73 -> bit_ok (w_SEQ P) (zlen (w_sq P)) bc ptr -> 0 <= sLL < 2^(st_log (w_tLL P)) ->
  evtF bsegs (w_RNG P) (sqd_post P)
    (MS (sqd_iregs P (w_DCTX P + 26692) (2147450880 + w_D8 P + 3336) (Z_to_bv 64 0x94150) x5 x6 x7 (Z_to_bv 64 A0) (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 (w_OFT P)) x13 x14 x15 x16 x17
                   (Z_to_bv 64 18446744073709551596) x27 x28 x29 x30 x31)
        (w_F P) (Z_to_bv 64 0x96148) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I5 (P : sqp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (jb j48 jc144 jc168 jd jseq jpad j104 : list byte) (p0 p1 p2 cw : word) (A0 : Z) (bc ptr sLL sOF : Z)
         (x5 x6 x7 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
  sqd_iinv P OEND LLO LEND LOCV m1 (sqd_ifrN P OEND LEND LLO (sqd_imidC P) sqd_ic176C jb j48 jc144 jc168 jd jseq) (sqd_iffD P cw bc jpad ptr sLL sOF j104 p0 p1 p2) ->
  A0 = w_FF P + 104 ->
  0 <= bc <= 82 -> bit_ok (w_SEQ P) (zlen (w_sq P)) bc ptr -> 0 <= sLL < 2^(st_log (w_tLL P)) -> 0 <= sOF < 2^(st_log (w_tOF P)) ->
  evtF bsegs (w_RNG P) (sqd_post P)
    (MS (sqd_iregs P (w_DCTX P + 26692) (2147450880 + w_D8 P + 3336) (Z_to_bv 64 0x94184) x5 x6 x7 (Z_to_bv 64 A0) (Z_to_bv 64 (w_FF P + 32)) (Z_to_bv 64 (w_MLT P)) x13 x14 x15 x16 x17
                   (Z_to_bv 64 18446744073709551596) x27 x28 x29 x30 x31)
        (w_F P) (Z_to_bv 64 0x96148) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I7 (P : sqp) (OEND LLO LEND LOCV : Z) : Prop :=
  forall (m1 : amem) (jb j48 jc144 jc168 jd jseq jpad : list byte) (p0 p1 p2 cw : word) (bc ptr sLL sOF sML : Z)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
  sqd_iinv P OEND LLO LEND LOCV m1 (sqd_ifrN P OEND LEND LLO (sqd_imidC P) sqd_ic176C jb j48 jc144 jc168 jd jseq) (sqd_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad) ->
  0 <= bc <= 91 -> bit_ok (w_SEQ P) (zlen (w_sq P)) bc ptr ->
  0 <= sLL < 2^(st_log (w_tLL P)) -> 0 <= sOF < 2^(st_log (w_tOF P)) -> 0 <= sML < 2^(st_log (w_tML P)) ->
  evtF bsegs (w_RNG P) (sqd_post P)
    (MS (sqd_iregs P (w_DCTX P + 26692) (2147450880 + w_D8 P + 3336) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 18446744073709551596) x27 x28 x29 x30 x31)
        (w_F P) (Z_to_bv 64 0x94184) (w_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma sqd_iinv_eq2 : forall P OEND LLO LEND LOCV m1 fr ff fr' ff',
  sqd_iinv P OEND LLO LEND LOCV m1 fr ff -> fr = fr' -> ff = ff' -> sqd_iinv P OEND LLO LEND LOCV m1 fr' ff'.
Proof. intros P OEND LLO LEND LOCV m1 fr ff fr' ff' H <- <-. exact H. Qed.

End CANSEC1.
