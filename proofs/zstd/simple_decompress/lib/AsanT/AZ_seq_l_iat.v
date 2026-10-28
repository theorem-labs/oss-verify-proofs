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
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_ibase AZ_seq_l_xat AZ_seq_l_la_at.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma sql_zbv_eqm : forall a b, a mod 2^64 = b mod 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. rewrite <- (Z_to_bv_mod64 a), <- (Z_to_bv_mod64 b), H. reflexivity. Qed.
Ltac sql_cells_eq :=
  let rec go := lazymatch goal with
    | |- @nil _ = _ => reflexivity
    | |- (_ :: _) = _ => apply f_equal2; [ first [reflexivity | do 2 apply f_equal; lia | apply f_equal; apply sql_zbv_eqm; Z.div_mod_to_equations; lia] | go ] end in go.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition sql_ifrI (P : slq) (OEND LEND LP : Z) (mid : list cell) (ja jb jc jd je jg jh ji jj jk jr jseq : list byte) : list cell :=
  let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [CB 8 j0; CB 40 ja; C8 (Z_to_bv 64 (2147450880 + D8 + 3336)); C8 (Z_to_bv 64 (DCTX + 26692)); C8 (Z_to_bv 64 (2147450880 + D8 + 3336)); C8 (Z_to_bv 64 (2147450880 + D8 + 3335));
   C8 (Z_to_bv 64 (DCTX + 26688)); CB 16 jb; C8 (Z_to_bv 64 (Z.min nbSeq 8)); C8 (Z_to_bv 64 FF); CB 16 jc; C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 DCTX);
   C8 (Z_to_bv 64 (DCTX + 26684)); CB 8 jd; C8 dend; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 (2147450880 + D8 + 3795)); C8 (Z_to_bv 64 (DCTX + 30360)); C8 (Z_to_bv 64 FF);
   CB 8 je; C8 (Z_to_bv 64 OEND)] ++ mid ++
  [C8 (Z_to_bv 64 SHF); CB 8 jg; C8 (Z_to_bv 64 (FF + 120)); CB 8 jh; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 nbSeq); C8 (Z_to_bv 64 (FF + 32)); C8 (Z_to_bv 64 (DCTX + 30368));
   C8 (Z_to_bv 64 LEND); CB 32 ji; C8 (Z_to_bv 64 (2147450880 + D8 + 3796)); CB 8 jj; C8 (Z_to_bv 64 2147450880); CB 16 jk; CB 24 j384; CB 192 jr; C8 (Z_to_bv 64 LP); CB 24 jseq].
(* [comment removed for export] *)
Definition sql_imidA (jf : list byte) : list cell := [CB 16 jf].
Definition sql_imidB (jf : list byte) : list cell := [CB 8 jf; C8 (Z_to_bv 64 1152921504606846976)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sql_iffA (P : slq) (jbd j72 : list byte) (p0 p1 p2 : word) : list cell := let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [CB 32 jfh; CB 40 jbd; CB 48 j72; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))].
(* [comment removed for export] *)
Definition sql_iffB (P : slq) (cw : word) (bc : Z) (jpad : list byte) (ptr : Z) (j72 : list byte) (p0 p1 p2 : word) : list cell := let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8));
   CB 48 j72; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))].
(* [comment removed for export] *)
Definition sql_iffC (P : slq) (cw : word) (bc : Z) (jpad : list byte) (ptr sLL : Z) (j88 : list byte) (p0 p1 p2 : word) : list cell := let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8));
   C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); CB 32 j88; C8 p0; C8 p1; C8 p2; CB 104 j144; C8 (Z_to_bv 64 (fflag L 2 FF))].
(* [comment removed for export] *)
Definition sql_iffD (P : slq) (cw : word) (bc : Z) (jpad : list byte) (ptr sLL sOF : Z) (j104 : list byte) (p0 p1 p2 : word) : list cell := let '(mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1) := P in
  [CB 32 jfh; C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8));
   C8 (Z_to_bv 64 sLL); C8 (Z_to_bv 64 (LLT + 8)); C8 (Z_to_bv 64 sOF); C8 (Z_to_bv 64 (OFT + 8)); CB 16 j104; C8 p0; C8 p1; C8 p2; CB 104 j144;
   C8 (Z_to_bv 64 (fflag L 2 FF))].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sql_iregs (P : slq) (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s9 s10 s11 t3 t4 t5 t6 : word) : bvmap 5 word :=
  mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P))
      a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (l_FF P)) (Z_to_bv 64 (l_nbSeq P)) s9 s10 s11 t3 t4 t5 t6.

Definition sql_ifrB (P : slq) (OEND : Z) (p1 : word) (r136 r176 r272 : list cell) (ja jb jc jd jg ji jr jseq : list byte) : list cell :=
  [CB 8 (l_j0 P); CB 24 ja; C8 (Z_to_bv 64 (l_DCTX P + 26688)); CB 16 jb; C8 (Z_to_bv 64 (l_DCTX P + 26692)); C8 (Z_to_bv 64 (l_DCTX P + 26684));
   C8 (Z_to_bv 64 (2147450880 + l_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + l_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + l_D8 P + 3335));
   CB 8 jc; C8 (Z_to_bv 64 (Z.min (l_nbSeq P) 8)); CB 8 jd; C8 (l_dend P); C8 (Z_to_bv 64 (l_PFX P))] ++ r136 ++
  [C8 (Z_to_bv 64 (2147450880 + l_D8 P + 3795)); C8 (Z_to_bv 64 (l_DCTX P + 30360)); C8 (Z_to_bv 64 OEND)] ++ r176 ++
  [C8 (Z_to_bv 64 (l_PFX P)); C8 (Z_to_bv 64 (l_DST P)); CB 8 jg; C8 (Z_to_bv 64 (l_FF P)); C8 (Z_to_bv 64 (l_FF P + 120));
   C8 (Z_to_bv 64 (2147450880 + l_D8 P + 3796))] ++ r272 ++
  [C8 p1; CB 8 ji; CB 24 (l_j384 P); CB 192 jr; C8 (Z_to_bv 64 (l_LITP P)); CB 24 jseq].
Definition sql_iregsB (P : slq) (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 : word) : bvmap 5 word :=
  mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P))
      a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2147450880) (Z_to_bv 64 (l_SEQ P)) (Z_to_bv 64 (l_CAP P)) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P))
      (Z_to_bv 64 (l_DCTX P)) (Z_to_bv 64 (l_nbSeq P)) (Z_to_bv 64 (l_FF P)) (Z_to_bv 64 (l_LBE P)) s11 t3 t4 t5 (Z_to_bv 64 (l_DCTX P + 30368)).

(* [comment removed for export] *)
Definition sql_at_ierr (P : slq) (OEND : Z) : Prop :=
  forall (m1 : amem) (ja jb jf : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x23 x24 x26 x27 x28 x29 x30 x31 : word),
  sql_iinv P OEND (l_LITP P) (l_LBE P) (l_LOC P) m1 [CB 248 ja; C8 (Z_to_bv 64 (l_FF P)); CB 312 jb]
                                             [CB 248 jf; C8 (Z_to_bv 64 (l_fflag P (l_L P) 2 (l_FF P)))] ->
  evtF bsegs (l_RNG P) (sql_post P) (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P)) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 (l_SHF P)) x23 x24 (Z_to_bv 64 (l_FF P)) x26 x27 x28 x29 x30 x31) (l_F P) (Z_to_bv 64 0x8e5a0) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I0 (P : slq) (OEND : Z) : Prop :=
  forall (m1 : amem) (ja jb jc jd je jf jg jh jseq jbd j72 : list byte) (p0 p1 p2 : word)
         (x1 x5 x6 x7 x17 x28 x29 x30 : word),
  sql_iinv P OEND (l_LITP P) (l_LBE P) (l_LOC P) m1
    [CB 8 (l_j0 P); CB 64 ja; C8 (Z_to_bv 64 (2147450880 + l_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + l_D8 P + 3336)); C8 (Z_to_bv 64 (2147450880 + l_D8 P + 3335));
     CB 24 jb; C8 (l_dend P); C8 (Z_to_bv 64 (l_PFX P)); CB 16 jc; C8 (Z_to_bv 64 (2147450880 + l_D8 P + 3795)); C8 (Z_to_bv 64 (l_DCTX P + 30360));
     C8 (Z_to_bv 64 OEND); CB 48 jd; C8 (Z_to_bv 64 (l_PFX P)); C8 (Z_to_bv 64 (l_DST P)); CB 8 je; C8 (Z_to_bv 64 (l_FF P)); C8 (Z_to_bv 64 (l_FF P + 120));
     C8 (Z_to_bv 64 (2147450880 + l_D8 P + 3796)); CB 32 jf; C8 p1; CB 8 jg; CB 24 (l_j384 P); CB 192 jh; C8 (Z_to_bv 64 (l_LITP P)); CB 24 jseq]
    [CB 32 (l_jfh P); CB 40 jbd; CB 48 j72; C8 p0; C8 p1; C8 p2; CB 104 (l_j144 P); C8 (Z_to_bv 64 (l_fflag P (l_L P) 2 (l_FF P)))] ->
  evtF bsegs (l_RNG P) (sql_post P)
    (MS (mkR x1 (Z_to_bv 64 (l_FRB P)) (l_gp P) (l_tp P) x5 x6 x7 (Z_to_bv 64 (l_SPV P)) (Z_to_bv 64 (l_FRB P))
             (Z_to_bv 64 (l_DCTX P + 26688)) (Z_to_bv 64 8) (Z_to_bv 64 (Z.min (l_nbSeq P) 8)) (Z_to_bv 64 (l_DCTX P + 26684)) (Z_to_bv 64 (l_DCTX P + 26692))
             (Z_to_bv 64 (-15)) p0 x17 (Z_to_bv 64 2147450880) (Z_to_bv 64 (l_SEQ P)) (Z_to_bv 64 (l_CAP P)) (Z_to_bv 64 (l_FF P + 32)) (Z_to_bv 64 (l_SHF P))
             (Z_to_bv 64 (l_DCTX P)) (Z_to_bv 64 (l_nbSeq P)) (Z_to_bv 64 (l_FF P)) (Z_to_bv 64 (l_LBE P)) (Z_to_bv 64 (zlen (l_sq P))) x28 x29 x30
             (Z_to_bv 64 (l_DCTX P + 30368)))
        (l_F P) (Z_to_bv 64 0x89cb8) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I1 (P : slq) (OEND : Z) : Prop :=
  forall (m1 : amem) (ja jb jc jd je jf jg jh ji jr jseq jpad j72 : list byte) (p0 p1 p2 cw : word) (bc ptr : Z)
         (x1 x5 x6 x7 x12 x14 x15 x17 x27 x28 x29 x30 : word),
  sql_iinv P OEND (l_LITP P) (l_LBE P) (l_LOC P) m1 (sql_ifrB P OEND p1 [CB 16 je] [CB 48 jf] [CB 32 jh] ja jb jc jd jg ji jr jseq) (sql_iffB P cw bc jpad ptr j72 p0 p1 p2) ->
  1 <= bc <= 64 -> bit_ok (l_SEQ P) (zlen (l_sq P)) bc ptr ->
  evtF bsegs (l_RNG P) (sql_post P)
    (MS (sql_iregsB P x1 x5 x6 x7 (Z_to_bv 64 (l_LLT P + 4)) (Z_to_bv 64 (l_SEQ P + 8)) x12 (Z_to_bv 64 (l_LLT P)) x14 x15 p0 x17 x27 x28 x29 x30)
        (l_F P) (Z_to_bv 64 0x8a130) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I3 (P : slq) (OEND : Z) : Prop :=
  forall (m1 : amem) (ja jb jc jd je jf jg jh jk ji jr jseq jpad j88 : list byte) (p0 p1 p2 cw : word) (bc ptr sLL : Z)
         (x1 x5 x12 x14 x15 x17 x27 x28 x29 x30 : word),
  sql_iinv P OEND (l_LITP P) (l_LBE P) (l_LOC P) m1
    (sql_ifrB P OEND p1 [CB 16 je] [CB 48 jf] [CB 16 jh; C8 (Z_to_bv 64 (l_LLT P + 8)); CB 8 jk] ja jb jc jd jg ji jr jseq)
    (sql_iffC P cw bc jpad ptr sLL j88 p0 p1 p2) ->
  0 <= bc <= 73 -> bit_ok (l_SEQ P) (zlen (l_sq P)) bc ptr -> 0 <= sLL < 2^(st_log (l_tLL P)) ->
  evtF bsegs (l_RNG P) (sql_post P)
    (MS (sql_iregsB P x1 x5 (Z_to_bv 64 139648) (Z_to_bv 64 sLL) (Z_to_bv 64 (l_OFT P + 4)) (Z_to_bv 64 (l_SEQ P + 8)) x12 (Z_to_bv 64 (l_OFT P)) x14 x15 p0 x17
                    x27 x28 x29 x30)
        (l_F P) (Z_to_bv 64 0x8a30c) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I5 (P : slq) (OEND : Z) : Prop :=
  forall (m1 : amem) (ja jb jc jd je jf jg jh jk ji jr jseq jpad j104 : list byte) (p0 p1 p2 cw : word) (bc ptr sLL sOF : Z)
         (x1 x7 x12 x13 x14 x15 x17 x27 x29 : word),
  sql_iinv P OEND (l_LITP P) (l_LBE P) (l_LOC P) m1
    (sql_ifrB P OEND p1 [CB 16 je] [CB 48 jf] [CB 8 jh; C8 (Z_to_bv 64 (l_OFT P + 8)); C8 (Z_to_bv 64 (l_LLT P + 8)); CB 8 jk] ja jb jc jd jg ji jr jseq)
    (sql_iffD P cw bc jpad ptr sLL sOF j104 p0 p1 p2) ->
  0 <= bc <= 82 -> bit_ok (l_SEQ P) (zlen (l_sq P)) bc ptr -> 0 <= sLL < 2^(st_log (l_tLL P)) -> 0 <= sOF < 2^(st_log (l_tOF P)) ->
  evtF bsegs (l_RNG P) (sql_post P)
    (MS (sql_iregsB P x1 (Z_to_bv 64 sLL) (Z_to_bv 64 139648) x7 (Z_to_bv 64 (l_MLT P + 4)) (Z_to_bv 64 (l_SEQ P + 8)) x12 x13 x14 x15 p0 x17
                    x27 (Z_to_bv 64 sOF) x29 (Z_to_bv 64 (l_MLT P)))
        (l_F P) (Z_to_bv 64 0x8a4b0) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Definition ai_I7 (P : slq) (OEND : Z) : Prop :=
  forall (m1 : amem) (ja jb jc jd jf jg ji jr jseq jpad : list byte) (p0 p1 p2 cw : word) (bc ptr sLL sOF sML : Z)
         (x1 x6 x7 x10 x12 x13 x14 x15 x17 x30 : word),
  sql_iinv P OEND (l_LITP P) (l_LBE P) (l_LOC P) m1
    (sql_ifrB P OEND p1 [C8 (Z_to_bv 64 (l_nbSeq P - 1)); C8 (Z_to_bv 64 (l_SHF P))]
       [C8 (Z_to_bv 64 (l_nbSeq P)); C8 (Z_to_bv 64 (l_DCTX P + 30368)); C8 (Z_to_bv 64 (l_DCTX P)); C8 (Z_to_bv 64 (l_FF P)); CB 16 jf]
       [C8 (Z_to_bv 64 (l_MLT P + 8)); C8 (Z_to_bv 64 (l_OFT P + 8)); C8 (Z_to_bv 64 (l_LLT P + 8)); C8 (Z_to_bv 64 139648)]
       ja jb jc jd jg ji jr jseq)
    (sql_ffr P cw bc ptr sLL sOF sML p0 p1 p2 jpad) ->
  0 <= bc <= 91 -> bit_ok (l_SEQ P) (zlen (l_sq P)) bc ptr ->
  0 <= sLL < 2^(st_log (l_tLL P)) -> 0 <= sOF < 2^(st_log (l_tOF P)) -> 0 <= sML < 2^(st_log (l_tML P)) ->
  evtF bsegs (l_RNG P) (sql_post P)
    (MS (sql_iregsB P x1 (Z_to_bv 64 sLL) x6 x7 x10 (Z_to_bv 64 (l_nbSeq P - 1)) x12 x13 x14 x15 p0 x17
                    (Z_to_bv 64 (l_DST P - l_PFX P)) (Z_to_bv 64 sOF) (Z_to_bv 64 sML) x30)
        (l_F P) (Z_to_bv 64 0x8a648) (l_fc P) None m1 (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma sql_iinv_eq2 : forall P OEND LLO LEND LOCV m1 fr ff fr' ff',
  sql_iinv P OEND LLO LEND LOCV m1 fr ff -> fr = fr' -> ff = ff' -> sql_iinv P OEND LLO LEND LOCV m1 fr' ff'.
Proof. intros P OEND LLO LEND LOCV m1 fr ff fr' ff' H <- <-. exact H. Qed.

End CANSEC1.
