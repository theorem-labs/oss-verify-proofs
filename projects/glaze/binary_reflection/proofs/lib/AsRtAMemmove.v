(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Definition ammove_words : list (option (bv 32)) :=
  [
   Some W_6ce40; Some W_6ce44; Some W_6ce48; Some W_6ce4c; Some W_6ce50; Some W_6ce54; Some W_6ce58; Some W_6ce5c;
   Some W_6ce60; Some W_6ce64; Some W_6ce68; None; None; Some W_6ce74; Some W_6ce78; Some W_6ce7c; Some W_6ce80;
   Some W_6ce84; Some W_6ce88; Some W_6ce8c; Some W_6ce90; Some W_6ce94; None; None; Some W_6cea0; Some W_6cea4;
   Some W_6cea8; Some W_6ceac; Some W_6ceb0; Some W_6ceb4; Some W_6ceb8; Some W_6cebc; Some W_6cec0; Some W_6cec4;
   Some W_6cec8; Some W_6cecc; Some W_6ced0; Some W_6ced4; Some W_6ced8; Some W_6cedc; Some W_6cee0; None; None;
   Some W_6ceec; Some W_6cef0; Some W_6cef4; Some W_6cef8; Some W_6cefc; Some W_6cf00; Some W_6cf04; Some W_6cf08;
   Some W_6cf0c; Some W_6cf10; Some W_6cf14; Some W_6cf18; Some W_6cf1c; Some W_6cf20; Some W_6cf24; Some W_6cf28;
   Some W_6cf2c; Some W_6cf30; Some W_6cf34; Some W_6cf38; Some W_6cf3c; Some W_6cf40; Some W_6cf44; Some W_6cf48;
   Some W_6cf4c; Some W_6cf50; Some W_6cf54; Some W_6cf58; Some W_6cf5c; Some W_6cf60; Some W_6cf64; Some W_6cf68;
   Some W_6cf6c; Some W_6cf70; Some W_6cf74; Some W_6cf78; Some W_6cf7c; Some W_6cf80; None; None; Some W_6cf8c;
   Some W_6cf90; Some W_6cf94; Some W_6cf98; Some W_6cf9c; Some W_6cfa0; Some W_6cfa4; Some W_6cfa8; Some W_6cfac;
   Some W_6cfb0; Some W_6cfb4; Some W_6cfb8; Some W_6cfbc; Some W_6cfc0; Some W_6cfc4; Some W_6cfc8; Some W_6cfcc;
   Some W_6cfd0; Some W_6cfd4; Some W_6cfd8; Some W_6cfdc; Some W_6cfe0; Some W_6cfe4; Some W_6cfe8; Some W_6cfec;
   Some W_6cff0; Some W_6cff4; Some W_6cff8; Some W_6cffc; Some W_6d000; Some W_6d004; Some W_6d008; Some W_6d00c;
   Some W_6d010; None; None; Some W_6d01c; Some W_6d020; Some W_6d024; Some W_6d028; Some W_6d02c; Some W_6d030;
   Some W_6d034; Some W_6d038; Some W_6d03c; Some W_6d040; Some W_6d044; Some W_6d048; Some W_6d04c; Some W_6d050;
   Some W_6d054; Some W_6d058; Some W_6d05c; Some W_6d060; Some W_6d064; Some W_6d068; Some W_6d06c; Some W_6d070;
   Some W_6d074; Some W_6d078; Some W_6d07c; Some W_6d080; Some W_6d084; Some W_6d088; Some W_6d08c; Some W_6d090;
   Some W_6d094; Some W_6d098; Some W_6d09c; Some W_6d0a0; Some W_6d0a4; Some W_6d0a8; Some W_6d0ac; Some W_6d0b0;
   Some W_6d0b4; Some W_6d0b8; Some W_6d0bc; Some W_6d0c0; Some W_6d0c4; Some W_6d0c8; Some W_6d0cc; None; None;
   Some W_6d0d8; Some W_6d0dc; Some W_6d0e0; Some W_6d0e4; Some W_6d0e8; Some W_6d0ec; Some W_6d0f0; Some W_6d0f4;
   Some W_6d0f8; Some W_6d0fc; Some W_6d100; Some W_6d104; Some W_6d108; Some W_6d10c; Some W_6d110; Some W_6d114;
   Some W_6d118; Some W_6d11c; Some W_6d120; Some W_6d124; Some W_6d128; Some W_6d12c; Some W_6d130; Some W_6d134;
   Some W_6d138; Some W_6d13c; Some W_6d140; Some W_6d144; Some W_6d148; Some W_6d14c; Some W_6d150; Some W_6d154;
   Some W_6d158; Some W_6d15c; Some W_6d160; Some W_6d164; Some W_6d168; Some W_6d16c; None; None; Some W_6d178;
   Some W_6d17c; Some W_6d180; Some W_6d184; Some W_6d188; Some W_6d18c; Some W_6d190; Some W_6d194; Some W_6d198;
   Some W_6d19c; Some W_6d1a0; Some W_6d1a4; Some W_6d1a8; Some W_6d1ac
  ]%list.


(* [comment removed for export] *)
Record ammove_tab : Type := AMMT {
  mm_base : word;          (* [comment removed for export] *)
  mm_rip : rip_tab;        (* [comment removed for export] *)
  mm_imm : word;           (* [comment removed for export] *)
  mm_g_flag : Z; mm_p_flag : Z }.   (* [comment removed for export] *)

Record ammove_tab_ok (segs : list Segment) (t : ammove_tab) : Prop := AMMTOK {
  mto_code : code_ato segs (mm_base t) 0 ammove_words;
  mto_rip : rip_tab_ok segs (mm_rip t);
  mto_rip_base : rt_base (mm_rip t) = at_ (mm_base t) 12624;
  mto_imm : code_at segs (mm_imm t) 0 imemmove_words;
  mto_imm_base : mm_imm t = at_ (mm_base t) 77976;
  mto_qcf1 : code_ato segs (at_ (mm_base t) 88) 0 (qc1f_words 11);
  mto_qcs1 : code_ato segs (at_ (mm_base t) 556) 0 qc1s_words;
  mto_qcf2 : code_ato segs (at_ (mm_base t) 164) 0 (qc1f_words 10);
  mto_qcs2 : code_ato segs (at_ (mm_base t) 720) 0 qc1s_words;
  mto_g44 : gload segs (mm_base t) 44 13 (mm_g_flag t);
  mto_g88 : gload segs (at_ (mm_base t) 88) 0 13 (mt_g_shoff (rt_m2s (mm_rip t)));
  mto_g164 : gload segs (at_ (mm_base t) 164) 0 13 (mt_g_shoff (rt_m2s (mm_rip t)));
  mto_b144 : gbnez segs (at_ (mm_base t) 144) 16 (at_ (mm_base t) 556);
  mto_b604 : gbeqz segs (at_ (mm_base t) 604) 13 (at_ (mm_base t) 148);
  mto_b220 : gbnez segs (at_ (mm_base t) 220) 16 (at_ (mm_base t) 720);
  mto_b768 : gbeqz segs (at_ (mm_base t) 768) 13 (at_ (mm_base t) 224);
  mto_base : (U (mm_base t) mod 2 = 0)%Z /\ (U (mm_base t) + 100000 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Definition amm_frame (mem : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 s6 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (word_to_le_bytes 8 ra))
    (at_ sp (-16)) (word_to_le_bytes 8 s0))
    (at_ sp (-24)) (word_to_le_bytes 8 s1))
    (at_ sp (-32)) (word_to_le_bytes 8 s2))
    (at_ sp (-40)) (word_to_le_bytes 8 s3))
    (at_ sp (-48)) (word_to_le_bytes 8 s4))
    (at_ sp (-56)) (word_to_le_bytes 8 s5))
    (at_ sp (-64)) (word_to_le_bytes 8 s6).

Section AMMOVE.
  Variable segs : list Segment.
  Variable base : word.
  Variable rt : rip_tab.
  Variable imm : word.
  Variables g_flag p_flag : Z.
  #[local] Abbreviation g_shoff := (mt_g_shoff (rt_m2s rt)).
  #[local] Abbreviation p_shoff := (mt_p_shoff (rt_m2s rt)).
  Hypothesis HCODE : code_ato segs base 0 ammove_words.
  Hypothesis RTOK : rip_tab_ok segs rt.
  Hypothesis RTB : rt_base rt = at_ base 12624.
  Hypothesis IMC : code_at segs imm 0 imemmove_words.
  Hypothesis IMB : imm = at_ base 77976.
  Hypothesis QCF1 : code_ato segs (at_ base 88) 0 (qc1f_words 11).
  Hypothesis QCS1 : code_ato segs (at_ base 556) 0 qc1s_words.
  Hypothesis QCF2 : code_ato segs (at_ base 164) 0 (qc1f_words 10).
  Hypothesis QCS2 : code_ato segs (at_ base 720) 0 qc1s_words.
  Hypothesis G44 : gload segs base 44 13 g_flag.
  Hypothesis G88 : gload segs (at_ base 88) 0 13 g_shoff.
  Hypothesis G164 : gload segs (at_ base 164) 0 13 g_shoff.
  Hypothesis B144 : gbnez segs (at_ base 144) 16 (at_ base 556).
  Hypothesis B604 : gbeqz segs (at_ base 604) 13 (at_ base 148).
  Hypothesis B220 : gbnez segs (at_ base 220) 16 (at_ base 720).
  Hypothesis B768 : gbeqz segs (at_ base 768) 13 (at_ base 224).
  Hypothesis Hbase : (U base mod 2 = 0)%Z /\ (U base + 100000 < 2 ^ 64)%Z.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_6ce40.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_6ce44.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_6ce48.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_6ce4c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_6ce50.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_6ce54.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_6ce58.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_6ce5c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_6ce60.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_6ce64.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_6ce68.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 10 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_6ce74.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_6ce78.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 14 _ HCODE eq_refl). Qed.
  Lemma Fo60 : fetch_word segs (at_ base 60) = Some W_6ce7c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 15 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_6ce80.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_6ce84.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_6ce88.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_6ce8c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_6ce90.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo84 : fetch_word segs (at_ base 84) = Some W_6ce94.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 21 _ HCODE eq_refl). Qed.













  Lemma Fo148 : fetch_word segs (at_ base 148) = Some W_6ced4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 37 _ HCODE eq_refl). Qed.
  Lemma Fo152 : fetch_word segs (at_ base 152) = Some W_6ced8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 38 _ HCODE eq_refl). Qed.
  Lemma Fo156 : fetch_word segs (at_ base 156) = Some W_6cedc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 39 _ HCODE eq_refl). Qed.
  Lemma Fo160 : fetch_word segs (at_ base 160) = Some W_6cee0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 40 _ HCODE eq_refl). Qed.













  Lemma Fo224 : fetch_word segs (at_ base 224) = Some W_6cf20.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 56 _ HCODE eq_refl). Qed.
  Lemma Fo228 : fetch_word segs (at_ base 228) = Some W_6cf24.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 57 _ HCODE eq_refl). Qed.
  Lemma Fo232 : fetch_word segs (at_ base 232) = Some W_6cf28.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 58 _ HCODE eq_refl). Qed.
  Lemma Fo236 : fetch_word segs (at_ base 236) = Some W_6cf2c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 59 _ HCODE eq_refl). Qed.
  Lemma Fo240 : fetch_word segs (at_ base 240) = Some W_6cf30.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 60 _ HCODE eq_refl). Qed.
  Lemma Fo244 : fetch_word segs (at_ base 244) = Some W_6cf34.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 61 _ HCODE eq_refl). Qed.
  Lemma Fo248 : fetch_word segs (at_ base 248) = Some W_6cf38.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 62 _ HCODE eq_refl). Qed.
  Lemma Fo252 : fetch_word segs (at_ base 252) = Some W_6cf3c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 63 _ HCODE eq_refl). Qed.
  Lemma Fo256 : fetch_word segs (at_ base 256) = Some W_6cf40.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 64 _ HCODE eq_refl). Qed.
  Lemma Fo260 : fetch_word segs (at_ base 260) = Some W_6cf44.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 65 _ HCODE eq_refl). Qed.
  Lemma Fo264 : fetch_word segs (at_ base 264) = Some W_6cf48.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 66 _ HCODE eq_refl). Qed.
  Lemma Fo268 : fetch_word segs (at_ base 268) = Some W_6cf4c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 67 _ HCODE eq_refl). Qed.
  Lemma Fo272 : fetch_word segs (at_ base 272) = Some W_6cf50.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 68 _ HCODE eq_refl). Qed.
  Lemma Fo276 : fetch_word segs (at_ base 276) = Some W_6cf54.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 69 _ HCODE eq_refl). Qed.






























  Lemma Fo408 : fetch_word segs (at_ base 408) = Some W_6cfd8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 102 _ HCODE eq_refl). Qed.
  Lemma Fo412 : fetch_word segs (at_ base 412) = Some W_6cfdc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 103 _ HCODE eq_refl). Qed.
  Lemma Fo416 : fetch_word segs (at_ base 416) = Some W_6cfe0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 104 _ HCODE eq_refl). Qed.
  Lemma Fo420 : fetch_word segs (at_ base 420) = Some W_6cfe4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 105 _ HCODE eq_refl). Qed.





























  Lemma Fo548 : fetch_word segs (at_ base 548) = Some W_6d064.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 137 _ HCODE eq_refl). Qed.
  Lemma Fo552 : fetch_word segs (at_ base 552) = Some W_6d068.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 138 _ HCODE eq_refl). Qed.
  Lemma Fo556 : fetch_word segs (at_ base 556) = Some W_6d06c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 139 _ HCODE eq_refl). Qed.
  Lemma Fo560 : fetch_word segs (at_ base 560) = Some W_6d070.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 140 _ HCODE eq_refl). Qed.











  Lemma Fo608 : fetch_word segs (at_ base 608) = Some W_6d0a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 152 _ HCODE eq_refl). Qed.
  Lemma Fo612 : fetch_word segs (at_ base 612) = Some W_6d0a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 153 _ HCODE eq_refl). Qed.
  Lemma Fo616 : fetch_word segs (at_ base 616) = Some W_6d0a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 154 _ HCODE eq_refl). Qed.
  Lemma Fo620 : fetch_word segs (at_ base 620) = Some W_6d0ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 155 _ HCODE eq_refl). Qed.
  Lemma Fo624 : fetch_word segs (at_ base 624) = Some W_6d0b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 156 _ HCODE eq_refl). Qed.
  Lemma Fo628 : fetch_word segs (at_ base 628) = Some W_6d0b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 157 _ HCODE eq_refl). Qed.
  Lemma Fo632 : fetch_word segs (at_ base 632) = Some W_6d0b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 158 _ HCODE eq_refl). Qed.
  Lemma Fo636 : fetch_word segs (at_ base 636) = Some W_6d0bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 159 _ HCODE eq_refl). Qed.
  Lemma Fo640 : fetch_word segs (at_ base 640) = Some W_6d0c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 160 _ HCODE eq_refl). Qed.
  Lemma Fo644 : fetch_word segs (at_ base 644) = Some W_6d0c4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 161 _ HCODE eq_refl). Qed.
  Lemma Fo648 : fetch_word segs (at_ base 648) = Some W_6d0c8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 162 _ HCODE eq_refl). Qed.
  Lemma Fo652 : fetch_word segs (at_ base 652) = Some W_6d0cc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 163 _ HCODE eq_refl). Qed.



























  Lemma Fo772 : fetch_word segs (at_ base 772) = Some W_6d144.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 193 _ HCODE eq_refl). Qed.
  Lemma Fo776 : fetch_word segs (at_ base 776) = Some W_6d148.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 194 _ HCODE eq_refl). Qed.
  Lemma Fo780 : fetch_word segs (at_ base 780) = Some W_6d14c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 195 _ HCODE eq_refl). Qed.
  Lemma Fo784 : fetch_word segs (at_ base 784) = Some W_6d150.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 196 _ HCODE eq_refl). Qed.
  Lemma Fo788 : fetch_word segs (at_ base 788) = Some W_6d154.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 197 _ HCODE eq_refl). Qed.
  Lemma Fo792 : fetch_word segs (at_ base 792) = Some W_6d158.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 198 _ HCODE eq_refl). Qed.
  Lemma Fo796 : fetch_word segs (at_ base 796) = Some W_6d15c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 199 _ HCODE eq_refl). Qed.
  Lemma Fo800 : fetch_word segs (at_ base 800) = Some W_6d160.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 200 _ HCODE eq_refl). Qed.
  Lemma Fo804 : fetch_word segs (at_ base 804) = Some W_6d164.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 201 _ HCODE eq_refl). Qed.
  Lemma Fo808 : fetch_word segs (at_ base 808) = Some W_6d168.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 202 _ HCODE eq_refl). Qed.













  Lemma Fo872 : fetch_word segs (at_ base 872) = Some W_6d1a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 218 _ HCODE eq_refl). Qed.
  Lemma Fo876 : fetch_word segs (at_ base 876) = Some W_6d1ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 ammove_words 219 _ HCODE eq_refl). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables dst src ra sp : word.
  Variable n : Z.
  Variable bs : list byte.
  Variable fl : byte.
  Variable regs : bvmap 5 word.
  Hypothesis Hsp : (0x10007fff8000 + 2304 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  (* [comment removed for export] *)
  Definition DM1 : word -> option byte :=
    amm_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22).
  (* [comment removed for export] *)
  Definition DM2 : word -> option byte :=
    rip_mem rt DM1 (at_ sp (-2144)) (at_ base 632) sp (Z_to_bv 64 n) (getr regs 18) (Z_to_bv 64 (n - 65))
            (at_ sp (-2136)) dst src (Z_to_bv 64 n).
  Definition DM3 : word -> option byte :=
    rip_mem rt DM2 (at_ sp (-2144)) (at_ base 792) sp dst (Z_to_bv 64 n) (Z_to_bv 64 (n - 65))
            (at_ sp (-2136)) src dst (Z_to_bv 64 n).
  (* [comment removed for export] *)
  Definition ammove_post (M : word -> option byte) : word -> option byte := imemmove_result M dst src bs.

  Lemma DM1_out : forall x : word, (U x < U sp - 64 \/ U sp <= U x)%Z -> DM1 x = mem x.
  Proof using Hsp base.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold DM1, amm_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma DM1_low : forall x : word, (U x < U sp - 2224)%Z -> DM1 x = mem x.
  Proof using Hsp base. intros x Hx. apply DM1_out. lia. Qed.
  Lemma DM1_agree : forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> DM1 x = mem x.
  Proof using Hsp base. intros x Hx. apply DM1_out. lia. Qed.
  Lemma DM1_grows : mem_grows mem DM1.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold DM1, amm_frame in G in change_no_check G' end).
    repeat (lazymatch goal with
            | |- mem_grows ?a ?a => apply mem_grows_refl
            | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
            end).
  Qed.
  Lemma rip_mem_grows' : forall t M (sp' raX s0 s1 s2 s3 s4 s5 b z : word), mem_grows M (rip_mem t M sp' raX s0 s1 s2 s3 s4 s5 b z).
  Proof using.
    intros. (lazymatch goal with |- ?G => let G' := eval unfold rip_mem, ps_frame in G in change_no_check G' end).
    destruct (Z.ltb _ _);
      repeat (lazymatch goal with
              | |- mem_grows ?a ?a => apply mem_grows_refl
              | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
              end).
  Qed.
  Lemma DM2_agree : forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> DM2 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold DM2 in G in change_no_check G' end). rewrite rip_mem_outside; [apply DM1_agree; exact Hx | rewrite at_u; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  Qed.

  Lemma DM2_grows : mem_grows mem DM2.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold DM2 in G in change_no_check G' end). eapply mem_grows_trans; [apply DM1_grows | apply rip_mem_grows']. Qed.
  Lemma DM3_agree : forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> DM3 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold DM3 in G in change_no_check G' end). rewrite rip_mem_outside; [apply DM2_agree; exact Hx | rewrite at_u; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  Qed.

  Lemma DM3_grows : mem_grows mem DM3.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold DM3 in G in change_no_check G' end). eapply mem_grows_trans; [apply DM2_grows | apply rip_mem_grows']. Qed.

  Lemma rd_o : forall (M : word -> option byte) (B : Z) (a : word) k bs0,
    (forall x : word, (U x < B)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= B)%Z -> (B <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M B a k bs0 HM Ha HB Hr. rewrite <- Hr. apply rdn_ext; [lia|].
    intros x Hx. apply HM. lia.
  Qed.
  Lemma rd_outF : forall (M : word -> option byte) (a : word) k bs0,
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= U sp - 2224 \/ U sp <= U a)%Z -> (U a + Z.of_nat k <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M a k bs0 HM Ha Hnw Hr. rewrite <- Hr. apply rdn_ext; [exact Hnw|].
    intros x Hx. apply HM. lia.
  Qed.
  Lemma rd_outZ : forall (M : word -> option byte) (c : Z) k bs0,
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) ->
    (0 <= c)%Z -> (c + Z.of_nat k <= U sp - 2224)%Z ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs0 -> rdn segs M (Z_to_bv 64 c) k = Some bs0.
  Proof using Hsp base.
    intros M c k bs0 HM Hc Hk Hr. pose proof (u64_range sp). apply (rd_outF M); try assumption; wd_ulia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MV : moveH segs mem dst src n bs.
  Hypothesis Hends : (U src + n <= 2 ^ 47)%Z /\ (U dst + n <= 2 ^ 47)%Z.
  Hypothesis Rgf : rdn segs mem (Z_to_bv 64 g_flag) 8 = Some (LE8 (Z_to_bv 64 p_flag)).
  Hypothesis Rfl : rdn segs mem (Z_to_bv 64 p_flag) 1 = Some [fl].
  Hypothesis Hfl : U fl <> 0%Z.
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 2224)%Z (g_flag :: p_flag :: m2s_cells (rt_m2s rt)).
  Hypothesis Hstk : store_ok segs mem (at_ sp (-2224)) 2224 = true.
  Hypothesis Hsrc_stk : (n = 0 \/ U src + n <= U sp - 2224 \/ U sp <= U src)%Z.
  Hypothesis Hdst_stk : (n = 0 \/ U dst + n <= U sp - 2224 \/ U sp <= U dst)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis R1 : getr regs 1 = ra.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R10 : getr regs 10 = dst.
  Hypothesis R11 : getr regs 11 = src.
  Hypothesis R12 : getr regs 12 = Z_to_bv 64 n.

  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC; unfold m2s_cells in HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ sp (-2224)) _ 2224);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac addr_n := gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; fold_at_vars; rewrite ?at_addi; zlit_at;
                 try (progress ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end)); unorm).
  Ltac rd_close LOW Hr :=
    apply (rd_o _ _ _ _ _ LOW);
    [ rewrite ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ]
    | lia
    | first [ exact Hr | rewrite <- Hr; f_equal; apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; unorm; lia ] ] ].
  Ltac cldb F D bb LOW Hr :=
    chain_step; [reflexivity
      | eapply step_lbu with (b := bb);
        [exact F | reflexivity | exact D | addr_n; rd_close LOW Hr]
      | step_simpl]; vn.
  Ltac gl G LOW Hr :=
    eapply msteps_trans; [ eapply G; apply (rd_o _ _ _ _ _ LOW); [(lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia | lia | exact Hr] | ]; zlit_at.

  (* [comment removed for export] *)
  #[local] Abbreviation CLX := (fun r : reg => In r [2; 8; 9; 18; 19; 20; 21; 22; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dblkA :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 76) DM1 rom)
      /\ getr r 1 = ra /\ getr r 2 = at_ sp (-2144) /\ getr r 8 = sp /\ getr r 10 = dst /\ getr r 11 = src
      /\ getr r 12 = Z_to_bv 64 n /\ getr r 20 = at_ sp (-2136)
      /\ (forall i : reg, In i [9; 18; 19; 21; 22; 23; 24; 25; 26; 27; 3; 4]%list -> getr r i = getr regs i)
      /\ regs_agree CLX regs r.
  Proof using R12 R11 R10 R2 R1 Hstk Hcells Hfl Rfl Rgf Hends MV Hsp fl bs G44 HCODE p_flag g_flag rt.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs. pose proof (u8_range fl) as Hflr.
    destruct MV as [Mn Mlen Msrc Mdst Mnws Mnwd]. cells_split.
    wd_eexists. split.
    - an Fo0 D_6ce40.                                    (* [comment removed for export] *)
      fsd Fo4 D_6ce44 (at_ sp (-8));                     (* [comment removed for export] *)
      fsd Fo8 D_6ce48 (at_ sp (-16));                    (* [comment removed for export] *)
      fsd Fo12 D_6ce4c (at_ sp (-24));
      fsd Fo16 D_6ce50 (at_ sp (-32));
      fsd Fo20 D_6ce54 (at_ sp (-40));
      fsd Fo24 D_6ce58 (at_ sp (-48));
      fsd Fo28 D_6ce5c (at_ sp (-56));
      fsd Fo32 D_6ce60 (at_ sp (-64));
      change (wbytes _ _ _) with DM1.
      an Fo36 D_6ce64.                                   (* [comment removed for export] *)
      an Fo40 D_6ce68.                                   (* [comment removed for export] *)
      gl G44 DM1_low Rgf.                                (* [comment removed for export] *)
      cldb Fo52 D_6ce74 fl DM1_low Rfl.                  (* [comment removed for export] *)
      ab_ft Fo56 D_6ce78 ltac:(condz).                 (* [comment removed for export] *)
      av Fo60 D_6ce7c (Z_to_bv 64 (2 ^ 64 - 1 - U src)) ltac:(apply v_not_word).         (* [comment removed for export] *)
      an Fo64 D_6ce80; an Fo68 D_6ce84.                  (* [comment removed for export] *)
      ab_ft Fo72 D_6ce88 ltac:(condz);                 (* [comment removed for export] *)
      wd_refl.
    - post; rewrite ?at_0; try reflexivity;
      [ intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi | ra_solve ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dblkSs : forall M r0, (1 <= n <= 64)%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 76) M rom) (mkst r (at_ base 88) M rom)
      /\ getr r 19 = Z_to_bv 64 (2 ^ 64 + n - 65) /\ regs_agree (fun x => In x [13; 19]%list) r0 r.
  Proof using HCODE.
    intros M r0 Hs R12'. wd_eexists. split.
    - av Fo76 D_6ce8c (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm (2 ^ 64 + n - 65) (-1)); f_equal; lia).
      an Fo80 D_6ce90.
      ab_ft Fo84 D_6ce94 ltac:(condz).
      wd_refl.
    - post. ra_solve.
  Qed.
  Lemma dblkSz : forall M r0, n = 0%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 76) M rom) (mkst r (at_ base 148) M rom)
      /\ getr r 19 = Z_to_bv 64 (2 ^ 64 + n - 65) /\ regs_agree (fun x => In x [13; 19]%list) r0 r.
  Proof using HCODE.
    intros M r0 Hz R12'. wd_eexists. split.
    - av Fo76 D_6ce8c (Z_to_bv 64 (2 ^ 64 + n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; rewrite <- (Z_to_bv64_addm (2 ^ 64 + n - 65) (-1)); f_equal; lia).
      an Fo80 D_6ce90.
      ab_tk Fo84 D_6ce94 ltac:(condz).
      ab_ft Fo408 D_6cfd8 ltac:(condz).
      an Fo412 D_6cfdc.
      wd_refl.
    - post. ra_solve.
  Qed.
  Lemma dblkSb : forall M r0, (65 <= n)%Z -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 76) M rom) (mkst r (at_ base 608) M rom)
      /\ getr r 19 = Z_to_bv 64 (n - 65) /\ regs_agree (fun x => In x [13; 19]%list) r0 r.
  Proof using MV bs src dst mem HCODE.
    intros M r0 Hb R12'. pose proof (u64_range dst) as Hd. destruct MV as [Mn Mlen Msrc Mdst Mnws Mnwd]. wd_eexists. split.
    - av Fo76 D_6ce8c (Z_to_bv 64 (n - 65)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).
      an Fo80 D_6ce90.
      ab_tk Fo84 D_6ce94 ltac:(condz).
      ab_tk Fo408 D_6cfd8 ltac:(condz).
      wd_refl.
    - post. ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dblkDs : forall M r0, (1 <= n <= 64)%Z -> getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n -> getr r0 19 = Z_to_bv 64 (2 ^ 64 + n - 65) ->
    exists r, msteps segs (mkst r0 (at_ base 148) M rom) (mkst r (at_ base 164) M rom)
      /\ regs_agree (fun x => In x [13]%list) r0 r.
  Proof using Hends src HCODE.
    intros M r0 Hs R10' R12' R19'. pose proof (u64_range dst) as Hd. wd_eexists. split.
    - av Fo148 D_6ced4 (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).
      ab_ft Fo152 D_6ced8 ltac:(condz).
      an Fo156 D_6cedc.
      ab_ft Fo160 D_6cee0 ltac:(condz).
      wd_refl.
    - ra_solve.
  Qed.
  Lemma dblkDz : forall M r0, n = 0%Z -> getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n -> getr r0 19 = Z_to_bv 64 (2 ^ 64 + n - 65) ->
    exists r, msteps segs (mkst r0 (at_ base 148) M rom) (mkst r (at_ base 224) M rom)
      /\ regs_agree (fun x => In x [13]%list) r0 r.
  Proof using Hends src HCODE.
    intros M r0 Hz R10' R12' R19'. pose proof (u64_range dst) as Hd. wd_eexists. split.
    - av Fo148 D_6ced4 (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).
      ab_ft Fo152 D_6ced8 ltac:(condz).
      an Fo156 D_6cedc.
      ab_tk Fo160 D_6cee0 ltac:(condz).
      ab_ft Fo548 D_6d064 ltac:(condz).
      an Fo552 D_6d068.
      wd_refl.
    - ra_solve.
  Qed.
  Lemma dblkDb : forall M r0, (65 <= n)%Z -> getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n -> getr r0 19 = Z_to_bv 64 (n - 65) ->
    exists r, msteps segs (mkst r0 (at_ base 148) M rom) (mkst r (at_ base 772) M rom)
      /\ regs_agree (fun x => In x [13]%list) r0 r.
  Proof using Hends MV bs src mem HCODE.
    intros M r0 Hb R10' R12' R19'. pose proof (u64_range dst) as Hd. destruct MV as [Mn Mlen Msrc Mdst Mnws Mnwd]. wd_eexists. split.
    - av Fo148 D_6ced4 (Z_to_bv 64 (2 ^ 64 - 1 - U dst)) ltac:(apply v_not_word).
      ab_ft Fo152 D_6ced8 ltac:(condz).
      an Fo156 D_6cedc.
      ab_tk Fo160 D_6cee0 ltac:(condz).
      ab_tk Fo548 D_6d064 ltac:(condz).
      wd_refl.
    - ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma qc1H_DM1 : forall (b : word) w0 w1 s1,
    (U b + n <= 2 ^ 47)%Z ->
    qc1H segs mem b n g_shoff p_shoff w0 w1 s1 -> qc1H segs DM1 b n g_shoff p_shoff w0 w1 s1.
  Proof using Hcells Hsp p_flag g_flag base.
    intros b w0 w1 s1 Hb [Q1 Q2 Q3 Q4 [Q5 Q6] Q7 Q8 Q9 Q10 Q11].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range b) as Hbr. cells_split.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos a 8).
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U b) ltac:(lia)) as S0. pose proof (HSh (U b + n - 1)%Z ltac:(lia)) as S1.
    assert (D0 : (Sh (U b) - 7 <= down8 (Sh (U b)) <= Sh (U b))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U b)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U b)) 8 ltac:(lia)); lia).
    assert (D1 : (Sh (U b + n - 1) - 7 <= down8 (Sh (U b + n - 1)) <= Sh (U b + n - 1))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U b + n - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U b + n - 1)) 8 ltac:(lia)); lia).
    Ltac ro Hr := apply (rd_o _ _ _ _ _ DM1_low); [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | lia | exact Hr].
    split; try assumption.
    - ro Q3. - ro Q4. - split; assumption. - ro Q7. - ro Q8. - ro Q9.
    - intros a Ha. pose proof (u64_range a). apply (rd_o _ _ _ _ _ DM1_low); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia | exact (Q11 a Ha)].
  Qed.

  Lemma dblkQ1 : forall r0 w0 w1 s1,
    qc1H segs mem src n g_shoff p_shoff w0 w1 s1 ->
    getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 88) DM1 rom) (mkst r (at_ base 148) DM1 rom)
      /\ regs_agree (fun x => In x qc1_clob) r0 r.
  Proof using Hcells Hends Hsp dst B604 B144 G88 QCS1 QCF1 p_flag g_flag.
    intros r0 w0 w1 s1 QH R11' R12'. pose proof (u64_range base).
    pose proof (qc1_pass segs (at_ base 88) (at_ base 556) (at_ base 148) 11 g_shoff p_shoff QCF1 QCS1 G88
             ltac:(rewrite at_at; exact B144) ltac:(rewrite at_at; exact B604) ltac:(rewrite at_at; reflexivity)
             (or_intror eq_refl)
             r0 DM1 rom src n w0 w1 s1 (qc1H_DM1 _ _ _ _ (proj1 Hends) QH) R11' R12') as X.
    rewrite at_at, Z.add_0_r in X. exact X.
  Qed.

  Lemma dblkQ2 : forall r0 w0 w1 s1,
    qc1H segs mem dst n g_shoff p_shoff w0 w1 s1 ->
    getr r0 10 = dst -> getr r0 12 = Z_to_bv 64 n ->
    exists r, msteps segs (mkst r0 (at_ base 164) DM1 rom) (mkst r (at_ base 224) DM1 rom)
      /\ regs_agree (fun x => In x qc1_clob) r0 r.
  Proof using Hcells Hends Hsp src B768 B220 G164 QCS2 QCF2 p_flag g_flag.
    intros r0 w0 w1 s1 QH R10' R12'. pose proof (u64_range base).
    pose proof (qc1_pass segs (at_ base 164) (at_ base 720) (at_ base 224) 10 g_shoff p_shoff QCF2 QCS2 G164
             ltac:(rewrite at_at; exact B220) ltac:(rewrite at_at; exact B768) ltac:(rewrite at_at; reflexivity)
             (or_introl eq_refl)
             r0 DM1 rom dst n w0 w1 s1 (qc1H_DM1 _ _ _ _ (proj2 Hends) QH) R10' R12') as X.
    rewrite at_at, Z.add_0_r in X. exact X.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ripH_on : forall (M : word -> option byte) (b raX : word) (s0 s1 : byte) (midend : word),
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) -> mem_grows mem M ->
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem b midend ->
    ((0x10007fff8000 <= U b /\ U b + n + 1 <= 0x800000000000) \/ U b + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U b))) 1 = Some [s0] -> (U s0 = 0 \/ U b mod 8 < U s0 < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U b + n - 1))) 1 = Some [s1] -> (U s1 = 0 \/ (U b + n - 1) mod 8 < U s1 < 128)%Z ->
    (forall a : word, (Sh (up8 (U b)) <= U a < Sh (down8 (U b + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok raX ->
    ripH segs rt M b (Z_to_bv 64 n) raX (at_ sp (-2144)) s0 s1 midend.
  Proof using Hstk Hcells Hsp p_flag g_flag base.
    intros M b raX s0 s1 midend HM HG Hn65 CH Hrng R0 H0 R1' H1' RZ HR.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range b) as Hb.
    destruct CH as [C1 C2 C3 C4 C5 C6 C7 C8 CC Clo Chi]. cells_split.
    assert (SH : forall x, (0 <= x < 0x800000000000)%Z -> (0x7fff8000 <= Sh x < 0x10007fff8000)%Z).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos x 8). pose proof (Z.div_lt_upper_bound x 8 0x100000000000 ltac:(lia) ltac:(lia)). lia. }
    pose proof (SH (U b) ltac:(lia)) as S0'.
    pose proof (SH (U b + n - 1)%Z ltac:(lia)) as S1'.
    assert (UP : (U b <= up8 (U b) <= U b + 7)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end); pose proof (Z.div_mod (U b + 7) 8); pose proof (Z.mod_pos_bound (U b + 7) 8); lia).
    assert (DN : (U b + n - 7 <= down8 (U b + n) <= U b + n)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (U b + n) 8); pose proof (Z.mod_pos_bound (U b + n) 8); lia).
    pose proof (SH (up8 (U b)) ltac:(lia)) as S2. pose proof (SH (down8 (U b + n)) ltac:(lia)) as S3.
    assert (Un : U (Z_to_bv 64 n) = n) by (apply u_Z2bv; lia).
    Ltac rdo HMx Hr := apply (rd_outZ _ _ _ _ HMx); [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr].
    split.
    - split; [rdo HM C1 | rdo HM C2 | rdo HM C3 | rdo HM C4 | rdo HM C5 | rdo HM C6 | rdo HM C7 | rdo HM C8 | exact CC | lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat constructor; rewrite ?at_u; lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rdo HM R0.
    - exact H0.
    - rewrite Un. rdo HM R1'.
    - rewrite Un. exact H1'.
    - rewrite Un. intros a Ha. pose proof (u64_range a). pose proof (RZ a Ha) as Ra.
      rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ra |- *. rdo HM Ra.
    - rewrite at_u by lia. lia.
    - rewrite at_at. replace (-2144 + -80)%Z with (-2224)%Z by lia. eapply store_ok_mono; [exact HG|].
      eapply (store_ok_sub segs mem (at_ sp (-2224)) _ 2224); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - exact HR.
  Qed.

  Lemma dblkR1 : forall r0 (s0b s1b : byte) (midend : word),
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem src midend ->
    ((0x10007fff8000 <= U src /\ U src + n + 1 <= 0x800000000000) \/ U src + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0b] -> (U s0b = 0 \/ U src mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U src + n - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 8 = sp -> getr r0 10 = dst -> getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    getr r0 18 = getr regs 18 -> getr r0 19 = Z_to_bv 64 (n - 65) -> getr r0 20 = at_ sp (-2136) ->
    exists r, msteps segs (mkst r0 (at_ base 608) DM1 rom) (mkst r (at_ base 148) DM2 rom)
      /\ getr r 2 = at_ sp (-2144) /\ getr r 8 = sp /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 n
      /\ getr r 19 = Z_to_bv 64 (n - 65) /\ getr r 20 = at_ sp (-2136)
      /\ regs_agree (fun x => In x ([1; 9; 18; 21; 22]%list ++ rip_clob)) r0 r.
  Proof using Hstk Hcells Hsp Hbase RTB RTOK HCODE p_flag g_flag.
    intros r0 s0b s1b midend Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz R2' R8' R10' R11' R12' R18' R19' R20'.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    assert (RA : ret_ok (at_ base 632)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    set (r1 := regupd (regupd (regupd (regupd (regupd (regupd r0 21 dst) 10 src) 22 src) 11 (Z_to_bv 64 n)) 9 (Z_to_bv 64 n)) 1 (at_ base 632)).
    destruct (region_clear segs rt RTOK DM1 rom src (Z_to_bv 64 n) (at_ base 632) (at_ sp (-2144)) s0b s1b midend r1
                (ripH_on DM1 src (at_ base 632) s0b s1b midend DM1_agree DM1_grows Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz RA))
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; reflexivity | subst r1; gres; exact R2' | subst r1; gres; reflexivity | subst r1; gres; reflexivity |].
    wd_eexists. split.
    - an Fo608 D_6d0a0.                                  (* [comment removed for export] *)
      an Fo612 D_6d0a4.                                  (* [comment removed for export] *)
      an Fo616 D_6d0a8.                                  (* [comment removed for export] *)
      an Fo620 D_6d0ac.                                  (* [comment removed for export] *)
      an Fo624 D_6d0b0.                                  (* [comment removed for export] *)
      an Fo628 D_6d0b4.                                  (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- RTB.
      eapply msteps_trans; [exact RUN2|].
      replace (rip_mem rt DM1 (at_ sp (-2144)) (at_ base 632) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) src (Z_to_bv 64 n))
         with DM2.
      2:{ (lazymatch goal with |- ?G => let G' := eval unfold DM2 in G in change_no_check G' end). subst r1. gres. rewrite R8', R18', R19', R20'. reflexivity. }
      assert (A22 : getr r2 22 = src) by (rewrite (AG2 22) by notin; subst r1; gres; reflexivity).
      assert (A9 : getr r2 9 = Z_to_bv 64 n) by (rewrite (AG2 9) by notin; subst r1; gres; reflexivity).
      assert (A21 : getr r2 21 = dst) by (rewrite (AG2 21) by notin; subst r1; gres; reflexivity).
      an Fo632 D_6d0b8.                                  (* [comment removed for export] *)
      an Fo636 D_6d0bc.                                  (* [comment removed for export] *)
      an Fo640 D_6d0c0.                                  (* [comment removed for export] *)
      an Fo644 D_6d0c4.                                  (* [comment removed for export] *)
      ab_tk Fo648 D_6d0c8 ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
      assert (A8 : getr r2 8 = sp) by (rewrite (AG2 8) by notin; subst r1; gres; exact R8').
      assert (A19 : getr r2 19 = Z_to_bv 64 (n - 65)) by (rewrite (AG2 19) by notin; subst r1; gres; exact R19').
      assert (A20 : getr r2 20 = at_ sp (-2136)) by (rewrite (AG2 20) by notin; subst r1; gres; exact R20').
      post; try assumption.
      intros x Hx. gres.
      assert (X : x <> 10 /\ x <> 18 /\ x <> 12 /\ x <> 11) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct X as (X1 & X2 & X3 & X4). rewrite !getr_other by assumption.
      rewrite (AG2 x) by (intros Hc; apply Hx; apply in_or_app; right; exact Hc).
      subst r1. assert (Y : x <> 1 /\ x <> 9 /\ x <> 11 /\ x <> 22 /\ x <> 10 /\ x <> 21) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct Y as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). rewrite !getr_other by assumption. reflexivity.
  Qed.

  Lemma dblkR2 : forall r0 (s0b s1b : byte) (midend : word),
    (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0b] -> (U s0b = 0 \/ U dst mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U dst + n - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 8 = sp -> getr r0 10 = dst -> getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    getr r0 19 = Z_to_bv 64 (n - 65) -> getr r0 20 = at_ sp (-2136) ->
    exists r, msteps segs (mkst r0 (at_ base 772) DM2 rom) (mkst r (at_ base 224) DM3 rom)
      /\ getr r 2 = at_ sp (-2144) /\ getr r 10 = dst /\ getr r 11 = src /\ getr r 12 = Z_to_bv 64 n
      /\ regs_agree (fun x => In x ([1; 9; 18; 19; 21]%list ++ rip_clob)) r0 r.
  Proof using Hstk Hcells Hsp Hbase RTB RTOK HCODE p_flag g_flag.
    intros r0 s0b s1b midend Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz R2' R8' R10' R11' R12' R19' R20'.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    assert (RA : ret_ok (at_ base 792)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    set (r1 := regupd (regupd (regupd (regupd (regupd r0 9 dst) 21 src) 11 (Z_to_bv 64 n)) 18 (Z_to_bv 64 n)) 1 (at_ base 792)).
    destruct (region_clear segs rt RTOK DM2 rom dst (Z_to_bv 64 n) (at_ base 792) (at_ sp (-2144)) s0b s1b midend r1
                (ripH_on DM2 dst (at_ base 792) s0b s1b midend DM2_agree DM2_grows Hn65 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz RA))
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; reflexivity | subst r1; gres; exact R2' | subst r1; gres; exact R10' | subst r1; gres; reflexivity |].
    wd_eexists. split.
    - an Fo772 D_6d144.                                  (* [comment removed for export] *)
      an Fo776 D_6d148.                                  (* [comment removed for export] *)
      an Fo780 D_6d14c.                                  (* [comment removed for export] *)
      an Fo784 D_6d150.                                  (* [comment removed for export] *)
      an Fo788 D_6d154.                                  (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- RTB.
      eapply msteps_trans; [exact RUN2|].
      replace (rip_mem rt DM2 (at_ sp (-2144)) (at_ base 792) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) dst (Z_to_bv 64 n))
         with DM3.
      2:{ (lazymatch goal with |- ?G => let G' := eval unfold DM3 in G in change_no_check G' end). subst r1. gres. rewrite R8', R19', R20'. reflexivity. }
      assert (A21 : getr r2 21 = src) by (rewrite (AG2 21) by notin; subst r1; gres; reflexivity).
      assert (A18 : getr r2 18 = Z_to_bv 64 n) by (rewrite (AG2 18) by notin; subst r1; gres; reflexivity).
      assert (A9 : getr r2 9 = dst) by (rewrite (AG2 9) by notin; subst r1; gres; reflexivity).
      an Fo792 D_6d158.                                  (* [comment removed for export] *)
      an Fo796 D_6d15c.                                  (* [comment removed for export] *)
      an Fo800 D_6d160.                                  (* [comment removed for export] *)
      an Fo804 D_6d164.                                  (* [comment removed for export] *)
      ab_tk Fo808 D_6d168 ltac:(condz).                (* [comment removed for export] *)
      wd_refl.
    - assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
      post; try assumption.
      intros x Hx. gres.
      assert (X : x <> 10 /\ x <> 19 /\ x <> 12 /\ x <> 11) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct X as (X1 & X2 & X3 & X4). rewrite !getr_other by assumption.
      rewrite (AG2 x) by (intros Hc; apply Hx; apply in_or_app; right; exact Hc).
      subst r1. assert (Y : x <> 1 /\ x <> 18 /\ x <> 11 /\ x <> 21 /\ x <> 9) by (repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto).
      destruct Y as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition amm_slots : list (Z * word) :=
    [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20);
     (-56, getr regs 21); (-64, getr regs 22)]%Z.

  Lemma slots_DM1 : forall (k : Z) (v : word), In (k, v) amm_slots -> rdn segs DM1 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp base.
    intros k v Hin. pose proof (u64_range sp). unfold amm_slots in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval unfold DM1, amm_frame in G in change_no_check G' end); rd8_chain|]). destruct Hin.
  Qed.
  Lemma slots_DM3 : forall (k : Z) (v : word), In (k, v) amm_slots -> rdn segs DM3 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp.
    intros k v Hin. pose proof (u64_range sp).
    assert (Hk : (-64 <= k /\ k + 8 <= 0)%Z).
    { unfold amm_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    rewrite <- (slots_DM1 k v Hin). apply rdn_ext; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    intros x Hx. rewrite at_u in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold DM3, DM2 in G in change_no_check G' end).
    rewrite !rip_mem_outside; first [reflexivity | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | rewrite at_u; lia].
  Qed.
  Lemma slots_post : forall (M : word -> option byte) (k : Z) (v : word),
    (forall k' v', In (k', v') amm_slots -> rdn segs M (at_ sp k') 8 = Some (word_to_le_bytes 8 v')) ->
    In (k, v) amm_slots -> rdn segs (ammove_post M) (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hdst_stk Hends MV Hsp n mem base.
    intros M k v HM Hin. pose proof (u64_range sp). pose proof (u64_range dst).
    destruct MV as [Mn Mlen Msrc Mdst Mnws Mnwd].
    assert (Hk : (-64 <= k /\ k + 8 <= 0)%Z).
    { unfold amm_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    (lazymatch goal with |- ?G => let G' := eval unfold ammove_post, imemmove_result in G in change_no_check G' end). destruct (Z.eqb (U dst) (U src)); [exact (HM k v Hin)|].
    destruct (Z.eq_dec n 0) as [E0 | NZ0].
    { assert (bs = []%list) as -> by (destruct bs; [reflexivity | rewrite E0 in Mlen; cbn in Mlen; lia]). (lazymatch goal with |- ?G => let G' := eval cbn [wbytes] in G in change_no_check G' end). exact (HM k v Hin). }
    rewrite rdn_wbytes_out; [exact (HM k v Hin) | rewrite Mlen, at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Mlen; lia].
  Qed.

  Lemma dblkC : forall (M : word -> option byte) r0,
    (forall x : word, (U x < U sp - 2224 \/ U sp <= U x)%Z -> M x = mem x) -> mem_grows mem M ->
    (forall k v, In (k, v) amm_slots -> rdn segs M (at_ sp k) 8 = Some (word_to_le_bytes 8 v)) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 10 = dst -> getr r0 11 = src -> getr r0 12 = Z_to_bv 64 n ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 224) M rom) (mkst r ra (ammove_post M) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R2 Hret Hdst_stk Hsrc_stk Hcells Hends MV Hsp Hbase IMB IMC HCODE p_flag g_flag imm rt.
    intros M r0 HMA HG SL R2' R10' R11' R12' AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. pose proof (u64_range dst) as Hd. pose proof (u64_range src) as Hs. cells_split.
    assert (HM : forall x : word, (U x < U sp - 2224)%Z -> M x = mem x) by (intros x Hx; apply HMA; lia).
    assert (RA : ret_ok (at_ base 228)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    assert (MVM : moveH segs M dst src n bs).
    { destruct MV as [Mn Mlen Msrc Mdst Mnws Mnwd]. split; try assumption.
      - rewrite <- Msrc. apply rdn_ext; [rewrite Mlen; lia|]. intros x Hx. apply HMA. rewrite Mlen in Hx. lia.
      - eapply store_ok_mono; [exact HG | exact Mdst]. }
    set (r1 := regupd r0 1 (at_ base 228)).
    destruct (imemmove_summary segs imm M dst src n bs rom r1 (at_ base 228) IMC MVM RA)
      as (r2 & RUN2 & KP); [subst r1; gres; reflexivity | subst r1; gres; exact R10' | subst r1; gres; exact R11' | subst r1; gres; exact R12' |].
    assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (KP 2) by notin; subst r1; gres; exact R2').
    assert (A10 : getr r2 10 = dst) by (rewrite (KP 10) by notin; subst r1; gres; exact R10').
    pose proof (fun k v H => slots_post M k v SL H) as SLP. unfold amm_slots in SLP.
    Ltac fldM F D vv SLP :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply SLP; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    wd_eexists. split; [|split].
    - an Fo224 D_6cf20.                                  (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- IMB, <- (at_0 imm).
      eapply msteps_trans; [exact RUN2|].
      an Fo228 D_6cf24.                                  (* [comment removed for export] *)
      fldM Fo232 D_6cf28 ra SLP.
      fldM Fo236 D_6cf2c (getr regs 8) SLP.
      fldM Fo240 D_6cf30 (getr regs 9) SLP.
      fldM Fo244 D_6cf34 (getr regs 18) SLP.
      fldM Fo248 D_6cf38 (getr regs 19) SLP.
      fldM Fo252 D_6cf3c (getr regs 20) SLP.
      fldM Fo256 D_6cf40 (getr regs 21) SLP.
      fldM Fo260 D_6cf44 (getr regs 22) SLP.
      an Fo264 D_6cf48.                                  (* [comment removed for export] *)
      aret Fo268 D_6cf4c ra.                             (* [comment removed for export] *)
      wd_refl.
    - gres. exact A10.
    - intros x Hx. unfold amset_saved in Hx. cbn [In] in Hx. gres.
      repeat (destruct Hx as [<-|Hx];
        [ gres; rwH; rewrite ?at_addi, ?at_0; first
            [ reflexivity
            | f_equal; lia
            | rewrite (KP _) by notin; subst r1; gres; rewrite ?(AG0 _) by notin; first [reflexivity | assumption | rwH; rewrite ?at_addi; f_equal; lia] ]
        |]).
      destruct Hx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac regx AG x := rewrite (AG x) by notin.
  Ltac notin2 := let Hc := fresh "Hin" in intros Hc; cbn [In app qc1_clob rip_clob] in Hc;
    decompose [or] Hc; first [discriminate | contradiction].
  Ltac regxi AG x := rewrite (AG x) by notin2.
  Ltac in_lit := (lazymatch goal with |- ?G => let G' := eval cbn [In app amset_saved] in G in change_no_check G' end); repeat (first [left; reflexivity | right]).
  Ltac from_or Hc := cbn [In app qc1_clob rip_clob] in Hc; decompose [or] Hc; first [contradiction | subst; in_lit; fail].

  Theorem ammove_zero : n = 0%Z ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (ammove_post DM1) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hsrc_stk Hstk Hcells Hfl Rfl Rgf Hends MV Hsp fl Hbase G44 IMB IMC HCODE p_flag g_flag imm rt.
    intros Hz.
    destruct dblkA as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A20 & AK & AG1).
    destruct (dblkSz DM1 r1 Hz A12) as (r2 & RUN2 & B19 & AG2).
    destruct (dblkDz DM1 r2 Hz) as (r3 & RUN3 & AG3); [regx AG2 (10:reg); exact A10 | regx AG2 (12:reg); exact A12 | exact B19 |].
    destruct (dblkC DM1 r3 DM1_agree DM1_grows slots_DM1) as (r4 & RUN4 & C10 & CK);
      [ regx AG3 (2:reg); regx AG2 (2:reg); exact A2 | regx AG3 (10:reg); regx AG2 (10:reg); exact A10
      | regx AG3 (11:reg); regx AG2 (11:reg); exact A11 | regx AG3 (12:reg); regx AG2 (12:reg); exact A12
      | intros x Hx; rewrite (AG3 x); [rewrite (AG2 x); [exact (AG1 x Hx) | intros Hc; apply Hx; from_or Hc] | intros Hc; apply Hx; from_or Hc] |].
    exists r4. split; [|split; [exact C10 | exact CK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
  Qed.

  Theorem ammove_small : forall w0s w1s s1s w0d w1d s1d, (1 <= n <= 64)%Z ->
    qc1H segs mem src n g_shoff p_shoff w0s w1s s1s ->
    qc1H segs mem dst n g_shoff p_shoff w0d w1d s1d ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (ammove_post DM1) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hsrc_stk Hstk Hcells Hfl Rfl Rgf Hends MV Hsp fl Hbase B768 B220 B604 B144 G164 G88 G44 QCS2 QCF2 QCS1 QCF1 IMB IMC HCODE p_flag g_flag imm.
    intros w0s w1s s1s w0d w1d s1d Hs QS QD.
    destruct dblkA as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A20 & AK & AG1).
    destruct (dblkSs DM1 r1 Hs A12) as (r2 & RUN2 & B19 & AG2).
    destruct (dblkQ1 r2 w0s w1s s1s QS) as (r3 & RUN3 & AG3); [regx AG2 (11:reg); exact A11 | regx AG2 (12:reg); exact A12 |].
    assert (C10 : getr r3 10 = dst) by (regxi AG3 (10:reg); regx AG2 (10:reg); exact A10).
    assert (C12 : getr r3 12 = Z_to_bv 64 n) by (regxi AG3 (12:reg); regx AG2 (12:reg); exact A12).
    assert (C19 : getr r3 19 = Z_to_bv 64 (2 ^ 64 + n - 65)) by (regxi AG3 (19:reg); exact B19).
    destruct (dblkDs DM1 r3 Hs C10 C12 C19) as (r4 & RUN4 & AG4).
    destruct (dblkQ2 r4 w0d w1d s1d QD) as (r5 & RUN5 & AG5);
      [regx AG4 (10:reg); exact C10 | regx AG4 (12:reg); exact C12 |].
    destruct (dblkC DM1 r5 DM1_agree DM1_grows slots_DM1) as (r6 & RUN6 & D10 & DK).
    { regxi AG5 (2:reg). regx AG4 (2:reg). regxi AG3 (2:reg). regx AG2 (2:reg). exact A2. }
    { regxi AG5 (10:reg). regx AG4 (10:reg). exact C10. }
    { regxi AG5 (11:reg). regx AG4 (11:reg). regxi AG3 (11:reg). regx AG2 (11:reg). exact A11. }
    { regxi AG5 (12:reg). regx AG4 (12:reg). exact C12. }
    { intros x Hx.
      rewrite (AG5 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG4 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG3 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG2 x) by (intros Hc; apply Hx; from_or Hc). exact (AG1 x Hx). }
    exists r6. split; [|split; [exact D10 | exact DK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
    eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN6.
  Qed.

  Theorem ammove_big : forall (s0s s1s s0d s1d : byte) (midend : word), (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem src midend -> m2sH segs (rt_m2s rt) mem dst midend ->
    ((0x10007fff8000 <= U src /\ U src + n + 1 <= 0x800000000000) \/ U src + n <= 0x7fff7fff)%Z ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0s] -> (U s0s = 0 \/ U src mod 8 < U s0s < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1s] -> (U s1s = 0 \/ (U src + n - 1) mod 8 < U s1s < 128)%Z ->
    (forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0d] -> (U s0d = 0 \/ U dst mod 8 < U s0d < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1d] -> (U s1d = 0 \/ (U dst + n - 1) mod 8 < U s1d < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra (ammove_post DM3) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R12 R11 R10 R2 R1 Hret Hdst_stk Hsrc_stk Hstk Hcells Hfl Rfl Rgf Hends MV Hsp fl Hbase G44 IMB IMC RTB RTOK HCODE p_flag g_flag imm.
    intros s0s s1s s0d s1d midend Hb CHs CHd Rgs Rgd Rs0s Hs0s Rs1s Hs1s Rzs Rs0d Hs0d Rs1d Hs1d Rzd.
    destruct dblkA as (r1 & RUN1 & A1 & A2 & A8 & A10 & A11 & A12 & A20 & AK & AG1).
    destruct (dblkSb DM1 r1 ltac:(lia) A12) as (r2 & RUN2 & B19 & AG2).
    destruct (dblkR1 r2 s0s s1s midend Hb CHs Rgs Rs0s Hs0s Rs1s Hs1s Rzs) as (r3 & RUN3 & C2 & C8 & C10 & C11 & C12 & C19 & C20 & AG3);
      [ regx AG2 (2:reg); exact A2 | regx AG2 (8:reg); exact A8 | regx AG2 (10:reg); exact A10 | regx AG2 (11:reg); exact A11
      | regx AG2 (12:reg); exact A12 | regx AG2 (18:reg); apply AK; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | exact B19 | regx AG2 (20:reg); exact A20 |].
    destruct (dblkDb DM2 r3 ltac:(lia) C10 C12 C19) as (r4 & RUN4 & AG4).
    destruct (dblkR2 r4 s0d s1d midend Hb CHd Rgd Rs0d Hs0d Rs1d Hs1d Rzd) as (r5 & RUN5 & D2 & D10 & D11 & D12 & AG5);
      [ regx AG4 (2:reg); exact C2 | regx AG4 (8:reg); exact C8 | regx AG4 (10:reg); exact C10 | regx AG4 (11:reg); exact C11
      | regx AG4 (12:reg); exact C12 | regx AG4 (19:reg); exact C19 | regx AG4 (20:reg); exact C20 |].
    destruct (dblkC DM3 r5 DM3_agree DM3_grows slots_DM3 D2 D10 D11 D12) as (r6 & RUN6 & E10 & EK).
    { intros x Hx.
      rewrite (AG5 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG4 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG3 x) by (intros Hc; apply Hx; from_or Hc).
      rewrite (AG2 x) by (intros Hc; apply Hx; from_or Hc). exact (AG1 x Hx). }
    exists r6. split; [|split; [exact E10 | exact EK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
    eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN6.
  Qed.

End AMMOVE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record ammoveH (segs : list Segment) (t : ammove_tab) (mem : word -> option byte)
       (dst src : word) (n : Z) (bs : list byte) (ra sp : word) (fl : byte) : Prop := AMMOVEH {
  amh_sp : (0x10007fff8000 + 2304 <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 <= 2 ^ 47)%Z;
  amh_mv : moveH segs mem dst src n bs;
  amh_ends : (bv_unsigned src + n <= 2 ^ 47)%Z /\ (bv_unsigned dst + n <= 2 ^ 47)%Z;
  amh_gf : rdn segs mem (Z_to_bv 64 (mm_g_flag t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mm_p_flag t)));
  amh_fl : rdn segs mem (Z_to_bv 64 (mm_p_flag t)) 1 = Some [fl];
  amh_flnz : bv_unsigned fl <> 0%Z;
  amh_cells : Forall (fun c => 0 <= c /\ c + 8 <= bv_unsigned sp - 2224)%Z
                (mm_g_flag t :: mm_p_flag t :: m2s_cells (rt_m2s (mm_rip t)));
  amh_stk : store_ok segs mem (at_ sp (-2224)) 2224 = true;
  amh_src_stk : (n = 0 \/ bv_unsigned src + n <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= bv_unsigned src)%Z;
  amh_dst_stk : (n = 0 \/ bv_unsigned dst + n <= bv_unsigned sp - 2224 \/ bv_unsigned sp <= bv_unsigned dst)%Z;
  amh_ret : ret_ok ra }.

Section PKG.
  Variable segs : list Segment.
  Variable t : ammove_tab.
  Hypothesis TOK : ammove_tab_ok segs t.
  #[local] Abbreviation U := bv_unsigned.

  Ltac pkg_finish P8 P7 :=
    lazymatch goal with
    | |- store_ok _ _ (at_ _ _) _ = true => exact P8
    | |- Forall _ _ => exact P7
    | _ => first [eassumption | reflexivity]
    end.

  Theorem asan_memmove_intrin_zero : forall mem rom (dst src ra sp : word) (n : Z) (bs : list byte) (fl : byte) regs,
    ammoveH segs t mem dst src n bs ra sp fl -> n = 0%Z ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (mm_base t) mem rom) (mkst r ra (ammove_post dst src bs (DM1 mem ra sp regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst src ra sp n bs fl regs [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11] Hz R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17].
    replace (mkst regs (mm_base t) mem rom) with (mkst regs (at_ (mm_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply ammove_zero. all: pkg_finish P8 P7.
  Qed.

  Theorem asan_memmove_intrin_small : forall mem rom (dst src ra sp : word) (n : Z) (bs : list byte) (fl : byte) regs w0s w1s s1s w0d w1d s1d,
    ammoveH segs t mem dst src n bs ra sp fl -> (1 <= n <= 64)%Z ->
    qc1H segs mem src n (mt_g_shoff (rt_m2s (mm_rip t))) (mt_p_shoff (rt_m2s (mm_rip t))) w0s w1s s1s ->
    qc1H segs mem dst n (mt_g_shoff (rt_m2s (mm_rip t))) (mt_p_shoff (rt_m2s (mm_rip t))) w0d w1d s1d ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (mm_base t) mem rom) (mkst r ra (ammove_post dst src bs (DM1 mem ra sp regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst src ra sp n bs fl regs w0s w1s s1s w0d w1d s1d [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11] Hs QS QD R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17].
    replace (mkst regs (mm_base t) mem rom) with (mkst regs (at_ (mm_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply ammove_small. all: pkg_finish P8 P7.
  Qed.

  Theorem asan_memmove_intrin_big : forall mem rom (dst src ra sp : word) (n : Z) (bs : list byte) (fl : byte) regs
      (s0s s1s s0d s1d : byte) (midend : word),
    ammoveH segs t mem dst src n bs ra sp fl -> (65 <= n <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s (mm_rip t)) mem src midend -> m2sH segs (rt_m2s (mm_rip t)) mem dst midend ->
    ((0x10007fff8000 <= U src /\ U src + n + 1 <= 0x800000000000) \/ U src + n <= 0x7fff7fff)%Z ->
    ((0x10007fff8000 <= U dst /\ U dst + n + 1 <= 0x800000000000) \/ U dst + n <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src))) 1 = Some [s0s] -> (U s0s = 0 \/ U src mod 8 < U s0s < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U src + n - 1))) 1 = Some [s1s] -> (U s1s = 0 \/ (U src + n - 1) mod 8 < U s1s < 128)%Z ->
    (forall a : word, (Sh (up8 (U src)) <= U a < Sh (down8 (U src + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst))) 1 = Some [s0d] -> (U s0d = 0 \/ U dst mod 8 < U s0d < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U dst + n - 1))) 1 = Some [s1d] -> (U s1d = 0 \/ (U dst + n - 1) mod 8 < U s1d < 128)%Z ->
    (forall a : word, (Sh (up8 (U dst)) <= U a < Sh (down8 (U dst + n)))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists r,
      msteps segs (mkst regs (mm_base t) mem rom)
                  (mkst r ra (ammove_post dst src bs (DM3 (mm_base t) (mm_rip t) mem dst src ra sp n regs)) rom)
      /\ getr r 10 = dst /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom dst src ra sp n bs fl regs s0s s1s s0d s1d midend [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11]
           Hb CHs CHd Rgs Rgd Rs0s Hs0s Rs1s Hs1s Rzs Rs0d Hs0d Rs1d Hs1d Rzd R1 R2 R10 R11 R12.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17].
    replace (mkst regs (mm_base t) mem rom) with (mkst regs (at_ (mm_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply ammove_big. all: pkg_finish P8 P7.
  Qed.
End PKG.
End FPGen1.
