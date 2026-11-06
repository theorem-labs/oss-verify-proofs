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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

Definition poison_words : list (option (bv 32)) :=
  [
  Some W_6f608; Some W_6f60c; Some W_6f610; Some W_6f614; Some W_6f618; Some W_6f61c; Some W_6f620; Some W_6f624;
   Some W_6f628; None; None; Some W_6f634; Some W_6f638; Some W_6f63c; Some W_6f640; None; None; Some W_6f64c;
   Some W_6f650; Some W_6f654; Some W_6f658; Some W_6f65c; Some W_6f660; None; None; None; None; Some W_6f674;
   Some W_6f678; Some W_6f67c; Some W_6f680; Some W_6f684; None; None; Some W_6f690; Some W_6f694; Some W_6f698;
   Some W_6f69c; Some W_6f6a0; None; None; Some W_6f6ac; Some W_6f6b0; Some W_6f6b4; Some W_6f6b8; Some W_6f6bc;
   Some W_6f6c0; Some W_6f6c4; Some W_6f6c8; Some W_6f6cc; Some W_6f6d0; Some W_6f6d4; Some W_6f6d8; Some W_6f6dc;
   Some W_6f6e0; Some W_6f6e4; Some W_6f6e8; Some W_6f6ec; Some W_6f6f0; Some W_6f6f4; Some W_6f6f8; Some W_6f6fc;
   Some W_6f700; Some W_6f704; Some W_6f708; Some W_6f70c; Some W_6f710; Some W_6f714; Some W_6f718; Some W_6f71c;
   Some W_6f720; Some W_6f724; Some W_6f728; Some W_6f72c; Some W_6f730; Some W_6f734; Some W_6f738; Some W_6f73c;
   Some W_6f740; Some W_6f744; Some W_6f748; Some W_6f74c; Some W_6f750; Some W_6f754; Some W_6f758; Some W_6f75c;
   Some W_6f760; Some W_6f764; Some W_6f768; Some W_6f76c; Some W_6f770; Some W_6f774; Some W_6f778; None; None;
   Some W_6f784; Some W_6f788; Some W_6f78c; Some W_6f790; Some W_6f794; Some W_6f798; Some W_6f79c; Some W_6f7a0;
   Some W_6f7a4; Some W_6f7a8; Some W_6f7ac; Some W_6f7b0; Some W_6f7b4; Some W_6f7b8; Some W_6f7bc; Some W_6f7c0;
   Some W_6f7c4; Some W_6f7c8; Some W_6f7cc; Some W_6f7d0; Some W_6f7d4; Some W_6f7d8; Some W_6f7dc; Some W_6f7e0;
   Some W_6f7e4; Some W_6f7e8; Some W_6f7ec; Some W_6f7f0; Some W_6f7f4; Some W_6f7f8; Some W_6f7fc; Some W_6f800;
   Some W_6f804; Some W_6f808; None; None; None; Some W_6f818; Some W_6f81c; Some W_6f820; Some W_6f824;
   Some W_6f828; Some W_6f82c; Some W_6f830; Some W_6f834; Some W_6f838; Some W_6f83c; Some W_6f840; Some W_6f844;
   Some W_6f848; None; None; None; None; Some W_6f85c; Some W_6f860; Some W_6f864; Some W_6f868; Some W_6f86c; None;
   None; Some W_6f878; Some W_6f87c; Some W_6f880; Some W_6f884; Some W_6f888; None; None; Some W_6f894;
   Some W_6f898; Some W_6f89c; Some W_6f8a0; Some W_6f8a4; Some W_6f8a8; Some W_6f8ac; Some W_6f8b0; None; None;
   Some W_6f8bc; Some W_6f8c0; None; None; Some W_6f8cc; Some W_6f8d0; Some W_6f8d4; Some W_6f8d8; Some W_6f8dc;
   Some W_6f8e0; Some W_6f8e4; Some W_6f8e8; Some W_6f8ec; Some W_6f8f0; Some W_6f8f4; Some W_6f8f8; Some W_6f8fc;
   Some W_6f900; Some W_6f904; Some W_6f908; Some W_6f90c; Some W_6f910; Some W_6f914; Some W_6f918; Some W_6f91c;
   Some W_6f920; Some W_6f924; Some W_6f928; Some W_6f92c; Some W_6f930; Some W_6f934; Some W_6f938; Some W_6f93c;
   Some W_6f940; Some W_6f944; Some W_6f948; Some W_6f94c; Some W_6f950; Some W_6f954; Some W_6f958; Some W_6f95c;
   Some W_6f960; Some W_6f964; Some W_6f968; Some W_6f96c; Some W_6f970; Some W_6f974; Some W_6f978; Some W_6f97c;
   Some W_6f980; Some W_6f984; Some W_6f988; Some W_6f98c; Some W_6f990; Some W_6f994; Some W_6f998; Some W_6f99c;
   Some W_6f9a0; Some W_6f9a4; None; None; Some W_6f9b0; Some W_6f9b4; Some W_6f9b8; Some W_6f9bc; Some W_6f9c0;
   Some W_6f9c4; Some W_6f9c8; Some W_6f9cc; Some W_6f9d0; Some W_6f9d4; Some W_6f9d8; Some W_6f9dc; Some W_6f9e0;
   Some W_6f9e4; Some W_6f9e8; Some W_6f9ec; Some W_6f9f0; Some W_6f9f4; Some W_6f9f8; Some W_6f9fc; Some W_6fa00;
   Some W_6fa04; Some W_6fa08; Some W_6fa0c; Some W_6fa10; Some W_6fa14; Some W_6fa18; Some W_6fa1c; Some W_6fa20;
   Some W_6fa24; Some W_6fa28; Some W_6fa2c; Some W_6fa30; Some W_6fa34; Some W_6fa38; Some W_6fa3c; Some W_6fa40;
   Some W_6fa44; Some W_6fa48; Some W_6fa4c; Some W_6fa50; None; None; None; Some W_6fa60; Some W_6fa64;
   Some W_6fa68; Some W_6fa6c; Some W_6fa70; None; None; None; Some W_6fa80; Some W_6fa84; Some W_6fa88;
   Some W_6fa8c; None; None; Some W_6fa98; None; None; Some W_6faa4; Some W_6faa8; Some W_6faac; None; None;
   None; None; Some W_6fac0; Some W_6fac4; Some W_6fac8; Some W_6facc; None; Some W_6fad4; None; None;
   Some W_6fae0; Some W_6fae4; Some W_6fae8; Some W_6faec; None; None; Some W_6faf8; Some W_6fafc; Some W_6fb00
  ]%list.

(* [comment removed for export] *)
Definition poison_clob : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28].
(* [comment removed for export] *)
Definition poison_clobx : list reg := [2; 8; 9; 18; 19; 20; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28].

(* [comment removed for export] *)
Definition shad (addr : word) : Z := (bv_unsigned addr / 8 + 0x7fff8000)%Z.
Definition shlen (size : word) : Z := (bv_unsigned size / 8)%Z.

(* [comment removed for export] *)
Definition ps_frame (mem : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (word_to_le_bytes 8 ra))
    (at_ sp (-16)) (word_to_le_bytes 8 s0))
    (at_ sp (-24)) (word_to_le_bytes 8 s1))
    (at_ sp (-32)) (word_to_le_bytes 8 s2))
    (at_ sp (-40)) (word_to_le_bytes 8 s3))
    (at_ sp (-48)) (word_to_le_bytes 8 s4))
    (at_ sp (-56)) (word_to_le_bytes 8 s5).

Section POISON.
  Variable segs : list Segment.
  Variables base mset : word.
  (* [comment removed for export] *)
  Variables g_shoff p_shoff g_midbeg p_midbeg g_midend p_midend g_hiend p_hiend g_rms p_rms g_cfl p_cfl c_cpm : Z.
  Hypothesis HCODE : code_ato segs base 0 poison_words.
  Hypothesis HMS : code_at segs mset 0 mmemset_words.
  Hypothesis G36 : gloadb segs base 36 13 c_cpm.
  Hypothesis G60 : gload segs base 60 13 g_shoff.
  Hypothesis G92 : gload segs base 92 15 g_midbeg.
  Hypothesis G100 : gload segs base 100 16 g_midend.
  Hypothesis G128 : gload segs base 128 5 g_hiend.
  Hypothesis G580 : gload segs base 580 14 g_midbeg.
  Hypothesis G588 : gload segs base 588 15 g_midend.
  Hypothesis G616 : gload segs base 616 15 g_hiend.
  Hypothesis G644 : gload2 segs base 644 13 19 g_rms.
  Hypothesis G684 : gload segs base 684 11 g_cfl.

  (* [comment removed for export] *)
  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_6f608.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_6f60c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_6f610.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_6f614.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_6f618.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_6f61c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_6f620.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_6f624.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_6f628.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo44 : fetch_word segs (at_ base 44) = Some W_6f634.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 11 _ HCODE eq_refl). Qed.
  Lemma Fo48 : fetch_word segs (at_ base 48) = Some W_6f638.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 12 _ HCODE eq_refl). Qed.
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_6f63c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_6f640.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 14 _ HCODE eq_refl). Qed.
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_6f64c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_6f650.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_6f654.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_6f658.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo84 : fetch_word segs (at_ base 84) = Some W_6f65c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 21 _ HCODE eq_refl). Qed.
  Lemma Fo88 : fetch_word segs (at_ base 88) = Some W_6f660.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 22 _ HCODE eq_refl). Qed.
  Lemma Fo108 : fetch_word segs (at_ base 108) = Some W_6f674.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 27 _ HCODE eq_refl). Qed.
  Lemma Fo112 : fetch_word segs (at_ base 112) = Some W_6f678.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 28 _ HCODE eq_refl). Qed.
  Lemma Fo116 : fetch_word segs (at_ base 116) = Some W_6f67c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 29 _ HCODE eq_refl). Qed.
  Lemma Fo120 : fetch_word segs (at_ base 120) = Some W_6f680.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 30 _ HCODE eq_refl). Qed.
  Lemma Fo124 : fetch_word segs (at_ base 124) = Some W_6f684.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 31 _ HCODE eq_refl). Qed.
  Lemma Fo136 : fetch_word segs (at_ base 136) = Some W_6f690.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 34 _ HCODE eq_refl). Qed.
  Lemma Fo140 : fetch_word segs (at_ base 140) = Some W_6f694.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 35 _ HCODE eq_refl). Qed.
  Lemma Fo144 : fetch_word segs (at_ base 144) = Some W_6f698.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 36 _ HCODE eq_refl). Qed.
  Lemma Fo148 : fetch_word segs (at_ base 148) = Some W_6f69c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 37 _ HCODE eq_refl). Qed.
  Lemma Fo152 : fetch_word segs (at_ base 152) = Some W_6f6a0.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 38 _ HCODE eq_refl). Qed.
  Lemma Fo228 : fetch_word segs (at_ base 228) = Some W_6f6ec.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 57 _ HCODE eq_refl). Qed.
  Lemma Fo232 : fetch_word segs (at_ base 232) = Some W_6f6f0.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 58 _ HCODE eq_refl). Qed.
  Lemma Fo236 : fetch_word segs (at_ base 236) = Some W_6f6f4.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 59 _ HCODE eq_refl). Qed.
  Lemma Fo240 : fetch_word segs (at_ base 240) = Some W_6f6f8.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 60 _ HCODE eq_refl). Qed.
  Lemma Fo244 : fetch_word segs (at_ base 244) = Some W_6f6fc.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 61 _ HCODE eq_refl). Qed.
  Lemma Fo248 : fetch_word segs (at_ base 248) = Some W_6f700.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 62 _ HCODE eq_refl). Qed.
  Lemma Fo252 : fetch_word segs (at_ base 252) = Some W_6f704.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 63 _ HCODE eq_refl). Qed.
  Lemma Fo256 : fetch_word segs (at_ base 256) = Some W_6f708.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 64 _ HCODE eq_refl). Qed.
  Lemma Fo260 : fetch_word segs (at_ base 260) = Some W_6f70c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 65 _ HCODE eq_refl). Qed.
  Lemma Fo352 : fetch_word segs (at_ base 352) = Some W_6f768.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 88 _ HCODE eq_refl). Qed.
  Lemma Fo356 : fetch_word segs (at_ base 356) = Some W_6f76c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 89 _ HCODE eq_refl). Qed.
  Lemma Fo360 : fetch_word segs (at_ base 360) = Some W_6f770.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 90 _ HCODE eq_refl). Qed.
  Lemma Fo364 : fetch_word segs (at_ base 364) = Some W_6f774.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 91 _ HCODE eq_refl). Qed.
  Lemma Fo368 : fetch_word segs (at_ base 368) = Some W_6f778.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 92 _ HCODE eq_refl). Qed.
  Lemma Fo560 : fetch_word segs (at_ base 560) = Some W_6f838.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 140 _ HCODE eq_refl). Qed.
  Lemma Fo564 : fetch_word segs (at_ base 564) = Some W_6f83c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 141 _ HCODE eq_refl). Qed.
  Lemma Fo568 : fetch_word segs (at_ base 568) = Some W_6f840.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 142 _ HCODE eq_refl). Qed.
  Lemma Fo572 : fetch_word segs (at_ base 572) = Some W_6f844.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 143 _ HCODE eq_refl). Qed.
  Lemma Fo576 : fetch_word segs (at_ base 576) = Some W_6f848.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 144 _ HCODE eq_refl). Qed.
  Lemma Fo596 : fetch_word segs (at_ base 596) = Some W_6f85c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 149 _ HCODE eq_refl). Qed.
  Lemma Fo600 : fetch_word segs (at_ base 600) = Some W_6f860.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 150 _ HCODE eq_refl). Qed.
  Lemma Fo604 : fetch_word segs (at_ base 604) = Some W_6f864.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 151 _ HCODE eq_refl). Qed.
  Lemma Fo608 : fetch_word segs (at_ base 608) = Some W_6f868.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 152 _ HCODE eq_refl). Qed.
  Lemma Fo612 : fetch_word segs (at_ base 612) = Some W_6f86c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 153 _ HCODE eq_refl). Qed.
  Lemma Fo624 : fetch_word segs (at_ base 624) = Some W_6f878.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 156 _ HCODE eq_refl). Qed.
  Lemma Fo628 : fetch_word segs (at_ base 628) = Some W_6f87c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 157 _ HCODE eq_refl). Qed.
  Lemma Fo632 : fetch_word segs (at_ base 632) = Some W_6f880.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 158 _ HCODE eq_refl). Qed.
  Lemma Fo636 : fetch_word segs (at_ base 636) = Some W_6f884.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 159 _ HCODE eq_refl). Qed.
  Lemma Fo640 : fetch_word segs (at_ base 640) = Some W_6f888.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 160 _ HCODE eq_refl). Qed.
  Lemma Fo652 : fetch_word segs (at_ base 652) = Some W_6f894.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 163 _ HCODE eq_refl). Qed.
  Lemma Fo656 : fetch_word segs (at_ base 656) = Some W_6f898.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 164 _ HCODE eq_refl). Qed.
  Lemma Fo660 : fetch_word segs (at_ base 660) = Some W_6f89c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 165 _ HCODE eq_refl). Qed.
  Lemma Fo664 : fetch_word segs (at_ base 664) = Some W_6f8a0.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 166 _ HCODE eq_refl). Qed.
  Lemma Fo668 : fetch_word segs (at_ base 668) = Some W_6f8a4.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 167 _ HCODE eq_refl). Qed.
  Lemma Fo672 : fetch_word segs (at_ base 672) = Some W_6f8a8.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 168 _ HCODE eq_refl). Qed.
  Lemma Fo676 : fetch_word segs (at_ base 676) = Some W_6f8ac.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 169 _ HCODE eq_refl). Qed.
  Lemma Fo680 : fetch_word segs (at_ base 680) = Some W_6f8b0.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 170 _ HCODE eq_refl). Qed.
  Lemma Fo692 : fetch_word segs (at_ base 692) = Some W_6f8bc.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 173 _ HCODE eq_refl). Qed.
  Lemma Fo696 : fetch_word segs (at_ base 696) = Some W_6f8c0.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 174 _ HCODE eq_refl). Qed.


  Lemma Fo732 : fetch_word segs (at_ base 732) = Some W_6f8e4.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 183 _ HCODE eq_refl). Qed.
  Lemma Fo736 : fetch_word segs (at_ base 736) = Some W_6f8e8.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 184 _ HCODE eq_refl). Qed.
  Lemma Fo740 : fetch_word segs (at_ base 740) = Some W_6f8ec.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 185 _ HCODE eq_refl). Qed.
  Lemma Fo744 : fetch_word segs (at_ base 744) = Some W_6f8f0.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 186 _ HCODE eq_refl). Qed.
  Lemma Fo748 : fetch_word segs (at_ base 748) = Some W_6f8f4.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 187 _ HCODE eq_refl). Qed.
  Lemma Fo752 : fetch_word segs (at_ base 752) = Some W_6f8f8.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 188 _ HCODE eq_refl). Qed.
  Lemma Fo756 : fetch_word segs (at_ base 756) = Some W_6f8fc.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 189 _ HCODE eq_refl). Qed.
  Lemma Fo760 : fetch_word segs (at_ base 760) = Some W_6f900.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 190 _ HCODE eq_refl). Qed.
  Lemma Fo764 : fetch_word segs (at_ base 764) = Some W_6f904.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 191 _ HCODE eq_refl). Qed.
  Lemma Fo768 : fetch_word segs (at_ base 768) = Some W_6f908.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 192 _ HCODE eq_refl). Qed.
  Lemma Fo772 : fetch_word segs (at_ base 772) = Some W_6f90c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 193 _ HCODE eq_refl). Qed.
  Lemma Fo776 : fetch_word segs (at_ base 776) = Some W_6f910.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 194 _ HCODE eq_refl). Qed.
  Lemma Fo780 : fetch_word segs (at_ base 780) = Some W_6f914.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 195 _ HCODE eq_refl). Qed.
  Lemma Fo784 : fetch_word segs (at_ base 784) = Some W_6f918.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 196 _ HCODE eq_refl). Qed.
  Lemma Fo788 : fetch_word segs (at_ base 788) = Some W_6f91c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 197 _ HCODE eq_refl). Qed.
  Lemma Fo792 : fetch_word segs (at_ base 792) = Some W_6f920.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 198 _ HCODE eq_refl). Qed.
  Lemma Fo796 : fetch_word segs (at_ base 796) = Some W_6f924.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 199 _ HCODE eq_refl). Qed.
  Lemma Fo800 : fetch_word segs (at_ base 800) = Some W_6f928.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 200 _ HCODE eq_refl). Qed.
  Lemma Fo804 : fetch_word segs (at_ base 804) = Some W_6f92c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 201 _ HCODE eq_refl). Qed.
  Lemma Fo808 : fetch_word segs (at_ base 808) = Some W_6f930.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 202 _ HCODE eq_refl). Qed.









  Lemma Fo848 : fetch_word segs (at_ base 848) = Some W_6f958.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 212 _ HCODE eq_refl). Qed.
  Lemma Fo852 : fetch_word segs (at_ base 852) = Some W_6f95c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 213 _ HCODE eq_refl). Qed.

  Lemma Fo860 : fetch_word segs (at_ base 860) = Some W_6f964.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 215 _ HCODE eq_refl). Qed.
  Lemma Fo864 : fetch_word segs (at_ base 864) = Some W_6f968.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 216 _ HCODE eq_refl). Qed.

  Lemma Fo872 : fetch_word segs (at_ base 872) = Some W_6f970.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 218 _ HCODE eq_refl). Qed.
  Lemma Fo876 : fetch_word segs (at_ base 876) = Some W_6f974.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 219 _ HCODE eq_refl). Qed.
  Lemma Fo880 : fetch_word segs (at_ base 880) = Some W_6f978.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 220 _ HCODE eq_refl). Qed.
  Lemma Fo884 : fetch_word segs (at_ base 884) = Some W_6f97c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 221 _ HCODE eq_refl). Qed.
  Lemma Fo888 : fetch_word segs (at_ base 888) = Some W_6f980.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 222 _ HCODE eq_refl). Qed.
  Lemma Fo892 : fetch_word segs (at_ base 892) = Some W_6f984.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 223 _ HCODE eq_refl). Qed.
  Lemma Fo896 : fetch_word segs (at_ base 896) = Some W_6f988.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 224 _ HCODE eq_refl). Qed.
  Lemma Fo900 : fetch_word segs (at_ base 900) = Some W_6f98c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 225 _ HCODE eq_refl). Qed.
  Lemma Fo904 : fetch_word segs (at_ base 904) = Some W_6f990.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 226 _ HCODE eq_refl). Qed.
  Lemma Fo908 : fetch_word segs (at_ base 908) = Some W_6f994.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 227 _ HCODE eq_refl). Qed.
  Lemma Fo912 : fetch_word segs (at_ base 912) = Some W_6f998.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 228 _ HCODE eq_refl). Qed.
  Lemma Fo916 : fetch_word segs (at_ base 916) = Some W_6f99c.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 229 _ HCODE eq_refl). Qed.
  Lemma Fo920 : fetch_word segs (at_ base 920) = Some W_6f9a0.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 230 _ HCODE eq_refl). Qed.
  Lemma Fo924 : fetch_word segs (at_ base 924) = Some W_6f9a4.
  Proof using HCODE. exact (code_ato_get segs base 0 poison_words 231 _ HCODE eq_refl). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables addr size value ra sp : word.
  Variable cpm : byte.          (* [comment removed for export] *)
  Variable midend : word.       (* [comment removed for export] *)
  Variable thr : Z.             (* [comment removed for export] *)

  #[local] Abbreviation U := bv_unsigned.
  #[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).

  (* [comment removed for export] *)
  Hypothesis Rg_shoff : rdn segs mem (Z_to_bv 64 g_shoff) 8 = Some (LE8 p_shoff).
  Hypothesis Rshoff : rdn segs mem (Z_to_bv 64 p_shoff) 8 = Some (LE8 0x7fff8000).
  Hypothesis Rg_midbeg : rdn segs mem (Z_to_bv 64 g_midbeg) 8 = Some (LE8 p_midbeg).
  Hypothesis Rmidbeg : rdn segs mem (Z_to_bv 64 p_midbeg) 8 = Some (LE8 0).
  Hypothesis Rg_midend : rdn segs mem (Z_to_bv 64 g_midend) 8 = Some (LE8 p_midend).
  Hypothesis Rmidend : rdn segs mem (Z_to_bv 64 p_midend) 8 = Some (word_to_le_bytes 8 midend).
  Hypothesis Rg_hiend : rdn segs mem (Z_to_bv 64 g_hiend) 8 = Some (LE8 p_hiend).
  Hypothesis Rhiend : rdn segs mem (Z_to_bv 64 p_hiend) 8 = Some (LE8 0x7fffffffffff).
  Hypothesis Rg_rms : rdn segs mem (Z_to_bv 64 g_rms) 8 = Some (LE8 p_rms).
  Hypothesis Rrms : rdn segs mem (Z_to_bv 64 p_rms) 8 = Some (word_to_le_bytes 8 mset).
  Hypothesis Hmset : U mset <> 0%Z.
  Hypothesis Hmset_ok : ret_ok mset.
  Hypothesis Rcpm : U value <> 0%Z -> rdn segs mem (Z_to_bv 64 c_cpm) 1 = Some [cpm] /\ U cpm <> 0%Z.
  Hypothesis Rcfl : U value = 0%Z ->
    rdn segs mem (Z_to_bv 64 g_cfl) 8 = Some (LE8 p_cfl)
    /\ rdn segs mem (Z_to_bv 64 (p_cfl + 120)) 8 = Some (LE8 thr)
    /\ (shlen size < thr)%Z /\ (0 <= thr < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Definition ps_cells : list Z :=
    [g_shoff; p_shoff; g_midbeg; p_midbeg; g_midend; p_midend; g_hiend; p_hiend; g_rms; p_rms; c_cpm; g_cfl; p_cfl; p_cfl + 120]%Z.
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 64)%Z ps_cells.
  (* [comment removed for export] *)
  Hypothesis Haddr8 : (U addr mod 8 = 0)%Z.
  Hypothesis Hsize8 : (U size mod 8 = 0)%Z.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Haddr_rng :
    (0x10007fff8000 <= U addr /\ 0x10007fff8008 <= U addr + U size /\ U addr + U size <= 0x800000000000
     /\ U addr + 8 <= 0x800000000000)%Z
    \/ (8 <= U addr + U size /\ U addr + U size <= 0x7fff8000 /\ U addr <= 0x7fff7fff)%Z.
  (* [comment removed for export] *)
  Hypothesis Hsp : (U sp < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-64)) 64 = true.
  Hypothesis Hshw : store_ok segs mem (Z_to_bv 64 (shad addr)) (Z.to_nat (shlen size)) = true.
  Hypothesis Hret : ret_ok ra.

  #[local] Abbreviation CL := (fun r => In r poison_clob).
  #[local] Abbreviation CLX := (fun r => In r poison_clobx).

  Lemma cell_bound : forall c, In c ps_cells -> (0 <= c /\ c + 8 <= U sp - 64)%Z.
  Proof using Hcells. intros c Hc. exact (proj1 (Forall_forall _ _) Hcells c Hc). Qed.

  Ltac cellb c := pose proof (cell_bound c ltac:((lazymatch goal with |- ?G => let G' := eval cbn [ps_cells In] in G in change_no_check G' end); am_tauto)).

  Lemma size_div8 : (U size = 8 * shlen size)%Z.
  Proof using Haddr_rng Hsize8 addr. (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). pose proof (Z.div_mod (U size) 8 ltac:(lia)). lia. Qed.
  Lemma addr_div8 : (U addr = 8 * (U addr / 8))%Z.
  Proof using Haddr_rng Haddr8 size. pose proof (Z.div_mod (U addr) 8 ltac:(lia)). lia. Qed.

  Section WithRegs.
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = addr.
  Hypothesis H11 : getr regs 11 = size.
  Hypothesis H12 : getr regs 12 = value.

  (* [comment removed for export] *)
  Definition M1 : word -> option byte :=
    ps_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21).

  (* [comment removed for export] *)
  Lemma rdM1 : forall c n bs, (0 <= c)%Z -> (c + Z.of_nat n <= U sp - 64)%Z ->
    rdn segs mem (Z_to_bv 64 c) n = Some bs -> rdn segs M1 (Z_to_bv 64 c) n = Some bs.
  Proof using Hsp size addr.
    intros c n bs Hc0 Hc Hr. (lazymatch goal with |- ?G => let G' := eval unfold M1, ps_frame in G in change_no_check G' end).
    rewrite !rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); unorm; try lia.
    exact Hr.
  Qed.

  Lemma M1_ok : forall (a : word) n, store_ok segs mem a n = true -> store_ok segs M1 a n = true.
  Proof using.
    intros a n H. (lazymatch goal with |- ?G => let G' := eval unfold M1, ps_frame in G in change_no_check G' end).
    repeat (eapply store_ok_mono; [apply wbytes_grows|]). exact H.
  Qed.

  (* [comment removed for export] *)
  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          eapply (store_ok_sub segs mem (at_ sp (-64)) _ 64);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Ltac cld F D vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?v_addi_0;
          first [ apply rdM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr]
                | (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; apply rdM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr] ]
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  Ltac gl G Hr :=
    eapply msteps_trans; [ eapply G; apply rdM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr] | ]; zlit_at.
  Ltac gl2 GX Hr :=
    eapply msteps_trans; [ eapply GX; apply rdM1; [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr] | ]; zlit_at.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkA :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 52) M1 rom)
      /\ getr r 1 = ra /\ getr r 2 = at_ sp (-64) /\ getr r 10 = addr /\ getr r 11 = size /\ getr r 12 = value
      /\ regs_agree CLX regs r.
  Proof using H12 H11 H10 H2 H1 Hstk Hsp Haddr_rng Hcells Rcpm cpm G36 HCODE c_cpm p_cfl g_cfl p_rms g_rms p_hiend g_hiend p_midend g_midend p_midbeg g_midbeg p_shoff g_shoff.
    pose proof (u64_range sp) as Hspr. pose proof Hcells as HC.
    unfold ps_cells in HC.
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
    (* [comment removed for export] *)
    Ltac prologue :=
      an Fo0 D_6f608;                                    (* [comment removed for export] *)
      fsd Fo4 D_6f60c (at_ sp (-8));                     (* [comment removed for export] *)
      fsd Fo8 D_6f610 (at_ sp (-16));                    (* [comment removed for export] *)
      fsd Fo12 D_6f614 (at_ sp (-24));                   (* [comment removed for export] *)
      fsd Fo16 D_6f618 (at_ sp (-32));                   (* [comment removed for export] *)
      fsd Fo20 D_6f61c (at_ sp (-40));                   (* [comment removed for export] *)
      fsd Fo24 D_6f620 (at_ sp (-48));                   (* [comment removed for export] *)
      fsd Fo28 D_6f624 (at_ sp (-56));                   (* [comment removed for export] *)
      change (wbytes _ _ _) with M1.
    destruct (Z.eq_dec (U value) 0) as [Hz|Hnz].
    - wd_eexists. split.
      + prologue.
        ab_tk Fo32 D_6f628 ltac:(condz).                 (* [comment removed for export] *)
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold poison_clobx in G in change_no_check G' end); solve_regs_agree.
    - destruct (Rcpm Hnz) as [Rc Hc]. pose proof (u_v_lb_nz cpm Hc).
      wd_eexists. split.
      + prologue.
        ab_ft Fo32 D_6f628 ltac:(condz).                 (* [comment removed for export] *)
        gl G36 Rc.                                         (* [comment removed for export] *)
        afence Fo44 D_6f634.                               (* [comment removed for export] *)
        ab_ft Fo48 D_6f638 ltac:(condz).                 (* [comment removed for export] *)
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold poison_clobx in G in change_no_check G' end); solve_regs_agree.
  Qed.

  Lemma div8_facts :
    ((U addr + U size - 8) / 8 = U addr / 8 + shlen size - 1)%Z /\ (0 <= shlen size <= 2 ^ 44)%Z
    /\ (0 <= U addr / 8 < 2 ^ 44)%Z.
  Proof using Haddr_rng Hsize8 Haddr8.
    (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). pose proof addr_div8. pose proof size_div8. unfold shlen in *.
    pose proof (u64_range addr). pose proof (u64_range size).
    assert (HR : (8 <= U addr + U size /\ U addr + U size <= 2 ^ 47 /\ U addr < 2 ^ 47)%Z) by (destruct Haddr_rng; lia).
    split; [|split; [split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]
                   |split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]]].
    replace (U addr + U size - 8)%Z with ((U addr / 8 + U size / 8 - 1) * 8)%Z by lia.
    rewrite Z.div_mul by lia. reflexivity.
  Qed.

  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC; unfold ps_cells in HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkB : forall r0,
    getr r0 1 = ra -> getr r0 2 = at_ sp (-64) -> getr r0 10 = addr -> getr r0 11 = size -> getr r0 12 = value ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 52) M1 rom) (mkst r (at_ base 680) M1 rom)
      /\ getr r 1 = ra /\ getr r 2 = at_ sp (-64) /\ getr r 12 = value
      /\ getr r 10 = Z_to_bv 64 (shad addr) /\ getr r 8 = Z_to_bv 64 (shlen size)
      /\ getr r 9 = Z_to_bv 64 0x7fff8000 /\ getr r 6 = mset /\ getr r 19 = Z_to_bv 64 p_rms
      /\ getr r 18 = Z_to_bv 64 (U addr / 8 + shlen size)
      /\ regs_agree CLX regs r.
  Proof using Hsp Haddr_rng Hsize8 Haddr8 Hcells Hmset Rrms Rg_rms Rhiend Rg_hiend Rmidend Rg_midend Rmidbeg Rg_midbeg Rshoff Rg_shoff midend G644 G616 G588 G580 G128 G100 G92 G60 HCODE c_cpm p_cfl g_cfl g_rms p_hiend g_hiend p_midend g_midend p_midbeg g_midbeg p_shoff g_shoff.
    intros r0 R1 R2 R10 R11 R12 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range addr) as Har. pose proof (u64_range size) as Hsr.
    pose proof (u64_range mset) as Hmr.
    destruct div8_facts as (Hd1 & Hd2 & Hd3).
    cells_split. destruct G644 as [x644 GX644].
    destruct Haddr_rng as [(Haddr_lo & Haddr_lo8 & Haddr_hi & Haddr_hi8) | (Hlow8 & Hlow_hi & Hlow_lo)].
    2:{ (* [comment removed for export] *)
    wd_eexists. split.
    - av Fo52 D_6f63c (Z_to_bv 64 0) ltac:(apply v_andi_7_aligned; exact Haddr8).   (* [comment removed for export] *)
      ab_ft Fo56 D_6f640 ltac:(condz).                   (* [comment removed for export] *)
      gl G60 Rg_shoff.                                     (* [comment removed for export] *)
      cld Fo68 D_6f64c (Z_to_bv 64 0x7fff8000) Rshoff.     (* [comment removed for export] *)
      an Fo72 D_6f650.                                     (* [comment removed for export] *)
      an Fo76 D_6f654.                                     (* [comment removed for export] *)
      an Fo80 D_6f658.                                     (* [comment removed for export] *)
      an Fo84 D_6f65c.                                     (* [comment removed for export] *)
      ab_tk Fo88 D_6f660 ltac:(condz).                   (* [comment removed for export] *)
      av Fo560 D_6f838 (Z_to_bv 64 0) ltac:(apply v_andi_7_aligned; exact Hsize8).  (* [comment removed for export] *)
      ab_ft Fo564 D_6f83c ltac:(condz).                  (* [comment removed for export] *)
      av Fo568 D_6f840 (Z_to_bv 64 (U addr + U size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); reflexivity).   (* [comment removed for export] *)
      av Fo572 D_6f844 (Z_to_bv 64 (U addr + U size - 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).  (* [comment removed for export] *)
      ab_tk Fo576 D_6f848 ltac:(condz).                  (* [comment removed for export] *)
      gl2 GX644 Rg_rms.                                     (* [comment removed for export] *)
      cld Fo652 D_6f894 mset Rrms.                         (* [comment removed for export] *)
      ab_ft Fo656 D_6f898 ltac:(condz).                  (* [comment removed for export] *)
      av Fo660 D_6f89c (Z_to_bv 64 (U addr / 8)) ltac:(apply v_srli_3).                     (* [comment removed for export] *)
      av Fo664 D_6f8a0 (Z_to_bv 64 (U addr / 8 + shlen size - 1)) ltac:(rewrite v_srli_3; unorm; rewrite Hd1; reflexivity). (* [comment removed for export] *)
      av Fo668 D_6f8a4 (Z_to_bv 64 (shad addr)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, shad in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av Fo672 D_6f8a8 (Z_to_bv 64 (U addr / 8 + shlen size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).  (* [comment removed for export] *)
      av Fo676 D_6f8ac (Z_to_bv 64 (shlen size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold poison_clobx in G in change_no_check G' end). ra_chain. }
    (* [comment removed for export] *)
    wd_eexists. split.
    - av Fo52 D_6f63c (Z_to_bv 64 0) ltac:(apply v_andi_7_aligned; exact Haddr8).   (* [comment removed for export] *)
      ab_ft Fo56 D_6f640 ltac:(condz).                   (* [comment removed for export] *)
      gl G60 Rg_shoff.                                     (* [comment removed for export] *)
      cld Fo68 D_6f64c (Z_to_bv 64 0x7fff8000) Rshoff.     (* [comment removed for export] *)
      an Fo72 D_6f650.                                     (* [comment removed for export] *)
      an Fo76 D_6f654.                                     (* [comment removed for export] *)
      an Fo80 D_6f658.                                     (* [comment removed for export] *)
      an Fo84 D_6f65c.                                     (* [comment removed for export] *)
      ab_ft Fo88 D_6f660 ltac:(condz).                   (* [comment removed for export] *)
      gl G92 Rg_midbeg.                                    (* [comment removed for export] *)
      gl G100 Rg_midend.                                   (* [comment removed for export] *)
      cld Fo108 D_6f674 (Z_to_bv 64 0) Rmidbeg.            (* [comment removed for export] *)
      cld Fo112 D_6f678 midend Rmidend.                    (* [comment removed for export] *)
      an Fo116 D_6f67c.                                    (* [comment removed for export] *)
      ab_tk Fo120 D_6f680 ltac:(condz).                  (* [comment removed for export] *)
      gl G128 Rg_hiend.                                    (* [comment removed for export] *)
      cld Fo136 D_6f690 (Z_to_bv 64 0x7fffffffffff) Rhiend. (* [comment removed for export] *)
      an Fo140 D_6f694.                                    (* [comment removed for export] *)
      an Fo144 D_6f698.                                    (* [comment removed for export] *)
      ab_ft Fo148 D_6f69c ltac:(condz).                  (* [comment removed for export] *)
      ab_tk Fo152 D_6f6a0 ltac:(condz).                  (* [comment removed for export] *)
      cld Fo352 D_6f768 (Z_to_bv 64 0x7fffffffffff) Rhiend. (* [comment removed for export] *)
      an Fo356 D_6f76c.                                    (* [comment removed for export] *)
      an Fo360 D_6f770.                                    (* [comment removed for export] *)
      ab_ft Fo364 D_6f774 ltac:(condz).                  (* [comment removed for export] *)
      ab_tk Fo368 D_6f778 ltac:(condz).                  (* [comment removed for export] *)
      av Fo560 D_6f838 (Z_to_bv 64 0) ltac:(apply v_andi_7_aligned; exact Hsize8).  (* [comment removed for export] *)
      ab_ft Fo564 D_6f83c ltac:(condz).                  (* [comment removed for export] *)
      av Fo568 D_6f840 (Z_to_bv 64 (U addr + U size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); reflexivity).   (* [comment removed for export] *)
      av Fo572 D_6f844 (Z_to_bv 64 (U addr + U size - 8)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).  (* [comment removed for export] *)
      ab_ft Fo576 D_6f848 ltac:(condz).                  (* [comment removed for export] *)
      gl G580 Rg_midbeg.                                   (* [comment removed for export] *)
      gl G588 Rg_midend.                                   (* [comment removed for export] *)
      cld Fo596 D_6f85c (Z_to_bv 64 0) Rmidbeg.            (* [comment removed for export] *)
      cld Fo600 D_6f860 midend Rmidend.                    (* [comment removed for export] *)
      an Fo604 D_6f864.                                    (* [comment removed for export] *)
      ab_tk Fo608 D_6f868 ltac:(condz).                  (* [comment removed for export] *)
      gl G616 Rg_hiend.                                    (* [comment removed for export] *)
      cld Fo624 D_6f878 (Z_to_bv 64 0x7fffffffffff) Rhiend. (* [comment removed for export] *)
      an Fo628 D_6f87c.                                    (* [comment removed for export] *)
      an Fo632 D_6f880.                                    (* [comment removed for export] *)
      ab_ft Fo636 D_6f884 ltac:(condz).                  (* [comment removed for export] *)
      ab_ft Fo640 D_6f888 ltac:(condz).                  (* [comment removed for export] *)
      gl2 GX644 Rg_rms.                                     (* [comment removed for export] *)
      cld Fo652 D_6f894 mset Rrms.                         (* [comment removed for export] *)
      ab_ft Fo656 D_6f898 ltac:(condz).                  (* [comment removed for export] *)
      av Fo660 D_6f89c (Z_to_bv 64 (U addr / 8)) ltac:(apply v_srli_3).                     (* [comment removed for export] *)
      av Fo664 D_6f8a0 (Z_to_bv 64 (U addr / 8 + shlen size - 1)) ltac:(rewrite v_srli_3; unorm; rewrite Hd1; reflexivity). (* [comment removed for export] *)
      av Fo668 D_6f8a4 (Z_to_bv 64 (shad addr)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, shad in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      av Fo672 D_6f8a8 (Z_to_bv 64 (U addr / 8 + shlen size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).  (* [comment removed for export] *)
      av Fo676 D_6f8ac (Z_to_bv 64 (shlen size)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold poison_clobx in G in change_no_check G' end). ra_chain.
  Qed.

  (* [comment removed for export] *)
  Ltac fld F D vv :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold M1, ps_frame in G in change_no_check G' end); rd8_chain
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkC : forall r0,
    getr r0 1 = ra -> getr r0 2 = at_ sp (-64) -> getr r0 12 = value ->
    getr r0 10 = Z_to_bv 64 (shad addr) -> getr r0 8 = Z_to_bv 64 (shlen size) ->
    getr r0 9 = Z_to_bv 64 0x7fff8000 -> getr r0 6 = mset -> getr r0 19 = Z_to_bv 64 p_rms ->
    regs_agree CLX regs r0 ->
    exists r,
      msteps segs (mkst r0 (at_ base 680) M1 rom) (mkst r (at_ mset 0) M1 rom)
      /\ getr r 1 = ra /\ getr r 2 = sp /\ getr r 10 = Z_to_bv 64 (shad addr) /\ getr r 11 = value
      /\ getr r 12 = Z_to_bv 64 (shlen size)
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21
      /\ regs_agree CLX regs r.
  Proof using H1 Hsp Haddr_rng Hsize8 Haddr8 Hcells Rcfl Hmset_ok thr G684 HCODE c_cpm p_cfl g_cfl g_rms p_hiend g_hiend p_midend g_midend p_midbeg g_midbeg p_shoff g_shoff.
    intros r0 R1 R2 R12 R10 R8 R9 R6 R19 AG0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range value) as Hvr.
    destruct div8_facts as (Hd1 & Hd2 & Hd3).
    cells_split.
    (* [comment removed for export] *)
    Ltac tail :=
      an Fo872 D_6f970;                                    (* [comment removed for export] *)
      an Fo876 D_6f974;                                    (* [comment removed for export] *)
      an Fo888 D_6f980;                                    (* [comment removed for export] *)
      fld Fo892 D_6f984 ra;                                (* [comment removed for export] *)
      fld Fo896 D_6f988 (getr regs 8);                     (* [comment removed for export] *)
      fld Fo900 D_6f98c (getr regs 9);                     (* [comment removed for export] *)
      fld Fo904 D_6f990 (getr regs 18);                    (* [comment removed for export] *)
      fld Fo908 D_6f994 (getr regs 19);                    (* [comment removed for export] *)
      fld Fo912 D_6f998 (getr regs 20);                    (* [comment removed for export] *)
      fld Fo916 D_6f99c (getr regs 21);                    (* [comment removed for export] *)
      an Fo920 D_6f9a0;                                    (* [comment removed for export] *)
      aret Fo924 D_6f9a4 mset;                             (* [comment removed for export] *)
      rewrite <- (at_0 mset); wd_refl.
    destruct (Z.eq_dec (U value) 0) as [Hz|Hnz].
    - destruct (Rcfl Hz) as (Rg & Rt & Hlt & Hthr).
      wd_eexists. split.
      + ab_ft Fo680 D_6f8b0 ltac:(condz).                (* [comment removed for export] *)
        gl G684 Rg.                                          (* [comment removed for export] *)
        cld Fo692 D_6f8bc (Z_to_bv 64 thr) Rt.               (* [comment removed for export] *)
        ab_tk Fo696 D_6f8c0 ltac:(condz).                  (* [comment removed for export] *)
        tail.
      + post; rewrite ?at_0; try reflexivity. (lazymatch goal with |- ?G => let G' := eval unfold poison_clobx in G in change_no_check G' end). ra_solve.
    - wd_eexists. split.
      + ab_tk Fo680 D_6f8b0 ltac:(condz).                (* [comment removed for export] *)
        tail.
      + post; rewrite ?at_0; try reflexivity. (lazymatch goal with |- ?G => let G' := eval unfold poison_clobx in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem poison_run :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom)
                  (mkst r ra (wbytes M1 (Z_to_bv 64 (shad addr)) (repeat (cbyte value) (Z.to_nat (shlen size)))) rom)
      /\ regs_agree CL regs r.
  Proof using H12 H11 H10 H2 H1 Hret Hshw Hstk Hsp Haddr_rng Hsize8 Haddr8 Hcells Rcfl Rcpm Hmset_ok Hmset Rrms Rg_rms Rhiend Rg_hiend Rmidend Rg_midend Rmidbeg Rg_midbeg Rshoff Rg_shoff thr midend cpm G684 G644 G616 G588 G580 G128 G100 G92 G60 G36 HMS HCODE c_cpm p_cfl g_cfl p_rms g_rms p_hiend g_hiend p_midend g_midend p_midbeg g_midbeg p_shoff g_shoff mset.
    pose proof (u64_range sp) as Hspr. destruct div8_facts as (Hd1 & Hd2 & Hd3).
    destruct blkA as (r1 & RUN1 & A1 & A2 & A10 & A11 & A12 & AG1).
    destruct (blkB r1 A1 A2 A10 A11 A12 AG1) as (r2 & RUN2 & B1 & B2 & B12 & B10 & B8 & B9 & B6 & B19 & B18 & AG2).
    destruct (blkC r2 B1 B2 B12 B10 B8 B9 B6 B19 AG2)
      as (r3 & RUN3 & C1 & C2 & C10 & C11 & C12 & C8 & C9 & C18 & C19 & C20 & C21 & AG3).
    assert (Hok1 : store_ok segs M1 (Z_to_bv 64 (shad addr)) (Z.to_nat (shlen size)) = true) by (apply M1_ok; exact Hshw).
    destruct (memset_summary segs mset HMS M1 (Z_to_bv 64 (shad addr)) value ra (shlen size) rom
                ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold shad in G in change_no_check G' end); wd_ulia) Hok1 Hret r3 C10 C11 C12 C1) as (r4 & RUN4 & D10 & AG4).
    exists r4. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      eapply msteps_trans; [exact RUN3|]. exact RUN4.
    - (* [comment removed for export] *)
      assert (AG3' : regs_agree CL regs r3).
      { apply (regs_agree_strengthen poison_clob poison_clobx regs r3 AG3).
        intros r Hr Hn. cbn [poison_clobx In] in Hr.
        repeat (destruct Hr as [<-|Hr]; [first [assumption | rewrite <- H2 in C2; exact C2 | exfalso; apply Hn; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto] |]).
        destruct Hr. }
      intros r Hr. rewrite (AG4 r); [apply AG3', Hr|].
      intros Hm. apply Hr. unfold ms_clob in Hm. cbn [In] in Hm. (lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end). repeat (destruct Hm as [<-|Hm]; [(lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat first [left; reflexivity | right] |]). destruct Hm.
  Qed.
  End WithRegs.

End POISON.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record poison_tab : Type := PT {
  pt_base : word; pt_mset : word;
  pt_g_shoff : Z; pt_p_shoff : Z; pt_g_midbeg : Z; pt_p_midbeg : Z; pt_g_midend : Z; pt_p_midend : Z;
  pt_g_hiend : Z; pt_p_hiend : Z; pt_g_rms : Z; pt_p_rms : Z; pt_g_cfl : Z; pt_p_cfl : Z; pt_c_cpm : Z }.

(* [comment removed for export] *)
Record poison_tab_ok (segs : list Segment) (t : poison_tab) : Prop := PTOK {
  pto_code : code_ato segs (pt_base t) 0 poison_words;
  pto_mset : code_at segs (pt_mset t) 0 mmemset_words;
  pto_g36 : gloadb segs (pt_base t) 36 13 (pt_c_cpm t);
  pto_g60 : gload segs (pt_base t) 60 13 (pt_g_shoff t);
  pto_g92 : gload segs (pt_base t) 92 15 (pt_g_midbeg t);
  pto_g100 : gload segs (pt_base t) 100 16 (pt_g_midend t);
  pto_g128 : gload segs (pt_base t) 128 5 (pt_g_hiend t);
  pto_g580 : gload segs (pt_base t) 580 14 (pt_g_midbeg t);
  pto_g588 : gload segs (pt_base t) 588 15 (pt_g_midend t);
  pto_g616 : gload segs (pt_base t) 616 15 (pt_g_hiend t);
  pto_g644 : gload2 segs (pt_base t) 644 13 19 (pt_g_rms t);
  pto_g684 : gload segs (pt_base t) 684 11 (pt_g_cfl t) }.

(* [comment removed for export] *)
Definition poison_cells (t : poison_tab) : list Z :=
  [pt_g_shoff t; pt_p_shoff t; pt_g_midbeg t; pt_p_midbeg t; pt_g_midend t; pt_p_midend t; pt_g_hiend t;
   pt_p_hiend t; pt_g_rms t; pt_p_rms t; pt_c_cpm t; pt_g_cfl t; pt_p_cfl t; pt_p_cfl t + 120]%Z.

(* [comment removed for export] *)
Record poisonH (segs : list Segment) (t : poison_tab) (mem : word -> option byte)
       (addr size value ra sp : word) (cpm : byte) (midend : word) (thr : Z) : Prop := POISONH {
  ph_g_shoff : rdn segs mem (Z_to_bv 64 (pt_g_shoff t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (pt_p_shoff t)));
  ph_shoff : rdn segs mem (Z_to_bv 64 (pt_p_shoff t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000));
  ph_g_midbeg : rdn segs mem (Z_to_bv 64 (pt_g_midbeg t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (pt_p_midbeg t)));
  ph_midbeg : rdn segs mem (Z_to_bv 64 (pt_p_midbeg t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  ph_g_midend : rdn segs mem (Z_to_bv 64 (pt_g_midend t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (pt_p_midend t)));
  ph_midend : rdn segs mem (Z_to_bv 64 (pt_p_midend t)) 8 = Some (word_to_le_bytes 8 midend);
  ph_g_hiend : rdn segs mem (Z_to_bv 64 (pt_g_hiend t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (pt_p_hiend t)));
  ph_hiend : rdn segs mem (Z_to_bv 64 (pt_p_hiend t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff));
  ph_g_rms : rdn segs mem (Z_to_bv 64 (pt_g_rms t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (pt_p_rms t)));
  ph_rms : rdn segs mem (Z_to_bv 64 (pt_p_rms t)) 8 = Some (word_to_le_bytes 8 (pt_mset t));
  ph_mset : bv_unsigned (pt_mset t) <> 0%Z;
  ph_mset_ok : ret_ok (pt_mset t);
  ph_cpm : bv_unsigned value <> 0%Z ->
           rdn segs mem (Z_to_bv 64 (pt_c_cpm t)) 1 = Some [cpm] /\ bv_unsigned cpm <> 0%Z;
  ph_cfl : bv_unsigned value = 0%Z ->
           rdn segs mem (Z_to_bv 64 (pt_g_cfl t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (pt_p_cfl t)))
           /\ rdn segs mem (Z_to_bv 64 (pt_p_cfl t + 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 thr))
           /\ (shlen size < thr)%Z /\ (0 <= thr < 2 ^ 64)%Z;
  ph_cells : Forall (fun c => 0 <= c /\ c + 8 <= bv_unsigned sp - 64)%Z (poison_cells t);
  ph_addr8 : (bv_unsigned addr mod 8 = 0)%Z;
  ph_size8 : (bv_unsigned size mod 8 = 0)%Z;
  ph_rng : (0x10007fff8000 <= bv_unsigned addr /\ 0x10007fff8008 <= bv_unsigned addr + bv_unsigned size
             /\ bv_unsigned addr + bv_unsigned size <= 0x800000000000 /\ bv_unsigned addr + 8 <= 0x800000000000)%Z
           \/ (8 <= bv_unsigned addr + bv_unsigned size /\ bv_unsigned addr + bv_unsigned size <= 0x7fff8000
               /\ bv_unsigned addr <= 0x7fff7fff)%Z;      (* [comment removed for export] *)
  ph_sp : (bv_unsigned sp < 2 ^ 64)%Z;
  ph_stk : store_ok segs mem (at_ sp (-64)) 64 = true;
  ph_shw : store_ok segs mem (Z_to_bv 64 (shad addr)) (Z.to_nat (shlen size)) = true;
  ph_ret : ret_ok ra }.

Theorem poison_shadow : forall segs t, poison_tab_ok segs t ->
  forall mem rom (addr size value ra sp : word) cpm midend thr regs,
  poisonH segs t mem addr size value ra sp cpm midend thr ->
  getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = addr -> getr regs 11 = size -> getr regs 12 = value ->
  exists r,
    msteps segs (mkst regs (pt_base t) mem rom)
                (mkst r ra (wbytes (ps_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                                             (getr regs 20) (getr regs 21))
                                   (Z_to_bv 64 (shad addr)) (repeat (cbyte value) (Z.to_nat (shlen size)))) rom)
    /\ regs_agree (fun r => In r poison_clob) regs r.
Proof using.
  intros segs t [TC TM T36 T60 T92 T100 T128 T580 T588 T616 T644 T684] mem rom addr size value ra sp cpm midend thr regs
         [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P21 P22 P23 P24] H1 H2 H10 H11 H12.
  rewrite <- (at_0 (pt_base t)).
  exact (poison_run segs (pt_base t) (pt_mset t) _ _ _ _ _ _ _ _ _ _ _ _ _ TC TM T36 T60 T92 T100 T128 T580 T588 T616 T644 T684
           mem rom addr size value ra sp cpm midend thr P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P21 P22 P23 P24
           regs H1 H2 H10 H11 H12).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma ps_frame_mrestrict : forall H mem (sp ra s0 s1 s2 s3 s4 s5 : word),
  (64 <= bv_unsigned sp)%Z -> hid_off H (bv_unsigned sp - 64) 64 ->
  ps_frame (mrestrict H mem) sp ra s0 s1 s2 s3 s4 s5 = mrestrict H (ps_frame mem sp ra s0 s1 s2 s3 s4 s5).
Proof using.
  intros H mem sp ra s0 s1 s2 s3 s4 s5 Hsp Hh. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end).
  rewrite !wbytes_mrestrict; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); try lia;
    try reflexivity; intros x Hx; apply Hh; lia.
Qed.

  (* [comment removed for export] *)
End FPGen1.
 Ltac rr Hh := rewrite rdn_mrestrict; [ assumption | wd_ulia_c | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [exact Hh | eapply hid_off_sub; [exact Hh | lia | lia]] ].
Section FPGen2.
Context {fx : FPState}.

End FPGen2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
