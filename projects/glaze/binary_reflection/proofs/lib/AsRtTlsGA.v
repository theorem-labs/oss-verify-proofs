(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsRtXStrlen.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Definition xstrlen_words : list (option (bv 32)) :=
  [
   Some W_5c574; Some W_5c578; Some W_5c57c; Some W_5c580; Some W_5c584; Some W_5c588; Some W_5c58c; Some W_5c590;
   Some W_5c594; Some W_5c598; Some W_5c59c; Some W_5c5a0; Some W_5c5a4; Some W_5c5a8; Some W_5c5ac; None;
   None; Some W_5c5b8; Some W_5c5bc; Some W_5c5c0; Some W_5c5c4; None; None; Some W_5c5d0;
   Some W_5c5d4; Some W_5c5d8; Some W_5c5dc; Some W_5c5e0; Some W_5c5e4; Some W_5c5e8; Some W_5c5ec; Some W_5c5f0;
   None; None; Some W_5c5fc; Some W_5c600; Some W_5c604; Some W_5c608; Some W_5c60c; Some W_5c610;
   Some W_5c614; Some W_5c618; Some W_5c61c; Some W_5c620; Some W_5c624; Some W_5c628; Some W_5c62c; Some W_5c630;
   Some W_5c634; Some W_5c638; Some W_5c63c; Some W_5c640; Some W_5c644; Some W_5c648; Some W_5c64c; Some W_5c650;
   Some W_5c654; Some W_5c658; Some W_5c65c; Some W_5c660; Some W_5c664; Some W_5c668; Some W_5c66c; Some W_5c670;
   Some W_5c674; Some W_5c678; Some W_5c67c; Some W_5c680; Some W_5c684; Some W_5c688; Some W_5c68c; Some W_5c690;
   Some W_5c694; Some W_5c698; Some W_5c69c; Some W_5c6a0; Some W_5c6a4; Some W_5c6a8; Some W_5c6ac; Some W_5c6b0;
   Some W_5c6b4; Some W_5c6b8; Some W_5c6bc; Some W_5c6c0; Some W_5c6c4; Some W_5c6c8; Some W_5c6cc; Some W_5c6d0;
   Some W_5c6d4; Some W_5c6d8; Some W_5c6dc; Some W_5c6e0; Some W_5c6e4; Some W_5c6e8; Some W_5c6ec; Some W_5c6f0;
   Some W_5c6f4; Some W_5c6f8; Some W_5c6fc; Some W_5c700; Some W_5c704; Some W_5c708; Some W_5c70c; Some W_5c710;
   Some W_5c714; Some W_5c718; Some W_5c71c; Some W_5c720; Some W_5c724; Some W_5c728; Some W_5c72c; Some W_5c730;
   Some W_5c734; Some W_5c738; Some W_5c73c; Some W_5c740; Some W_5c744; Some W_5c748; Some W_5c74c; None;
   None; Some W_5c758; Some W_5c75c; Some W_5c760; Some W_5c764; Some W_5c768; Some W_5c76c; Some W_5c770;
   Some W_5c774; Some W_5c778; Some W_5c77c; Some W_5c780; Some W_5c784; Some W_5c788; Some W_5c78c; Some W_5c790;
   Some W_5c794; Some W_5c798; Some W_5c79c; Some W_5c7a0; Some W_5c7a4; Some W_5c7a8; Some W_5c7ac; Some W_5c7b0;
   Some W_5c7b4; Some W_5c7b8; Some W_5c7bc; Some W_5c7c0; Some W_5c7c4; Some W_5c7c8; Some W_5c7cc; None;
   None; Some W_5c7d8; Some W_5c7dc; Some W_5c7e0; Some W_5c7e4; Some W_5c7e8; Some W_5c7ec; Some W_5c7f0;
   Some W_5c7f4; Some W_5c7f8; Some W_5c7fc; Some W_5c800; Some W_5c804
  ]%list.


(* [comment removed for export] *)
Record xstrlen_tab : Type := XSLT {
  xs_base : word;          (* [comment removed for export] *)
  xs_rip : rip_tab;        (* [comment removed for export] *)
  xs_sl : strlen_tab;      (* [comment removed for export] *)
  xs_c_rsl : Z;            (* [comment removed for export] *)
  xs_g_cf : Z; xs_p_cf : Z;        (* [comment removed for export] *)
  xs_c_inited : Z }.       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition asan_inited_call (segs : list Segment) (entry : word) (c_inited : Z) : Prop :=
  forall regs mem rom (ra : word),
    rdn segs mem (Z_to_bv 64 c_inited) 1 = Some [Z_to_bv 8 1] -> ret_ok ra -> getr regs 1 = ra ->
    msteps segs (mkst regs entry mem rom) (mkst (regupd regs 10 (Z_to_bv 64 1)) ra mem rom).
Definition tai_mem (mem : word -> option byte) (sp ra s0 : word) : word -> option byte :=
  wbytes (wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ra)) (at_ sp (-16)) (word_to_le_bytes 8 s0).
Definition try_asan_init_call (segs : list Segment) (entry : word) (c_inited : Z) : Prop :=
  forall regs mem rom (ra : word),
    rdn segs mem (Z_to_bv 64 c_inited) 1 = Some [Z_to_bv 8 1] -> ret_ok ra -> getr regs 1 = ra ->
    (0 <= c_inited)%Z -> (c_inited + 1 <= U (getr regs 2) - 16 \/ U (getr regs 2) <= c_inited)%Z ->
    (16 <= U (getr regs 2))%Z -> (U (getr regs 2) < 2 ^ 64)%Z ->
    store_ok segs mem (at_ (getr regs 2) (-16)) 16 = true ->
    exists r', msteps segs (mkst regs entry mem rom) (mkst r' ra (tai_mem mem (getr regs 2) ra (getr regs 8)) rom)
      /\ getr r' 10 = Z_to_bv 64 1 /\ (forall x : reg, x <> 10 -> x <> 11 -> getr r' x = getr regs x).

Record xstrlen_tab_ok (segs : list Segment) (t : xstrlen_tab) : Prop := XSLTOK {
  xso_code : code_ato segs (xs_base t) 0 xstrlen_words;
  xso_rip : rip_tab_ok segs (xs_rip t);
  xso_rip_base : rt_base (xs_rip t) = at_ (xs_base t) 80412;
  xso_sl : strlen_tab_ok segs (xs_sl t);
  xso_sl_ok : ret_ok (st_base (xs_sl t));
  xso_ai : asan_inited_call segs (at_ (xs_base t) 100144) (xs_c_inited t);
  xso_tai : try_asan_init_call segs (at_ (xs_base t) 104000) (xs_c_inited t);
  xso_g60 : gload segs (xs_base t) 60 11 (xs_c_rsl t);
  xso_g84 : gload2 segs (xs_base t) 84 11 19 (xs_g_cf t);
  xso_g128 : gload segs (at_ (xs_base t) 128) 0 11 (mt_g_shoff (rt_m2s (xs_rip t)));
  xso_b180 : gbnez segs (at_ (xs_base t) 180) 14 (at_ (xs_base t) 400);
  xso_b452 : gbeqz segs (at_ (xs_base t) 452) 10 (at_ (xs_base t) 652);
  xso_base : (U (xs_base t) mod 2 = 0)%Z /\ (U (xs_base t) + 500000 < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Definition xsl_frame (mem : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 s6 : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ sp (-8)) (word_to_le_bytes 8 ra))
    (at_ sp (-16)) (word_to_le_bytes 8 s0))
    (at_ sp (-24)) (word_to_le_bytes 8 s1))
    (at_ sp (-32)) (word_to_le_bytes 8 s2))
    (at_ sp (-40)) (word_to_le_bytes 8 s3))
    (at_ sp (-48)) (word_to_le_bytes 8 s4))
    (at_ sp (-56)) (word_to_le_bytes 8 s5))
    (at_ sp (-64)) (word_to_le_bytes 8 s6).

Section XSTRLEN.
  Variable segs : list Segment.
  Variable base : word.
  Variable rt : rip_tab.
  Variable slt : strlen_tab.
  Variables c_rsl g_cf p_cf c_inited : Z.
  #[local] Abbreviation g_shoff := (mt_g_shoff (rt_m2s rt)).
  #[local] Abbreviation p_shoff := (mt_p_shoff (rt_m2s rt)).
  Hypothesis HCODE : code_ato segs base 0 xstrlen_words.
  Hypothesis RTOK : rip_tab_ok segs rt.
  Hypothesis RTB : rt_base rt = at_ base 80412.
  Hypothesis SLOK : strlen_tab_ok segs slt.
  Hypothesis SLRET : ret_ok (st_base slt).
  Hypothesis HAI : asan_inited_call segs (at_ base 100144) c_inited.
  Hypothesis HTAI : try_asan_init_call segs (at_ base 104000) c_inited.
  Hypothesis G60 : gload segs base 60 11 c_rsl.
  Hypothesis G84 : gload2 segs base 84 11 19 g_cf.
  Hypothesis G128 : gload segs (at_ base 128) 0 11 g_shoff.
  Hypothesis B180 : gbnez segs (at_ base 180) 14 (at_ base 400).
  Hypothesis B452 : gbeqz segs (at_ base 452) 10 (at_ base 652).
  Hypothesis Hbase : (U base mod 2 = 0)%Z /\ (U base + 500000 < 2 ^ 64)%Z.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_5c574.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_5c578.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_5c57c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_5c580.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_5c584.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_5c588.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_5c58c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_5c590.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_5c594.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_5c598.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_5c59c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 10 _ HCODE eq_refl). Qed.
  Lemma Fo44 : fetch_word segs (at_ base 44) = Some W_5c5a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 11 _ HCODE eq_refl). Qed.
  Lemma Fo48 : fetch_word segs (at_ base 48) = Some W_5c5a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 12 _ HCODE eq_refl). Qed.
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_5c5a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_5c5ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 14 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo68 : fetch_word segs (at_ base 68) = Some W_5c5b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 17 _ HCODE eq_refl). Qed.
  Lemma Fo72 : fetch_word segs (at_ base 72) = Some W_5c5bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 18 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_5c5c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_5c5c4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 20 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo92 : fetch_word segs (at_ base 92) = Some W_5c5d0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 23 _ HCODE eq_refl). Qed.
  Lemma Fo96 : fetch_word segs (at_ base 96) = Some W_5c5d4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 24 _ HCODE eq_refl). Qed.
  Lemma Fo100 : fetch_word segs (at_ base 100) = Some W_5c5d8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 25 _ HCODE eq_refl). Qed.
  Lemma Fo104 : fetch_word segs (at_ base 104) = Some W_5c5dc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 26 _ HCODE eq_refl). Qed.
  Lemma Fo108 : fetch_word segs (at_ base 108) = Some W_5c5e0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 27 _ HCODE eq_refl). Qed.
  Lemma Fo112 : fetch_word segs (at_ base 112) = Some W_5c5e4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 28 _ HCODE eq_refl). Qed.
  Lemma Fo116 : fetch_word segs (at_ base 116) = Some W_5c5e8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 29 _ HCODE eq_refl). Qed.
  Lemma Fo120 : fetch_word segs (at_ base 120) = Some W_5c5ec.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 30 _ HCODE eq_refl). Qed.
  Lemma Fo124 : fetch_word segs (at_ base 124) = Some W_5c5f0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 31 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo136 : fetch_word segs (at_ base 136) = Some W_5c5fc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 34 _ HCODE eq_refl). Qed.
  Lemma Fo140 : fetch_word segs (at_ base 140) = Some W_5c600.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 35 _ HCODE eq_refl). Qed.
  Lemma Fo144 : fetch_word segs (at_ base 144) = Some W_5c604.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 36 _ HCODE eq_refl). Qed.
  Lemma Fo148 : fetch_word segs (at_ base 148) = Some W_5c608.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 37 _ HCODE eq_refl). Qed.
  Lemma Fo152 : fetch_word segs (at_ base 152) = Some W_5c60c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 38 _ HCODE eq_refl). Qed.
  Lemma Fo156 : fetch_word segs (at_ base 156) = Some W_5c610.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 39 _ HCODE eq_refl). Qed.
  Lemma Fo160 : fetch_word segs (at_ base 160) = Some W_5c614.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 40 _ HCODE eq_refl). Qed.
  Lemma Fo164 : fetch_word segs (at_ base 164) = Some W_5c618.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 41 _ HCODE eq_refl). Qed.
  Lemma Fo168 : fetch_word segs (at_ base 168) = Some W_5c61c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 42 _ HCODE eq_refl). Qed.
  Lemma Fo172 : fetch_word segs (at_ base 172) = Some W_5c620.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 43 _ HCODE eq_refl). Qed.
  Lemma Fo176 : fetch_word segs (at_ base 176) = Some W_5c624.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 44 _ HCODE eq_refl). Qed.
  Lemma Fo180 : fetch_word segs (at_ base 180) = Some W_5c628.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 45 _ HCODE eq_refl). Qed.
  Lemma Fo184 : fetch_word segs (at_ base 184) = Some W_5c62c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 46 _ HCODE eq_refl). Qed.
  Lemma Fo188 : fetch_word segs (at_ base 188) = Some W_5c630.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 47 _ HCODE eq_refl). Qed.
  Lemma Fo192 : fetch_word segs (at_ base 192) = Some W_5c634.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 48 _ HCODE eq_refl). Qed.
  Lemma Fo196 : fetch_word segs (at_ base 196) = Some W_5c638.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 49 _ HCODE eq_refl). Qed.
  Lemma Fo200 : fetch_word segs (at_ base 200) = Some W_5c63c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 50 _ HCODE eq_refl). Qed.
  Lemma Fo204 : fetch_word segs (at_ base 204) = Some W_5c640.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 51 _ HCODE eq_refl). Qed.
  Lemma Fo208 : fetch_word segs (at_ base 208) = Some W_5c644.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 52 _ HCODE eq_refl). Qed.
  Lemma Fo212 : fetch_word segs (at_ base 212) = Some W_5c648.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 53 _ HCODE eq_refl). Qed.
  Lemma Fo216 : fetch_word segs (at_ base 216) = Some W_5c64c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 54 _ HCODE eq_refl). Qed.
  Lemma Fo220 : fetch_word segs (at_ base 220) = Some W_5c650.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 55 _ HCODE eq_refl). Qed.
  Lemma Fo224 : fetch_word segs (at_ base 224) = Some W_5c654.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 56 _ HCODE eq_refl). Qed.


















  Lemma Fo300 : fetch_word segs (at_ base 300) = Some W_5c6a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 75 _ HCODE eq_refl). Qed.
  Lemma Fo304 : fetch_word segs (at_ base 304) = Some W_5c6a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 76 _ HCODE eq_refl). Qed.
  Lemma Fo308 : fetch_word segs (at_ base 308) = Some W_5c6a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 77 _ HCODE eq_refl). Qed.









  Lemma Fo348 : fetch_word segs (at_ base 348) = Some W_5c6d0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 87 _ HCODE eq_refl). Qed.

  Lemma Fo356 : fetch_word segs (at_ base 356) = Some W_5c6d8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 89 _ HCODE eq_refl). Qed.

  Lemma Fo364 : fetch_word segs (at_ base 364) = Some W_5c6e0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 91 _ HCODE eq_refl). Qed.



  Lemma Fo380 : fetch_word segs (at_ base 380) = Some W_5c6f0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 95 _ HCODE eq_refl). Qed.
  Lemma Fo384 : fetch_word segs (at_ base 384) = Some W_5c6f4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 96 _ HCODE eq_refl). Qed.
  Lemma Fo388 : fetch_word segs (at_ base 388) = Some W_5c6f8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 97 _ HCODE eq_refl). Qed.

  Lemma Fo396 : fetch_word segs (at_ base 396) = Some W_5c700.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 99 _ HCODE eq_refl). Qed.
  Lemma Fo400 : fetch_word segs (at_ base 400) = Some W_5c704.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 100 _ HCODE eq_refl). Qed.
  Lemma Fo404 : fetch_word segs (at_ base 404) = Some W_5c708.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 101 _ HCODE eq_refl). Qed.
  Lemma Fo408 : fetch_word segs (at_ base 408) = Some W_5c70c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 102 _ HCODE eq_refl). Qed.
  Lemma Fo412 : fetch_word segs (at_ base 412) = Some W_5c710.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 103 _ HCODE eq_refl). Qed.
  Lemma Fo416 : fetch_word segs (at_ base 416) = Some W_5c714.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 104 _ HCODE eq_refl). Qed.
  Lemma Fo420 : fetch_word segs (at_ base 420) = Some W_5c718.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 105 _ HCODE eq_refl). Qed.
  Lemma Fo424 : fetch_word segs (at_ base 424) = Some W_5c71c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 106 _ HCODE eq_refl). Qed.
  Lemma Fo428 : fetch_word segs (at_ base 428) = Some W_5c720.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 107 _ HCODE eq_refl). Qed.
  Lemma Fo432 : fetch_word segs (at_ base 432) = Some W_5c724.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 108 _ HCODE eq_refl). Qed.
  Lemma Fo436 : fetch_word segs (at_ base 436) = Some W_5c728.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 109 _ HCODE eq_refl). Qed.
  Lemma Fo440 : fetch_word segs (at_ base 440) = Some W_5c72c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 110 _ HCODE eq_refl). Qed.
  Lemma Fo444 : fetch_word segs (at_ base 444) = Some W_5c730.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 111 _ HCODE eq_refl). Qed.
  Lemma Fo448 : fetch_word segs (at_ base 448) = Some W_5c734.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 112 _ HCODE eq_refl). Qed.
  Lemma Fo452 : fetch_word segs (at_ base 452) = Some W_5c738.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 113 _ HCODE eq_refl). Qed.
  Lemma Fo456 : fetch_word segs (at_ base 456) = Some W_5c73c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 114 _ HCODE eq_refl). Qed.
  Lemma Fo460 : fetch_word segs (at_ base 460) = Some W_5c740.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 115 _ HCODE eq_refl). Qed.
  Lemma Fo464 : fetch_word segs (at_ base 464) = Some W_5c744.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 116 _ HCODE eq_refl). Qed.
  Lemma Fo468 : fetch_word segs (at_ base 468) = Some W_5c748.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 117 _ HCODE eq_refl). Qed.

  (* [comment removed for export] *)
  Lemma Fo484 : fetch_word segs (at_ base 484) = Some W_5c758.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 121 _ HCODE eq_refl). Qed.
  Lemma Fo488 : fetch_word segs (at_ base 488) = Some W_5c75c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 122 _ HCODE eq_refl). Qed.
  Lemma Fo492 : fetch_word segs (at_ base 492) = Some W_5c760.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 123 _ HCODE eq_refl). Qed.
  Lemma Fo496 : fetch_word segs (at_ base 496) = Some W_5c764.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 124 _ HCODE eq_refl). Qed.
  Lemma Fo500 : fetch_word segs (at_ base 500) = Some W_5c768.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 125 _ HCODE eq_refl). Qed.
  Lemma Fo504 : fetch_word segs (at_ base 504) = Some W_5c76c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 126 _ HCODE eq_refl). Qed.


































  Lemma Fo652 : fetch_word segs (at_ base 652) = Some W_5c800.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 163 _ HCODE eq_refl). Qed.
  Lemma Fo656 : fetch_word segs (at_ base 656) = Some W_5c804.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 xstrlen_words 164 _ HCODE eq_refl). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition qc3_clob : list reg := [10; 11; 12; 13; 14; 15; 21]%list.
  Definition qc3l_clob : list reg := [10; 11; 13]%list.

  (* [comment removed for export] *)
  Lemma qc3_loop : forall (k : nat) regs mem rom (cur e : Z),
    (e - cur = Z.of_nat k)%Z -> (0 < Z.of_nat k)%Z -> (0 <= cur)%Z -> (e < 2 ^ 64)%Z ->
    getr regs 11 = Z_to_bv 64 cur -> getr regs 12 = Z_to_bv 64 e -> getr regs 10 = Z_to_bv 64 0 ->
    (forall a : word, (cur <= U a < e)%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    exists r,
      msteps segs (mkst regs (at_ base 432) mem rom) (mkst r (at_ base 448) mem rom)
      /\ getr r 11 = Z_to_bv 64 e /\ getr r 12 = Z_to_bv 64 e /\ getr r 10 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r qc3l_clob) regs r.
  Proof using HCODE.
    induction k as [|k IH]; intros regs mem rom cur e Hk Hpos Hc He R11 R12 R10 Hz; [cbn in Hpos; lia|].
    pose proof (u64_range base) as Hbr.
    assert (Rd : rdn segs mem (v_addi (getr regs 11) 0) 1 = Some [Z_to_bv 8 0]).
    { rewrite R11, v_addi_0. apply Hz. unorm. lia. }
    destruct (Z.eq_dec (Z.of_nat k) 0) as [K0 | Kpos].
    - wd_eexists. split.
      + chain_step; [reflexivity | eapply step_lbu; [exact Fo432 | reflexivity | exact D_5c724 | exact Rd] | step_simpl]; vn.
        av Fo436 D_5c728 (Z_to_bv 64 e) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).          (* [comment removed for export] *)
        an Fo440 D_5c72c.                                                                      (* [comment removed for export] *)
        ab_ft Fo444 D_5c730 ltac:(condz).                                                     (* [comment removed for export] *)
        wd_refl.
      + post. (lazymatch goal with |- ?G => let G' := eval unfold qc3l_clob in G in change_no_check G' end). ra_solve.
    - set (r1 := regupd (regupd (regupd regs 13 (Z_to_bv 64 0)) 11 (Z_to_bv 64 (cur + 1))) 10 (Z_to_bv 64 0)).
      destruct (IH r1 mem rom (cur + 1)%Z e ltac:(lia) ltac:(lia) ltac:(lia) He) as (r2 & RUN & A11 & A12 & A10 & AG);
        [subst r1; gres; reflexivity | subst r1; gres; exact R12 | subst r1; gres; reflexivity | intros a Ha; apply Hz; lia | ].
      exists r2. split.
      + chain_step; [reflexivity | eapply step_lbu; [exact Fo432 | reflexivity | exact D_5c724 | exact Rd] | step_simpl]; vn.
        av Fo436 D_5c728 (Z_to_bv 64 (cur + 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).  (* [comment removed for export] *)
        an Fo440 D_5c72c.                                                                      (* [comment removed for export] *)
        ab_tk Fo444 D_5c730 ltac:(condz).                                                     (* [comment removed for export] *)
        replace (at_ base (444 + -12)) with (at_ base 432) by (f_equal; lia).
        exact RUN.
      + split; [exact A11 | split; [exact A12 | split; [exact A10 |]]].
        intros x Hx. rewrite (AG x Hx). subst r1.
        assert (x <> 13 /\ x <> 11 /\ x <> 10) as (X1 & X2 & X3).
        { unfold qc3l_clob in Hx. repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto. }
        rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma qc3_slow : forall regs mem rom (b : word) (n : Z) (s1 : byte) (a0v : word),
    (1 <= n)%Z -> (U b + n <= 2 ^ 47)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U b + n - 1))) 1 = Some [s1] ->
    (U s1 = 0 \/ ((U b + n - 1) mod 8 < U s1 /\ U s1 < 128))%Z ->
    (forall a : word, (Sh (U b) <= U a < Sh (U b + n - 1))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr regs 11 = Z_to_bv 64 (Sh (U b)) -> getr regs 12 = Z_to_bv 64 (Sh (U b + n - 1)) ->
    getr regs 13 = Z_to_bv 64 (U b + n - 1) -> getr regs 10 = a0v ->
    exists r,
      msteps segs (mkst regs (at_ base 400) mem rom) (mkst r (at_ base 184) mem rom)
      /\ getr r 10 = a0v /\ regs_agree (fun r => In r qc3_clob) regs r.
  Proof using B452 HCODE.
    intros regs mem rom b n s1 a0v Hn Hend Rs1 Hs1 Hz R11 R12 R13 R10.
    pose proof (u64_range base) as Hbr. pose proof (u64_range b) as Hbr2. pose proof (u8_range s1) as Hs1r.
    set (last := (U b + n - 1)%Z) in *.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). split; [|]. 1: pose proof (Z.div_pos a 8). all: try lia.
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U b) ltac:(lia)) as S0. pose proof (HSh last ltac:(lia)) as S1.
    assert (SLE : (Sh (U b) <= Sh last)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end); apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
    pose proof (Z.mod_pos_bound last 8 ltac:(lia)) as M8.
    assert (A5 : v_and (Z_to_bv 64 (if (0 <? U s1)%Z then 1 else 0))
                       (v_xori (Z_to_bv 64 (if (last mod 8 <? U s1)%Z then 1 else 0)) 1) = Z_to_bv 64 0).
    { destruct Hs1 as [Z0 | [L1 L2]].
      - rewrite Z0. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). apply bv_eq. vm_compute. reflexivity.
      - replace (0 <? U s1)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (last mod 8 <? U s1)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        apply bv_eq. vm_compute. reflexivity. }
    destruct (Z.eq_dec (Sh (U b)) (Sh last)) as [EQ | NE].
    - (* [comment removed for export] *)
      wd_eexists. split.
      + an Fo400 D_5c704.                                                                  (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lb; [exact Fo404 | reflexivity | exact D_5c708 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rs1] | step_simpl]; vn.
        rewrite (v_lb_small s1) by lia.                                                         (* [comment removed for export] *)
        av Fo408 D_5c70c (Z_to_bv 64 (last mod 8)) ltac:(rewrite v_andi_7; unorm; reflexivity).  (* [comment removed for export] *)
        an Fo412 D_5c710. rewrite v_sltu_0_l by lia.                                       (* [comment removed for export] *)
        an Fo416 D_5c714. rewrite v_slt_smallZ by lia.                                     (* [comment removed for export] *)
        an Fo420 D_5c718.                                                                  (* [comment removed for export] *)
        an Fo424 D_5c71c. rewrite A5.                                                      (* [comment removed for export] *)
        ab_tk Fo428 D_5c720 ltac:(condz).                                                 (* [comment removed for export] *)
        replace (at_ base (428 + 20)) with (at_ base 448) by (f_equal; lia).
        an Fo448 D_5c734.                                                                  (* [comment removed for export] *)
        eapply mst_step; [reflexivity | apply (proj1 (B452 _ _ _)); gres; reflexivity |].   (* [comment removed for export] *)
        an Fo652 D_5c800.                                                                  (* [comment removed for export] *)
        an Fo656 D_5c804.                                                                  (* [comment removed for export] *)
        wd_refl.
      + split; [gres; rwH; reflexivity|]. (lazymatch goal with |- ?G => let G' := eval unfold qc3_clob in G in change_no_check G' end). ra_solve.
    - (* [comment removed for export] *)
      set (r1 := regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 21 a0v)
                   10 (Z_to_bv 64 (U s1))) 13 (Z_to_bv 64 (last mod 8))) 14 (Z_to_bv 64 (if (0 <? U s1)%Z then 1 else 0)))
                   10 (Z_to_bv 64 (if (last mod 8 <? U s1)%Z then 1 else 0)))
                   10 (v_xori (Z_to_bv 64 (if (last mod 8 <? U s1)%Z then 1 else 0)) 1)) 10 (Z_to_bv 64 0)).
      destruct (qc3_loop (Z.to_nat (Sh last - Sh (U b))) r1 mem rom (Sh (U b)) (Sh last)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & A11 & A12 & A10 & AG);
        [subst r1; gres; exact R11 | subst r1; gres; exact R12 | subst r1; gres; reflexivity | exact Hz |].
      assert (A21 : getr r2 21 = a0v) by (rewrite (AG 21) by notin; subst r1; gres; reflexivity).
      wd_eexists. split.
      + an Fo400 D_5c704.                                                                  (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lb; [exact Fo404 | reflexivity | exact D_5c708 | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Rs1] | step_simpl]; vn.
        rewrite (v_lb_small s1) by lia.
        av Fo408 D_5c70c (Z_to_bv 64 (last mod 8)) ltac:(rewrite v_andi_7; unorm; reflexivity).
        an Fo412 D_5c710. rewrite v_sltu_0_l by lia.
        an Fo416 D_5c714. rewrite v_slt_smallZ by lia.
        an Fo420 D_5c718.
        an Fo424 D_5c71c. rewrite A5.
        ab_ft Fo428 D_5c720 ltac:(condz).                                                 (* [comment removed for export] *)
        change (regupd _ 10 (Z_to_bv 64 0)) with r1.
        eapply msteps_trans; [exact RUN|].
        an Fo448 D_5c734.                                                                  (* [comment removed for export] *)
        eapply mst_step; [reflexivity | apply (proj1 (B452 _ _ _)); gres; reflexivity |].   (* [comment removed for export] *)
        an Fo652 D_5c800.                                                                  (* [comment removed for export] *)
        an Fo656 D_5c804.                                                                  (* [comment removed for export] *)
        wd_refl.
      + split; [gres; rwH; first [reflexivity | exact A21]|].
        intros x Hx. gres.
        assert (X10 : x <> 10) by (clear - Hx; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto). rewrite !getr_other by assumption.
        rewrite (AG x) by (clear - Hx; intros Hc; apply Hx; unfold qc3l_clob, qc3_clob in *; cbn in Hc |- *; tauto). subst r1.
        assert (x <> 21 /\ x <> 13 /\ x <> 14) as (X1 & X2 & X3).
        { unfold qc3_clob in Hx. repeat split; intros ->; apply Hx; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto. }
        rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma qc3_fast : forall regs mem rom (b : word) (n : Z) w0 w1 s1,
    qc1H segs mem b n g_shoff p_shoff w0 w1 s1 ->
    getr regs 18 = b -> getr regs 10 = Z_to_bv 64 (n - 1) ->
    exists r,
      msteps segs (mkst regs (at_ base 128) mem rom) (mkst r (at_ base 180) mem rom)
      /\ getr r 11 = Z_to_bv 64 (Sh (U b)) /\ getr r 12 = Z_to_bv 64 (Sh (U b + n - 1))
      /\ getr r 13 = Z_to_bv 64 (U b + n - 1) /\ getr r 14 = v_or (Z_to_bv 64 (bytes_le_to_Z w1)) (Z_to_bv 64 (bytes_le_to_Z w0))
      /\ getr r 10 = Z_to_bv 64 (n - 1)
      /\ regs_agree (fun r => In r qc3_clob) regs r.
  Proof using G128 HCODE.
    intros regs mem rom b n w0 w1 s1 QH Rb R10.
    destruct QH as [Hn Hend Rg Rp [Hg Hp] Rw0 Rw1 Rs1 Hs1 Hz].
    pose proof (u64_range base) as Hbr. pose proof (u64_range b) as Hbr2.
    set (last := (U b + n - 1)%Z) in *.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos a 8).
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U b) ltac:(lia)) as S0. pose proof (HSh last ltac:(lia)) as S1.
    assert (Dv0 : (0 <= U b / 8 < 2 ^ 44)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Dv1 : (0 <= last / 8 < 2 ^ 44)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    wd_eexists. split.
    - (* [comment removed for export] *)
      eapply msteps_trans; [rewrite <- (at_0 (at_ base 128)); eapply (G128 regs mem rom (Z_to_bv 64 p_shoff)); exact Rg |]. rewrite at_at. zlit_at.
      (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000)) (v := Z_to_bv 64 0x7fff8000);
          [exact Fo136 | reflexivity | exact D_5c5fc | gres; rewrite v_addi_0; exact Rp | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
      av Fo140 D_5c600 (Z_to_bv 64 last) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).          (* [comment removed for export] *)
      av Fo144 D_5c604 (Z_to_bv 64 (U b / 8)) ltac:(rewrite v_srli_3; reflexivity).                 (* [comment removed for export] *)
      av Fo148 D_5c608 (Z_to_bv 64 (last / 8)) ltac:(rewrite v_srli_3; unorm; reflexivity).             (* [comment removed for export] *)
      av Fo152 D_5c60c (Z_to_bv 64 (Sh (U b))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, Sh in G in change_no_check G' end); unorm; f_equal; lia).            (* [comment removed for export] *)
      av Fo156 D_5c610 (Z_to_bv 64 (Sh last)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, Sh in G in change_no_check G' end); unorm; f_equal; lia).             (* [comment removed for export] *)
      av Fo160 D_5c614 (Z_to_bv 64 (down8 (Sh (U b)))) ltac:(rewrite v_andi_m8; unorm; reflexivity).    (* [comment removed for export] *)
      av Fo164 D_5c618 (Z_to_bv 64 (down8 (Sh last))) ltac:(rewrite v_andi_m8; unorm; reflexivity).     (* [comment removed for export] *)
      pose proof (rdn_length _ _ _ _ _ Rw0) as L0. pose proof (rdn_length _ _ _ _ _ Rw1) as L1.
      pose proof (bytes_le_to_Z_nonneg w0) as N0. pose proof (bytes_le_to_Z_bound w0) as B0. rewrite L0 in B0.
      pose proof (bytes_le_to_Z_nonneg w1) as N1. pose proof (bytes_le_to_Z_bound w1) as B1. rewrite L1 in B1.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul] in B0, B1.
      chain_step; [reflexivity
        | eapply step_ld with (bs := w0) (v := Z_to_bv 64 (bytes_le_to_Z w0));
          [exact Fo168 | reflexivity | exact D_5c61c | gres; rewrite v_addi_0; exact Rw0 | rewrite u_Z2bv by lia; reflexivity]
        | step_simpl]; vn.                                                                               (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := w1) (v := Z_to_bv 64 (bytes_le_to_Z w1));
          [exact Fo172 | reflexivity | exact D_5c620 | gres; rewrite v_addi_0; exact Rw1 | rewrite u_Z2bv by lia; reflexivity]
        | step_simpl]; vn.                                                                               (* [comment removed for export] *)
      an Fo176 D_5c624.                                                                                  (* [comment removed for export] *)
      wd_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold qc3_clob in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  Lemma qc3_pass : forall regs mem rom (b : word) (n : Z) w0 w1 s1,
    qc1H segs mem b n g_shoff p_shoff w0 w1 s1 ->
    getr regs 18 = b -> getr regs 10 = Z_to_bv 64 (n - 1) ->
    exists r,
      msteps segs (mkst regs (at_ base 128) mem rom) (mkst r (at_ base 184) mem rom)
      /\ getr r 10 = Z_to_bv 64 (n - 1) /\ regs_agree (fun r => In r qc3_clob) regs r.
  Proof using B452 B180 G128 HCODE.
    intros regs mem rom b n w0 w1 s1 QH Rb R10. pose proof (u64_range base) as Hbr.
    destruct (qc3_fast regs mem rom b n w0 w1 s1 QH Rb R10) as (r1 & RUN1 & A11 & A12 & A13 & A14 & A10 & AG1).
    destruct QH as [Hn Hend Rg Rp [Hg Hp] Rw0 Rw1 Rs1 Hs1 Hz].
    destruct (decide (v_or (Z_to_bv 64 (bytes_le_to_Z w1)) (Z_to_bv 64 (bytes_le_to_Z w0)) = Z_to_bv 64 0)) as [Z0 | NZ].
    - exists r1. split; [|split; [exact A10 | exact AG1]].
      eapply msteps_trans; [exact RUN1|].
      eapply mst_step; [reflexivity | apply (proj2 (B180 _ _ _)); rewrite A14; exact Z0 |].
      rewrite at_addi. replace (at_ base (180 + 4)) with (at_ base 184) by (f_equal; lia).
      wd_refl.
    - destruct (qc3_slow r1 mem rom b n s1 (Z_to_bv 64 (n - 1)) Hn Hend Rs1 Hs1 Hz A11 A12 A13 A10) as (r2 & RUN2 & B10 & AG2).
      exists r2. split; [|split; [exact B10|]].
      + eapply msteps_trans; [exact RUN1|].
        eapply mst_step; [reflexivity | apply (proj1 (B180 _ _ _)); rewrite A14; exact NZ |].
        exact RUN2.
      + intros x Hx. rewrite (AG2 x Hx). exact (AG1 x Hx).
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  Variables s ra sp : word.
  Variable K : Z.
  Variable buf : list byte.
  Variable fl : byte.
  Variable regs : bvmap 5 word.
  Hypothesis Hsp : (0x10007fff8000 + 2304 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  (* [comment removed for export] *)
  Definition XS1 : word -> option byte :=
    xsl_frame mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22).
  Definition XS2 : word -> option byte := tai_mem XS1 (at_ sp (-2144)) (at_ base 60) sp.
  Definition XS3 : word -> option byte :=
    rip_mem rt XS2 (at_ sp (-2144)) (at_ base 468) sp (Z_to_bv 64 (K + 1)) s (Z_to_bv 64 p_cf) (at_ sp (-2136)) (Z_to_bv 64 K)
            s (Z_to_bv 64 (K + 1)).

  Lemma XS1_out : forall x : word, (U x < U sp - 64 \/ U sp <= U x)%Z -> XS1 x = mem x.
  Proof using Hsp base.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold XS1, xsl_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; try reflexivity; (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma XS1_grows : mem_grows mem XS1.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold XS1, xsl_frame in G in change_no_check G' end). repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma XS2_agree : forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> XS2 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold XS2, tai_mem in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; [apply XS1_out; lia | | | |];
      (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_at, ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia.
  Qed.
  Lemma XS2_low : forall x : word, (U x < U sp - 2240)%Z -> XS2 x = mem x.
  Proof using Hsp. intros x Hx. apply XS2_agree. lia. Qed.
  Lemma XS2_grows : mem_grows mem XS2.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold XS2, tai_mem in G in change_no_check G' end). eapply mem_grows_trans; [apply XS1_grows|].
    repeat (lazymatch goal with
            | |- mem_grows ?a ?a => apply mem_grows_refl
            | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
            end).
  Qed.
  Lemma XS3_agree : forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> XS3 x = mem x.
  Proof using Hsp.
    intros x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold XS3 in G in change_no_check G' end). rewrite rip_mem_outside; [apply XS2_agree; exact Hx | rewrite at_u; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]].
  Qed.

  Lemma XS3_grows : mem_grows mem XS3.
  Proof using.
    (lazymatch goal with |- ?G => let G' := eval unfold XS3, rip_mem, ps_frame in G in change_no_check G' end). eapply mem_grows_trans; [apply XS2_grows|].
    destruct (Z.ltb _ _);
      repeat (lazymatch goal with
              | |- mem_grows ?a ?a => apply mem_grows_refl
              | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]
              end).
  Qed.
  Lemma rd_o : forall (M : word -> option byte) (B : Z) (a : word) k bs0,
    (forall x : word, (U x < B)%Z -> M x = mem x) ->
    (U a + Z.of_nat k <= B)%Z -> (B <= 2 ^ 64)%Z ->
    rdn segs mem a k = Some bs0 -> rdn segs M a k = Some bs0.
  Proof using base.
    intros M B a k bs0 HM Ha HB Hr. rewrite <- Hr. apply rdn_ext; [lia|]. intros x Hx. apply HM. lia.
  Qed.
  Lemma rd_outZ : forall (M : word -> option byte) (c : Z) k bs0,
    (forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> M x = mem x) ->
    (0 <= c)%Z -> (c + Z.of_nat k <= U sp - 2240)%Z ->
    rdn segs mem (Z_to_bv 64 c) k = Some bs0 -> rdn segs M (Z_to_bv 64 c) k = Some bs0.
  Proof using Hsp base.
    intros M c k bs0 HM Hc Hk Hr. pose proof (u64_range sp). rewrite <- Hr. apply rdn_ext; [wd_ulia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. apply HM. lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis SH : strlH segs mem s buf K.
  Hypothesis Hend : (U s + K + 1 <= 2 ^ 47)%Z.
  Hypothesis Rrsl : rdn segs mem (Z_to_bv 64 c_rsl) 8 = Some (LE8 (st_base slt)).
  Hypothesis RM : rdn segs mem (Z_to_bv 64 (st_cM slt)) 8 = Some (LE8 (Z_to_bv 64 Mc)).
  Hypothesis RH : rdn segs mem (Z_to_bv 64 (st_cH slt)) 8 = Some (LE8 (Z_to_bv 64 Hc)).
  Hypothesis Rgcf : rdn segs mem (Z_to_bv 64 g_cf) 8 = Some (LE8 (Z_to_bv 64 p_cf)).
  Hypothesis Rfl : rdn segs mem (Z_to_bv 64 (p_cf + 251)) 1 = Some [fl].
  Hypothesis Hfl : U fl <> 0%Z.
  Hypothesis Rini : rdn segs mem (Z_to_bv 64 c_inited) 1 = Some [Z_to_bv 8 1].
  Hypothesis Hcells : Forall (fun c => 0 <= c /\ c + 8 <= U sp - 2240)%Z
    (c_rsl :: st_cM slt :: st_cH slt :: g_cf :: p_cf :: (p_cf + 251)%Z :: c_inited :: m2s_cells (rt_m2s rt)).
  Hypothesis Hstk : store_ok segs mem (at_ sp (-2240)) 2240 = true.
  Hypothesis Hs_stk : (U s + Z.of_nat (length buf) <= U sp - 2240 \/ U sp <= U s)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis R1 : getr regs 1 = ra.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R10 : getr regs 10 = s.

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
          eapply (store_ok_sub segs mem (at_ sp (-2240)) _ 2240);
          [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.
  Ltac gl G LOW Hr :=
    eapply msteps_trans; [ eapply G; apply (rd_o _ _ _ _ _ LOW); [(lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_ulia | lia | exact Hr] | ]; zlit_at.

  #[local] Abbreviation CLX := (fun r : reg => In r [2; 8; 9; 18; 19; 20; 21; 22; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list).

  (* [comment removed for export] *)
  Lemma strlH_on : forall M : word -> option byte,
    (forall x : word, (U x < U sp - 2240 \/ U sp <= U x)%Z -> M x = mem x) -> strlH segs M s buf K.
  Proof using Hs_stk SH Hsp base.
    intros M HM. destruct SH as [B1 B2 B3 B4 B5 B6]. split; try assumption.
    rewrite <- B1. apply rdn_ext; [lia|]. intros x Hx. apply HM. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma xblkA :
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r (at_ base 76) XS2 rom)
      /\ getr r 2 = at_ sp (-2144) /\ getr r 8 = sp /\ getr r 9 = Z_to_bv 64 1 /\ getr r 10 = s
      /\ getr r 11 = st_base slt /\ getr r 18 = s
      /\ (forall i : reg, In i [19; 20; 21; 22; 23; 24; 25; 26; 27; 3; 4]%list -> getr r i = getr regs i).
  Proof using R10 R2 R1 Hstk Hcells Rini Rrsl Hsp buf Hbase G60 HTAI HAI HCODE c_inited p_cf g_cf c_rsl rt.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range s) as Hsr. pose proof (u64_range base) as Hbr. cells_split.
    (* [comment removed for export] *)
    set (rc := regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 2 (at_ sp (-2032))) 8 sp) 2 (at_ sp (-2144))) 18 s) 1 (at_ base 52)) 10 (Z_to_bv 64 1)) 1 (at_ base 60)).
    destruct (HTAI rc XS1 rom (at_ base 60)) as (rT & RUNT & T10 & TAG).
    { apply (rd_o _ _ _ _ _ (fun x Hx => XS1_out x (or_introl Hx))); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | lia | exact Rini]. }
    { apply ret_ok_at; [lia | reflexivity | lia]. }
    { subst rc; gres; reflexivity. }
    { lia. }
    { subst rc; gres. rewrite at_u by lia. lia. }
    { subst rc; gres. rewrite at_u by lia. lia. }
    { subst rc; gres. rewrite at_u; lia. }
    { subst rc; gres. rewrite at_at. eapply store_ok_mono; [apply XS1_grows|].
      eapply (store_ok_sub segs mem (at_ sp (-2240)) _ 2240); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (T2 : getr rT 2 = at_ sp (-2144)) by (rewrite TAG by (intros X; discriminate X); subst rc; gres; reflexivity).
    assert (T8 : getr rT 8 = sp) by (rewrite TAG by (intros X; discriminate X); subst rc; gres; reflexivity).
    assert (T18 : getr rT 18 = s) by (rewrite TAG by (intros X; discriminate X); subst rc; gres; reflexivity).
    wd_eexists. split.
    - an Fo0 D_5c574.                                    (* [comment removed for export] *)
      fsd Fo4 D_5c578 (at_ sp (-8)).                     (* [comment removed for export] *)
      fsd Fo8 D_5c57c (at_ sp (-16)).                    (* [comment removed for export] *)
      fsd Fo12 D_5c580 (at_ sp (-24)).
      fsd Fo16 D_5c584 (at_ sp (-32)).
      fsd Fo20 D_5c588 (at_ sp (-40)).
      fsd Fo24 D_5c58c (at_ sp (-48)).
      fsd Fo28 D_5c590 (at_ sp (-56)).
      fsd Fo32 D_5c594 (at_ sp (-64)).
      change (wbytes _ _ _) with XS1.
      an Fo36 D_5c598.                                   (* [comment removed for export] *)
      an Fo40 D_5c59c.                                   (* [comment removed for export] *)
      an Fo44 D_5c5a0.                                   (* [comment removed for export] *)
      an Fo48 D_5c5a4.                                   (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply HAI. 3: (gres; reflexivity).
        - apply (rd_o _ _ _ _ _ (fun x Hx => XS1_out x (or_introl Hx))); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_ulia | lia | exact Rini].
        - apply ret_ok_at; [lia | reflexivity | lia]. }
      ab_ft Fo52 D_5c5a8 ltac:(condz).                 (* [comment removed for export] *)
      an Fo56 D_5c5ac.                                   (* [comment removed for export] *)
      lazymatch goal with |- msteps _ (mkst ?r _ _ _) _ => change r with rc end.
      eapply msteps_trans; [exact RUNT|].
      replace (tai_mem XS1 (getr rc 2) (at_ base 60) (getr rc 8)) with XS2 by (subst rc; gres; reflexivity).
      gl G60 XS2_low Rrsl.                               (* [comment removed for export] *)
      an Fo68 D_5c5b8.                                   (* [comment removed for export] *)
      an Fo72 D_5c5bc.                                   (* [comment removed for export] *)
      wd_refl.
    - post; try reflexivity.
      intros i Hi. cbn [In] in Hi.
      repeat (destruct Hi as [<-|Hi]; [gres; rewrite TAG by (intros X; discriminate X); subst rc; gres; reflexivity|]). destruct Hi.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma KL' : (0 <= K)%Z /\ (K + 1 <= Z.of_nat (length buf))%Z.
  Proof using SH Hsp sp s mem base segs.
    destruct SH as [B1 B2 B3 B4 B5 B6]. pose proof (u64_range s).
    pose proof (Z.div_mod (U s + K) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U s + K) 8 ltac:(lia)). lia.
  Qed.

  #[local] Abbreviation KEEP := ([3; 4; 21; 22; 23; 24; 25; 26; 27]%list : list reg).

  Lemma xblkB0 : forall r0,
    getr r0 2 = at_ sp (-2144) -> getr r0 8 = sp -> getr r0 9 = Z_to_bv 64 1 -> getr r0 10 = s ->
    getr r0 11 = st_base slt -> getr r0 18 = s ->
    exists r,
      msteps segs (mkst r0 (at_ base 76) XS2 rom) (mkst r (at_ base 124) XS2 rom)
      /\ getr r 2 = at_ sp (-2144) /\ getr r 8 = sp /\ getr r 9 = Z_to_bv 64 (K + 1) /\ getr r 10 = Z_to_bv 64 K
      /\ getr r 11 = Z_to_bv 64 64 /\ getr r 18 = s /\ getr r 19 = Z_to_bv 64 p_cf /\ getr r 20 = at_ sp (-2136)
      /\ (forall i : reg, In i KEEP -> getr r i = getr r0 i).
  Proof using Hs_stk Hcells Hfl Rfl Rgcf RH RM Hend SH Hsp fl buf Hbase G84 SLRET SLOK HCODE c_inited g_cf c_rsl rt.
    intros r0 R2' R8' R9' R10' R11' R18'.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range s) as Hsr. pose proof (u64_range base) as Hbr. pose proof (u8_range fl) as Hflr.
    pose proof KL' as [HK0 HKL]. cells_split.
    assert (RA : ret_ok (at_ base 80)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    set (r1 := regupd r0 1 (at_ base 80)).
    destruct (strlen_run segs slt SLOK XS2 s buf K rom r1 (at_ base 80) (strlH_on XS2 XS2_agree)
                (rd_outZ XS2 (st_cM slt) 8 _ XS2_agree ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) RM) (rd_outZ XS2 (st_cH slt) 8 _ XS2_agree ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) RH)
                RA ltac:(subst r1; gres; reflexivity) ltac:(subst r1; gres; exact R10'))
      as (r2 & RUN2 & A10 & KC).
    assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (KC 2) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); subst r1; gres; exact R2').
    assert (A8 : getr r2 8 = sp) by (rewrite (KC 8) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); subst r1; gres; exact R8').
    assert (A9 : getr r2 9 = Z_to_bv 64 1) by (rewrite (KC 9) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); subst r1; gres; exact R9').
    assert (A18 : getr r2 18 = s) by (rewrite (KC 18) by (clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto); subst r1; gres; exact R18').
    destruct G84 as (xg & GL2).
    wd_eexists. split.
    - aret Fo76 D_5c5c0 (st_base slt).                (* [comment removed for export] *)
      rewrite at_addi; zlit_at. change (regupd _ 1 _) with r1.
      eapply msteps_trans; [exact RUN2 |].
      ab_ft Fo80 D_5c5c4 ltac:(condz).                 (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply GL2. apply (rd_outZ XS2 _ _ _ XS2_agree); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rgcf]. }
      zlit_at.
      chain_step; [reflexivity
        | eapply step_lbu with (b := fl);
          [exact Fo92 | reflexivity | exact D_5c5d0
          | gres; rwH; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; apply (rd_outZ XS2 _ _ _ XS2_agree); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rfl] ]
        | step_simpl]; vn.                               (* [comment removed for export] *)
      ab_ft Fo96 D_5c5d4 ltac:(condz).                 (* [comment removed for export] *)
      av Fo100 D_5c5d8 (Z_to_bv 64 (K + 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      av Fo104 D_5c5dc (Z_to_bv 64 (2 ^ 64 - 1 - U s)) ltac:(apply v_not_word).          (* [comment removed for export] *)
      an Fo108 D_5c5e0. an Fo112 D_5c5e4.              (* [comment removed for export] *)
      ab_ft Fo116 D_5c5e8 ltac:(condz).                (* [comment removed for export] *)
      an Fo120 D_5c5ec.                                  (* [comment removed for export] *)
      wd_refl.
    - post; try reflexivity; try ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia).
      intros i Hi. cbn [In] in Hi.
      assert (X : i <> 11 /\ i <> 20 /\ i <> 9 /\ i <> 19 /\ i <> 1) by (clear - Hi; repeat split; intros ->; cbn in Hi; intuition discriminate).
      destruct X as (X11 & X20 & X9 & X19 & X1).
      gres. rewrite !getr_other by assumption.
      rewrite (KC i) by (clear - Hi; (lazymatch goal with |- ?G => let G' := eval unfold callee_saved in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intuition (subst; tauto)).
      subst r1. rewrite getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma qc1H_XS2 : forall w0 w1 s1,
    qc1H segs mem s (K + 1) g_shoff p_shoff w0 w1 s1 -> qc1H segs XS2 s (K + 1) g_shoff p_shoff w0 w1 s1.
  Proof using Hcells Hend Hsp buf c_inited p_cf g_cf c_rsl slt.
    intros w0 w1 s1 [Q1 Q2 Q3 Q4 [Q5 Q6] Q7 Q8 Q9 Q10 Q11].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range s) as Hd. cells_split.
    assert (HSh : forall a, (0 <= a < 2 ^ 47)%Z -> (0x7fff8000 <= Sh a < 0x7fff8000 + 2 ^ 44)%Z).
    { intros a Ha. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos a 8).
      assert (a / 8 < 2 ^ 44)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
    pose proof (HSh (U s) ltac:(lia)) as S0. pose proof (HSh (U s + (K + 1) - 1)%Z ltac:(lia)) as S1.
    assert (D0 : (Sh (U s) - 7 <= down8 (Sh (U s)) <= Sh (U s))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U s)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U s)) 8 ltac:(lia)); lia).
    assert (D1 : (Sh (U s + (K + 1) - 1) - 7 <= down8 (Sh (U s + (K + 1) - 1)) <= Sh (U s + (K + 1) - 1))%Z)
      by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (Sh (U s + (K + 1) - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (Sh (U s + (K + 1) - 1)) 8 ltac:(lia)); lia).
    Ltac ro Hr := apply (rd_o _ _ _ _ _ XS2_low); [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | lia | exact Hr].
    split; try assumption.
    - ro Q3. - ro Q4. - split; assumption. - ro Q7. - ro Q8. - ro Q9.
    - intros a Ha. pose proof (u64_range a). apply (rd_o _ _ _ _ _ XS2_low); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia | exact (Q11 a Ha)].
  Qed.

  Lemma ripH_on : forall (raX : word) (s0 s1 : byte) (midend : word),
    (65 <= K + 1 <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem s midend ->
    ((0x10007fff8000 <= U s /\ U s + (K + 1) + 1 <= 0x800000000000) \/ U s + (K + 1) <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U s))) 1 = Some [s0] -> (U s0 = 0 \/ U s mod 8 < U s0 < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U s + (K + 1) - 1))) 1 = Some [s1] -> (U s1 = 0 \/ (U s + (K + 1) - 1) mod 8 < U s1 < 128)%Z ->
    (forall a : word, (Sh (up8 (U s)) <= U a < Sh (down8 (U s + (K + 1))))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    ret_ok raX ->
    ripH segs rt XS2 s (Z_to_bv 64 (K + 1)) raX (at_ sp (-2144)) s0 s1 midend.
  Proof using Hs_stk Hstk Hcells Hend Hsp buf c_inited p_cf g_cf c_rsl slt.
    intros raX s0 s1 midend Hn65 CH Hhi R0 H0 R1' H1' RZ HR.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range s) as Hb.
    destruct CH as [C1 C2 C3 C4 C5 C6 C7 C8 CC Clo Chi]. cells_split.
    assert (SH' : forall x, (0 <= x < 0x800000000000)%Z -> (0x7fff8000 <= Sh x < 0x10007fff8000)%Z).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Sh in G in change_no_check G' end). pose proof (Z.div_pos x 8). pose proof (Z.div_lt_upper_bound x 8 0x100000000000 ltac:(lia) ltac:(lia)). lia. }
    pose proof (SH' (U s) ltac:(lia)) as S0.
    pose proof (SH' (U s + (K + 1) - 1)%Z ltac:(lia)) as S1.
    assert (UP : (U s <= up8 (U s) <= U s + 7)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold up8 in G in change_no_check G' end); pose proof (Z.div_mod (U s + 7) 8); pose proof (Z.mod_pos_bound (U s + 7) 8); lia).
    assert (DN : (U s + (K + 1) - 7 <= down8 (U s + (K + 1)) <= U s + (K + 1))%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold down8 in G in change_no_check G' end); pose proof (Z.div_mod (U s + (K + 1)) 8); pose proof (Z.mod_pos_bound (U s + (K + 1)) 8); lia).
    pose proof (SH' (up8 (U s)) ltac:(lia)) as S2. pose proof (SH' (down8 (U s + (K + 1))) ltac:(lia)) as S3.
    assert (Un : U (Z_to_bv 64 (K + 1)) = (K + 1)%Z) by (apply u_Z2bv; lia).
    Ltac rdo Hr := apply (rd_outZ XS2 _ _ _ XS2_agree); [lia | (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact Hr].
    split.
    - split; [rdo C1 | rdo C2 | rdo C3 | rdo C4 | rdo C5 | rdo C6 | rdo C7 | rdo C8 | exact CC | lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold m2s_cells in G in change_no_check G' end). repeat constructor; rewrite ?at_u; lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rewrite Un. lia.
    - rdo R0.
    - exact H0.
    - rewrite Un. rdo R1'.
    - rewrite Un. exact H1'.
    - rewrite Un. intros a Ha. pose proof (u64_range a). pose proof (RZ a Ha) as Ra.
      rewrite <- (Z_to_bv_bv_unsigned 64 a) in Ra |- *. rdo Ra.
    - rewrite at_u by lia. lia.
    - rewrite at_at. replace (-2144 + -80)%Z with (-2224)%Z by lia. eapply store_ok_mono; [exact XS2_grows|].
      eapply (store_ok_sub segs mem (at_ sp (-2240)) _ 2240); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    - exact HR.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma xblkR : forall r0 (s0b s1b : byte) (midend : word),
    (64 <= K)%Z -> (K + 1 <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem s midend ->
    ((0x10007fff8000 <= U s /\ U s + (K + 1) + 1 <= 0x800000000000) \/ U s + (K + 1) <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U s))) 1 = Some [s0b] -> (U s0b = 0 \/ U s mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U s + (K + 1) - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U s + (K + 1) - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U s)) <= U a < Sh (down8 (U s + (K + 1))))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 8 = sp -> getr r0 9 = Z_to_bv 64 (K + 1) -> getr r0 10 = Z_to_bv 64 K ->
    getr r0 11 = Z_to_bv 64 64 -> getr r0 18 = s -> getr r0 19 = Z_to_bv 64 p_cf -> getr r0 20 = at_ sp (-2136) ->
    exists r, msteps segs (mkst r0 (at_ base 124) XS2 rom) (mkst r (at_ base 184) XS3 rom)
      /\ getr r 2 = at_ sp (-2144) /\ getr r 10 = Z_to_bv 64 K
      /\ (forall i : reg, In i [3; 4; 22; 23; 24; 25; 26; 27]%list -> getr r i = getr r0 i).
  Proof using Hs_stk Hstk Hcells Hend Hsp buf Hbase RTB RTOK HCODE c_inited g_cf c_rsl slt.
    intros r0 s0b s1b midend HK64 HK43 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz R2' R8' R9' R10' R11' R18' R19' R20'.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr. pose proof (u64_range s) as Hsr.
    assert (RA : ret_ok (at_ base 468)) by (apply ret_ok_at; [lia | reflexivity | lia]).
    set (r1 := regupd (regupd (regupd (regupd r0 21 (Z_to_bv 64 K)) 10 s) 11 (Z_to_bv 64 (K + 1))) 1 (at_ base 468)).
    destruct (region_clear segs rt RTOK XS2 rom s (Z_to_bv 64 (K + 1)) (at_ base 468) (at_ sp (-2144)) s0b s1b midend r1
                (ripH_on (at_ base 468) s0b s1b midend ltac:(lia) CH Hrng Rs0 Hs0 Rs1 Hs1 Rz RA))
      as (r2 & RUN2 & A10 & AG2); [subst r1; gres; reflexivity | subst r1; gres; exact R2' | subst r1; gres; reflexivity | subst r1; gres; reflexivity |].
    assert (A21 : getr r2 21 = Z_to_bv 64 K) by (rewrite (AG2 21) by notin; subst r1; gres; reflexivity).
    wd_eexists. split.
    - ab_tk Fo124 D_5c5f0 ltac:(condz).                (* [comment removed for export] *)
      an Fo384 D_5c6f4.                                  (* [comment removed for export] *)
      ab_tk Fo388 D_5c6f8 ltac:(condz).                (* [comment removed for export] *)
      an Fo456 D_5c73c.                                  (* [comment removed for export] *)
      an Fo460 D_5c740.                                  (* [comment removed for export] *)
      an Fo464 D_5c744.                                  (* [comment removed for export] *)
      change (regupd _ 1 _) with r1. rewrite <- RTB.
      eapply msteps_trans; [exact RUN2|].
      replace (rip_mem rt XS2 (at_ sp (-2144)) (at_ base 468) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) s (Z_to_bv 64 (K + 1)))
         with XS3.
      2:{ (lazymatch goal with |- ?G => let G' := eval unfold XS3 in G in change_no_check G' end). subst r1. gres. rewrite R8', R9', R18', R19', R20'. reflexivity. }
      ab_tk Fo468 D_5c748 ltac:(condz).                (* [comment removed for export] *)
      an Fo652 D_5c800.                                  (* [comment removed for export] *)
      an Fo656 D_5c804.                                  (* [comment removed for export] *)
      wd_refl.
    - assert (A2 : getr r2 2 = at_ sp (-2144)) by (rewrite (AG2 2) by notin; subst r1; gres; exact R2').
      post; try assumption.
      intros i Hi. cbn [In] in Hi. gres.
      assert (X : i <> 10) by (clear - Hi; intros ->; cbn in Hi; intuition discriminate). rewrite !getr_other by assumption.
      rewrite (AG2 i) by (clear - Hi; intros Hc; cbn [In rip_clob] in Hc; intuition (subst; discriminate)).
      subst r1. assert (Y : i <> 1 /\ i <> 11 /\ i <> 10 /\ i <> 21) by (clear - Hi; repeat split; intros ->; cbn in Hi; intuition discriminate).
      destruct Y as (Y1 & Y2 & Y3 & Y4). rewrite !getr_other by assumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition xs_slots : list (Z * word) :=
    [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20);
     (-56, getr regs 21); (-64, getr regs 22)]%Z.
  Lemma slots_XS1 : forall (k : Z) (v : word), In (k, v) xs_slots -> rdn segs XS1 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp buf base.
    intros k v Hin. pose proof (u64_range sp). unfold xs_slots in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval unfold XS1, xsl_frame in G in change_no_check G' end); rd8_chain|]). destruct Hin.
  Qed.
  Lemma slots_XS2 : forall (k : Z) (v : word), In (k, v) xs_slots -> rdn segs XS2 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp buf.
    intros k v Hin. pose proof (u64_range sp).
    assert (Hk : (-64 <= k /\ k + 8 <= 0)%Z).
    { unfold xs_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    rewrite <- (slots_XS1 k v Hin). apply rdn_ext; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    intros x Hx. rewrite at_u in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold XS2, tai_mem in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; first [reflexivity | (lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); rewrite ?at_at, ?at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Qed.
  Lemma slots_XS3 : forall (k : Z) (v : word), In (k, v) xs_slots -> rdn segs XS3 (at_ sp k) 8 = Some (word_to_le_bytes 8 v).
  Proof using Hsp buf.
    intros k v Hin. pose proof (u64_range sp).
    assert (Hk : (-64 <= k /\ k + 8 <= 0)%Z).
    { unfold xs_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
    rewrite <- (slots_XS2 k v Hin). apply rdn_ext; [rewrite at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    intros x Hx. rewrite at_u in Hx by lia. (lazymatch goal with |- ?G => let G' := eval unfold XS3 in G in change_no_check G' end). apply rip_mem_outside; rewrite at_u; lia.
  Qed.

  Lemma xblkC : forall (M : word -> option byte) r0,
    (forall k v, In (k, v) xs_slots -> rdn segs M (at_ sp k) 8 = Some (word_to_le_bytes 8 v)) ->
    getr r0 2 = at_ sp (-2144) -> getr r0 10 = Z_to_bv 64 K ->
    (forall i : reg, In i [3; 4; 23; 24; 25; 26; 27]%list -> getr r0 i = getr regs i) ->
    exists r,
      msteps segs (mkst r0 (at_ base 184) M rom) (mkst r ra M rom)
      /\ getr r 10 = Z_to_bv 64 K /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R2 Hret HCODE.
    intros M r0 SL R2' R10' KEEP0.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range base) as Hbr.
    pose proof SL as SLP. unfold xs_slots in SLP.
    Ltac fldM F D vv SLP :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply SLP; clear; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    wd_eexists. split; [|split].
    - an Fo184 D_5c62c.                                  (* [comment removed for export] *)
      fldM Fo188 D_5c630 ra SLP.
      fldM Fo192 D_5c634 (getr regs 8) SLP.
      fldM Fo196 D_5c638 (getr regs 9) SLP.
      fldM Fo200 D_5c63c (getr regs 18) SLP.
      fldM Fo204 D_5c640 (getr regs 19) SLP.
      fldM Fo208 D_5c644 (getr regs 20) SLP.
      fldM Fo212 D_5c648 (getr regs 21) SLP.
      fldM Fo216 D_5c64c (getr regs 22) SLP.
      an Fo220 D_5c650.                                  (* [comment removed for export] *)
      aret Fo224 D_5c654 ra.                             (* [comment removed for export] *)
      wd_refl.
    - gres. exact R10'.
    - intros x Hx. unfold amset_saved in Hx. cbn [In] in Hx. gres.
      repeat (destruct Hx as [<-|Hx];
        [ gres; rwH; rewrite ?at_addi, ?at_0; first
            [ reflexivity
            | f_equal; lia
            | rewrite <- R2; apply KEEP0; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto
            | apply KEEP0; clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto ]
        |]).
      destruct Hx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem xstrlen_small : forall w0 w1 s1, (K <= 63)%Z ->
    qc1H segs mem s (K + 1) g_shoff p_shoff w0 w1 s1 ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra XS2 rom)
      /\ getr r 10 = Z_to_bv 64 K /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R10 R2 R1 Hret Hs_stk Hstk Hcells Rini Hfl Rfl Rgcf RH RM Rrsl Hend SH Hsp fl buf Hbase B452 B180 G128 G84 G60 HTAI HAI SLRET SLOK HCODE c_inited p_cf g_cf c_rsl slt.
    intros w0 w1 s1 HK QH. pose proof (u64_range base) as Hbr. pose proof KL' as [HK0 HKL].
    destruct xblkA as (r1 & RUN1 & A2 & A8 & A9 & A10 & A11 & A18 & AK1).
    destruct (xblkB0 r1 A2 A8 A9 A10 A11 A18) as (r2 & RUN2 & B2 & B8 & B9 & B10 & B11 & B18 & B19 & B20 & BK).
    destruct (qc3_pass r2 XS2 rom s (K + 1) w0 w1 s1 (qc1H_XS2 w0 w1 s1 QH) B18 ltac:(rewrite B10; f_equal; lia)) as (r3 & RUN3 & C10 & AG3).
    destruct (xblkC XS2 r3 slots_XS2) as (r4 & RUN4 & D10 & DK).
    { rewrite (AG3 2) by notin. exact B2. }
    { rewrite C10. f_equal. lia. }
    { intros i Hi. rewrite (AG3 i) by (clear - Hi; intros Hc; cbn [In qc3_clob] in Hc; cbn in Hi; intuition (subst; discriminate)).
      rewrite (BK i) by (clear - Hi; cbn in Hi |- *; tauto). rewrite <- (AK1 i) by (clear - Hi; cbn in Hi |- *; tauto). reflexivity. }
    exists r4. split; [|split; [exact D10 | exact DK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
    eapply msteps_trans.
    { ab_ft Fo124 D_5c5f0 ltac:(condz). exact RUN3. }
    exact RUN4.
  Qed.

  Theorem xstrlen_big : forall (s0b s1b : byte) (midend : word), (64 <= K)%Z -> (K + 1 <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s rt) mem s midend ->
    ((0x10007fff8000 <= U s /\ U s + (K + 1) + 1 <= 0x800000000000) \/ U s + (K + 1) <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U s))) 1 = Some [s0b] -> (U s0b = 0 \/ U s mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U s + (K + 1) - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U s + (K + 1) - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U s)) <= U a < Sh (down8 (U s + (K + 1))))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra XS3 rom)
      /\ getr r 10 = Z_to_bv 64 K /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using R10 R2 R1 Hret Hs_stk Hstk Hcells Rini Hfl Rfl Rgcf RH RM Rrsl Hend SH Hsp fl buf Hbase G84 G60 HTAI HAI SLRET SLOK RTB RTOK HCODE c_inited g_cf c_rsl slt.
    intros s0b s1b midend HK HK43 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz. pose proof (u64_range base) as Hbr.
    destruct xblkA as (r1 & RUN1 & A2 & A8 & A9 & A10 & A11 & A18 & AK1).
    destruct (xblkB0 r1 A2 A8 A9 A10 A11 A18) as (r2 & RUN2 & B2 & B8 & B9 & B10 & B11 & B18 & B19 & B20 & BK).
    destruct (xblkR r2 s0b s1b midend HK HK43 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz B2 B8 B9 B10 B11 B18 B19 B20) as (r3 & RUN3 & C2 & C10 & CK).
    destruct (xblkC XS3 r3 slots_XS3 C2 C10) as (r4 & RUN4 & D10 & DK).
    { intros i Hi. rewrite (CK i) by (clear - Hi; cbn in Hi |- *; tauto). rewrite (BK i) by (clear - Hi; cbn in Hi |- *; tauto).
      rewrite <- (AK1 i) by (clear - Hi; cbn in Hi |- *; tauto). reflexivity. }
    exists r4. split; [|split; [exact D10 | exact DK]].
    eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. exact RUN4.
  Qed.
End XSTRLEN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record xstrlenH (segs : list Segment) (t : xstrlen_tab) (mem : word -> option byte)
       (s : word) (K : Z) (buf : list byte) (ra sp : word) (fl : byte) : Prop := XSTRLENH {
  xsh_sp : (0x10007fff8000 + 2304 <= bv_unsigned sp)%Z /\ (bv_unsigned sp + 16 <= 2 ^ 47)%Z;
  xsh_str : strlH segs mem s buf K;
  xsh_end : (bv_unsigned s + K + 1 <= 2 ^ 47)%Z;
  xsh_rsl : rdn segs mem (Z_to_bv 64 (xs_c_rsl t)) 8 = Some (word_to_le_bytes 8 (st_base (xs_sl t)));
  xsh_cM : rdn segs mem (Z_to_bv 64 (st_cM (xs_sl t))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 Mc));
  xsh_cH : rdn segs mem (Z_to_bv 64 (st_cH (xs_sl t))) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 Hc));
  xsh_gcf : rdn segs mem (Z_to_bv 64 (xs_g_cf t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (xs_p_cf t)));
  xsh_fl : rdn segs mem (Z_to_bv 64 (xs_p_cf t + 251)) 1 = Some [fl];
  xsh_flnz : bv_unsigned fl <> 0%Z;
  xsh_ini : rdn segs mem (Z_to_bv 64 (xs_c_inited t)) 1 = Some [Z_to_bv 8 1];
  xsh_cells : Forall (fun c => 0 <= c /\ c + 8 <= bv_unsigned sp - 2240)%Z
     (xs_c_rsl t :: st_cM (xs_sl t) :: st_cH (xs_sl t) :: xs_g_cf t :: xs_p_cf t :: (xs_p_cf t + 251)%Z :: xs_c_inited t
      :: m2s_cells (rt_m2s (xs_rip t)));
  xsh_stk : store_ok segs mem (at_ sp (-2240)) 2240 = true;
  xsh_s_stk : (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= bv_unsigned s)%Z;
  xsh_ret : ret_ok ra }.

Section PKG.
  Variable segs : list Segment.
  Variable t : xstrlen_tab.
  Hypothesis TOK : xstrlen_tab_ok segs t.
  #[local] Abbreviation U := bv_unsigned.

  Ltac pkg_finish P12 P11 :=
    lazymatch goal with
    | |- store_ok _ _ (at_ _ _) _ = true => exact P12
    | |- Forall _ _ => exact P11
    | _ => first [eassumption | reflexivity]
    end.

  Theorem asan_strlen_icpt_small : forall mem rom (s ra sp : word) (K : Z) (buf : list byte) (fl : byte) regs w0 w1 s1,
    xstrlenH segs t mem s K buf ra sp fl -> (K <= 63)%Z ->
    qc1H segs mem s (K + 1) (mt_g_shoff (rt_m2s (xs_rip t))) (mt_p_shoff (rt_m2s (xs_rip t))) w0 w1 s1 ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = s ->
    exists r,
      msteps segs (mkst regs (xs_base t) mem rom) (mkst r ra (XS2 (xs_base t) mem ra sp regs) rom)
      /\ getr r 10 = Z_to_bv 64 K /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom s ra sp K buf fl regs w0 w1 s1 [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14] HK QH R1 R2 R10.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13].
    replace (mkst regs (xs_base t) mem rom) with (mkst regs (at_ (xs_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply xstrlen_small. all: pkg_finish P12 P11.
  Qed.

  Theorem asan_strlen_icpt_big : forall mem rom (s ra sp : word) (K : Z) (buf : list byte) (fl : byte) regs
      (s0b s1b : byte) (midend : word),
    xstrlenH segs t mem s K buf ra sp fl -> (64 <= K)%Z -> (K + 1 <= 2 ^ 43)%Z ->
    m2sH segs (rt_m2s (xs_rip t)) mem s midend ->
    ((0x10007fff8000 <= U s /\ U s + (K + 1) + 1 <= 0x800000000000) \/ U s + (K + 1) <= 0x7fff7fff)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U s))) 1 = Some [s0b] -> (U s0b = 0 \/ U s mod 8 < U s0b < 128)%Z ->
    rdn segs mem (Z_to_bv 64 (Sh (U s + (K + 1) - 1))) 1 = Some [s1b] -> (U s1b = 0 \/ (U s + (K + 1) - 1) mod 8 < U s1b < 128)%Z ->
    (forall a : word, (Sh (up8 (U s)) <= U a < Sh (down8 (U s + (K + 1))))%Z -> rdn segs mem a 1 = Some [Z_to_bv 8 0]) ->
    getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = s ->
    exists r,
      msteps segs (mkst regs (xs_base t) mem rom)
                  (mkst r ra (XS3 (xs_base t) (xs_rip t) (xs_p_cf t) mem s ra sp K regs) rom)
      /\ getr r 10 = Z_to_bv 64 K /\ (forall x, In x amset_saved -> getr r x = getr regs x).
  Proof using TOK.
    intros mem rom s ra sp K buf fl regs s0b s1b midend [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14]
           HK HK43 CH Hrng Rs0 Hs0 Rs1 Hs1 Rz R1 R2 R10.
    destruct TOK as [T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13].
    replace (mkst regs (xs_base t) mem rom) with (mkst regs (at_ (xs_base t) 0) mem rom) by (rewrite at_0; reflexivity).
    eapply xstrlen_big. all: pkg_finish P12 P11.
  Qed.
End PKG.
End FPGen1.
End AsRtXStrlen.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct AsRtXStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation W8 w := (word_to_le_bytes 8 w).

(* [comment removed for export] *)
Definition scr_rel (mem Mf : word -> option byte) (lo hi : Z) : Prop :=
  (forall a : word, (U a < lo \/ hi <= U a)%Z -> Mf a = mem a)
  /\ mem_grows mem Mf
  /\ (forall a : word, Mf a <> mem a -> Mf a <> None).
Lemma scr_rel_refl : forall mem lo hi, scr_rel mem mem lo hi.
Proof using. intros mem lo hi. split; [reflexivity|]. split; [apply mem_grows_refl|]. intros a NE. exfalso. apply NE. reflexivity. Qed.
Lemma scr_rel_wb : forall mem M1 lo hi (d : word) bs,
  scr_rel mem M1 lo hi -> (lo <= U d)%Z -> (U d + Z.of_nat (length bs) <= hi)%Z -> (hi <= 2 ^ 64)%Z ->
  scr_rel mem (wbytes M1 d bs) lo hi.
Proof using.
  intros mem M1 lo hi d bs (O & G & D) Hlo Hhi H64. split; [|split].
  - intros a Ha. rewrite MemsetLibF.MemSplit.wbytes_outside by lia. apply O. exact Ha.
  - eapply mem_grows_trans; [exact G | apply wbytes_grows].
  - intros a NE. destruct (Z_lt_le_dec (U a) (U d)) as [C1|C1].
    { rewrite MemsetLibF.MemSplit.wbytes_outside in NE |- * by lia. apply D. exact NE. }
    destruct (Z_lt_le_dec (U a) (U d + Z.of_nat (length bs))) as [C2|C2].
    { rewrite MemsetLibF.MemSplit.wbytes_inside by lia. discriminate. }
    rewrite MemsetLibF.MemSplit.wbytes_outside in NE |- * by lia. apply D. exact NE.
Qed.
Lemma scr_rel_mono : forall mem Mf lo hi lo' hi', scr_rel mem Mf lo hi -> (lo' <= lo)%Z -> (hi <= hi')%Z -> scr_rel mem Mf lo' hi'.
Proof using. intros mem Mf lo hi lo' hi' (O & G & D) H1 H2. split; [|split; assumption]. intros a Ha. apply O. lia. Qed.
Lemma scr_rel_trans : forall m1 m2 m3 lo hi, scr_rel m1 m2 lo hi -> scr_rel m2 m3 lo hi -> scr_rel m1 m3 lo hi.
Proof using.
  intros m1 m2 m3 lo hi (O1 & G1 & D1) (O2 & G2 & D2). split; [|split].
  - intros a Ha. rewrite (O2 a Ha). apply O1. exact Ha.
  - eapply mem_grows_trans; eassumption.
  - intros a NE. destruct (decide (m3 a = m2 a)) as [E|N]; [|apply D2; exact N]. rewrite E in NE |- *. apply D1. exact NE.
Qed.
(* [comment removed for export] *)
Lemma scr_rel_rdn : forall segs mem Mf lo hi c n bs, scr_rel mem Mf lo hi ->
  (0 <= c < 2 ^ 64)%Z -> (c + Z.of_nat n <= 2 ^ 64)%Z -> (c + Z.of_nat n <= lo \/ hi <= c)%Z ->
  rdn segs mem (Z_to_bv 64 c) n = Some bs -> rdn segs Mf (Z_to_bv 64 c) n = Some bs.
Proof using.
  intros segs mem Mf lo hi c n bs (O & _ & _) Hc0 Hc64 Hd Hr.
  rewrite (rdn_ext segs n Mf mem (Z_to_bv 64 c)); [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; intros x Hx; apply O; lia].
Qed.
Lemma scr_rel_ok : forall segs mem Mf lo hi (a : word) n, scr_rel mem Mf lo hi ->
  store_ok segs mem a n = true -> store_ok segs Mf a n = true.
Proof using. intros segs mem Mf lo hi a n (_ & G & _) OK. eapply store_ok_mono; [exact G | exact OK]. Qed.

(* [comment removed for export] *)
Definition tgth_words : list (option (bv 32)) :=
  [
   Some W_5c52c
  ]%list.

(* [comment removed for export] *)
Definition tgic_words : list (option (bv 32)) :=
  [
   Some W_60e60; Some W_60e64; Some W_60e68; Some W_60e6c; Some W_60e70; Some W_60e74; Some W_60e78; None; None;
   Some W_60e84; Some W_60e88; Some W_60e8c; Some W_60e90; Some W_60e94; Some W_60e98; Some W_60e9c; Some W_60ea0;
   Some W_60ea4; Some W_60ea8; Some W_60eac; Some W_60eb0; Some W_60eb4; Some W_60eb8; Some W_60ebc; Some W_60ec0;
   Some W_60ec4; Some W_60ec8; Some W_60ecc; Some W_60ed0; Some W_60ed4; Some W_60ed8
  ]%list.

(* [comment removed for export] *)
Definition tgct_words : list (option (bv 32)) :=
  [
   Some W_783b4; Some W_783b8; Some W_783bc; Some W_783c0; Some W_783c4; Some W_783c8; Some W_783cc; Some W_783d0
  ]%list.

(* [comment removed for export] *)
Definition tgts_words : list (option (bv 32)) :=
  [
   None; None; Some W_70a3c; Some W_70a40; Some W_70a44; None
  ]%list.

(* [comment removed for export] *)
Definition tgdt_words : list (option (bv 32)) :=
  [
   Some W_85ac8; Some W_85acc; Some W_85ad0; Some W_85ad4; Some W_85ad8; Some W_85adc; Some W_85ae0; Some W_85ae4;
   Some W_85ae8; Some W_85aec; Some W_85af0; Some W_85af4; Some W_85af8; Some W_85afc; Some W_85b00; None; None;
   Some W_85b0c; Some W_85b10; Some W_85b14; None; None; Some W_85b20; None; Some W_85b28; None; Some W_85b30;
   Some W_85b34; Some W_85b38; Some W_85b3c; Some W_85b40; Some W_85b44; Some W_85b48; Some W_85b4c; Some W_85b50;
   Some W_85b54; Some W_85b58; Some W_85b5c; None; Some W_85b64; Some W_85b68; Some W_85b6c; Some W_85b70;
   Some W_85b74; Some W_85b78; Some W_85b7c; Some W_85b80; Some W_85b84; None; None; Some W_85b90; Some W_85b94;
   Some W_85b98; Some W_85b9c; Some W_85ba0; None; Some W_85ba8; Some W_85bac; Some W_85bb0; Some W_85bb4;
   Some W_85bb8; Some W_85bbc; Some W_85bc0; Some W_85bc4; Some W_85bc8; Some W_85bcc; Some W_85bd0; Some W_85bd4;
   Some W_85bd8; Some W_85bdc; Some W_85be0; Some W_85be4; Some W_85be8; Some W_85bec; Some W_85bf0; None;
   Some W_85bf8; None; Some W_85c00; None; None; Some W_85c0c; Some W_85c10; Some W_85c14; Some W_85c18;
   Some W_85c1c; Some W_85c20; Some W_85c24; Some W_85c28; Some W_85c2c; Some W_85c30; Some W_85c34; Some W_85c38;
   Some W_85c3c; Some W_85c40; Some W_85c44; Some W_85c48; Some W_85c4c; Some W_85c50; Some W_85c54; Some W_85c58;
   Some W_85c5c; Some W_85c60; Some W_85c64; Some W_85c68; Some W_85c6c; Some W_85c70; Some W_85c74; Some W_85c78;
   Some W_85c7c; Some W_85c80; Some W_85c84; Some W_85c88; Some W_85c8c; Some W_85c90; Some W_85c94; Some W_85c98;
   Some W_85c9c; Some W_85ca0; Some W_85ca4; Some W_85ca8; Some W_85cac; Some W_85cb0; Some W_85cb4; Some W_85cb8;
   Some W_85cbc; Some W_85cc0; Some W_85cc4; Some W_85cc8; Some W_85ccc; Some W_85cd0; Some W_85cd4; Some W_85cd8;
   Some W_85cdc; Some W_85ce0
  ]%list.

(* [comment removed for export] *)
Definition mtga_words : list (option (bv 32)) :=
  [
   Some W_f5fc0; Some W_f5fc4; Some W_f5fc8; Some W_f5fcc; Some W_f5fd0; Some W_f5fd4; Some W_f5fd8; Some W_f5fdc;
   Some W_f5fe0
  ]%list.

(* [comment removed for export] *)
Definition mpgs_words : list (option (bv 32)) :=
  [
   Some W_f7074; Some W_f7078; Some W_f707c; Some W_f7080; Some W_f7084; Some W_f7088; Some W_f708c
  ]%list.

Section TLSGA.
  Variables (segs : list Segment) (hb tga pgs : word).
  Variables (c_inited c_rtga c_tsd g_cf p_cf g_verb p_verb c_tlsd : Z).
  Hypothesis HC_TH : code_ato segs hb 0 tgth_words.
  Hypothesis HC_IC : code_ato segs hb 18740 tgic_words.
  Hypothesis HC_CT : code_ato segs hb 114312 tgct_words.
  Hypothesis HC_TS : code_ato segs hb 83208 tgts_words.
  Hypothesis HC_DT : code_ato segs hb 169372 tgdt_words.
  Hypothesis HC_TGA : code_ato segs tga 0 mtga_words.
  Hypothesis HC_PGS : code_ato segs pgs 0 mpgs_words.
  Hypothesis TAI : try_asan_init_call segs (at_ hb 104072) c_inited.
  Hypothesis G18613 : gload segs hb 18768 11 c_rtga.                 (* [comment removed for export] *)
  Hypothesis A8318c : gaddr2 segs hb 83208 10 10 (Z_to_bv 64 c_tsd). (* [comment removed for export] *)
  Hypothesis J831ac : gjump segs hb 83228 pgs.                       (* [comment removed for export] *)
  Hypothesis G1692e8 : gload segs hb 169432 11 g_cf.                 (* [comment removed for export] *)
  Hypothesis G169308 : gload2 segs hb 169452 10 26 g_verb.           (* [comment removed for export] *)
  Hypothesis GS169320 : gauipc_ld segs hb 169464 169472 10 21 c_tlsd. (* [comment removed for export] *)
  Hypothesis Hhb : (U hb mod 2 = 0)%Z /\ (U hb + 180000 < 2 ^ 64)%Z.
  Hypothesis Htga : ret_ok tga.
  Hypothesis Hpgs : (U pgs mod 2 = 0)%Z /\ (U pgs + 64 < 2 ^ 64)%Z.
  Hypothesis Htga64 : (U tga + 64 < 2 ^ 64)%Z.


  Lemma F_5c52c : fetch_word segs (at_ hb 0) = Some W_5c52c.   (* [comment removed for export] *)
  Proof using HC_TH. exact (code_ato_get segs hb 0 tgth_words 0 _ HC_TH eq_refl). Qed.


  Lemma F_60e60 : fetch_word segs (at_ hb 18740) = Some W_60e60.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 0 _ HC_IC eq_refl). Qed.
  Lemma F_60e64 : fetch_word segs (at_ hb 18744) = Some W_60e64.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 1 _ HC_IC eq_refl). Qed.
  Lemma F_60e68 : fetch_word segs (at_ hb 18748) = Some W_60e68.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 2 _ HC_IC eq_refl). Qed.
  Lemma F_60e6c : fetch_word segs (at_ hb 18752) = Some W_60e6c.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 3 _ HC_IC eq_refl). Qed.
  Lemma F_60e70 : fetch_word segs (at_ hb 18756) = Some W_60e70.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 4 _ HC_IC eq_refl). Qed.
  Lemma F_60e74 : fetch_word segs (at_ hb 18760) = Some W_60e74.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 5 _ HC_IC eq_refl). Qed.
  Lemma F_60e78 : fetch_word segs (at_ hb 18764) = Some W_60e78.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 6 _ HC_IC eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma F_60e84 : fetch_word segs (at_ hb 18776) = Some W_60e84.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 9 _ HC_IC eq_refl). Qed.
  Lemma F_60e88 : fetch_word segs (at_ hb 18780) = Some W_60e88.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 10 _ HC_IC eq_refl). Qed.
  Lemma F_60e8c : fetch_word segs (at_ hb 18784) = Some W_60e8c.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 11 _ HC_IC eq_refl). Qed.
  Lemma F_60e90 : fetch_word segs (at_ hb 18788) = Some W_60e90.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 12 _ HC_IC eq_refl). Qed.
  Lemma F_60e94 : fetch_word segs (at_ hb 18792) = Some W_60e94.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 13 _ HC_IC eq_refl). Qed.
  Lemma F_60e98 : fetch_word segs (at_ hb 18796) = Some W_60e98.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 14 _ HC_IC eq_refl). Qed.
  Lemma F_60e9c : fetch_word segs (at_ hb 18800) = Some W_60e9c.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 15 _ HC_IC eq_refl). Qed.
  Lemma F_60ea0 : fetch_word segs (at_ hb 18804) = Some W_60ea0.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 16 _ HC_IC eq_refl). Qed.
  Lemma F_60ea4 : fetch_word segs (at_ hb 18808) = Some W_60ea4.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 17 _ HC_IC eq_refl). Qed.
  Lemma F_60ea8 : fetch_word segs (at_ hb 18812) = Some W_60ea8.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 18 _ HC_IC eq_refl). Qed.


  Lemma F_60eb4 : fetch_word segs (at_ hb 18824) = Some W_60eb4.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 21 _ HC_IC eq_refl). Qed.
  Lemma F_60eb8 : fetch_word segs (at_ hb 18828) = Some W_60eb8.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 22 _ HC_IC eq_refl). Qed.
  Lemma F_60ebc : fetch_word segs (at_ hb 18832) = Some W_60ebc.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 23 _ HC_IC eq_refl). Qed.
  Lemma F_60ec0 : fetch_word segs (at_ hb 18836) = Some W_60ec0.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 24 _ HC_IC eq_refl). Qed.
  Lemma F_60ec4 : fetch_word segs (at_ hb 18840) = Some W_60ec4.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 25 _ HC_IC eq_refl). Qed.
  Lemma F_60ec8 : fetch_word segs (at_ hb 18844) = Some W_60ec8.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 26 _ HC_IC eq_refl). Qed.
  Lemma F_60ecc : fetch_word segs (at_ hb 18848) = Some W_60ecc.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 27 _ HC_IC eq_refl). Qed.
  Lemma F_60ed0 : fetch_word segs (at_ hb 18852) = Some W_60ed0.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 28 _ HC_IC eq_refl). Qed.
  Lemma F_60ed4 : fetch_word segs (at_ hb 18856) = Some W_60ed4.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 29 _ HC_IC eq_refl). Qed.
  Lemma F_60ed8 : fetch_word segs (at_ hb 18860) = Some W_60ed8.   (* [comment removed for export] *)
  Proof using HC_IC. exact (code_ato_get segs hb 18740 tgic_words 30 _ HC_IC eq_refl). Qed.


  Lemma F_783b4 : fetch_word segs (at_ hb 114312) = Some W_783b4.   (* [comment removed for export] *)
  Proof using HC_CT. exact (code_ato_get segs hb 114312 tgct_words 0 _ HC_CT eq_refl). Qed.
  Lemma F_783b8 : fetch_word segs (at_ hb 114316) = Some W_783b8.   (* [comment removed for export] *)
  Proof using HC_CT. exact (code_ato_get segs hb 114312 tgct_words 1 _ HC_CT eq_refl). Qed.
  Lemma F_783bc : fetch_word segs (at_ hb 114320) = Some W_783bc.   (* [comment removed for export] *)
  Proof using HC_CT. exact (code_ato_get segs hb 114312 tgct_words 2 _ HC_CT eq_refl). Qed.
  Lemma F_783c0 : fetch_word segs (at_ hb 114324) = Some W_783c0.   (* [comment removed for export] *)
  Proof using HC_CT. exact (code_ato_get segs hb 114312 tgct_words 3 _ HC_CT eq_refl). Qed.
  Lemma F_783c4 : fetch_word segs (at_ hb 114328) = Some W_783c4.   (* [comment removed for export] *)
  Proof using HC_CT. exact (code_ato_get segs hb 114312 tgct_words 4 _ HC_CT eq_refl). Qed.
  Lemma F_783c8 : fetch_word segs (at_ hb 114332) = Some W_783c8.   (* [comment removed for export] *)
  Proof using HC_CT. exact (code_ato_get segs hb 114312 tgct_words 5 _ HC_CT eq_refl). Qed.
  Lemma F_783cc : fetch_word segs (at_ hb 114336) = Some W_783cc.   (* [comment removed for export] *)
  Proof using HC_CT. exact (code_ato_get segs hb 114312 tgct_words 6 _ HC_CT eq_refl). Qed.
  Lemma F_783d0 : fetch_word segs (at_ hb 114340) = Some W_783d0.   (* [comment removed for export] *)
  Proof using HC_CT. exact (code_ato_get segs hb 114312 tgct_words 7 _ HC_CT eq_refl). Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma F_70a3c : fetch_word segs (at_ hb 83216) = Some W_70a3c.   (* [comment removed for export] *)
  Proof using HC_TS. exact (code_ato_get segs hb 83208 tgts_words 2 _ HC_TS eq_refl). Qed.
  Lemma F_70a40 : fetch_word segs (at_ hb 83220) = Some W_70a40.   (* [comment removed for export] *)
  Proof using HC_TS. exact (code_ato_get segs hb 83208 tgts_words 3 _ HC_TS eq_refl). Qed.
  Lemma F_70a44 : fetch_word segs (at_ hb 83224) = Some W_70a44.   (* [comment removed for export] *)
  Proof using HC_TS. exact (code_ato_get segs hb 83208 tgts_words 4 _ HC_TS eq_refl). Qed.
  (* [comment removed for export] *)


  Lemma F_85ac8 : fetch_word segs (at_ hb 169372) = Some W_85ac8.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 0 _ HC_DT eq_refl). Qed.
  Lemma F_85acc : fetch_word segs (at_ hb 169376) = Some W_85acc.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 1 _ HC_DT eq_refl). Qed.
  Lemma F_85ad0 : fetch_word segs (at_ hb 169380) = Some W_85ad0.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 2 _ HC_DT eq_refl). Qed.
  Lemma F_85ad4 : fetch_word segs (at_ hb 169384) = Some W_85ad4.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 3 _ HC_DT eq_refl). Qed.
  Lemma F_85ad8 : fetch_word segs (at_ hb 169388) = Some W_85ad8.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 4 _ HC_DT eq_refl). Qed.
  Lemma F_85adc : fetch_word segs (at_ hb 169392) = Some W_85adc.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 5 _ HC_DT eq_refl). Qed.
  Lemma F_85ae0 : fetch_word segs (at_ hb 169396) = Some W_85ae0.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 6 _ HC_DT eq_refl). Qed.
  Lemma F_85ae4 : fetch_word segs (at_ hb 169400) = Some W_85ae4.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 7 _ HC_DT eq_refl). Qed.
  Lemma F_85ae8 : fetch_word segs (at_ hb 169404) = Some W_85ae8.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 8 _ HC_DT eq_refl). Qed.
  Lemma F_85aec : fetch_word segs (at_ hb 169408) = Some W_85aec.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 9 _ HC_DT eq_refl). Qed.
  Lemma F_85af0 : fetch_word segs (at_ hb 169412) = Some W_85af0.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 10 _ HC_DT eq_refl). Qed.
  Lemma F_85af4 : fetch_word segs (at_ hb 169416) = Some W_85af4.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 11 _ HC_DT eq_refl). Qed.
  Lemma F_85af8 : fetch_word segs (at_ hb 169420) = Some W_85af8.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 12 _ HC_DT eq_refl). Qed.
  Lemma F_85afc : fetch_word segs (at_ hb 169424) = Some W_85afc.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 13 _ HC_DT eq_refl). Qed.
  Lemma F_85b00 : fetch_word segs (at_ hb 169428) = Some W_85b00.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 14 _ HC_DT eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma F_85b0c : fetch_word segs (at_ hb 169440) = Some W_85b0c.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 17 _ HC_DT eq_refl). Qed.
  Lemma F_85b10 : fetch_word segs (at_ hb 169444) = Some W_85b10.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 18 _ HC_DT eq_refl). Qed.
  Lemma F_85b14 : fetch_word segs (at_ hb 169448) = Some W_85b14.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 19 _ HC_DT eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma F_85b20 : fetch_word segs (at_ hb 169460) = Some W_85b20.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 22 _ HC_DT eq_refl). Qed.
  (* [comment removed for export] *)
  Lemma F_85b28 : fetch_word segs (at_ hb 169468) = Some W_85b28.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 24 _ HC_DT eq_refl). Qed.
  (* [comment removed for export] *)
  Lemma F_85b30 : fetch_word segs (at_ hb 169476) = Some W_85b30.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 26 _ HC_DT eq_refl). Qed.
  Lemma F_85b34 : fetch_word segs (at_ hb 169480) = Some W_85b34.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 27 _ HC_DT eq_refl). Qed.
  Lemma F_85b38 : fetch_word segs (at_ hb 169484) = Some W_85b38.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 28 _ HC_DT eq_refl). Qed.
  Lemma F_85b3c : fetch_word segs (at_ hb 169488) = Some W_85b3c.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 29 _ HC_DT eq_refl). Qed.
  Lemma F_85b40 : fetch_word segs (at_ hb 169492) = Some W_85b40.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 30 _ HC_DT eq_refl). Qed.
  Lemma F_85b44 : fetch_word segs (at_ hb 169496) = Some W_85b44.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 31 _ HC_DT eq_refl). Qed.
  Lemma F_85b48 : fetch_word segs (at_ hb 169500) = Some W_85b48.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 32 _ HC_DT eq_refl). Qed.
  Lemma F_85b4c : fetch_word segs (at_ hb 169504) = Some W_85b4c.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 33 _ HC_DT eq_refl). Qed.




























  Lemma F_85bd0 : fetch_word segs (at_ hb 169636) = Some W_85bd0.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 66 _ HC_DT eq_refl). Qed.
  Lemma F_85bd4 : fetch_word segs (at_ hb 169640) = Some W_85bd4.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 67 _ HC_DT eq_refl). Qed.
  Lemma F_85bd8 : fetch_word segs (at_ hb 169644) = Some W_85bd8.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 68 _ HC_DT eq_refl). Qed.
  Lemma F_85bdc : fetch_word segs (at_ hb 169648) = Some W_85bdc.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 69 _ HC_DT eq_refl). Qed.
  Lemma F_85be0 : fetch_word segs (at_ hb 169652) = Some W_85be0.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 70 _ HC_DT eq_refl). Qed.







































  Lemma F_85c90 : fetch_word segs (at_ hb 169828) = Some W_85c90.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 114 _ HC_DT eq_refl). Qed.
  Lemma F_85c94 : fetch_word segs (at_ hb 169832) = Some W_85c94.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 115 _ HC_DT eq_refl). Qed.
  Lemma F_85c98 : fetch_word segs (at_ hb 169836) = Some W_85c98.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 116 _ HC_DT eq_refl). Qed.
  Lemma F_85c9c : fetch_word segs (at_ hb 169840) = Some W_85c9c.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 117 _ HC_DT eq_refl). Qed.
  Lemma F_85ca0 : fetch_word segs (at_ hb 169844) = Some W_85ca0.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 118 _ HC_DT eq_refl). Qed.
  Lemma F_85ca4 : fetch_word segs (at_ hb 169848) = Some W_85ca4.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 119 _ HC_DT eq_refl). Qed.
  Lemma F_85ca8 : fetch_word segs (at_ hb 169852) = Some W_85ca8.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 120 _ HC_DT eq_refl). Qed.
  Lemma F_85cac : fetch_word segs (at_ hb 169856) = Some W_85cac.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 121 _ HC_DT eq_refl). Qed.
  Lemma F_85cb0 : fetch_word segs (at_ hb 169860) = Some W_85cb0.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 122 _ HC_DT eq_refl). Qed.
  Lemma F_85cb4 : fetch_word segs (at_ hb 169864) = Some W_85cb4.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 123 _ HC_DT eq_refl). Qed.
  Lemma F_85cb8 : fetch_word segs (at_ hb 169868) = Some W_85cb8.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 124 _ HC_DT eq_refl). Qed.
  Lemma F_85cbc : fetch_word segs (at_ hb 169872) = Some W_85cbc.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 125 _ HC_DT eq_refl). Qed.
  Lemma F_85cc0 : fetch_word segs (at_ hb 169876) = Some W_85cc0.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 126 _ HC_DT eq_refl). Qed.
  Lemma F_85cc4 : fetch_word segs (at_ hb 169880) = Some W_85cc4.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 127 _ HC_DT eq_refl). Qed.
  Lemma F_85cc8 : fetch_word segs (at_ hb 169884) = Some W_85cc8.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 128 _ HC_DT eq_refl). Qed.
  Lemma F_85ccc : fetch_word segs (at_ hb 169888) = Some W_85ccc.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 129 _ HC_DT eq_refl). Qed.
  Lemma F_85cd0 : fetch_word segs (at_ hb 169892) = Some W_85cd0.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 130 _ HC_DT eq_refl). Qed.
  Lemma F_85cd4 : fetch_word segs (at_ hb 169896) = Some W_85cd4.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 131 _ HC_DT eq_refl). Qed.
  Lemma F_85cd8 : fetch_word segs (at_ hb 169900) = Some W_85cd8.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 132 _ HC_DT eq_refl). Qed.
  Lemma F_85cdc : fetch_word segs (at_ hb 169904) = Some W_85cdc.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 133 _ HC_DT eq_refl). Qed.
  Lemma F_85ce0 : fetch_word segs (at_ hb 169908) = Some W_85ce0.   (* [comment removed for export] *)
  Proof using HC_DT. exact (code_ato_get segs hb 169372 tgdt_words 134 _ HC_DT eq_refl). Qed.


  Lemma F_f5fc0 : fetch_word segs (at_ tga 0) = Some W_f5fc0.   (* [comment removed for export] *)
  Proof using HC_TGA. exact (code_ato_get segs tga 0 mtga_words 0 _ HC_TGA eq_refl). Qed.
  Lemma F_f5fc4 : fetch_word segs (at_ tga 4) = Some W_f5fc4.   (* [comment removed for export] *)
  Proof using HC_TGA. exact (code_ato_get segs tga 0 mtga_words 1 _ HC_TGA eq_refl). Qed.
  Lemma F_f5fc8 : fetch_word segs (at_ tga 8) = Some W_f5fc8.   (* [comment removed for export] *)
  Proof using HC_TGA. exact (code_ato_get segs tga 0 mtga_words 2 _ HC_TGA eq_refl). Qed.
  Lemma F_f5fcc : fetch_word segs (at_ tga 12) = Some W_f5fcc.   (* [comment removed for export] *)
  Proof using HC_TGA. exact (code_ato_get segs tga 0 mtga_words 3 _ HC_TGA eq_refl). Qed.
  Lemma F_f5fd0 : fetch_word segs (at_ tga 16) = Some W_f5fd0.   (* [comment removed for export] *)
  Proof using HC_TGA. exact (code_ato_get segs tga 0 mtga_words 4 _ HC_TGA eq_refl). Qed.
  Lemma F_f5fd4 : fetch_word segs (at_ tga 20) = Some W_f5fd4.   (* [comment removed for export] *)
  Proof using HC_TGA. exact (code_ato_get segs tga 0 mtga_words 5 _ HC_TGA eq_refl). Qed.
  Lemma F_f5fd8 : fetch_word segs (at_ tga 24) = Some W_f5fd8.   (* [comment removed for export] *)
  Proof using HC_TGA. exact (code_ato_get segs tga 0 mtga_words 6 _ HC_TGA eq_refl). Qed.
  Lemma F_f5fdc : fetch_word segs (at_ tga 28) = Some W_f5fdc.   (* [comment removed for export] *)
  Proof using HC_TGA. exact (code_ato_get segs tga 0 mtga_words 7 _ HC_TGA eq_refl). Qed.
  Lemma F_f5fe0 : fetch_word segs (at_ tga 32) = Some W_f5fe0.   (* [comment removed for export] *)
  Proof using HC_TGA. exact (code_ato_get segs tga 0 mtga_words 8 _ HC_TGA eq_refl). Qed.


  Lemma F_f7074 : fetch_word segs (at_ pgs 0) = Some W_f7074.   (* [comment removed for export] *)
  Proof using HC_PGS. exact (code_ato_get segs pgs 0 mpgs_words 0 _ HC_PGS eq_refl). Qed.
  Lemma F_f7078 : fetch_word segs (at_ pgs 4) = Some W_f7078.   (* [comment removed for export] *)
  Proof using HC_PGS. exact (code_ato_get segs pgs 0 mpgs_words 1 _ HC_PGS eq_refl). Qed.
  Lemma F_f707c : fetch_word segs (at_ pgs 8) = Some W_f707c.   (* [comment removed for export] *)
  Proof using HC_PGS. exact (code_ato_get segs pgs 0 mpgs_words 2 _ HC_PGS eq_refl). Qed.
  Lemma F_f7080 : fetch_word segs (at_ pgs 12) = Some W_f7080.   (* [comment removed for export] *)
  Proof using HC_PGS. exact (code_ato_get segs pgs 0 mpgs_words 3 _ HC_PGS eq_refl). Qed.
  Lemma F_f7084 : fetch_word segs (at_ pgs 16) = Some W_f7084.   (* [comment removed for export] *)
  Proof using HC_PGS. exact (code_ato_get segs pgs 0 mpgs_words 4 _ HC_PGS eq_refl). Qed.
  Lemma F_f7088 : fetch_word segs (at_ pgs 20) = Some W_f7088.   (* [comment removed for export] *)
  Proof using HC_PGS. exact (code_ato_get segs pgs 0 mpgs_words 5 _ HC_PGS eq_refl). Qed.
  Lemma F_f708c : fetch_word segs (at_ pgs 24) = Some W_f708c.   (* [comment removed for export] *)
  Proof using HC_PGS. exact (code_ato_get segs pgs 0 mpgs_words 6 _ HC_PGS eq_refl). Qed.

  Variable mem : word -> option byte.
  Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Variables (ra S argw tpw offw dtvp dtv1 keysp Tw Aw tlsb tlse g12 dbeg : word).
  #[local] Abbreviation LE8' z := (word_to_le_bytes 8 (Z_to_bv 64 z)).
  Hypothesis Rinit : rdn segs mem (Z_to_bv 64 c_inited) 1 = Some [Z_to_bv 8 1].
  Hypothesis Rrtga : rdn segs mem (Z_to_bv 64 c_rtga) 8 = Some (W8 tga).
  Hypothesis Rarg0 : rdn segs mem (Z_to_bv 64 (U argw)) 8 = Some (LE8' 1).                       (* [comment removed for export] *)
  Hypothesis Rarg8 : rdn segs mem (Z_to_bv 64 (U argw + 8)) 8 = Some (W8 offw).              (* [comment removed for export] *)
  Hypothesis Rdtvp : rdn segs mem (Z_to_bv 64 (U tpw - 8)) 8 = Some (W8 dtvp).            (* [comment removed for export] *)
  Hypothesis Rdtv1 : rdn segs mem (Z_to_bv 64 (U dtvp + 8)) 8 = Some (W8 dtv1).              (* [comment removed for export] *)
  Hypothesis Rtsdi : rdn segs mem (Z_to_bv 64 c_tsd) 1 = Some [Z_to_bv 8 1].    (* [comment removed for export] *)
  Hypothesis Rkey : rdn segs mem (Z_to_bv 64 (c_tsd + 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).   (* [comment removed for export] *)
  Hypothesis Rkeys : rdn segs mem (Z_to_bv 64 (U tpw - 88)) 8 = Some (W8 keysp).          (* [comment removed for export] *)
  Hypothesis RT : rdn segs mem (Z_to_bv 64 (U keysp)) 8 = Some (W8 Tw).                          (* [comment removed for export] *)
  Hypothesis RA : rdn segs mem (Z_to_bv 64 (U Tw + 152)) 8 = Some (W8 Aw).                   (* [comment removed for export] *)
  Hypothesis Rtlsb : rdn segs mem (Z_to_bv 64 (U Aw + 48)) 8 = Some (W8 tlsb).
  Hypothesis Rtlse : rdn segs mem (Z_to_bv 64 (U Aw + 56)) 8 = Some (W8 tlse).
  Hypothesis Rg_cf : rdn segs mem (Z_to_bv 64 g_cf) 8 = Some (LE8' p_cf).
  Hypothesis Ritga : rdn segs mem (Z_to_bv 64 (p_cf + 137)) 1 = Some [Z_to_bv 8 1]. (* [comment removed for export] *)
  Hypothesis Rg_verb : rdn segs mem (Z_to_bv 64 g_verb) 8 = Some (LE8' p_verb).
  Hypothesis Rverb : rdn segs mem (Z_to_bv 64 p_verb) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis Rtlsd : rdn segs mem (Z_to_bv 64 c_tlsd) 8 = Some (LE8' 8).        (* [comment removed for export] *)
  Hypothesis Rg12 : rdn segs mem (Z_to_bv 64 (U tpw + 8)) 8 = Some (W8 g12).                 (* [comment removed for export] *)
  Hypothesis Rdbeg : rdn segs mem (Z_to_bv 64 (U g12 + 24)) 8 = Some (W8 dbeg).              (* [comment removed for export] *)
  Hypothesis HTnz : U Tw <> 0%Z.
  Hypothesis HAnz : U Aw <> 0%Z.
  Hypothesis Hg12 : U g12 <> 0%Z /\ U g12 <> (2 ^ 64 - 1)%Z.
  Hypothesis Hdbeg : U dbeg <> 0%Z.
  (* [comment removed for export] *)
  Definition tg_cells : list (Z * Z) :=
    [(c_inited, 1); (c_rtga, 8); (U argw, 16); (U tpw - 8, 8); (U dtvp + 8, 8); (c_tsd, 8); (U tpw - 88, 8); (U keysp, 8);
     (U Tw + 152, 8); (U Aw + 48, 16); (g_cf, 8); (p_cf + 137, 1); (g_verb, 8); (p_verb, 4); (c_tlsd, 8); (U tpw + 8, 8); (U g12 + 24, 8)]%Z.
  Hypothesis Hcells : Forall (fun c => 0 <= fst c /\ fst c + snd c <= U S - 176)%Z tg_cells.
  Hypothesis Hpcf : (0 <= p_cf)%Z.
  Hypothesis HS : (176 <= U S)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ S (-176)) 176 = true.
  Hypothesis Hret : ret_ok ra.

  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = S.
  Hypothesis H4 : getr regs 4 = tpw.
  Hypothesis H10 : getr regs 10 = argw.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition TM1 : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes mem (at_ S (-8)) (W8 ra)) (at_ S (-16)) (W8 (getr regs 8))) (at_ S (-24)) (W8 (getr regs 9)))
           (at_ S (-32)) (W8 (getr regs 18)).
  (* [comment removed for export] *)
  Definition TM2 : word -> option byte := tai_mem TM1 (at_ S (-32)) (at_ hb 18768) argw.

  Ltac cells_split :=
    let HC := fresh "HC" in
    pose proof Hcells as HC; unfold tg_cells in HC;
    repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end;
    cbn [fst snd] in *.
  Ltac addr_eq :=
    apply bv_eq; rewrite ?v_addi_0;
    repeat match goal with |- context [v_addi ?b ?e] => change (v_addi b e) with (at_ b e) end;
    (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  (* [comment removed for export] *)
  Ltac rd_sideK Hb := match goal with Hr' : (0 <= bv_unsigned S < 2 ^ 64)%Z |- _ => clear - Hb HS Hr' end; rd8_side.
  Ltac rd_peelK Hb := repeat (rewrite rdn_wbytes_out; [ | rd_sideK Hb | rd_sideK Hb | rd_sideK Hb ]).
  Ltac rd_thru Hr :=
    (lazymatch goal with |- ?G => let G' := eval unfold TM2, tai_mem, TM1 in G in change_no_check G' end); rewrite ?at_at; zlit_at;
    first
    [ lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?c) _ = _ =>
        first [ match goal with Hb : (0 <= c)%Z /\ _ |- _ => rd_peelK Hb end
              | lazymatch c with (?x + _)%Z => match goal with Hb : (0 <= x)%Z /\ _ |- _ => rd_peelK Hb end end ]
      end
    | idtac ];
    repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]);
    lazymatch goal with |- rdn _ mem _ _ = _ => exact Hr end.
  (* [comment removed for export] *)
  Ltac rd_sideS := match goal with Hr' : (0 <= bv_unsigned S < 2 ^ 64)%Z |- _ => clear - HS Hr' end; rd8_side.
  Ltac rd8_chainS :=
    repeat (rewrite rdn_wbytes_out; [ | rd_sideS | rd_sideS | rd_sideS ]);
    apply rdn_wbytes_hit8; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia.
  Ltac sok :=
    (lazymatch goal with |- ?G => let G' := eval unfold TM2, tai_mem, TM1 in G in change_no_check G' end); repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub segs mem (at_ S (-176)) _ 176);
    [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia].
  Ltac fsd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sok ]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac cldz F D cc vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 cc : word) by addr_eq end;
          rd_thru Hr
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac fld F D vv :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold TM2, tai_mem, TM1 in G in change_no_check G' end); rewrite ?at_at; zlit_at; rd8_chainS
        | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Ltac glk G Hr := eapply msteps_trans; [ eapply G; rd_thru Hr | ]; zlit_at.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkTA :
    exists r,
      msteps segs (mkst regs (at_ hb 0) mem rom) (mkst r (at_ hb 104072) TM1 rom)
      /\ getr r 1 = at_ hb 18768 /\ getr r 2 = at_ S (-32) /\ getr r 8 = argw /\ getr r 4 = tpw
      /\ regs_agree (fun x => In x [1; 2; 8]%list) regs r.
  Proof using H10 H4 H2 H1 Hstk HS Hg12 g12 Hhb HC_IC HC_TH pgs.
    pose proof (u64_range S) as HSr. destruct Hhb as [Hb2 Hb64].
    wd_eexists. split.
    - an F_5c52c D_5c52c.                                      (* [comment removed for export] *)
      an F_60e60 D_60e60.                                      (* [comment removed for export] *)
      fsd F_60e64 D_60e64 (at_ S (-8)).                       (* [comment removed for export] *)
      fsd F_60e68 D_60e68 (at_ S (-16)).                      (* [comment removed for export] *)
      fsd F_60e6c D_60e6c (at_ S (-24)).                      (* [comment removed for export] *)
      fsd F_60e70 D_60e70 (at_ S (-32)).                      (* [comment removed for export] *)
      change (wbytes _ _ _) with TM1.
      an F_60e74 D_60e74.                                      (* [comment removed for export] *)
      an F_60e78 D_60e78.                                      (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.

  Definition TGB : list reg := [1; 2; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 26]%list.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma blkTB : forall r1,
    getr r1 10 = Z_to_bv 64 1 -> getr r1 2 = at_ S (-32) -> getr r1 8 = argw -> getr r1 4 = tpw ->
    exists r Mf,
      msteps segs (mkst r1 (at_ hb 18768) TM2 rom) (mkst r ra Mf rom)
      /\ scr_rel mem Mf (U S - 176) (U S)
      /\ getr r 10 = v_add offw dtv1 /\ getr r 1 = ra /\ getr r 2 = S
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18
      /\ getr r 19 = getr r1 19 /\ getr r 20 = getr r1 20 /\ getr r 21 = getr r1 21 /\ getr r 22 = getr r1 22 /\ getr r 26 = getr r1 26
      /\ regs_agree (fun x => In x TGB) r1 r.
  Proof using Hret Hstk HS Hpcf Hcells Hdbeg Hg12 HAnz HTnz Rdbeg Rg12 Rtlsd Rverb Rg_verb Ritga Rg_cf Rtlse Rtlsb RA RT Rkeys Rkey Rtsdi Rdtv1 Rdtvp Rarg8 Rarg0 Rrtga dbeg g12 tlse tlsb Aw Tw keysp dtvp Hpgs Htga Hhb GS169320 G169308 G1692e8 J831ac A8318c G18613 HC_PGS HC_TGA HC_DT HC_TS HC_CT HC_IC c_tlsd p_verb g_verb p_cf g_cf c_tsd c_rtga c_inited pgs tga.
    intros r1 Q10 Q2 Q8 Q4.
    pose proof (u64_range S) as HSr. destruct Hhb as [Hb2 Hb64]. destruct Hpgs as [Hp2 Hp64]. cells_split.
    pose proof (u64_range argw) as Har. pose proof (u64_range tpw) as Htr. pose proof (u64_range dtvp) as Hdr.
    pose proof (u64_range keysp) as Hkr. pose proof (u64_range Tw) as HTr. pose proof (u64_range Aw) as HAr. pose proof (u64_range g12) as Hgr.
    pose proof (u64_range hb) as Hhr. pose proof (u64_range tga) as Htgr. pose proof (u64_range pgs) as Hpgr.
    destruct G169308 as [x169348 GX]. destruct A8318c as [x83104 AX]. destruct GS169320 as (xs & GSa & GSl).
    assert (RT18633 : ret_ok (at_ hb 18788)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    assert (RT18645 : ret_ok (at_ hb 18800)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    assert (RT1141e0 : ret_ok (at_ hb 114324)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    assert (RT186e1 : ret_ok (at_ hb 18836)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    wd_eexists. wd_eexists. split; [|split].
    - glk G18613 Rrtga.                                        (* [comment removed for export] *)
      an F_60e84 D_60e84.                                      (* [comment removed for export] *)
      an F_60e88 D_60e88.                                      (* [comment removed for export] *)
      aret F_60e8c D_60e8c tga.                                (* [comment removed for export] *)
      (* [comment removed for export] *)
      rewrite <- (at_0 tga).
      an F_f5fc0 D_f5fc0.                                      (* [comment removed for export] *)
      cldz F_f5fc4 D_f5fc4 (U argw) (Z_to_bv 64 1) Rarg0.      (* [comment removed for export] *)
      cldz F_f5fc8 D_f5fc8 (U tpw - 8)%Z dtvp Rdtvp.           (* [comment removed for export] *)
      cldz F_f5fcc D_f5fcc (U argw + 8)%Z offw Rarg8.          (* [comment removed for export] *)
      an F_f5fd0 D_f5fd0.                                      (* [comment removed for export] *)
      av F_f5fd4 D_f5fd4 (at_ dtvp 8) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, at_ in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      cldz F_f5fd8 D_f5fd8 (U dtvp + 8)%Z dtv1 Rdtv1.          (* [comment removed for export] *)
      an F_f5fdc D_f5fdc.                                      (* [comment removed for export] *)
      aret F_f5fe0 D_f5fe0 (at_ hb 18788).                     (* [comment removed for export] *)
      an F_60e90 D_60e90.                                      (* [comment removed for export] *)
      ab_ft F_60e94 D_60e94 ltac:(condz).                      (* [comment removed for export] *)
      an F_60e98 D_60e98.                                      (* [comment removed for export] *)
      an F_783b4 D_783b4.                                      (* [comment removed for export] *)
      fsd F_783b8 D_783b8 (at_ S (-40)).                      (* [comment removed for export] *)
      an F_783bc D_783bc.                                      (* [comment removed for export] *)
      eapply msteps_trans; [eapply AX|]; zlit_at.              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu; [exact F_70a3c | reflexivity | exact D_70a3c | ];
          gres; rwH; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 c_tsd : word) by addr_eq end;
          rd_thru Rtsdi
        | step_simpl]; vn.                                       (* [comment removed for export] *)
      ab_ft F_70a40 D_70a40 ltac:(vals_lit; condz).            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [exact F_70a44 | reflexivity | exact D_70a44
          | gres; rwH; imm_norm;
            lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 (c_tsd + 4) : word) by addr_eq end;
            rd_thru Rkey
          | apply bytes4_small; lia]
        | step_simpl]; vn.                                       (* [comment removed for export] *)
      rewrite ?(v_lw_small 0) by lia.
      eapply msteps_trans; [apply J831ac|].                    (* [comment removed for export] *)
      rewrite <- (at_0 pgs).
      an F_f7074 D_f7074.                                      (* [comment removed for export] *)
      cldz F_f7078 D_f7078 (U tpw - 88)%Z keysp Rkeys.         (* [comment removed for export] *)
      an F_f707c D_f707c.                                      (* [comment removed for export] *)
      an F_f7080 D_f7080.                                      (* [comment removed for export] *)
      av F_f7084 D_f7084 keysp ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned).   (* [comment removed for export] *)
      cldz F_f7088 D_f7088 (U keysp) Tw RT.                    (* [comment removed for export] *)
      aret F_f708c D_f708c (at_ hb 114324).                    (* [comment removed for export] *)
      ab_ft F_783c0 D_783c0 ltac:(condz).                      (* [comment removed for export] *)
      cldz F_783c4 D_783c4 (U Tw + 152)%Z Aw RA.               (* [comment removed for export] *)
      fld F_783c8 D_783c8 (at_ hb 18800).                      (* [comment removed for export] *)
      an F_783cc D_783cc.                                      (* [comment removed for export] *)
      aret F_783d0 D_783d0 (at_ hb 18800).                     (* [comment removed for export] *)
      ab_ft F_60e9c D_60e9c ltac:(condz).                      (* [comment removed for export] *)
      cldz F_60ea0 D_60ea0 (U Aw + 48)%Z tlsb Rtlsb.           (* [comment removed for export] *)
      cldz F_60ea4 D_60ea4 (U Aw + 56)%Z tlse Rtlse.           (* [comment removed for export] *)
      an F_60ea8 D_60ea8.                                      (* [comment removed for export] *)
      an F_60eb4 D_60eb4.                                      (* [comment removed for export] *)
      an F_60eb8 D_60eb8.                                      (* [comment removed for export] *)
      an F_60ebc D_60ebc.                                      (* [comment removed for export] *)
      an F_85ac8 D_85ac8.                                      (* [comment removed for export] *)
      fsd F_85acc D_85acc (at_ S (-40)).                      (* [comment removed for export] *)
      fsd F_85ad0 D_85ad0 (at_ S (-48)).                      (* [comment removed for export] *)
      fsd F_85ad4 D_85ad4 (at_ S (-56)).                      (* [comment removed for export] *)
      fsd F_85ad8 D_85ad8 (at_ S (-64)).                      (* [comment removed for export] *)
      fsd F_85adc D_85adc (at_ S (-72)).                      (* [comment removed for export] *)
      fsd F_85ae0 D_85ae0 (at_ S (-80)).                      (* [comment removed for export] *)
      fsd F_85ae4 D_85ae4 (at_ S (-88)).                      (* [comment removed for export] *)
      fsd F_85ae8 D_85ae8 (at_ S (-96)).                      (* [comment removed for export] *)
      fsd F_85aec D_85aec (at_ S (-104)).                     (* [comment removed for export] *)
      fsd F_85af0 D_85af0 (at_ S (-112)).                     (* [comment removed for export] *)
      fsd F_85af4 D_85af4 (at_ S (-120)).                     (* [comment removed for export] *)
      fsd F_85af8 D_85af8 (at_ S (-128)).                     (* [comment removed for export] *)
      fsd F_85afc D_85afc (at_ S (-136)).                     (* [comment removed for export] *)
      an F_85b00 D_85b00.                                      (* [comment removed for export] *)
      glk G1692e8 Rg_cf.                                       (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lbu; [exact F_85b0c | reflexivity | exact D_85b0c | ];
          gres; rwH; imm_norm;
          lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 (p_cf + 137) : word) by addr_eq end;
          rd_thru Ritga
        | step_simpl]; vn.                                       (* [comment removed for export] *)
      ab_ft F_85b10 D_85b10 ltac:(vals_lit; condz).            (* [comment removed for export] *)
      an F_85b14 D_85b14.                                      (* [comment removed for export] *)
      eapply msteps_trans; [eapply GX; rd_thru Rg_verb|]; zlit_at.          (* [comment removed for export] *)
      cldz F_85b20 D_85b20 (U argw) (Z_to_bv 64 1) Rarg0.      (* [comment removed for export] *)
      eapply msteps_trans; [apply GSa|]; zlit_at.              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [exact F_85b28 | reflexivity | exact D_85b28
          | gres; rwH; imm_norm;
            lazymatch goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 p_verb : word) by addr_eq end;
            rd_thru Rverb
          | apply bytes4_small; lia]
        | step_simpl]; vn.                                       (* [comment removed for export] *)
      rewrite ?(v_lw_small 0) by lia.
      eapply msteps_trans; [eapply GSl; [gres; reflexivity | rd_thru Rtlsd]|]; zlit_at.   (* [comment removed for export] *)
      an F_85b30 D_85b30.                                      (* [comment removed for export] *)
      av F_85b34 D_85b34 (at_ tpw 8) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, at_ in G in change_no_check G' end); unorm; f_equal; lia).   (* [comment removed for export] *)
      ab_ft F_85b38 D_85b38 ltac:(condz).                      (* [comment removed for export] *)
      cldz F_85b3c D_85b3c (U tpw + 8)%Z g12 Rg12.             (* [comment removed for export] *)
      an F_85b40 D_85b40.                                      (* [comment removed for export] *)
      afence F_85b44 D_85b44.
      ab_ft F_85b48 D_85b48 ltac:(condz).                      (* [comment removed for export] *)
      ab_tk F_85b4c D_85b4c ltac:(condz).                      (* [comment removed for export] *)
      ab_ft F_85bd0 D_85bd0 ltac:(condz).                      (* [comment removed for export] *)
      fsd F_85bd4 D_85bd4 (at_ S (-160)).                     (* [comment removed for export] *)
      fsd F_85bd8 D_85bd8 (at_ S (-152)).                     (* [comment removed for export] *)
      an F_85bdc D_85bdc.                                      (* [comment removed for export] *)
      ab_tk F_85be0 D_85be0 ltac:(condz).                      (* [comment removed for export] *)
      an F_85c90 D_85c90.                                      (* [comment removed for export] *)
      an F_85c94 D_85c94.                                      (* [comment removed for export] *)
      av F_85c98 D_85c98 (at_ g12 16) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add, at_ in G in change_no_check G' end); unorm; f_equal; lia).  (* [comment removed for export] *)
      cldz F_85c9c D_85c9c (U g12 + 24)%Z dbeg Rdbeg.          (* [comment removed for export] *)
      ab_ft F_85ca0 D_85ca0 ltac:(condz).                      (* [comment removed for export] *)
      an F_85ca4 D_85ca4.                                      (* [comment removed for export] *)
      fld F_85ca8 D_85ca8 (at_ hb 18836).                      (* [comment removed for export] *)
      fld F_85cac D_85cac argw.                                (* [comment removed for export] *)
      fld F_85cb0 D_85cb0 (v_add offw dtv1).                   (* [comment removed for export] *)
      fld F_85cb4 D_85cb4 (Z_to_bv 64 1).                      (* [comment removed for export] *)
      fld F_85cb8 D_85cb8 (getr r1 19).                        (* [comment removed for export] *)
      fld F_85cbc D_85cbc (getr r1 20).                        (* [comment removed for export] *)
      fld F_85cc0 D_85cc0 (getr r1 21).                        (* [comment removed for export] *)
      fld F_85cc4 D_85cc4 (getr r1 22).                        (* [comment removed for export] *)
      fld F_85cc8 D_85cc8 (getr r1 23).                        (* [comment removed for export] *)
      fld F_85ccc D_85ccc (getr r1 24).                        (* [comment removed for export] *)
      fld F_85cd0 D_85cd0 (getr r1 25).                        (* [comment removed for export] *)
      fld F_85cd4 D_85cd4 (getr r1 26).                        (* [comment removed for export] *)
      fld F_85cd8 D_85cd8 (getr r1 27).                        (* [comment removed for export] *)
      an F_85cdc D_85cdc.                                      (* [comment removed for export] *)
      aret F_85ce0 D_85ce0 (at_ hb 18836).                     (* [comment removed for export] *)
      an F_60ec0 D_60ec0.                                      (* [comment removed for export] *)
      fld F_60ec4 D_60ec4 ra.                                  (* [comment removed for export] *)
      fld F_60ec8 D_60ec8 (getr regs 8).                       (* [comment removed for export] *)
      fld F_60ecc D_60ecc (getr regs 9).                       (* [comment removed for export] *)
      fld F_60ed0 D_60ed0 (getr regs 18).                      (* [comment removed for export] *)
      an F_60ed4 D_60ed4.                                      (* [comment removed for export] *)
      aret F_60ed8 D_60ed8 ra.                                 (* [comment removed for export] *)
      wd_refl.
    - (lazymatch goal with |- ?G => let G' := eval unfold TM2, tai_mem, TM1 in G in change_no_check G' end). rewrite ?at_at. zlit_at.
      repeat (apply scr_rel_wb; [ | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ] | wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia | lia ]).
      apply scr_rel_refl.
    - post. (lazymatch goal with |- ?G => let G' := eval unfold TGB in G in change_no_check G' end). ra_solve.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem tlsga_run :
    exists r Mf,
      msteps segs (mkst regs (at_ hb 0) mem rom) (mkst r ra Mf rom)
      /\ scr_rel mem Mf (U S - 176) (U S)
      /\ getr r 10 = v_add offw dtv1 /\ getr r 1 = ra /\ getr r 2 = S
      /\ regs_agree (fun x => In x [10; 11; 12; 13]%list) regs r.
  Proof using H10 H4 H2 H1 Hret Hstk HS Hpcf Hcells Hdbeg Hg12 HAnz HTnz Rdbeg Rg12 Rtlsd Rverb Rg_verb Ritga Rg_cf Rtlse Rtlsb RA RT Rkeys Rkey Rtsdi Rdtv1 Rdtvp Rarg8 Rarg0 Rrtga Rinit dbeg g12 tlse tlsb Aw Tw keysp dtvp tpw argw Hpgs Htga Hhb GS169320 G169308 G1692e8 J831ac A8318c G18613 TAI HC_PGS HC_TGA HC_DT HC_TS HC_CT HC_IC HC_TH c_tlsd p_verb g_verb p_cf g_cf c_tsd c_rtga c_inited pgs tga.
    pose proof (u64_range S) as HSr. destruct Hhb as [Hb2 Hb64]. pose proof (u64_range hb) as Hhr.
    assert (RT18613 : ret_ok (at_ hb 18768)) by (apply ret_ok_at; [exact Hb2 | reflexivity | lia]).
    destruct blkTA as (r0 & RUN0 & A1 & A2 & A8 & A4 & AG0).
    assert (C0 : (0 <= c_inited /\ c_inited + 1 <= U S - 176)%Z).
    { pose proof Hcells as HC. unfold tg_cells in HC. apply Forall_cons_iff in HC. destruct HC as [X _]. cbn [fst snd] in X. exact X. }
    assert (SP0 : U (getr r0 2) = (U S - 32)%Z) by (rewrite A2, at_u by lia; lia).
    destruct (TAI r0 TM1 rom (at_ hb 18768)) as (r1 & RUN1 & B10 & BK).
    { (lazymatch goal with |- ?G => let G' := eval unfold TM1 in G in change_no_check G' end). repeat (rewrite wd_rdn_wbytes_out3; [ | rd8_side ]). exact Rinit. }
    { exact RT18613. }
    { exact A1. }
    { lia. }
    { left. rewrite SP0. lia. }
    { rewrite SP0. lia. }
    { rewrite SP0. lia. }
    { rewrite A2, at_at. zlit_at. (lazymatch goal with |- ?G => let G' := eval unfold TM1 in G in change_no_check G' end). repeat (eapply store_ok_mono; [apply wbytes_grows|]).
      eapply (store_ok_sub segs mem (at_ S (-176)) _ 176); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia]. }
    rewrite A2, A8 in RUN1. fold TM2 in RUN1.
    assert (B2 : getr r1 2 = at_ S (-32)) by (rewrite (BK 2) by (intros E; discriminate E); exact A2).
    assert (B8 : getr r1 8 = argw) by (rewrite (BK 8) by (intros E; discriminate E); exact A8).
    assert (B4 : getr r1 4 = tpw) by (rewrite (BK 4) by (intros E; discriminate E); exact A4).
    destruct (blkTB r1 B10 B2 B8 B4) as (r & Mf & RUN2 & SR & E10 & E1 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & AG2).
    exists r, Mf. split; [|split; [exact SR | split; [exact E10 | split; [exact E1 | split; [exact E2|]]]]].
    - eapply msteps_trans; [exact RUN0|]. eapply msteps_trans; [exact RUN1 | exact RUN2].
    - intros x Hx.
      destruct (In_dec (fun a b : reg => decide (a = b)) x TGB) as [I|NI].
      + (* [comment removed for export] *)
        unfold TGB in I. cbn [In] in I.
        assert (K01 : forall y : reg, y <> 10 -> y <> 11 -> y <> 1 -> y <> 2 -> y <> 8 -> getr r1 y = getr regs y).
        { intros y N10 N11 N1 N2 N8. rewrite (BK y N10 N11). apply AG0. (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). intros [E|[E|[E|[]]]]; [apply N1 | apply N2 | apply N8]; symmetry; exact E. }
        repeat (destruct I as [<-|I];
                [ first [ rewrite E1; symmetry; exact H1 | rewrite E2; symmetry; exact H2 | exact E8 | exact E9 | exact E18
                        | exfalso; apply Hx; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]
                        | rewrite E19; apply K01; intros E; discriminate E | rewrite E20; apply K01; intros E; discriminate E
                        | rewrite E21; apply K01; intros E; discriminate E | rewrite E22; apply K01; intros E; discriminate E
                        | rewrite E26; apply K01; intros E; discriminate E ] |]).
        destruct I.
      + rewrite (AG2 x NI).
        assert (N10 : x <> 10) by (intros ->; apply NI; (lazymatch goal with |- ?G => let G' := eval unfold TGB in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]).
        assert (N11 : x <> 11) by (intros ->; apply NI; (lazymatch goal with |- ?G => let G' := eval unfold TGB in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]).
        rewrite (BK x N10 N11). apply AG0. intros I0. apply NI. (lazymatch goal with |- ?G => let G' := eval unfold TGB in G in change_no_check G' end). cbn [In] in I0 |- *. first [ solve [clear - I0; tauto] | tauto ].
  Qed.
End TLSGA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record tlsga_tab := TGT { tg_hb : word; tg_tga : word; tg_pgs : word;
  tg_c_inited : Z; tg_c_rtga : Z; tg_c_tsd : Z; tg_g_cf : Z; tg_p_cf : Z; tg_g_verb : Z; tg_p_verb : Z; tg_c_tlsd : Z }.

Definition tlsga_tab_ok (segs : list Segment) (t : tlsga_tab) : Prop :=
  let hb := tg_hb t in
  code_ato segs hb 0 tgth_words /\ code_ato segs hb 18740 tgic_words /\ code_ato segs hb 114312 tgct_words
  /\ code_ato segs hb 83208 tgts_words /\ code_ato segs hb 169372 tgdt_words
  /\ code_ato segs (tg_tga t) 0 mtga_words /\ code_ato segs (tg_pgs t) 0 mpgs_words
  /\ try_asan_init_call segs (at_ hb 104072) (tg_c_inited t)
  /\ gload segs hb 18768 11 (tg_c_rtga t) /\ gaddr2 segs hb 83208 10 10 (Z_to_bv 64 (tg_c_tsd t)) /\ gjump segs hb 83228 (tg_pgs t)
  /\ gload segs hb 169432 11 (tg_g_cf t) /\ gload2 segs hb 169452 10 26 (tg_g_verb t)
  /\ gauipc_ld segs hb 169464 169472 10 21 (tg_c_tlsd t)
  /\ ((U hb mod 2 = 0)%Z /\ (U hb + 180000 < 2 ^ 64)%Z)
  /\ ret_ok (tg_tga t)
  /\ ((U (tg_pgs t) mod 2 = 0)%Z /\ (U (tg_pgs t) + 64 < 2 ^ 64)%Z)
  /\ (0 <= tg_p_cf t)%Z.

(* [comment removed for export] *)
Record tlsga_vals := TGV { tv_arg : word; tv_tp : word; tv_off : word; tv_dtvp : word; tv_dtv1 : word; tv_keysp : word;
  tv_T : word; tv_A : word; tv_tlsb : word; tv_tlse : word; tv_g12 : word; tv_dbeg : word }.

(* [comment removed for export] *)
Definition tg_reads (t : tlsga_tab) (v : tlsga_vals) : list (Z * nat * list byte) :=
  [ (tg_c_inited t, 1%nat, [Z_to_bv 8 1]);
    (tg_c_rtga t, 8%nat, W8 (tg_tga t));
    (U (tv_arg v), 8%nat, W8 (Z_to_bv 64 1));
    (U (tv_arg v) + 8, 8%nat, W8 (tv_off v));
    (U (tv_tp v) - 8, 8%nat, W8 (tv_dtvp v));
    (U (tv_dtvp v) + 8, 8%nat, W8 (tv_dtv1 v));
    (tg_c_tsd t, 1%nat, [Z_to_bv 8 1]);
    (tg_c_tsd t + 4, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 0));
    (U (tv_tp v) - 88, 8%nat, W8 (tv_keysp v));
    (U (tv_keysp v), 8%nat, W8 (tv_T v));
    (U (tv_T v) + 152, 8%nat, W8 (tv_A v));
    (U (tv_A v) + 48, 8%nat, W8 (tv_tlsb v));
    (U (tv_A v) + 56, 8%nat, W8 (tv_tlse v));
    (tg_g_cf t, 8%nat, W8 (Z_to_bv 64 (tg_p_cf t)));
    (tg_p_cf t + 137, 1%nat, [Z_to_bv 8 1]);
    (tg_g_verb t, 8%nat, W8 (Z_to_bv 64 (tg_p_verb t)));
    (tg_p_verb t, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 0));
    (tg_c_tlsd t, 8%nat, W8 (Z_to_bv 64 8));
    (U (tv_tp v) + 8, 8%nat, W8 (tv_g12 v));
    (U (tv_g12 v) + 24, 8%nat, W8 (tv_dbeg v)) ]%Z.

(* [comment removed for export] *)
Definition tlsgaH (segs : list Segment) (t : tlsga_tab) (mem : word -> option byte) (S : word) (v : tlsga_vals) : Prop :=
  Forall (fun c => (0 <= fst (fst c))%Z /\ (fst (fst c) + Z.of_nat (snd (fst c)) <= U S - 176)%Z
                   /\ rdn segs mem (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (snd c)) (tg_reads t v)
  /\ U (tv_T v) <> 0%Z /\ U (tv_A v) <> 0%Z /\ (U (tv_g12 v) <> 0%Z /\ U (tv_g12 v) <> (2 ^ 64 - 1)%Z) /\ U (tv_dbeg v) <> 0%Z
  /\ (176 <= U S)%Z
  /\ store_ok segs mem (at_ S (-176)) 176 = true.

(* [comment removed for export] *)
Definition tg_res (v : tlsga_vals) : word := v_add (tv_off v) (tv_dtv1 v).

Theorem tlsga_run_t : forall segs t, tlsga_tab_ok segs t ->
  forall mem rom (ra S : word) v regs,
  tlsgaH segs t mem S v -> ret_ok ra ->
  getr regs 1 = ra -> getr regs 2 = S -> getr regs 4 = tv_tp v -> getr regs 10 = tv_arg v ->
  exists r Mf,
    msteps segs (mkst regs (tg_hb t) mem rom) (mkst r ra Mf rom)
    /\ scr_rel mem Mf (U S - 176) (U S)
    /\ getr r 10 = tg_res v /\ getr r 1 = ra /\ getr r 2 = S
    /\ regs_agree (fun x => In x [10; 11; 12; 13]%list) regs r.
Proof using.
  intros segs t TOK mem rom ra S v regs (RD & NT & NA & NG & ND & HS & STK) Hret H1 H2 H4 H10.
  destruct t as [hb tga pgs c_inited c_rtga c_tsd g_cf p_cf g_verb p_verb c_tlsd].
  destruct v as [argw tpw offw dtvp dtv1 keysp Tw Aw tlsb tlse g12 dbeg].
  unfold tlsga_tab_ok, tg_reads, tg_res in *.
  cbn [tg_hb tg_tga tg_pgs tg_c_inited tg_c_rtga tg_c_tsd tg_g_cf tg_p_cf tg_g_verb tg_p_verb tg_c_tlsd
       tv_arg tv_tp tv_off tv_dtvp tv_dtv1 tv_keysp tv_T tv_A tv_tlsb tv_tlse tv_g12 tv_dbeg] in *.
  destruct TOK as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & TAI & G1 & A1 & J1 & G2 & G3 & GS & HB & RTG & HP & PCF).
  repeat match type of RD with Forall _ (_ :: _) => apply Forall_cons_iff in RD; destruct RD as [? RD] end.
  cbn [fst snd] in *.
  repeat match goal with H : _ /\ _ /\ rdn _ _ _ _ = _ |- _ => let a := fresh "B" in let b := fresh "B" in let c := fresh "R" in destruct H as (a & b & c) end.
  replace (mkst regs hb mem rom) with (mkst regs (at_ hb 0) mem rom) by (rewrite at_0; reflexivity).
  eapply (tlsga_run segs hb tga pgs c_inited c_rtga c_tsd g_cf p_cf g_verb p_verb c_tlsd C1 C2 C3 C4 C5 C6 C7 TAI G1 A1 J1 G2 G3 GS HB RTG HP
            mem rom ra S argw tpw offw dtvp dtv1 keysp Tw Aw tlsb tlse g12 dbeg); try eassumption.
  (lazymatch goal with |- ?G => let G' := eval unfold tg_cells in G in change_no_check G' end). repeat (apply Forall_cons; [(lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia|]). apply Forall_nil.
Qed.

(* [comment removed for export] *)
Lemma tlsgaH_above : forall segs t mem M' (S : word) v,
  tlsgaH segs t mem S v -> mem_grows mem M' -> (forall a : word, (U a < U S)%Z -> M' a = mem a) ->
  tlsgaH segs t M' S v.
Proof using.
  intros segs t mem M' S v (RD & REST) GR EQ. pose proof (u64_range S) as HSr.
  split; [|destruct REST as (NT & NA & NG & ND & HS & STK); repeat (split; [assumption|]); eapply store_ok_mono; [exact GR | exact STK]].
  eapply Forall_impl; [|exact RD]. intros [[c n] bs] (B1 & B2 & R). cbn [fst snd] in *. split; [exact B1|]. split; [exact B2|].
  rewrite (rdn_ext segs n M' mem (Z_to_bv 64 c)); [exact R | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; intros x Hx; apply EQ; lia].
Qed.
(* [comment removed for export] *)
Lemma tlsgaH_mrestrict : forall segs t (Hd : word -> bool) mem (S : word) v,
  tlsgaH segs t mem S v ->
  Forall (fun c => hid_off Hd (fst (fst c)) (Z.of_nat (snd (fst c)))) (tg_reads t v) -> hid_off Hd (U S - 176) 176 ->
  tlsgaH segs t (mrestrict Hd mem) S v.
Proof using.
  intros segs t Hd mem S v (RD & NT & NA & NG & ND & HS & STK) HC HSC. pose proof (u64_range S) as HSr.
  split; [|repeat (split; [assumption|]); rewrite store_ok_mrestrict; [exact STK | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HSC]].
  revert HC. induction RD as [|[[c n] bs] l (B1 & B2 & R) RD IH]; intros HC; [constructor|].
  apply Forall_cons_iff in HC. destruct HC as [HC1 HC]. cbn [fst snd] in *.
  constructor; [|exact (IH HC)]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). split; [exact B1|]. split; [exact B2|].
  rewrite rdn_mrestrict; [exact R | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact HC1].
Qed.
End FPGen1.
