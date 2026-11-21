(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress2_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ShapeAlg ShapeEF Spec S7LibStmt U7LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO Require Import FOCore.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker port727, as a worker's Thm_uncompress3_halts (A1) *)

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP7 Require S7MainHs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP7 Require U7MainHs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* pair 23 (uncompress2 UBSan) with UNPATCHED originals, in the FROZEN form of R29U.head.v ().
   x1_srco_tgt / x2_src_tgto: the two cross agreements, each by thm_of_lib's own proof (copied by the maker from
   Thm_uncompress2_ubsan_mr.v) with ONE realization taken from the unpatched closure UnpW. Both realizations state the
   same harness spec. ca_iff / cb_iff: the accept-all rows of the pair at its unpatched originals. *)
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_zlib_uncompress2_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_zlib_uncompress2_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_TopI.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U.T_TopI.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP7.S7MainHs.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP7.U7MainHs.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I7SW.S_TopI.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I7U.T_TopI.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress2_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.AgreeW.AgreeCross.

Theorem x1_srco_tgt :
  strong_universal_error_free_T_scfg alloc_forced_cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress2_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress2_fuzzer_ubsan.M.phdrs).
Proof.
  (* [comment removed for export] *)
  intros [rsp rbrk rmb rdraw] [asp abrk amb adraw] inp Hens Hent Hvalid.
  (* [comment removed for export] *)
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfits]]]. destruct Hent as [Hasp [Habrk [Hamb Hafits]]].
  destruct Hvalid as [Hargv [Henvp [Hfs Hrest]]].
  apply (shape_strong_equiv_ef _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
  - (* a worker port727, as a worker's Thm_uncompress3_halts: the 727 launch premises *)
    assert (Hvl : valid_launch inp) by (decompose [and] Hrest; assumption).
    assert (Hcr : in_channel_reader inp = true) by (decompose [and] Hrest; assumption).
    exact (OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP7.S7MainHs.s7_realizes_spec_hs (@OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I7SW.S_TopI.zlib_contract_S7)
             rsp rbrk rmb rdraw inp Hrsp Hrbrk Hargv Henvp Hfs Hvl (proj2 Hrfits) Hcr).
  - assert (Hvl : valid_launch inp) by (decompose [and] Hrest; assumption).
    assert (Hcr : in_channel_reader inp = true) by (decompose [and] Hrest; assumption).
    exact (OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP7.U7MainHs.u7_realizes_spec_hs (@OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U.T_TopI.zlib_contract_U7)
             asp abrk amb adraw inp Hasp Habrk Hargv Henvp Hfs Hvl (proj2 Hafits) Hcr).
Qed.

Theorem x2_src_tgto :
  strong_universal_error_free_T_scfg alloc_forced_cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.phdrs).
Proof.
  (* [comment removed for export] *)
  intros [rsp rbrk rmb rdraw] [asp abrk amb adraw] inp Hens Hent Hvalid.
  (* [comment removed for export] *)
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfits]]]. destruct Hent as [Hasp [Habrk [Hamb Hafits]]].
  destruct Hvalid as [Hargv [Henvp [Hfs Hrest]]].
  apply (shape_strong_equiv_ef _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
  - (* a worker port727, as a worker's Thm_uncompress3_halts: the 727 launch premises *)
    assert (Hvl : valid_launch inp) by (decompose [and] Hrest; assumption).
    assert (Hcr : in_channel_reader inp = true) by (decompose [and] Hrest; assumption).
    exact (OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP7.S7MainHs.s7_realizes_spec_hs (@OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S.S_TopI.zlib_contract_S7)
             rsp rbrk rmb rdraw inp Hrsp Hrbrk Hargv Henvp Hfs Hvl (proj2 Hrfits) Hcr).
  - assert (Hvl : valid_launch inp) by (decompose [and] Hrest; assumption).
    assert (Hcr : in_channel_reader inp = true) by (decompose [and] Hrest; assumption).
    exact (OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP7.U7MainHs.u7_realizes_spec_hs (@OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I7U.T_TopI.zlib_contract_U7)
             asp abrk amb adraw inp Hasp Habrk Hargv Henvp Hfs Hvl (proj2 Hafits) Hcr).
Qed.

Lemma ca_iff : forall cfg,
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.phdrs) ->
  LinuxProcessSemantics.EquivalenceDefinition.Classifier.classifies_good_inputs_T_s cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_zlib_uncompress2_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Cla_zlib_uncompress2_fuzzer_ubsan.M.phdrs).
Proof.
  intros cfg T.
  exact (OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.classifies_of_accepts_all cfg _ _ _ T
           OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress2_fuzzer_ubsan.cla_accepts_all).
Qed.

Lemma cb_iff : forall cfg,
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress2_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress2_fuzzer_ubsan.M.phdrs) ->
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress2_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress2_fuzzer_ubsan.M.phdrs) ->
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.phdrs) ->
  LinuxProcessSemantics.EquivalenceDefinition.Classifier.classifies_patch_diff_T_s cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress2_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress2_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress2_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress2_fuzzer_ubsan.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress2_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress2_fuzzer_ubsan.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_zlib_uncompress2_fuzzer_ubsan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_zlib_uncompress2_fuzzer_ubsan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Clb_zlib_uncompress2_fuzzer_ubsan.M.phdrs).
Proof.
  intros cfg X1 B X2.
  exact (OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.AgreeW.AgreeCross.cb_iff_of_cross cfg _ _ _ _ _ X1 B X2
           OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress2_fuzzer_ubsan.src_brk
           OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress2_fuzzer_ubsan.tgt_brk
           OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress2_fuzzer_ubsan.clb_accepts_all).
Qed.
