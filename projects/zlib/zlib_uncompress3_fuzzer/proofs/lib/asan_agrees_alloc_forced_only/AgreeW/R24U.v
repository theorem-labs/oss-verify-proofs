From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress3_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress3_fuzzer_asan.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* p2425-w 2026-11-19, pair 24 (uncompress3 ASan) with UNPATCHED originals: R29U.head.v (an earlier development run, frozen 6d57ad8d)
   by exact substitutions (p2425-w u119_mk_agree24_r1.py). x1_srco_tgt / x2_src_tgto: the two cross agreements, each the
   package's own base lemma (BaseAsanU3.base_asan_plain_u3) in a JOIN copy at the mixed images: X1W (SrcO plain, published
   Tgt) and X2W (published Src, TgtO asan). ca_iff / cb_iff: the accept-all rows of the pair at its unpatched originals. *)
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.BaseAsanU3.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.BaseAsanU3.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.BaseAsanU3.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.BaseAsanU3.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress3_fuzzer_asan.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AgreeW.AgreeCross.

Theorem x1_srco_tgt :
  strong_universal_error_free_T_scfg alloc_forced_cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.BaseAsanU3.base_asan_plain_u3.
Qed.

Theorem x2_src_tgto :
  strong_universal_error_free_T_scfg alloc_forced_cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.BaseAsanU3.base_asan_plain_u3.
Qed.

Lemma ca_iff : forall cfg,
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.phdrs) ->
  LinuxProcessSemantics.EquivalenceDefinition.Classifier.classifies_good_inputs_T_s cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Cla_zlib_uncompress3_fuzzer_asan.M.phdrs).
Proof.
  intros cfg T.
  exact (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Cls.AcceptAllGeneric.classifies_of_accepts_all cfg _ _ _ T
           OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress3_fuzzer_asan.cla_accepts_all).
Qed.

Lemma cb_iff : forall cfg,
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.phdrs) ->
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.phdrs) ->
  strong_universal_error_free_T_scfg cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.phdrs) ->
  LinuxProcessSemantics.EquivalenceDefinition.Classifier.classifies_patch_diff_T_s cfg
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Src_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.TgtO_zlib_uncompress3_fuzzer_asan.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Tgt_zlib_uncompress3_fuzzer_asan.M.phdrs)
    (mkImage OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.loaded_segments
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.init_pc
             OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World.Clb_zlib_uncompress3_fuzzer_asan.M.phdrs).
Proof.
  intros cfg X1 B X2.
  exact (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AgreeW.AgreeCross.cb_iff_of_cross cfg _ _ _ _ _ X1 B X2
           OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress3_fuzzer_asan.src_brk
           OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress3_fuzzer_asan.tgt_brk
           OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress3_fuzzer_asan.clb_accepts_all).
Qed.
