(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/fast_float/from_chars/proofs/lib/TopHaltsA.v and its sibling
   TopHaltsB.v at commit c395a1e0dfa, lines 4-6 (the Stdlib/LPS import block), lines 14-15 (lim_source_le_target,
   verbatim) and lines 17-19 of each (the halts_allowed_T_scfg_budgets theorem statement), with from_chars's Asan and
   AsanUbsan images replaced by this harness's Plain and Ubsan, SpecHalts.HALT_CODES by this tree's HALT_CODES, and the
   theorem names by halts_skcms_iccprofile_info_plain and _ubsan.  The proof bodies are not copied: from_chars's single
   halts_allowed_lowered_of_realizes call is replaced here by HaltsBridge.halts_of_realizes_spec for the plain build and
   by must_exit_of_realizes_spec composed with Halts.Lim.LimTransfer.lim_transfer_scfg for the UBSan build. *)
(* Modified by gabelogan195, 2026-11: made from projects/skcms/iccprofile_info/proofs/lib/Halts/HaltsTops.v at commit
   f92feaf8b7e, lines 20-26 (the import block) and 40-51 (halts_skcms_iccprofile_info_ubsan), restated for the ASan and
   ASan+UBSan images as halts_skcms_iccprofile_info_asan and _asan_ubsan, with lim_source_le_target used from HaltsTops
   rather than copied; and from HaltsBridge.v at the same commit, lines 144-164 (must_exit_of_realizes_spec), restated as
   must_exit_of_srealizes for a realization in Asan.SpinAlgCfg.srealizes_cfg, which the new lemma srealizes_info reads as
   an Info.ShapeAlg.realizes; the realizations are Asan.InfoAsanTop.info_asan_tgt_C and Asan.InfoBothTop.info_both_tgt_C,
   closed with the certificates Asan.InfoAsanClosed and Asan.InfoBothClosed close the agreement theorems with. *)
(** The halting theorems of the ASan and ASan+UBSan builds, in the form [Statements.v] states them.

    Each build's realization is the one its agreement theorem is proved from: [srealizes_cfg] of [spec], at the
    target budget (512 GiB), on every valid entry and input, with no budget premise.  [srealizes_cfg] has no
    spinning leaf ([Asan.SpinAlgCfg]), so it is an [Info.ShapeAlg.realizes] and the walk of [HaltsBridge] applies
    to it.  [Statements.asan_halts] and [Statements.asan_ubsan_halts] ask for 16 GiB, so the walk is followed by
    the budget transfer of [Halts.Lim.LimTransfer]: a run that must exit at the larger budget must exit at the
    smaller one on every input the smaller budget never refuses, which is exactly the statements' own premise. *)

From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require ShapeAlg Spec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsLibFuzz BoLibFuzz.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require SpinAlgCfg AsanSpec InfoAsanTop InfoAsanFinal InfoBothTop
  InfoBothFinal AsanMainForest AsanMainForestBoth AsanMainCertKWClosed AsanMainCertKWClosedBoth.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts Require Import SpecHalts HaltsBridge.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts Require HaltsTops.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.Lim Require Import LimTransfer.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module IS := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ShapeAlg.
Module ISpec := OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Spec.
Module SC := OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan.SpinAlgCfg.
Module ASpec := OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan.AsanSpec.

(** [SC.srealizes_cfg] and [IS.realizes] have the same three constructors, over the same node relation. *)
Lemma srealizes_info : forall segs c (T : IS.TSet), SC.srealizes_cfg segs c T -> IS.realizes segs c T.
Proof.
  intros segs c T H.
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exact (IS.rz_node segs c I evs nx T i0 Hnode IH).
  - exact (IS.rz_halt segs c Hh).
  - exact (IS.rz_conseq segs c T T' IH Heq).
Qed.

(** From a realization of [spec] at [lim], on every valid entry and input, to [must_exit_in_scfg] at [lim]. *)
Theorem must_exit_of_srealizes : forall segs pc ph lim,
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     match en with
     | mkEntry sp brk0 mbase rnd =>
         SC.srealizes_cfg segs (init_config segs pc ph sp brk0 mbase rnd lim inp) (ASpec.spec (in_argv inp) (in_fs inp))
     end) ->
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
    must_exit_in_scfg forced_only_cfg HALT_CODES (mkImage segs pc ph) lim en inp.
Proof.
  intros segs pc ph lim HT [sp brk0 mbase rnd] inp Hen Hinp.
  pose proof (HT (mkEntry sp brk0 mbase rnd) inp Hen Hinp) as HR. cbv beta iota in HR.
  cbn [must_exit_in_scfg].
  apply (must_exit_in_at_cfg_mono_classic forced_only_cfg IS.CFG segs HALT_CODES _
           (forced_only_cfg_least IS.CFG)).
  apply (realizes_must_exit_in segs HALT_CODES _ (ISpec.spec (in_argv inp) (in_fs inp))).
  - apply (IS.rz_conseq segs _ (ASpec.spec (in_argv inp) (in_fs inp))).
    + exact (srealizes_info _ _ _ HR).
    + intros tr. exact (iff_sym (InfoAsanTop.spec_bridge (in_argv inp) (in_fs inp) tr)).
  - cbn [init_config cfg_model]. reflexivity.
  - exact (exits_in_spec (in_argv inp) (in_fs inp)).
  - exact (kill_free_spec (in_argv inp) (in_fs inp)).
Qed.

(** The realization of the ASan build at 512 GiB, closed as [Asan.InfoAsanClosed] closes its agreement theorem. *)
Lemma asan_tgt : InfoAsanTop.asan_tgt_stmt.
Proof.
  exact (InfoAsanTop.info_asan_tgt_C AsLibFuzz.as_fuzz_closed
           (InfoAsanFinal.info_asan_certs (AsanMainForest.TREE AsanMainCertKWClosed.KWT)
              (AsanMainForest.TREES AsanMainCertKWClosed.KWT AsanMainCertKWClosed.KW_ok))).
Qed.

(** The realization of the ASan+UBSan build at 512 GiB, closed as [Asan.InfoBothClosed] closes its agreement theorem. *)
Lemma both_tgt : InfoBothTop.asan_tgt_stmt.
Proof.
  exact (InfoBothTop.info_both_tgt_C BoLibFuzz.as_fuzz_closed
           (InfoBothFinal.info_both_certs (AsanMainForestBoth.TREE AsanMainCertKWClosedBoth.KWT)
              (AsanMainForestBoth.TREES AsanMainCertKWClosedBoth.KWT AsanMainCertKWClosedBoth.KW_ok))).
Qed.

Theorem halts_skcms_iccprofile_info_asan :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HALT_CODES
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
  intros en inp Hen Hinp Hbud.
  exact (lim_transfer_scfg forced_only_cfg HALT_CODES
           (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs) en inp
           ShippedBudgets.lim_source target_alloc_limit HaltsTops.lim_source_le_target
           (must_exit_of_srealizes Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs
              target_alloc_limit asan_tgt en inp Hen Hinp)
           Hbud).
Qed.

Theorem halts_skcms_iccprofile_info_asan_ubsan :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HALT_CODES
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  intros en inp Hen Hinp Hbud.
  exact (lim_transfer_scfg forced_only_cfg HALT_CODES
           (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs) en inp
           ShippedBudgets.lim_source target_alloc_limit HaltsTops.lim_source_le_target
           (must_exit_of_srealizes AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs
              target_alloc_limit both_tgt en inp Hen Hinp)
           Hbud).
Qed.
