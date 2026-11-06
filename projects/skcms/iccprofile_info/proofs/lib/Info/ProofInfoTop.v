(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec ShapeAlg ProofInfoPlan ProofInfoRows ProofInfoLib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefMain UbMain RefDriver UbDriver
  RefTargetPhase RefTargetPhaseK UbTargetPhase UbTargetPhaseK RefLim.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fp0.

Lemma info_ref_realizes_lim (AL : RefLim.AllocLim) : realizes_spec_stmt SSEGS SPC SPH (@RefLim.LIM AL).
Proof.
  exact (@RefMain.ref_realizes_spec AL
           (@RefDriver.ref_main_phase AL (RefTargetPhase.target_phase fuzz_contract_src1)
                                         (RefTargetPhaseK.target_phase_k fuzz_contract_src1))).
Qed.

Theorem info_ref_realizes : realizes_spec_stmt SSEGS SPC SPH source_alloc_limit.
Proof. exact (info_ref_realizes_lim RefLim.SrcLim). Qed.

Theorem info_ref_realizes_san : realizes_spec_stmt SSEGS SPC SPH SanitizerBudgets.lim_source.
Proof. exact (info_ref_realizes_lim RefLim.SanLim). Qed.

Theorem info_ub_realizes : realizes_spec_stmt TSEGS TPC TPH target_alloc_limit.
Proof.
  exact (UbMain.ub_realizes_spec
           (UbDriver.ref_main_phase (UbTargetPhase.target_phase fuzz_contract_infoub)
                                   (UbTargetPhaseK.target_phase_k fuzz_contract_infoub))).
Qed.

(* [comment removed for export] *)
Theorem info_ubsan :
  strong_universal_error_free_T_scfg CFG (mkImage SSEGS SPC SPH) (mkImage TSEGS TPC TPH).
Proof. exact (info_ubsan_scfg info_ref_realizes info_ub_realizes). Qed.

(* [comment removed for export] *)
Theorem info_ubsan_ca_iff : forall (C : Image),
  (forall inp en, valid_input inp -> valid_entry C en inp ->
     must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp) ->
  classifies_good_inputs_T_s CFG (mkImage SSEGS SPC SPH) (mkImage TSEGS TPC TPH) C.
Proof. exact (ca_iff_info_ubsan info_ref_realizes info_ub_realizes). Qed.

(* [comment removed for export] *)
Theorem info_ubsan_cb_iff : forall (C : Image),
  (forall inp en, valid_input inp -> valid_entry C en inp ->
     must_exit_with_scfg forced_only_cfg verdict_accept C classifier_alloc_limit en inp) ->
  classifies_patch_diff_T_s CFG (mkImage SSEGS SPC SPH) (mkImage SSEGS SPC SPH)
                                (mkImage TSEGS TPC TPH) (mkImage TSEGS TPC TPH) C.
Proof. exact (cb_iff_info_ubsan info_ref_realizes info_ub_realizes). Qed.
