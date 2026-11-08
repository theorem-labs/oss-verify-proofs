(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from projects/fast_float/from_chars/proofs/lib/TopHaltsA.v and its sibling
   TopHaltsB.v at commit c395a1e0dfa, lines 4-6 (the Stdlib/LPS import block), lines 14-15 (lim_source_le_target,
   verbatim) and lines 17-19 of each (the halts_allowed_T_scfg_budgets theorem statement), with from_chars's Asan and
   AsanUbsan images replaced by this harness's Plain and Ubsan, SpecHalts.HALT_CODES by this tree's HALT_CODES, and the
   theorem names by halts_skcms_iccprofile_info_plain and _ubsan.  The proof bodies are not copied: from_chars's single
   halts_allowed_lowered_of_realizes call is replaced here by HaltsBridge.halts_of_realizes_spec for the plain build and
   by must_exit_of_realizes_spec composed with Halts.Lim.LimTransfer.lim_transfer_scfg for the UBSan build. *)
(** The halting theorems of this harness, in the form [Statements.v] states them.

    The plain build's realization is proved at 16 GiB already, so its halting
    theorem is the walk of [HaltsBridge] and nothing else.  The UBSan build's
    realization is proved at 512 GiB (it is the TARGET of the ubsan pair), and
    [Statements.ubsan_halts] asks for 16 GiB, so the walk is followed by the
    budget transfer of [Halts.Lim.LimTransfer]: a run that must exit at the
    larger budget must exit at the smaller one on every input the smaller
    budget never refuses, which is exactly the statement's own premise. *)

From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import ProofInfoPlan ProofInfoTop.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts Require Import SpecHalts HaltsBridge.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Halts.Lim Require Import LimTransfer.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lim_source_le_target : (ShippedBudgets.lim_source <= target_alloc_limit)%Z.
Proof. vm_compute. discriminate. Qed.

Theorem halts_skcms_iccprofile_info_plain :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HALT_CODES
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Proof.
  exact (halts_of_realizes_spec Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs
           source_alloc_limit info_ref_realizes).
Qed.

Theorem halts_skcms_iccprofile_info_ubsan :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source HALT_CODES
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros en inp Hen Hinp Hbud.
  exact (lim_transfer_scfg forced_only_cfg HALT_CODES
           (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs) en inp
           ShippedBudgets.lim_source target_alloc_limit lim_source_le_target
           (must_exit_of_realizes_spec Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
              target_alloc_limit info_ub_realizes en inp Hen Hinp)
           Hbud).
Qed.
