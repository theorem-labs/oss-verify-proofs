(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import RealizesAbort RealizesHalts.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.LimBridge Require Import LimHalts.
From OSSVerify.Proofs.fast_float.from_chars.lib Require SpecHalts TopBothH.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require TopBothF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lim_source_le_target : (ShippedBudgets.lim_source <= target_alloc_limit)%Z.
Proof. vm_compute. discriminate. Qed.

Theorem halts_both :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source SpecHalts.HALT_CODES
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  exact (halts_allowed_lowered_of_realizes FXDB.TopBothF.DCFG _ _ _ ShippedBudgets.lim_source target_alloc_limit SpecHalts.HALT_CODES SpecHalts.SPECH
           lim_source_le_target (FXDB.TopBothF.both_realizes_D TopBothH.Hleaves) SpecHalts.spec_exits_in_SPECH SpecHalts.no_kill_SPECH).
Qed.
