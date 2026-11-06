(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/A/CfFreeBranchWitPreset.v, with its module paths changed. *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane, DeallocNmaxA): free_cf's two branches (its size test, Quarantine::Put) at preset's
   OWN instance, CfParams_preset (A/CfParamsPreset.v:93-98, cf_malloc_max = 2 ^ 28 + 2 ^ 27) and CfImg_A: the generic
   witnesses of Reusable/YGcfFreeBranchWit.v instantiated, each with its equation closed by reflexivity.
   - preset_A_free_cf_enqueue_witness: from init_state, a granted malloc_cf (2 ^ 28) then free_cf on it takes the
     enqueue side (the chunk's size test is true; the free path asks a class-24 batch map);
   - preset_A_free_cf_recycle_witness: the same at 2 ^ 28 + 1 takes the recycle side (the test is false; no map).
   Nothing here is a function's proof (rule 24). No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfFreeBranchWit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfImgA CfParamsPreset.

Lemma preset_A_free_cf_enqueue_witness :
  ltac:(let t := type of (@preset_free_cf_enqueue_witness CfImg_A CfParams_preset eq_refl) in exact t).
Proof. exact (@preset_free_cf_enqueue_witness CfImg_A CfParams_preset eq_refl). Qed.

Lemma preset_A_free_cf_recycle_witness :
  ltac:(let t := type of (@preset_free_cf_recycle_witness CfImg_A CfParams_preset eq_refl) in exact t).
Proof. exact (@preset_free_cf_recycle_witness CfImg_A CfParams_preset eq_refl). Qed.
