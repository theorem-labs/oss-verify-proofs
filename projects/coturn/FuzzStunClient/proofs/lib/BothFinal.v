(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require OSSVerify.coturn.FuzzStunClient.images.Plain.
Require OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import BothTopW.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import Main5W1Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem both_base :
  strong_universal_error_free_T_budgets SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OSSVerify.coturn.FuzzStunClient.images.Plain.M.loaded_segments
             OSSVerify.coturn.FuzzStunClient.images.Plain.M.init_pc
             OSSVerify.coturn.FuzzStunClient.images.Plain.M.phdrs)
    (mkImage OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.loaded_segments
             OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.init_pc
             OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.phdrs).
Proof. exact (both_base_W1 TW1 TW1_ok). Qed.
