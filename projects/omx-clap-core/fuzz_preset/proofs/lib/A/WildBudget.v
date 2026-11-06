(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/A/WildBudget.v, with its module paths changed. *)
(* Theorem Labs, 2026-10: fuzz_preset, LIB_WILD_BUDGET of the trace carrier P'' (a Theorem Labs lane's internal file WILD-COUNT.md
   section 7; a Theorem Labs lane asked for it on the k1-batch-102 candidate, 00:51Z). rule 24: no function proved. rule 24:
   proves no function (kind: arithmetic over the kit's per-function wild budgets).
   LLVMFuzzerTestOneInput's three arms (merged fuzz_preset.c:800-836) call the five texts that may store a fresh wild
   trace: check_no_overread, parse_noting, then arm A pj_free, arm B check_reject_clean_starved, arm C
   check_round_trip + check_reject_clean_starved + pj_free. Their budgets are the kit's prh_wk (lib/A/PRH_Base.v, the
   Definition after Inductive prh_fn). The entry's room K_LLVMF (lib/Reusable/YCbqGwild.v, 140) covers the largest arm.
   The texts need 76 (arm C); 140 is the published ceiling. *)
From Stdlib Require Import Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.

Lemma lib_wild_budget :
  (* arm C, rc = 0 (fuzz_preset.c:831-834), the largest *)
  (PRH_Base.prh_wk PRH_Base.F_check_no_overread + PRH_Base.prh_wk PRH_Base.F_parse_noting
   + PRH_Base.prh_wk PRH_Base.F_check_round_trip + PRH_Base.prh_wk PRH_Base.F_check_reject_clean_starved
   + PRH_Base.prh_wk PRH_Base.F_pj_free <= YCbqGwild.K_LLVMF)%nat /\
  (* arm A, memory ran out or check_as_written failed (:820-823) *)
  (PRH_Base.prh_wk PRH_Base.F_check_no_overread + PRH_Base.prh_wk PRH_Base.F_parse_noting
   + PRH_Base.prh_wk PRH_Base.F_pj_free <= YCbqGwild.K_LLVMF)%nat /\
  (* arm B, rc <> 0 (:825-829) *)
  (PRH_Base.prh_wk PRH_Base.F_check_no_overread + PRH_Base.prh_wk PRH_Base.F_parse_noting
   + PRH_Base.prh_wk PRH_Base.F_check_reject_clean_starved <= YCbqGwild.K_LLVMF)%nat.
Proof. cbn. unfold YCbqGwild.K_LLVMF. lia. Qed.

(* the exact need of the texts: arm C's sum is 76 *)
Lemma lib_wild_need :
  (PRH_Base.prh_wk PRH_Base.F_check_no_overread + PRH_Base.prh_wk PRH_Base.F_parse_noting
   + PRH_Base.prh_wk PRH_Base.F_check_round_trip + PRH_Base.prh_wk PRH_Base.F_check_reject_clean_starved
   + PRH_Base.prh_wk PRH_Base.F_pj_free = 76)%nat.
Proof. reflexivity. Qed.

(* every budget the kit's texts write fits the entry's room *)
Lemma prh_wk_le_K : forall F, (PRH_Base.prh_wk F <= YCbqGwild.K_LLVMF)%nat.
Proof. intros F. unfold YCbqGwild.K_LLVMF. destruct F; cbn; lia. Qed.
