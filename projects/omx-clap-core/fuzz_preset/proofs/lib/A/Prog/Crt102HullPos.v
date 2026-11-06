(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Crt102HullPos.v, with its module paths changed. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset, the walk of check_round_trip (both images): the hull premise
   `p <> 0 -> PresetHullBudget.hull_budget S []` of a free call of the walk - fuzz_free's (lib/A/PRH_FnAlloc.v
   tfuzz_free_specX, at p) and pj_free's (lib/A/PRH_FnPj.v tpj_free_specX, the same form at v): the admission at a
   non-NULL free; a free makes no secondary entry, so the list is empty.
   WHY A POSITION AND A RUN BOUND. hull_budget S [] bounds the two meters nsec_cf / sec_T_cf, which are run TOTALS
   (they only grow), so no live-set fact (room_live_cf, the class-24 count) gives it. A run position does: the
   interface's count conjunct (lib/Spec/PresetRoomPos.v rp_count) and A17's prefix bounds put the meters at a position
   of a run of at most 4 calls under preset's caps with one call's worth to spare (lib/A/PresetHullPay.v
   hull_budget_of_room_pos); the empty list needs none of it (nsec [] = 0 <= NCALL, tsec [] = 0 <= TCALL).
   The run bound `(length rp_os <= 4)%nat` is tcheck_round_trip_specX's own entry premise (lib/A/PRH_FnCheck.v, "THE
   RUN HAS AT MOST 4 CALLS"); the position is the walk's (Crt102Glue.crt_pos_room on A', the stepped position on B').
   - hull_budget_nil_of_room_pos: the budget for [] at a position.
   - hull_free_of_room_pos: the same in the form of fuzz_free's premise, applied to the call's pointer: at a site
     with the run bound HOS4 and a position HRP at the call state Sc,
     `hull_free_of_room_pos _ _ _ _ _ _ _ p HOS4 HRP : p <> 0 -> PresetHullBudget.hull_budget Sc []`.
   IMAGE-FREE: preset's CfParams instance (lib/A/CfParamsPreset.v) is the one both images' free texts take, so this
   one file serves A' and B'. CLOSURE: Requires only lib/Spec PresetRoomPos / PresetSecTotal / PresetHullBudget and
   lib/A CfParamsPreset / PresetHullPay - no crt segment file - so every crt segment file may Require it.
   Rule 24: proves no function (kind: model / count bound; no program walk). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PresetHullPay.
Import ListNotations.
Local Open Scope Z_scope.

(* the budget for the empty list at a position of a run of at most 4 calls *)
Lemma hull_budget_nil_of_room_pos : forall sm x os i H0 hist S, (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  @PresetHullBudget.hull_budget CfParamsPreset.CfParams_preset S [].
Proof.
intros sm x os i H0 hist S Hl HP.
apply (PresetHullPay.hull_budget_of_room_pos sm x os i H0 hist S [] Hl HP).
- rewrite PresetHullBudget.hull_nsec_nil, PresetSecTotal.NCALL_value. lia.
- rewrite PresetHullBudget.hull_tsec_nil, PresetSecTotal.TCALL_value. lia.
Qed.

(* fuzz_free's premise at a free of pointer p whose call state holds the position *)
Lemma hull_free_of_room_pos : forall sm x os i H0 hist S (p : Z), (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  p <> 0 -> @PresetHullBudget.hull_budget CfParamsPreset.CfParams_preset S [].
Proof.
intros sm x os i H0 hist S p Hl HP _. exact (hull_budget_nil_of_room_pos sm x os i H0 hist S Hl HP).
Qed.

Print Assumptions hull_budget_nil_of_room_pos.
Print Assumptions hull_free_of_room_pos.
