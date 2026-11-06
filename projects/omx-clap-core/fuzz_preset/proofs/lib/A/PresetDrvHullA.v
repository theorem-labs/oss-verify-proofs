(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetDrvHullA.v, with its module paths and module names changed; 1 of its 27 lines of code is new or changed and 1 line of the source is left out. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset (asan image A), the END of row A18 of the COUNT meter (a Theorem Labs lane,
   lane CountDrvA): at every allocator call of the harness loop the state meets a Theorem Labs lane's admission premise
   cf_hull_ok, stated by its two bounds (A17's caps; lib/A/PresetDrvHull.v header):
     PresetRoomPos.rp_nsec S <= SEC_N_CAP /\ YGcfNames.sec_T_cf S <= SEC_T_CAP.
   THE CALLS AND THEIR STATES.
   - The harness loop (lib/A/PresetD1rAPf.v calls_loop_cf): every allocator call of target_run's 1-4 calls is at a
     position i of the model run, where the interface carries its clause (row A16, lib/Spec/PresetRoomPos.v
     iface_room_pos, last conjunct rp_count); PresetDrvHull.drv_cf_hull_ok_of_count closes it with A17's
     nsec_run_prefix / tsec_run_prefix and sec_n_fits / sec_t_fits_exact: drv_cf_hull_ok_at_call_A. The interface's
     iface_room_at at a call's entry (lib/A/PresetCfnA.v) is the position i = length (hruns sm x os):
     drv_cf_hull_ok_at_entry_A.
   - The count starts from the driver's base: PresetD2eA.iface_room_at_driver builds iface_room_at at os = [] from
     PresetRoomPos.rp_base, which lib/A/PresetD1sitesA.v drv_rp_base_A gives at both loop entries.
   - The loop makes no allocator call between two harness calls (calls_loop_cf goes from one call's post state through
     lib_reseat_cf, the printf leaf, which keeps the allocator state, and the runner segments to the next call); after
     the last call its frees keep both counts (A14 secs_free_step). The driver's calls before the loop are
     PresetDrvHull.drv_cf_hull_ok_drv.
   secs_steps_cf is discharged by A14's YGcfSecsStep.secs_steps_cf_holds inside PresetDrvHull: no theorem below has a
   premise beyond the state's own facts. Rule 24: no function is proved here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfNames YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetRoomPos PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDrvHull.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Module PCA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PresetCfnA.
Import ListNotations.
Local Open Scope Z_scope.

(* EVERY ALLOCATOR CALL OF THE HARNESS LOOP: the interface's clause at any position i of the run (each call's entry
   and post) gives the hull *)
Theorem drv_cf_hull_ok_at_call_A : forall sm x os i H0 hist S, (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  PresetRoomPos.rp_nsec S <= PresetSecTotal.SEC_N_CAP /\ YGcfNames.sec_T_cf S <= PresetSecTotal.SEC_T_CAP.
Proof.
intros sm x os i H0 hist S Hl HP. unfold PresetRoomPos.iface_room_pos in HP.
destruct HP as (_ & _ & _ & _ & _ & HC). exact (PresetDrvHull.drv_cf_hull_ok_of_count sm x os i S Hl HC).
Qed.

(* at a harness call's entry (the interface's iface_room_at over the calls os made before it) *)
Theorem drv_cf_hull_ok_at_entry_A : forall sm x os H0 hist S, (length os <= 4)%nat ->
  PCA.iface_room_at sm x os H0 hist S ->
  PresetRoomPos.rp_nsec S <= PresetSecTotal.SEC_N_CAP /\ YGcfNames.sec_T_cf S <= PresetSecTotal.SEC_T_CAP.
Proof.
intros sm x os H0 hist S Hl (_ & _ & _ & _ & _ & HC).
apply (PresetDrvHull.drv_cf_hull_ok_of_count sm x os (length (PresetRun.hruns sm x os)) S Hl).
rewrite firstn_all. exact HC.
Qed.

Print Assumptions drv_cf_hull_ok_at_call_A.
Print Assumptions drv_cf_hull_ok_at_entry_A.
Print Assumptions PresetDrvHull.drv_cf_hull_ok_drv.
