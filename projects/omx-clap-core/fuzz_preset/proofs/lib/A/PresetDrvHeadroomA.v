(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetDrvHeadroomA.v, with its module paths changed; 10 of its 28 lines of code are new or changed. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset (asan image A), ENTRY HEADROOM at every realloc call of the
   harness run. Kind: model / count bound. Rule 24: no function is proved here.
   THE CALLS. Each realloc call of target_run's 1-4 calls is at a position i of the model run, where the interface
   carries its clause (lib/Spec/PresetRoomPos.v iface_room_pos, last conjunct rp_count), and the call is the run's
   event there, nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HRe m n) (m the old block's request, n the
   new one; the event premise of lib/Spec/PresetRoomPosKeep.v room_pos_keep_realloc). drv_cf_headroom_at_call_A: at
   the call's entry state S the allocator meets preset's ENTRY HEADROOM field, cf_hull_adm S n at CfParams_preset
   (lib/Reusable/YGcfNames.v CfParams.cf_hull_adm; preset's instance lib/A/CfParamsPreset.v preset_hull_adm, the
   CHARGE form under the caps of preset's admission field cf_hull_ok):
     YGcfNames.nsec_cf S + (if YG00.from_primary n then 0 else 1) <= preset_kmax /\
     YGcfNames.sec_T_cf S + (if YG00.from_primary n then 0 else YG00.sec_map_size n) <= preset_T_max,
   one statement for a secondary n (one entry of sec_map_size n) and a primary n (+0: the hull itself). The field's
   law cf_hull_adm_post then gives cf_hull_ok at every end state of the realloc tree (secs_call_post). The arithmetic
   is image-free (lib/A/PresetDrvHeadroom.v drv_cf_headroom_of_count, which proves the charge form: the count at i,
   the event's charge at i, A17's prefix bounds at S i and A17's caps, which are preset_kmax / preset_T_max); the
   theorem below is that body read as cf_hull_adm, by conversion. secs_steps_cf is discharged inside it: the
   theorem has no premise beyond the state's own facts and the run position. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG00 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PresetDrvHeadroom.
Import ListNotations.
Local Open Scope Z_scope.

(* EVERY REALLOC CALL OF THE HARNESS RUN: the entry state has room for the call's charge *)
Theorem drv_cf_headroom_at_call_A : forall sm x os i H0 hist S m n, (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HRe m n) ->
  @YGcfNames.cf_hull_adm CfParamsPreset.CfParams_preset S n.
Proof.
intros sm x os i H0 hist S m n Hl HP He. destruct HP as (_ & _ & _ & _ & _ & HC).
exact (PresetDrvHeadroom.drv_cf_headroom_of_count sm x os i S m n Hl HC He).
Qed.

(* EVERY MALLOC CALL OF THE HARNESS RUN (the HMal twin: event HMal n at i, lib/A/PresetDrvHeadroom.v
   drv_cf_headroom_of_count_mal): the entry state has room for the call's charge, so cf_hull_ok holds at the call
   and at its post (cf_hull_adm_post) *)
Theorem drv_cf_headroom_at_malloc_A : forall sm x os i H0 hist S n, (length os <= 4)%nat ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HMal n) ->
  @YGcfNames.cf_hull_adm CfParamsPreset.CfParams_preset S n.
Proof.
intros sm x os i H0 hist S n Hl HP He. destruct HP as (_ & _ & _ & _ & _ & HC).
exact (PresetDrvHeadroom.drv_cf_headroom_of_count_mal sm x os i S n Hl HC He).
Qed.

Set Printing Implicit.
Check drv_cf_headroom_at_call_A.
Print Assumptions drv_cf_headroom_at_call_A.
Check drv_cf_headroom_at_malloc_A.
Print Assumptions drv_cf_headroom_at_malloc_A.
