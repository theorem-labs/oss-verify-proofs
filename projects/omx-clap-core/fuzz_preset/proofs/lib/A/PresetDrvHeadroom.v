(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetDrvHeadroom.v, with its module paths changed; 18 of its 48 lines of code are new or changed. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset, ENTRY HEADROOM at a realloc call of the harness run, its
   IMAGE-INDEPENDENT part. Kind: model / count bound. Rule 24: no function is proved here.
   WHAT IT SAYS. A realloc call at position i of the model run is the run's event there,
   nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HRe m n): m is the old block's request, n the new one
   (the event premise of lib/Spec/PresetRoomPosKeep.v room_pos_keep_realloc). At the call's ENTRY state S the
   allocator has room for the call's CHARGE under the caps of preset's admission field cf_hull_ok
   (lib/A/CfParamsPreset.v: cf_hull_ok S := nsec_cf S <= preset_kmax /\ sec_T_cf S <= preset_T_max, which is
   sec_meter_ok_cf at CfParams_preset by cf_hull_ok_conv_preset):
     YGcfNames.nsec_cf S + (if YG00.from_primary n then 0 else 1) <= preset_kmax /\
     YGcfNames.sec_T_cf S + (if YG00.from_primary n then 0 else YG00.sec_map_size n) <= preset_T_max.
   This is the body of preset's ENTRY HEADROOM field cf_hull_adm S n (lib/A/CfParamsPreset.v preset_hull_adm), which
   the image theorems conclude by conversion. The charge is the one a realloc tree may add
   (YGcfNames.secs_call_post): one user secondary entry of sec_map_size n mapped bytes for a secondary n, nothing
   for a primary n, whose bound is then cf_hull_ok S itself. So every end state of realloc_tree_with at S meets
   cf_hull_ok (the field's law cf_hull_adm_post).
   HOW (drv_cf_headroom_of_count). The interface's count conjunct at i (lib/Spec/PresetRoomPos.v rp_count over
   firstn i of the run) bounds S by rp_NB / rp_TB plus A17's nsec / tsec of the prefix. The prefix at S i is the
   prefix at i plus the event (PresetRoomPosKeep.rp_firstn_S), whose own counts (PresetSecTotal.nsec / tsec of
   [HRe m n]) are exactly the charge above; A17 bounds the prefix at S i by 4 NCALL / 4 TCALL
   (lib/Spec/PresetSecTotalRun.v nsec_run_prefix / tsec_run_prefix), and PresetDrvHull.drv_rp_NB_fits /
   drv_rp_TB_fits close it against A17's caps. A17's caps are preset's field values, proved once here and used
   inside the proofs only: drv_preset_kmax_cap (preset_kmax = SEC_N_CAP = 2 ^ 17) and drv_preset_T_max_cap
   (preset_T_max = SEC_T_CAP = 2 ^ 36). The state counts are the cf layer's YGcfNames.nsec_cf / sec_T_cf
   (PresetRoomPos.rp_nsec is nsec_cf: rp_nsec_layer). secs_steps_cf, the closed premise of the count conjunct, is
   discharged by YGcfSecsStep.secs_steps_cf_holds, so the theorem has no premise beyond the state's own facts and the
   run position. The image theorems are lib/A/PresetDrvHeadroomA.v (asan) and lib/AU/PresetDrvHeadroomB.v
   (asan-ubsan).
   THE MALLOC TWIN (drv_cf_headroom_of_count_mal; image theorems drv_cf_headroom_at_malloc_A / _B): the same
   headroom at a malloc event HMal n of the run (an allocation of n bytes, or realloc (NULL, n)), whose charge is
   the same as a realloc's to n. A caller with a position that makes a malloc call (the tx_put grow from no
   buffer) takes it there. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG00 YGcfNames YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetRun PresetRoom PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetSecTotal PresetSecTotalRun PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PresetDrvHull.
Import ListNotations.
Local Open Scope Z_scope.

(* preset's field values are A17's caps *)
Lemma drv_preset_kmax_cap : CfParamsPreset.preset_kmax = PresetSecTotal.SEC_N_CAP.
Proof. reflexivity. Qed.

Lemma drv_preset_T_max_cap : CfParamsPreset.preset_T_max = PresetSecTotal.SEC_T_CAP.
Proof. reflexivity. Qed.

(* THE HEADROOM: the interface's count at the position i of a realloc event HRe m n leaves room for the event's
   charge under preset's caps *)
Lemma drv_cf_headroom_of_count : forall sm x os i S m n, (length os <= 4)%nat ->
  PresetRoomPos.rp_count (firstn i (PresetRun.hruns sm x os)) S ->
  nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HRe m n) ->
  YGcfNames.nsec_cf S + (if YG00.from_primary n then 0 else 1) <= CfParamsPreset.preset_kmax /\
  YGcfNames.sec_T_cf S + (if YG00.from_primary n then 0 else YG00.sec_map_size n) <= CfParamsPreset.preset_T_max.
Proof.
intros sm x os i S m n Hl HC He. rewrite drv_preset_kmax_cap, drv_preset_T_max_cap.
destruct (HC YGcfSecsStep.secs_steps_cf_holds) as [N T]. rewrite PresetRoomPos.rp_nsec_layer in N.
pose proof (PresetSecTotalRun.nsec_run_prefix sm x os (Datatypes.S i) Hl) as Np.
pose proof (PresetSecTotalRun.tsec_run_prefix sm x os (Datatypes.S i) Hl) as Tp.
rewrite (PresetRoomPosKeep.rp_firstn_S _ i _ He), PresetSecTotal.nsec_app, Nat2Z.inj_add in Np.
rewrite (PresetRoomPosKeep.rp_firstn_S _ i _ He), PresetSecTotal.tsec_app in Tp.
cbn [PresetSecTotal.nsec PresetRun.nprodR PresetRun.prod_evR PresetSecTotal.tsec PresetSecTotal.sec_mapped] in Np, Tp.
change (PresetRoom.is_primary n) with (YG00.from_primary n) in Np, Tp.
pose proof PresetDrvHull.drv_rp_NB_fits as Fn. pose proof PresetDrvHull.drv_rp_TB_fits as Ft.
destruct (YG00.from_primary n); cbn [negb] in Np, Tp |- *; split; lia.
Qed.

(* THE HEADROOM AT A MALLOC (the HMal twin): the same count at the position i of a malloc event HMal n (fuzz_malloc's
   or fuzz_strdup's allocator call, realloc (NULL, n), a raw __wrap_malloc of the harness, a writer grow from no
   buffer) leaves room for the event's charge under preset's caps; the event's own counts are the same charge as a
   realloc to n *)
Lemma drv_cf_headroom_of_count_mal : forall sm x os i S n, (length os <= 4)%nat ->
  PresetRoomPos.rp_count (firstn i (PresetRun.hruns sm x os)) S ->
  nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HMal n) ->
  YGcfNames.nsec_cf S + (if YG00.from_primary n then 0 else 1) <= CfParamsPreset.preset_kmax /\
  YGcfNames.sec_T_cf S + (if YG00.from_primary n then 0 else YG00.sec_map_size n) <= CfParamsPreset.preset_T_max.
Proof.
intros sm x os i S n Hl HC He. rewrite drv_preset_kmax_cap, drv_preset_T_max_cap.
destruct (HC YGcfSecsStep.secs_steps_cf_holds) as [N T]. rewrite PresetRoomPos.rp_nsec_layer in N.
pose proof (PresetSecTotalRun.nsec_run_prefix sm x os (Datatypes.S i) Hl) as Np.
pose proof (PresetSecTotalRun.tsec_run_prefix sm x os (Datatypes.S i) Hl) as Tp.
rewrite (PresetRoomPosKeep.rp_firstn_S _ i _ He), PresetSecTotal.nsec_app, Nat2Z.inj_add in Np.
rewrite (PresetRoomPosKeep.rp_firstn_S _ i _ He), PresetSecTotal.tsec_app in Tp.
cbn [PresetSecTotal.nsec PresetRun.nprodR PresetRun.prod_evR PresetSecTotal.tsec PresetSecTotal.sec_mapped] in Np, Tp.
change (PresetRoom.is_primary n) with (YG00.from_primary n) in Np, Tp.
pose proof PresetDrvHull.drv_rp_NB_fits as Fn. pose proof PresetDrvHull.drv_rp_TB_fits as Ft.
destruct (YG00.from_primary n); cbn [negb] in Np, Tp |- *; split; lia.
Qed.

Print Assumptions drv_cf_headroom_of_count.
Print Assumptions drv_cf_headroom_of_count_mal.
