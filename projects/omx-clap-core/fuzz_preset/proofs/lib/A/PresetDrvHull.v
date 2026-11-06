(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetDrvHull.v, with its module paths and module names changed; 29 of its 76 lines of code are new or changed and 1 line of the source is left out. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset, the END of row A18 of the COUNT meter (a Theorem Labs lane, lane CountDrvA),
   its IMAGE-INDEPENDENT part: the closing arithmetic that puts a state inside a Theorem Labs lane's admission premise cf_hull_ok.
   cf_hull_ok is the cf layer's CfParams field (lib/A/CfParamsPreset.v: nsec_cf S <= preset_kmax /\ sec_T_cf S <=
   preset_T_max); it is stated here by its two bounds, A17's caps (lib/Spec/PresetSecTotal.v
   SEC_N_CAP = 2 ^ 17 = cf_kmax CfParams_preset, SEC_T_CAP = 2 ^ 36 = cf_T_max), over the layer's Z counts:
     PresetRoomPos.rp_nsec S <= SEC_N_CAP /\ YGcfNames.sec_T_cf S <= SEC_T_CAP.
   - drv_cf_hull_ok_of_count: the interface's count conjunct (row A16, lib/Spec/PresetRoomPos.v rp_count) at a prefix
     firstn i of a run of at most 4 calls bounds the state by rp_NB / rp_TB plus A17's nsec / tsec of the prefix,
     which A17 bounds by 4 NCALL / 4 TCALL (lib/Spec/PresetSecTotalRun.v nsec_run_prefix / tsec_run_prefix); A17's
     sec_n_fits / sec_t_fits_exact close it, since rp_NB = 64 <= NB_MAX_ALLOWED and rp_TB = 2 ^ 30 <= TB_MAX_EXACT
     (drv_rp_NB_fits / drv_rp_TB_fits).
   - drv_cf_hull_ok_of_base: the rp base itself (the driver's own entries before the first harness call).
   - drv_cf_hull_ok_drv: every driver state of the read loop (lib/A/PresetDrvSecsA.v drv_secs_cf at cap <= 2 ^ 26)
     and each state one malloc of at most 2 ^ 26 bytes after one.
   secs_steps_cf, the closed premise of every count conjunct, is discharged here once, by A14's
   YGcfSecsStep.secs_steps_cf_holds. Image independent: the image-specific theorems (the interface's iface_room_at) are
   lib/A/PresetDrvHullA.v and its asan-ubsan twin. Rule 24: no function is proved here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetRoomPos PresetSecTotal PresetSecTotalRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDrvSecsA CfParamsPreset.
Import ListNotations.
Local Open Scope Z_scope.

(* A17's closing arithmetic at the interface's base (rp_NB, rp_TB) *)
Lemma drv_rp_NB_fits : PresetRoomPos.rp_NB + 4 * PresetSecTotal.NCALL <= PresetSecTotal.SEC_N_CAP.
Proof.
apply PresetSecTotal.sec_n_fits. rewrite PresetSecTotal.NB_MAX_ALLOWED_value. unfold PresetRoomPos.rp_NB. lia.
Qed.

Lemma drv_rp_TB_fits : PresetRoomPos.rp_TB + 4 * PresetSecTotal.TCALL <= PresetSecTotal.SEC_T_CAP.
Proof.
apply PresetSecTotal.sec_t_fits_exact. rewrite PresetSecTotal.TB_MAX_EXACT_value. unfold PresetRoomPos.rp_TB.
change (2 ^ 30) with 1073741824. lia.
Qed.

(* the interface's count at a prefix of a run of at most 4 calls is inside the hull *)
Lemma drv_cf_hull_ok_of_count : forall sm x os i S, (length os <= 4)%nat ->
  PresetRoomPos.rp_count (firstn i (PresetRun.hruns sm x os)) S ->
  PresetRoomPos.rp_nsec S <= PresetSecTotal.SEC_N_CAP /\ YGcfNames.sec_T_cf S <= PresetSecTotal.SEC_T_CAP.
Proof.
intros sm x os i S Hl HC.
destruct (HC YGcfSecsStep.secs_steps_cf_holds) as [N T].
pose proof (PresetSecTotalRun.nsec_run_prefix sm x os i Hl) as Np.
pose proof (PresetSecTotalRun.tsec_run_prefix sm x os i Hl) as Tp.
pose proof drv_rp_NB_fits as Fn. pose proof drv_rp_TB_fits as Ft.
split; lia.
Qed.

(* a state with the rp base is inside the hull *)
Lemma drv_cf_hull_ok_of_base : forall S, PresetRoomPos.rp_base S ->
  PresetRoomPos.rp_nsec S <= PresetSecTotal.SEC_N_CAP /\ YGcfNames.sec_T_cf S <= PresetSecTotal.SEC_T_CAP.
Proof.
intros S HB. destruct (HB YGcfSecsStep.secs_steps_cf_holds) as [N T].
unfold PresetRoomPos.rp_NB, PresetRoomPos.rp_TB in N, T. unfold PresetSecTotal.SEC_N_CAP, PresetSecTotal.SEC_T_CAP.
change (2 ^ 30) with 1073741824 in T. change (2 ^ 17) with 131072. change (2 ^ 36) with 68719476736.
split; lia.
Qed.

(* THE FIELD AT THE PRESET INSTANCE: cf_hull_ok at CfParams_preset IS the bound pair (lib/A/CfParamsPreset.v:
   nsec_cf S <= preset_kmax /\ sec_T_cf S <= preset_T_max, preset_kmax = 2 ^ 17 = SEC_N_CAP, preset_T_max = 2 ^ 36 =
   SEC_T_CAP, rp_nsec = nsec_cf), by conversion. The driver's call pres state the field (PresetD1sitesA.v drv_pre_cf);
   their proofs reach it from the bounds above through this lemma. *)
Lemma drv_cf_hull_ok_preset : forall S,
  PresetRoomPos.rp_nsec S <= PresetSecTotal.SEC_N_CAP /\ YGcfNames.sec_T_cf S <= PresetSecTotal.SEC_T_CAP ->
  @cf_hull_ok CfParamsPreset.CfParams_preset S.
Proof. intros S H. exact H. Qed.

(* the interface's count over a whole run of at most 4 calls, in the field's form (the exit path's frees) *)
Lemma drv_cf_hull_ok_of_run : forall sm x os S, (length os <= 4)%nat ->
  PresetRoomPos.rp_count (PresetRun.hruns sm x os) S -> @cf_hull_ok CfParamsPreset.CfParams_preset S.
Proof.
intros sm x os S Hl HC. apply drv_cf_hull_ok_preset.
apply (drv_cf_hull_ok_of_count sm x os (length (PresetRun.hruns sm x os)) S Hl). rewrite firstn_all. exact HC.
Qed.

(* THE DRIVER'S OWN CALLS before the loop: the read loop's states (drv_secs_cf at cap <= 2 ^ 26) and the state one
   malloc of at most 2 ^ 26 bytes after one, i.e. the first malloc's post, each grow's entry, post and free, the tail,
   and the payload malloc's post *)
Section drv.
Context {ci : CfImg}.
Theorem drv_cf_hull_ok_drv : forall S cap, PresetDrvSecsA.drv_secs_cf S cap -> 65536 <= cap <= 2 ^ 26 ->
  (PresetRoomPos.rp_nsec S <= PresetSecTotal.SEC_N_CAP /\ YGcfNames.sec_T_cf S <= PresetSecTotal.SEC_T_CAP) /\
  (forall n trc tr (q : sptr) S', 0 <= n <= 2 ^ 26 -> apath (malloc_cf n trc S) tr (q, S') ->
   PresetRoomPos.rp_nsec S' <= PresetSecTotal.SEC_N_CAP /\ YGcfNames.sec_T_cf S' <= PresetSecTotal.SEC_T_CAP).
Proof.
intros S cap H Hc. destruct (PresetDrvSecsA.drv_secs_rp_base S cap H Hc) as [B0 B1]. split.
- exact (drv_cf_hull_ok_of_base S B0).
- intros n trc tr q S' Hn Hp. exact (drv_cf_hull_ok_of_base S' (B1 n trc tr q S' Hn Hp)).
Qed.

(* a free keeps the hull: free_cf maps no secondary entry (secs_steps_cf's free step, YGcfSecsStep.secs_same) *)
Lemma drv_cf_hull_ok_free : forall (p : sptr) trc S tr S', @cf_hull_ok CfParamsPreset.CfParams_preset S ->
  apath (free_cf p trc S) tr (tt, S') -> @cf_hull_ok CfParamsPreset.CfParams_preset S'.
Proof.
intros p trc S tr S' H Hp. apply drv_cf_hull_ok_preset.
assert (H' : PresetRoomPos.rp_nsec S <= PresetSecTotal.SEC_N_CAP /\ YGcfNames.sec_T_cf S <= PresetSecTotal.SEC_T_CAP)
  by exact H.
destruct (proj1 (proj2 (YGcfSecsStep.secs_steps_cf_holds ci)) p trc S tr S' Hp) as [N T].
rewrite PresetRoomPos.rp_nsec_layer in *. rewrite N, T. exact H'.
Qed.

(* drv_cf_hull_ok_drv in the field's form at the preset instance *)
Theorem drv_cf_hull_ok_drv_preset : forall S cap, PresetDrvSecsA.drv_secs_cf S cap -> 65536 <= cap <= 2 ^ 26 ->
  @cf_hull_ok CfParamsPreset.CfParams_preset S /\
  (forall n trc tr (q : sptr) S', 0 <= n <= 2 ^ 26 -> apath (malloc_cf n trc S) tr (q, S') ->
   @cf_hull_ok CfParamsPreset.CfParams_preset S').
Proof.
intros S cap H Hc. destruct (drv_cf_hull_ok_drv S cap H Hc) as [B0 B1]. split.
- exact (drv_cf_hull_ok_preset S B0).
- intros n trc tr q S' Hn Hp. exact (drv_cf_hull_ok_preset S' (B1 n trc tr q S' Hn Hp)).
Qed.
End drv.
