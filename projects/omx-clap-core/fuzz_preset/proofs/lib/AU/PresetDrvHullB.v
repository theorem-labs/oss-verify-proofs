(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset (asan-ubsan image B'), the END of row A18 of the COUNT meter
   (a Theorem Labs lane, lane CountDrvB; the asan twin is lane CountDrvA's lib/A/PresetDrvHullA.v): at every allocator call of
   the closed-walk driver the state meets a Theorem Labs lane's admission premise cf_hull_ok, stated by its two bounds (cf_hull_ok is
   the cf layer's CfParams field, lib/A/CfParamsPreset.v; the bounds are A17's caps, lib/Spec/PresetSecTotal.v
   SEC_N_CAP = 2 ^ 17 = cf_kmax CfParams_preset, SEC_T_CAP = 2 ^ 36 = cf_T_max, over the layer's Z counts):
     PresetRoomPos.rp_nsec S <= SEC_N_CAP /\ YGcfNames.sec_T_cf S <= SEC_T_CAP.
   The closing arithmetic is image-free and is CountDrvA's (lib/A/PresetDrvHull.v: drv_cf_hull_ok_of_count,
   drv_cf_hull_ok_drv, from A16's rp_count / rp_base, A17's nsec_run_prefix / tsec_run_prefix and sec_n_fits /
   sec_t_fits_exact, and A14's secs_steps_cf_holds); this file applies it at the B' driver's states.
   THE B' CALLS AND THEIR STATES (measured on this image's walk, lib/AU and lib/Reusable).
   - The harness loop (lib/AU/PresetD1rBPf.v calls_loop_cf, :355-847): each harness call's allocator calls are at a
     position i of the model run, where the B' interface's clause PCB.iface_room_pos (= lib/Spec/PresetRoomPos.v
     iface_room_pos) holds: drv_cf_hull_ok_at_call_B. At a call's entry the clause is PCB.iface_room_at:
     drv_cf_hull_ok_at_entry_B. Between two harness calls the loop makes NO allocator call: lib_reseat_cf (:481) and
     the printf leaf (PF1 / PFN, :534 / :536; printf_post_cf keeps ARcf at the same state) keep S', and the next call
     takes PCB.iface_room_at at os ++ [o] (:832); after the last call the loop only frees (FREEN :663 / FREE :678,
     then PresetD1rBt.tfib_main_tail_cf :762), and free_cf keeps both counts (A14 secs_free_step).
   - The driver before the loop: the first malloc(65536) from init_state (lib/AU/PresetD2runBPfM.v m1_common_cf,
     ss_m1 a0 = 65536 at main + 0x50, lib/Reusable/YD1t.v:48), each grow's malloc(2 cap) at main + 0xa8 and free of
     the old buffer at main + 0xcc (lib/AU/PresetPinvB23Pf.v gr_grow_cf; lib/Reusable/YD20.v:35 / :37), and the
     payload malloc (lib/AU/PresetD2eBPf.v runqm_at, payload_len data < cap): their states carry the B' invariant
     drv_minv_cf, whose last conjunct is PresetDrvSecsA.drv_secs_cf, at cap <= 2 ^ 26, or are one malloc of at most
     2 ^ 26 bytes after one; the image-free PresetDrvHull.drv_cf_hull_ok_drv puts them inside the hull:
     drv_cf_hull_ok_drv_B. The same base is what PresetD2eB.iface_room_at_driver turns into the interface's count at
     os = [] (lib/AU/PresetD1sitesB.v drv_rp_base_B), so the loop's count starts from the driver's base.
   No theorem below has a premise beyond the states' own facts (secs_steps_cf is discharged inside the shared lemmas).
   Rule 24: no function is proved here (the closing arithmetic of a driver invariant). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetRoomPos PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDrvHull.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetD1sitesB.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Module PCB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PresetCfnB.
Import ListNotations.
Local Open Scope Z_scope.

(* EVERY ALLOCATOR CALL OF THE B' HARNESS LOOP: the B' interface's clause at any position i of the run (each call's
   entry and post) gives the hull *)
Theorem drv_cf_hull_ok_at_call_B : forall sm x os i H0 hist S, (length os <= 4)%nat ->
  PCB.iface_room_pos sm x os i H0 hist S ->
  PresetRoomPos.rp_nsec S <= PresetSecTotal.SEC_N_CAP /\ YGcfNames.sec_T_cf S <= PresetSecTotal.SEC_T_CAP.
Proof.
intros sm x os i H0 hist S Hl HP. unfold PresetRoomPos.iface_room_pos in HP.
destruct HP as (_ & _ & _ & _ & _ & HC). exact (PresetDrvHull.drv_cf_hull_ok_of_count sm x os i S Hl HC).
Qed.

(* at a B' harness call's entry (PCB.iface_room_at over the calls os made before it) *)
Theorem drv_cf_hull_ok_at_entry_B : forall sm x os H0 hist S, (length os <= 4)%nat ->
  PCB.iface_room_at sm x os H0 hist S ->
  PresetRoomPos.rp_nsec S <= PresetSecTotal.SEC_N_CAP /\ YGcfNames.sec_T_cf S <= PresetSecTotal.SEC_T_CAP.
Proof.
intros sm x os H0 hist S Hl (_ & _ & _ & _ & _ & HC).
apply (PresetDrvHull.drv_cf_hull_ok_of_count sm x os (length (PresetRun.hruns sm x os)) S Hl).
rewrite firstn_all. exact HC.
Qed.

(* THE B' DRIVER'S OWN CALLS before the loop: a state of the B' invariant drv_minv_cf at cap <= 2 ^ 26 (the read loop's
   states, the grow's entry and post, the tail) and the state one malloc of at most 2 ^ 26 bytes after one (the first
   malloc's post, the payload malloc's post) are inside the hull *)
Theorem drv_cf_hull_ok_drv_B : forall (ci : CfImg) (B : YG0f.asyms) S cap dl, PresetD1sitesB.drv_minv_cf B S cap dl ->
  65536 <= cap <= 2 ^ 26 ->
  (PresetRoomPos.rp_nsec S <= PresetSecTotal.SEC_N_CAP /\ YGcfNames.sec_T_cf S <= PresetSecTotal.SEC_T_CAP) /\
  (forall n trc tr (q : sptr) S', 0 <= n <= 2 ^ 26 -> apath (@malloc_cf ci n trc S) tr (q, S') ->
   PresetRoomPos.rp_nsec S' <= PresetSecTotal.SEC_N_CAP /\ YGcfNames.sec_T_cf S' <= PresetSecTotal.SEC_T_CAP).
Proof.
intros ci B S cap dl (_ & _ & _ & _ & _ & HS) Hc. exact (@PresetDrvHull.drv_cf_hull_ok_drv ci S cap HS Hc).
Qed.

Print Assumptions drv_cf_hull_ok_at_call_B.
Print Assumptions drv_cf_hull_ok_at_entry_B.
Print Assumptions drv_cf_hull_ok_drv_B.
