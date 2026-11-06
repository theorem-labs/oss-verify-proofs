(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's LIVE-SECONDARY CALL PREMISE at its cf instance, STATE FORM (row SEC-COUNT-102,
   h-pre-b2). The premise is YG0dcf.v:60, acall_pre_cf's conjunct
     Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max
   which every allocator call carries (amalloc_realizes_cf :159-166, afree_realizes_cf :188-196, YGcfRealloc.v's
   arealloc_realizes_cf :93-95; all take acall_pre_cf). Here it is DERIVED, at CfParams_preset (cf_sec_live_max =
   16,000), from three facts a walk has at the call:
     Wf_cf U S                                  (ARcf's amc_wf, YG0ncf.v:90: the pre's first conjunct, YG0dcf.v:50);
     qtight S                                   (qmeter_cf S, YG0dcf.v:56, YG0ncf.v:156: qmeter_cf S := qtight S /\
                                                 mroom_cf S, qmeter_cf_tight YG0ncf.v:203);
     YGcfRoomLive.sec_cnt S <= LSEC + DRV        (the live secondary requests: the texts' position-free entry premise,
                                                 PRH_FnAlloc.v:264 / :368, PRH_FnCheck.v:837, Caw102A_Base.v's caw_cnt
                                                 :247-249; at a model position it is PresetRoomCounts.counts_of_room_pos_rl,
                                                 from PresetLiveSec.live_sec_state).
   HOW. st_sec_arr holds the live AND the quarantined secondaries (YG01cf.v:153-165: an entry leaves it only at the
   quarantine recycle). The engine bounds it by the state alone, YGcfSecBound.sec_arr_bound_cf (lib/Reusable/
   YGcfSecBound.v:119-130): length st_sec_arr <= live_sec_blocks S + QSEC_MAX, under WfP_cf and qtight.
     LIVE part: live_sec_blocks S = sec_cnt S under Wf_cf (YGcfRoomLive.live_sec_blocks_req :1172), <= LSEC + DRV.
     QUARANTINED part: QSEC_MAX = (kQuarantineMax + kQuarantineCacheMax) / 64,513 = 4,177 (QSEC_MAX_value). Its
       source is the ENGINE'S quarantine byte cap qtight (YG01.v:230-231: thread cache <= kQuarantineCacheMax = 2 ^ 20,
       global <= kQuarantineMax = 2 ^ 28, quar_n <= queued_n), which the call pre carries as qmeter_cf (YG0dcf.v:56).
       YGcfSecBound.qsec_bytes (:85-113) turns it into 64,513 * #(quarantined PSec chunks) <= 2 ^ 28 + 2 ^ 20 through
       YGcfRoom.quar_bytes_ok_cf; 64,513 is the least secondary request (sec_req_min / sec_req_min_exact). CITED, not
       assumed: no new engine fact is needed.
     SIDE: LSEC + DRV + QSEC_MAX = 9,521 + 3 + 4,177 = 13,701 < 16,000 (sec_live_margin; PresetLiveSec.LSEC_side is
       the same sum with QT / 64513 for QSEC_MAX). The 13,367 of CfParamsPreset.v's comment is an older derivation and
       is not used.
   LEAF: Requires YGcfSecBound / YGcfRoomLive (engine), PresetLiveBounds (the LSEC / DRV leaf) and CfParamsPreset only,
   no PresetCfnA / PresetLiveSec / lib/Prog, so the image-A' / B' walks (Caw102A_WA0, FuzzReallocAp) can cite it in
   their closures. sec_live_of_cnt_witness states sec_live_of_cnt's three premises DIRECTLY at the allocator's start
   state YG00.init_state, at CfParams_preset and every universe U (so at as_universe B): Wf_cf by YG01cf.wf_init_cf,
   qtight by YG01.qtight_init (YGcfRoom.room_inv_cf_init is the same term), sec_cnt init_state = 0 <= LSEC + DRV by
   computation; it applies sec_live_of_cnt to them (0 < 16,000). The model-position forms (iface_room_pos,
   run_allocs_follow) and their start-state witness are in lib/A/PresetSecLiveA.v.
   rule 24: proves no function (kind: allocator-state bound). No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YGcfNames YG01cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecBound YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the margin at preset's instance: LSEC + DRV + QSEC_MAX = 9,521 + 3 + 4,177 = 13,701 < 16,000 *)
Lemma sec_live_margin :
  PresetLiveBounds.LSEC + PresetLiveBounds.DRV + YGcfSecBound.QSEC_MAX < @cf_sec_live_max CfParams_preset.
Proof.
  rewrite PresetLiveBounds.LSEC_value, YGcfSecBound.QSEC_MAX_value. unfold PresetLiveBounds.DRV.
  change (@cf_sec_live_max CfParams_preset) with 16000. lia.
Qed.

(* THE STATE BRIDGE: YG0dcf.v:60 at CfParams_preset, from Wf_cf, the quarantine cap qtight and the live count. *)
Theorem sec_live_of_cnt : forall U S, Wf_cf (cp := CfParams_preset) U S -> qtight S ->
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  Z.of_nat (length (st_sec_arr S)) < @cf_sec_live_max CfParams_preset.
Proof.
  intros U S W T C.
  pose proof (YGcfSecBound.sec_arr_bound_cf (cp := CfParams_preset) U 0 0 0 S W T) as A.
  rewrite (YGcfRoomLive.live_sec_blocks_req (cp := CfParams_preset) U S W) in A.
  pose proof sec_live_margin as M. lia.
Qed.

(* nothing is allocated at the start state *)
Lemma sec_cnt_init : YGcfRoomLive.sec_cnt init_state = 0.
Proof. vm_compute. reflexivity. Qed.

(* THE WITNESS of sec_live_of_cnt (satisfiability at the real instance): its three premises hold at the start state
   YG00.init_state at CfParams_preset, for every universe U, and it concludes 0 < 16,000 there *)
Theorem sec_live_of_cnt_witness : forall U,
  Wf_cf (cp := CfParams_preset) U init_state /\ qtight init_state /\
  YGcfRoomLive.sec_cnt init_state <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (length (st_sec_arr init_state)) = 0 /\
  Z.of_nat (length (st_sec_arr init_state)) < @cf_sec_live_max CfParams_preset.
Proof.
  intros U.
  pose proof (wf_init_cf (cp := CfParams_preset) U) as W.
  pose proof qtight_init as T.
  assert (C : YGcfRoomLive.sec_cnt init_state <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV).
  { rewrite sec_cnt_init, PresetLiveBounds.LSEC_value. unfold PresetLiveBounds.DRV. lia. }
  split; [exact W|]. split; [exact T|]. split; [exact C|]. split; [reflexivity|].
  exact (sec_live_of_cnt U init_state W T C).
Qed.

Print Assumptions sec_live_margin.
Print Assumptions sec_live_of_cnt.
Print Assumptions sec_live_of_cnt_witness.
