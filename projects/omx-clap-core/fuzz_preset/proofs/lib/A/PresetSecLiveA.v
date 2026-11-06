(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image A, row SEC-COUNT-102 (h-pre-b2): THE BRIDGE from the walk's facts at an
   allocator call to the engine's live-secondary call premise, YG0dcf.v:60 (acall_pre_cf's conjunct
   `Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max`), at CfParams_preset (cf_sec_live_max = 16,000).
     sec_live_call_ok    : Wf_cf U S -> PresetCfnA.run_allocs_follow sm x H0 S -> premise;
     sec_live_call_ok_ar : the same with ARcf (the pre's first conjunct, YG0dcf.v:50) in place of Wf_cf (amc_wf);
     sec_live_of_pos     : the same from PresetRoomPos.iface_room_pos at any position i of the model run.
   HOW. run_allocs_follow (PresetCfnA.v:562-564) is iface_room_pos at a position i of hruns plus the consumer
   allocation there. iface_room_pos carries (a) P8's live-set premise, the allocator's live requests = hlive (firstn i
   (hruns sm x os)) ++ at most DRV = 3 driver blocks, which PresetRoomCounts.counts_of_room_pos_rl turns into
   sec_cnt S <= LSEC + DRV (PresetLiveSec.live_sec_state, LSEC = 9,521; above MAXB the run is empty), and (b)
   room_inv_cf S, which IS qtight S (YGcfRoom.v:51), the engine's quarantine byte cap. CfSecLivePreset.sec_live_of_cnt
   then gives the premise: YGcfSecBound.sec_arr_bound_cf bounds st_sec_arr (live AND quarantined secondaries) by
   live_sec_blocks S + QSEC_MAX, QSEC_MAX = (2 ^ 28 + 2 ^ 20) / 64,513 = 4,177 from qtight (YGcfSecBound.qsec_bytes);
   9,521 + 3 + 4,177 = 13,701 < 16,000.
   THE WITNESS (satisfiability at the real instance): sec_live_call_witness. At the harness START state, the
   allocator's initial state YG00.init_state, at CfParams_preset, for every strtod model sm and every input x of at
   most MAXB bytes: Wf_cf holds (YG01cf.wf_init_cf), run_allocs_follow sm x [] init_state holds (P8's premises at
   position 0 of the first call: empty live set, d = [], empty quarantine and history, then
   PresetCfnA.run_allocs_follow_entry: the call's first event is check_no_overread's fuzz_copy allocation), and the
   bridge's conclusion there is 0 < 16,000 (st_sec_arr init_state is empty).
   THE CONSUMERS (YG0dcf.v:60 is reached by every allocator call through acall_pre_cf: amalloc_realizes_cf
   YG0dcf.v:159-166, afree_realizes_cf :188-196, arealloc_realizes_cf YGcfRealloc.v:93-95):
     - the call pre itself: its conjuncts ARcf (:50, gives Wf_cf by amc_wf) and qmeter_cf (:56, gives qtight) are the
       bridge's state hypotheses; the live count is the walk's;
     - Caw102A_Top.v:85 / Caw102A_WA0.v:131 (AMALLOC, the scratch malloc at the entry state cw_S D, Caw102A_WA0.v:402-423):
       the walk has ARcf, qtight and caw_cnt D's sec_cnt (cw_S D) <= LSEC + DRV (the named argument CAW_CNT), and NO
       model position (f97c's text dropped it), so run_allocs_follow is NOT supplied there; the state form
       CfSecLivePreset.sec_live_of_cnt takes exactly what it has;
     - FuzzReallocAp.v:2244 (AREAL_cf, the realloc call at :2500-2521): the walk has ARcf (HAR), qtight (HQT) and
       the text premise sec_cnt S <= LSEC + DRV (Hsec, PRH_FnAlloc.v:368), no position: sec_live_of_cnt again.
     Today both walks take the premise from room_live_cf (YGcfRoomLive.room_live_room -> QM_cf_of_room); the bridge
     needs no room_live_cf for this conjunct (QM_cf's ERRB_ROOM and batch_room_cf still come from it).
   Requires PresetCfnA (run_allocs_follow is defined there), so it is image A's interface level; the walks that keep
   PresetCfnA out of their closure cite lib/A/CfSecLivePreset.v.
   rule 24: proves no function (kind: allocator-state bound and its witness). No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YGcfNames YG01cf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfFrees YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfSecLivePreset PresetCfnA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------- the bridge *)
(* at any position of the model run *)
Lemma sec_live_of_pos : forall U sm x os i H0 hist S, Wf_cf (cp := CfParams_preset) U S ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  Z.of_nat (length (st_sec_arr S)) < @cf_sec_live_max CfParams_preset.
Proof.
  intros U sm x os i H0 hist S W H.
  destruct (PresetRoomCounts.counts_of_room_pos_rl sm x os i H0 hist S H) as [C _].
  destruct H as (_ & T & _).
  exact (CfSecLivePreset.sec_live_of_cnt U S W T C).
Qed.

(* THE BRIDGE: at an allocator call that is a consumer allocation of the run (the walk's named fact
   run_allocs_follow, PresetCfnA.v:562-564) *)
Theorem sec_live_call_ok : forall U sm x H0 S, Wf_cf (cp := CfParams_preset) U S ->
  PresetCfnA.run_allocs_follow sm x H0 S ->
  Z.of_nat (length (st_sec_arr S)) < @cf_sec_live_max CfParams_preset.
Proof.
  intros U sm x H0 S W (os & i & hist & Hpos & _ & _).
  exact (sec_live_of_pos U sm x os i H0 hist S W Hpos).
Qed.

(* the same, with the call pre's own first conjunct ARcf (YG0dcf.v:50) supplying Wf_cf *)
Section AR. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Theorem sec_live_call_ok_ar : forall segs B ly S Hp W mem md sm x H0,
  ARcf (cp := CfParams_preset) segs B ly S Hp W mem md -> PresetCfnA.run_allocs_follow sm x H0 S ->
  Z.of_nat (length (st_sec_arr S)) < @cf_sec_live_max CfParams_preset.
Proof.
  intros segs B ly S Hp W mem md sm x H0 HAR HR.
  exact (sec_live_call_ok _ sm x H0 S (amc_wf _ _ _ _ _ (proj1 HAR)) HR).
Qed.
End AR.

(* ---------------------------------------------------------------- the witness (satisfiability at the start state) *)
(* P8's premises at the entry of the first call (os = []): nothing live, nothing quarantined, no history *)
Lemma sec_live_start_room : forall sm x, PresetCfnA.iface_room_at sm x [] [] [] init_state.
Proof.
  intros sm x. unfold PresetCfnA.iface_room_at.
  split; [|split; [exact YGcfRoom.room_inv_cf_init|split; [exact YGcfRoom.quar_fifo_cf_init|split]]].
  - exists []. split; [cbn [length]; lia|].
    change (PresetRoom.rs_live (YGcfRoom.room_of_cf init_state)) with (@nil Z).
    change (PresetReqAt.hlive (PresetRun.hruns sm x []) ++ []) with (@nil Z).
    constructor.
  - constructor.
  - split; [unfold YGcfFrees.cf_frees_follow; reflexivity | exact (PresetRoomPos.rp_count_start init_state eq_refl)].
Qed.

Lemma sec_live_start_count : Z.of_nat (length (st_sec_arr init_state)) = 0.
Proof. reflexivity. Qed.

(* the bridge's hypotheses hold at the start state, at the unit's instance, on every input of at most MAXB bytes *)
Theorem sec_live_call_start : forall U sm x, Z.of_nat (length x) <= PresetReqAt.MAXB ->
  Wf_cf (cp := CfParams_preset) U init_state /\ PresetCfnA.run_allocs_follow sm x [] init_state.
Proof.
  intros U sm x Hx. split; [exact (wf_init_cf (cp := CfParams_preset) U)|].
  exact (PresetCfnA.run_allocs_follow_entry sm x [] [] [] init_state (sec_live_start_room sm x) Hx).
Qed.

(* THE WITNESS: there, the bridge concludes 0 < 16,000 *)
Corollary sec_live_call_witness : forall U sm x, Z.of_nat (length x) <= PresetReqAt.MAXB ->
  Wf_cf (cp := CfParams_preset) U init_state /\ PresetCfnA.run_allocs_follow sm x [] init_state /\
  Z.of_nat (length (st_sec_arr init_state)) = 0 /\
  Z.of_nat (length (st_sec_arr init_state)) < @cf_sec_live_max CfParams_preset.
Proof.
  intros U sm x Hx. destruct (sec_live_call_start U sm x Hx) as [W R].
  split; [exact W|]. split; [exact R|]. split; [exact sec_live_start_count|].
  exact (sec_live_call_ok U sm x [] init_state W R).
Qed.

Lemma sec_live_max_value : @cf_sec_live_max CfParams_preset = 16000.
Proof. reflexivity. Qed.

Print Assumptions sec_live_of_pos.
Print Assumptions sec_live_call_ok.
Print Assumptions sec_live_call_ok_ar.
Print Assumptions sec_live_call_witness.
