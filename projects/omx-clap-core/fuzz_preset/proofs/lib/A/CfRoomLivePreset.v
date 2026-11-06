(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's non-primary room invariant room_live_cf (lib/Reusable/YGcfRoomLive.v) at
   CfParams_preset (CfParamsPreset.v). PER-UNIT file: the instance half (YGcfRoomLive.v, generic in CfParams) meets
   the harness half (lib/Spec/PresetLiveSec.v, h-hpreset-7).
   - room_live_cf_init_preset: room_live_cf at the allocator's initial state.
   - room_live_step_counts: one harness allocator call (rl_call: malloc_cf, free_cf, the realloc tree, realloc(NULL, n))
     keeps room_live_cf, under Wf_cf, qtight and the live-set premises in the form live_sec_state and live_c24_state
     conclude at L := PresetRoom.rs_live (YGcfRoom.room_of_cf S), word for word, so they feed it with no rewriting;
     rs_live_blocks is the bridge to the allocator's live requests map snd (blocks S) (an equality, by definition of
     room_of_cf). live_premises_hold (PresetLiveSec.v) shows those premises are satisfiable.
   - room_live_np_init_u / room_live_np_step_u / room_live_np_tail_u: h-pre-b1's iface_room_np_init / _step / _tail
     (PresetCfnA.v section 3b, frozen at 3f83c075b61f = 59de238d7ae) with NP := room_live_cf, bodies unfolded word for
     word; h-pre-b1 wraps each in one exact. Their names differ from the interface's definitions on purpose.
   The keeps' side conditions are closed by computation at LSEC + DRV = 9,524 and L24 + DRV (+ 1 for a realloc's two
   blocks) = 146,223: 9,524 + QSEC_MAX 4,177 + 3 < 16,000 (the +3 is the call's new entry and RK_realloc's 2 of
   headroom), and 8,192 * (146,223 + 1 + N24Q) + 4 * kUserMapSize <= kFreeArrayOffset (N24Q = 78,594).
   Model and invariant lemmas only; no function is proved (rule 24). No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetReqAt PresetGate PresetLiveSec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YGcfNames YG00cf YG01cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YGcfSecBound YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* The parameter premise at preset's instance: QSEC_MAX = 4,177 and cf_sec_live_max = 16,000. *)
Lemma preset_rl_param_ok : rl_param_ok (cp := CfParams_preset).
Proof. unfold rl_param_ok. apply Z.ltb_lt. vm_compute. reflexivity. Qed.

(* The bridge: the room view's live list is the allocator's live requests. *)
Lemma rs_live_blocks : forall S, PresetRoom.rs_live (YGcfRoom.room_of_cf S) = map snd (blocks S).
Proof. intros S. reflexivity. Qed.

(* The generic keeps' live-set premises at the harness's figures. *)
Lemma preset_rl_sec_ok : forall S,
  Z.of_nat (PresetReqAt.cnt PresetLiveSec.sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))) <=
    PresetLiveSec.LSEC + PresetGate.DRV ->
  rl_sec_ok (cp := CfParams_preset) (PresetLiveSec.LSEC + PresetGate.DRV) S.
Proof.
intros S H. rewrite rs_live_blocks in H. split; [exact H|]. apply Z.ltb_lt. vm_compute. reflexivity.
Qed.

Lemma preset_ccnt24 : forall S,
  Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls 24) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))) <=
    PresetLiveSec.L24 + PresetGate.DRV ->
  ccnt24 S <= PresetLiveSec.L24 + PresetGate.DRV.
Proof. intros S H. rewrite rs_live_blocks in H. exact H. Qed.

Lemma preset_rl_b24_ok : forall S, ccnt24 S <= PresetLiveSec.L24 + PresetGate.DRV ->
  rl_b24_ok (PresetLiveSec.L24 + PresetGate.DRV + 1) S.
Proof. intros S H. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* room_live_cf at the allocator's initial state. *)
Theorem room_live_cf_init_preset : room_live_cf (cp := CfParams_preset) init_state.
Proof. exact (room_live_cf_init_gen (cp := CfParams_preset) preset_rl_param_ok). Qed.

Section P. Context {ci : CfImg}.

(* One harness allocator call (rl_call) from a Wf_cf, qtight state whose live requests satisfy live_sec_state's and
   live_c24_state's conclusions keeps room_live_cf. *)
Theorem room_live_step_counts : forall U S S', Wf_cf (cp := CfParams_preset) U S -> qtight S ->
  room_live_cf (cp := CfParams_preset) S ->
  Z.of_nat (PresetReqAt.cnt PresetLiveSec.sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))) <=
    PresetLiveSec.LSEC + PresetGate.DRV ->
  Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls 24) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))) <=
    PresetLiveSec.L24 + PresetGate.DRV ->
  rl_call (cp := CfParams_preset) U S S' -> room_live_cf (cp := CfParams_preset) S'.
Proof.
intros U S S' W T R Hs H24 St.
pose proof (preset_rl_sec_ok S Hs) as HS. pose proof (preset_ccnt24 S H24) as Hc.
exact (room_live_call_keep (cp := CfParams_preset) U _ _ S S' W T HS Hc (preset_rl_b24_ok S Hc) R St).
Qed.

(* At most 3 live blocks satisfy both live-set premises. *)
Lemma preset_counts_of_three : forall S, (length (blocks S) <= 3)%nat ->
  Z.of_nat (PresetReqAt.cnt PresetLiveSec.sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))) <=
    PresetLiveSec.LSEC + PresetGate.DRV /\
  Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls 24) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))) <=
    PresetLiveSec.L24 + PresetGate.DRV.
Proof.
intros S H. rewrite rs_live_blocks.
pose proof (PresetLiveSec.cnt_le_len PresetLiveSec.sec_req (map snd (blocks S))) as A1.
pose proof (PresetLiveSec.cnt_le_len (PresetRoom.in_cls 24) (map snd (blocks S))) as A2.
rewrite length_map in A1, A2. rewrite PresetLiveSec.LSEC_value, PresetLiveSec.L24_value. unfold PresetGate.DRV. lia.
Qed.

(* h-pre-b1's interface (PresetCfnA.v section 3b) at NP := room_live_cf, its bodies unfolded word for word. Here
   CfParams_preset is the only CfParams instance, so Wf_cf, room_live_cf and ROOM_cf_k are at preset's. *)
#[local] Existing Instance CfParams_preset.

(* iface_room_np_init, PresetCfnA.v:454 at 3f83c075b61f (= :512 at 59de238d7ae). *)
Lemma room_live_np_init_u : room_live_cf YG00.init_state.
Proof. exact room_live_cf_init_preset. Qed.

(* iface_room_np_step, PresetCfnA.v:455-459 at 3f83c075b61f (= :513-517 at 59de238d7ae). *)
Lemma room_live_np_step_u :
(forall U S n tr trc p S', Wf_cf U S -> YG01.qtight S -> room_live_cf S -> (length (YG01.blocks S) <= 3)%nat ->
  YG00.apath (YG00cf.malloc_cf n tr S) trc (p, S') -> room_live_cf S') /\
(forall U S p tr trc S', Wf_cf U S -> YG01.qtight S -> room_live_cf S -> (length (YG01.blocks S) <= 3)%nat ->
  YG00.apath (YG00cf.free_cf p tr S) trc (tt, S') -> room_live_cf S').
Proof.
split.
- intros U S n tr trc p S' W T R Hb H. destruct (preset_counts_of_three S Hb) as [C1 C2].
  apply (room_live_step_counts U S S' W T R C1 C2). left. exists n, tr, trc, p. exact H.
- intros U S p tr trc S' W T R Hb H. destruct (preset_counts_of_three S Hb) as [C1 C2].
  apply (room_live_step_counts U S S' W T R C1 C2). right. left. exists p, tr, trc. exact H.
Qed.

(* iface_room_np_tail, PresetCfnA.v:460 at 3f83c075b61f (= :518 at 59de238d7ae). *)
Lemma room_live_np_tail_u : forall S, room_live_cf S -> ROOM_cf_k S 2.
Proof. intros S H. exact (room_live_room_k S H). Qed.

End P.
