(* omx-clap-core/fuzz_preset, Spec: P8's conclusion (h-hpreset-7's port of asan_halts / agrees, piece P8;
   c-frame-alloc). No consumer allocation of the harness model returns NULL on a full class.

   preset_room: at every consumer allocation i of target_run's calls (PresetRun.hruns / hcons, any number of calls,
   any grants), an allocator state s whose live chunks are the model's live requests plus at most 3 of the driver's,
   whose quarantine is quar_bytes_ok and a FIFO window (fifo_ok) of its accounted free history H0 ++ the model's frees,
   has a free slot of every primary class c (room_at s c): classes but 17 by PresetGate.gate_not17, class 17 by
   PresetClose17.room17.
   no_null_preset: so the instance's NULL fact (YGcfRoom.malloc_cf_null_full, in its grant-flag form) leaves only an
   environment refusal (g = false) as the cause of a NULL there.

   Nothing here is a function's proof (rule 24). *)
(* Modified by Theorem Labs, 2026-10-30, for the kit: the accounted free
   history is H0 ++ PresetRunQ.hfrees_q (the model's frees that enter the quarantine; a free above kQuarantineMax is
   recycled at once, free_cf's size test), not H0 ++ hfrees. *)
From Stdlib Require Import ZArith List Lia Bool Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import
  PjTree PresetReqAt PresetRun PresetRunQ PresetRoom PresetGate PresetSite17 PresetClose17.
Import ListNotations.
Local Open Scope Z_scope.

Theorem preset_room : forall sm x os i s H0 c, Z.of_nat (length x) <= MAXB ->
  nth i (hcons sm x os) false = true -> alloc_at (hruns sm x os) i -> 1 <= c <= 30 ->
  (exists d, (length d <= 3)%nat /\ Permutation (rs_live s) (hlive (firstn i (hruns sm x os)) ++ d)) ->
  quar_bytes_ok s -> fifo_ok (map acct_size (H0 ++ hfrees_q (firstn i (hruns sm x os)))) (rs_quar s) ->
  room_at s c.
Proof.
  intros sm x os i s H0 c Hx Hc Ha Hcr Hd Hq Hf.
  destruct (Z.eq_dec c 17) as [->|Hc17]; [exact (room17 sm x os i s H0 Hx Hc Ha Hd Hq Hf)|].
  apply room_at_of_room_ok; [exact Hq|].
  pose proof (gate_not17 sm x os Hx c Hcr Hc17 i) as G.
  destruct Hd as (d & Hdl & Hp). apply (g_room_mono c _ _ G).
  rewrite (ccnt_perm c _ _ Hp), ccnt_app. pose proof (g_ccnt_len c d).
  change (ccnt c (hlive (firstn i (hruns sm x os)))) with (cnt (in_cls c) (hlive (firstn i (hruns sm x os)))).
  unfold DRV. lia.
Qed.

Corollary no_null_preset : forall sm x os i s H0 n c (g : bool) (null : Prop), Z.of_nat (length x) <= MAXB ->
  nth i (hcons sm x os) false = true -> alloc_at (hruns sm x os) i -> cls n = Some c ->
  (exists d, (length d <= 3)%nat /\ Permutation (rs_live s) (hlive (firstn i (hruns sm x os)) ++ d)) ->
  quar_bytes_ok s -> fifo_ok (map acct_size (H0 ++ hfrees_q (firstn i (hruns sm x os)))) (rs_quar s) ->
  (g = true -> null -> null_full s n) -> null -> g = false.
Proof.
  intros sm x os i s H0 n c g null Hx Hc Ha Hn Hd Hq Hf Hnf Hnull.
  apply (no_null_of_room_at g null s n c Hnf Hn); [|exact Hnull].
  exact (preset_room sm x os i s H0 c Hx Hc Ha (g_cls_range n c Hn) Hd Hq Hf).
Qed.
