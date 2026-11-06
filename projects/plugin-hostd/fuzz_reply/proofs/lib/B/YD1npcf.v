(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/plugin-hostd/fuzz_reply/lib/A/AD1npcf.v, with its module paths and module names changed. *)
(* Image B's twin of lib/A/AD1npcf.v (a working branch 46f1762ad5a), image-free: A's text with lib/B/YD1w_cf.v
   for lib/A/AD1w_cf.v.
   The cf driver's room bookkeeping, in one place.  The donor driver threads event bounds (`st_nev S < EV_MAX` at
   each allocator call, `st_nev S <= 1` / `<= 64` at its cut points, `st_nev S + EV_LIB * r + 3 <= EV_MAX` into the
   loop).  The cf driver threads instead the interface's non-primary room NP (B/YD1w_cf.v), with its two laws as
   the driver's named hypotheses:
   - before an allocator call, ROOM_cf (YGcfRoomPre.v, carried by YD1vcf's drv_pre) comes from NP by
     iface_room_np_tail (ROOM_cf_k S 2, YGcfRoomKeep.v);
   - after a driver malloc_cf / free_cf, NP comes back by iface_room_np_step, under the driver's live-set bound
     (NP_LIVE = 3: before the first call the driver holds at most two blocks).
   After the last harness call the driver uses neither law for its second free: the tail law's ROOM_cf_k S 2 pays
   both frees through YGcfRoomStep.free_room_keep_cf (room_after_free_cf below). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00cf YG01cf YG0ncf YGcfNames YGcfRoomPre YGcfRoomKeep YGcfRoomStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1w_cf.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Section n. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable B : asyms.
Variable NP : astate -> Prop.

(* ROOM_cf before a driver allocator call *)
Lemma room_of_np : iface_room_np_tail NP -> forall S, NP S -> ROOM_cf S.
Proof. intros T S H. exact (RK_room S 2 (T S H)). Qed.

(* NP after a driver malloc_cf, from the call's model path *)
Lemma np_after_malloc_cf : iface_room_np_step NP ->
  forall segs ly S Hp W mem md n tr trc p S',
  ARcf segs B ly S Hp W mem md -> qtight S -> NP S -> (length (blocks S) <= NP_LIVE)%nat ->
  apath (malloc_cf n tr S) trc (p, S') -> NP S'.
Proof.
  intros [M _] segs ly S Hp W mem md n tr trc p S' HAR HQ HN HL HP.
  exact (M (as_universe B) S n tr trc p S' (amc_wf _ _ _ _ _ (proj1 HAR)) HQ HN HL HP).
Qed.

(* NP after a driver free_cf, from the call's model path *)
Lemma np_after_free_cf : iface_room_np_step NP ->
  forall segs ly S Hp W mem md p tr trc S',
  ARcf segs B ly S Hp W mem md -> qtight S -> NP S -> (length (blocks S) <= NP_LIVE)%nat ->
  apath (free_cf p tr S) trc (tt, S') -> NP S'.
Proof.
  intros [_ F] segs ly S Hp W mem md p tr trc S' HAR HQ HN HL HP.
  exact (F (as_universe B) S p tr trc S' (amc_wf _ _ _ _ _ (proj1 HAR)) HQ HN HL HP).
Qed.

(* the room one free leaves of a headroom k + 1 (after the last harness call) *)
Lemma room_after_free_cf : forall segs ly S Hp W mem md k p tr trc S',
  ARcf segs B ly S Hp W mem md -> ROOM_cf_k S (Datatypes.S k) -> apath (free_cf p tr S) trc (tt, S') -> ROOM_cf_k S' k.
Proof.
  intros segs ly S Hp W mem md k p tr trc S' HAR R HP.
  pose proof (amc_wf _ _ _ _ _ (proj1 HAR)) as W0. unfold Wf_cf in W0.
  exact (free_room_keep_cf k p tr S trc S' (room_shape_cf_of_WfP_cf _ _ _ _ _ W0) R HP).
Qed.
End n.
