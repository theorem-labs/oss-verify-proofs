(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), FAKE-STACK SHADOW VISIBILITY.
   ARmcf's amc_areas (cgif's am_areas, verbatim) keeps, in every state, the shadow of the fake stack's FRAMES part
   visible: aareas (YG0n.v:133-139) lists (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8).
   So the shadow byte of every a in [ly_F + kFakeFramesOff, ly_F + kFakeStackSize) is present. The region's header
   [ly_F, ly_F + kFakeFramesOff) is NOT covered by that entry and is not claimed here.
   A live frame's shadow hull stays inside that part and does not poke out: fs_frame_off is a multiple of 64 and
   fs_frame_off cid pos + fs_frame_bytes cid <= kFakeFramesOff + (cid + 1) * 2 ^ 20 <= kFakeStackSize; class 10's
   last frame ends EXACTLY at the region's end, 36,864 + 11 * 2 ^ 20 = 11,571,200 = 0xb09000 = kFakeStackSize.
   Frame start and end are 64-aligned, so the 8-aligned shadow hull of [x, x + n) is exactly
   [shadow_addr x, shadow_addr (x + n)). No address. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK13 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section V. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Theorem ARcf_fs_shadow_vis : forall segs B ly S Hp W mem md a,
ARcf segs B ly S Hp W mem md -> ly_F ly + kFakeFramesOff <= a < ly_F ly + kFakeStackSize ->
aview segs (w_H W) mem (shadow_addr a) <> None.
Proof.
intros segs B ly S Hp W mem md a (M & _ & _) Ha.
pose proof (lo_F_al _ (amc_layout _ _ _ _ _ M)) as FA. unfold page_aligned in FA.
assert (Hel : In (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8) (aareas S)).
{ unfold aareas. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
  cbn. right. right. right. right. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (amc_areas _ _ _ _ _ M) _ Hel) as V. unfold range_vis in V. cbn [fst snd aeval] in V.
remember (ly_F ly + kFakeFramesOff) as b eqn:Hb.
assert (B8 : b mod 8 = 0).
{ rewrite Hb. unfold kFakeFramesOff. apply Z.mod_divide in FA as [q Hq]; [|lia]. rewrite Hq.
  replace (q * 4096 + (4096 + 32768)) with ((512 * q + 4608) * 8) by ring. apply Z_mod_mult. }
assert (K : kFakeStackSize - kFakeFramesOff = 1441792 * 8) by (unfold kFakeStackSize, kFakeFramesOff; reflexivity).
assert (Bm : b = 8 * (b / 8)) by (pose proof (Z.div_mod b 8 ltac:(lia)); lia).
assert (E : shadow_addr a = shadow_addr b + (a / 8 - b / 8)) by (unfold shadow_addr; lia).
rewrite E. apply V.
assert (D1 : b / 8 <= a / 8) by (apply Z.div_le_mono; lia).
assert (D2 : a / 8 < b / 8 + 1441792) by (apply Z.div_lt_upper_bound; lia).
rewrite K, Z.div_mul by lia. lia.
Qed.

(* h-rw-pre-5's exact text. *)
Definition ARx_frame_hull_vis (segs : list Segment) (B : asyms) (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop) : Prop :=
forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
shadow_hull_vis (aview segs (w_H W) mem) (frame_addr ly cid pos) (fs_frame_bytes cid).

Lemma div8_64_cf : forall q, q * 64 / 8 = q * 8.
Proof. intros q. replace (q * 64) with (q * 8 * 8) by ring. apply Z.div_mul. lia. Qed.

Theorem ARx_frame_hull_vis_cf_ok : forall segs B, AR_laws_cf segs B -> ARx_frame_hull_vis segs B (ARcf segs B).
Proof.
intros segs B _ ly S Hp W mem md cid pos HA Hin.
pose proof HA as (M & _ & _).
destruct (frame_facts_cf B ly S Hp _ cid pos M Hin) as (Hc & Hp' & _ & _ & FA & F1 & F2 & F3 & F4 & F5 & _).
unfold page_aligned in FA.
apply Z.mod_divide in FA as [qF HqF]; [|lia]. apply Z.mod_divide in F3 as [qO HqO]; [|lia].
apply Z.mod_divide in F5 as [qN HqN]; [|lia].
assert (EX : frame_addr ly cid pos = (64 * qF + qO) * 64) by (unfold frame_addr; lia).
assert (EN : frame_addr ly cid pos + fs_frame_bytes cid = (64 * qF + qO + qN) * 64) by lia.
unfold shadow_hull_vis. intros s Hs.
rewrite EX in Hs. replace ((64 * qF + qO) * 64 + fs_frame_bytes cid - 1) with ((64 * qF + qO + qN) * 64 - 1) in Hs by lia.
unfold shadow_addr, SHADOW_OFF in Hs. rewrite div8_64_cf in Hs.
set (x8 := (64 * qF + qO) * 8) in *. set (e := 64 * qF + qO + qN) in *.
assert (Q1 : (2147450880 + x8) / 8 * 8 = 2147450880 + x8).
{ unfold x8. replace (2147450880 + (64 * qF + qO) * 8) with ((268431360 + (64 * qF + qO)) * 8) by ring.
  rewrite Z.div_mul by lia. reflexivity. }
assert (Q2 : (e * 64 - 1) / 8 = e * 8 - 1) by (symmetry; apply Z.div_unique with (r := 7); lia).
rewrite Q2 in Hs.
assert (Q3 : (2147450880 + (e * 8 - 1)) / 8 = 268431360 + e - 1) by (symmetry; apply Z.div_unique with (r := 7); lia).
rewrite Q1, Q3 in Hs.
set (a := (64 * qF + qO) * 64 + 8 * (s - (2147450880 + x8))).
assert (Ea : s = shadow_addr a).
{ unfold shadow_addr, SHADOW_OFF, a, x8.
  replace ((64 * qF + qO) * 64 + 8 * (s - (2147450880 + (64 * qF + qO) * 8))) with ((s - 2147450880) * 8) by ring.
  rewrite Z.div_mul by lia. lia. }
rewrite Ea. apply (ARcf_fs_shadow_vis segs B ly S Hp W mem md a HA).
unfold a, x8. unfold kFakeFramesOff, kFakeStackSize in *.
assert (HO : fs_frame_off cid pos = qO * 64) by exact HqO.
lia.
Qed.

End V.
