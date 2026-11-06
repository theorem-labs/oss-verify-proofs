(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset, row A18 of the COUNT meter (a Theorem Labs lane, lane CountDrvA): the BASE,
   i.e. the secondary map entries the driver itself makes before the first harness call. drv_secs_cf is the last
   conjunct of lib/A/PresetD1sitesA.v drv_minv_cf; this file holds its definition and its steps.
   IMAGE INDEPENDENT: no asyms, no image literal, only the allocator model. The asan-ubsan driver (lib/AU) Requires this
   file as it stands.
   WHAT THE DRIVER MAPS (the walk of record). Before the first harness call, main makes exactly these allocator calls:
   - malloc_cf 65536 from init_state, where st_secs = [] (lib/A/PresetD2runAPfM.v m1_common_cf);
   - per grow of the read buffer, malloc_cf (2 * cap) then free_cf of the old buffer (lib/A/PresetPinvA23Pf.v
     gr_grow_cf), with cap = 2 ^ e doubling from 2 ^ 16 and 2 * cap <= 2 ^ 26 (the tail has 65536 <= cap <= 2 ^ 26);
     the read loop has NO realloc;
   - the payload copy's malloc_cf (payload_len data) (lib/A/PresetD2eAPf.v runqm_at), 0 < payload_len data < cap.
   Between two harness calls the loop makes no allocator call (lib/A/PresetD1rAPf.v calls_loop_cf), so this base is
   fixed before the first call. Every request of the first two kinds is secondary (65536 > 64512), and
   sec_map_size (2 ^ k) = 2 ^ k + 8192 for 16 <= k (drv_sec_map_size_pages); free_cf keeps both counts (A14). So at
   buffer size cap the state holds at most log2 cap - 15 counted entries of at most
   2 cap - 65536 + 8192 (log2 cap - 15) bytes: drv_secs_cf. At cap <= 2 ^ 26 that is 11 entries and 134,242,304
   bytes; one more malloc_cf of n <= 2 ^ 26 bytes adds at most 1 entry of at most n + 12,294 bytes
   (drv_sec_map_size_le). Both are inside rp_base (rp_NB = 64, rp_TB = 2 ^ 30, lib/Spec/PresetRoomPos.v):
   drv_secs_rp_base.
   THE FORM. drv_secs_cf is conditional on A14's closed secs_steps_cf (lib/Reusable/YGcfSecsStep.v), as
   PresetRoomPos.rp_base is, so no lemma below takes a premise for the steps: each one reads the call steps out of
   secs_steps_cf (its malloc projection, A14's secs_malloc_step, and its free projection, secs_free_step), and a top
   discharges secs_steps_cf once with YGcfSecsStep.secs_steps_cf_holds. The counts are the cf layer's Z counts
   (lib/Reusable/YGcfNames.v nsec_cf / sec_T_cf); the count of entries is stated through PresetRoomPos.rp_nsec.
   Rule 24: no function is proved here (a driver invariant of an existing walk). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetSecTotal.
Import ListNotations.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. The base conjunct.                                                    *)
Definition drv_secs_cf (S : astate) (cap : Z) : Prop :=
  YGcfSecsStep.secs_steps_cf ->
  PresetRoomPos.rp_nsec S <= Z.log2 cap - 15 /\
  YGcfNames.sec_T_cf S <= 2 * cap - 65536 + 8192 * (Z.log2 cap - 15).

(* ---------------------------------------------------------------------- *)
(* 2. The mapped size of one secondary (YG00.v:63-75).                       *)
Lemma drv_rz_size_le : forall n, 0 <= rz_size n <= 2048.
Proof.
intros n. unfold rz_size, rz_log.
repeat match goal with |- context [if n <=? ?c then _ else _] => destruct (n <=? c) end;
split; apply Z.leb_le; reflexivity.
Qed.

(* a request of whole pages above the primary limit maps itself, two 2048-byte red zones and one page *)
Lemma drv_sec_map_size_pages : forall n, 64513 <= n -> n mod 4096 = 0 -> sec_map_size n = n + 8192.
Proof.
intros n Hn Hm.
pose proof (proj2 (Z.div_exact n 4096 ltac:(lia)) Hm) as Hk.
set (k := n / 4096) in Hk. clearbody k. subst n.
assert (Hz : rz_size (4096 * k) = 2048).
{ unfold rz_size, rz_log.
  repeat match goal with |- context [if ?x <=? ?c then _ else _] => destruct (Z.leb_spec x c); [lia|] end.
  reflexivity. }
assert (Hr : rounded_size (4096 * k) = 4096 * k).
{ unfold rounded_size, round_up. rewrite Z.max_l by lia.
  match goal with |- ?t / 8 * 8 = _ => replace t with (512 * k * 8 + 7) by lia end.
  rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
assert (Hf : from_primary (4096 * k) = false).
{ unfold from_primary, needed_primary, kMaxSize. rewrite Hr, Hz. apply Z.leb_gt. lia. }
unfold sec_map_size, needed_size. rewrite Hf. cbv beta iota. unfold needed_primary. rewrite Hr, Hz. unfold round_up, kPage.
match goal with |- ?t / 4096 * 4096 + 4096 = _ => replace t with ((k + 1) * 4096 + 4095) by lia end.
rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
Qed.

(* any request: the size rounded to 8, at most two 2048-byte red zones, page rounding and one page *)
Lemma drv_sec_map_size_le : forall n, sec_map_size n <= Z.max n 8 + 12294.
Proof.
intros n. pose proof (drv_rz_size_le n) as Hz.
assert (Hr : rounded_size n <= Z.max n 8 + 7).
{ unfold rounded_size, round_up. pose proof (Z.mul_div_le (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia. }
assert (Hd : needed_size n <= Z.max n 8 + 7 + 4096).
{ unfold needed_size, needed_primary. destruct (from_primary n); lia. }
unfold sec_map_size, round_up, kPage. pose proof (Z.mul_div_le (needed_size n + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

(* one allocator call's rule (the layer's secs_call_post), weakened to one entry of at most sec_map_size n bytes *)
Lemma drv_secs_post_le : forall n s r, YGcfNames.secs_call_post n s r ->
  PresetRoomPos.rp_nsec (snd r) <= PresetRoomPos.rp_nsec s + 1 /\
  YGcfNames.sec_T_cf (snd r) <= YGcfNames.sec_T_cf s + sec_map_size n.
Proof.
intros n s [q s'] H.
unfold YGcfNames.secs_call_post, YGcfNames.secs_step, YGcfNames.secs_call_d, YGcfNames.secs_call_t in H.
cbn [fst snd] in H. unfold PresetRoomPos.rp_nsec. cbn [snd].
pose proof (PresetSecTotal.sec_map_size_pos n) as Hp.
revert H. destruct q; destruct (from_primary n); cbv beta iota; intros [N T]; split; lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The steps over the driver's allocator calls.                          *)
Section steps.
Context {ci : CfImg}.

(* the first malloc (main+0x54) from a state with no secondary map entry *)
Lemma drv_secs_first : forall S trc tr (q : sptr) S', st_secs S = [] ->
  apath (malloc_cf 65536 trc S) tr (q, S') -> drv_secs_cf S' 65536.
Proof.
intros S trc tr q S' E Hp Hss.
destruct (Hss ci) as (HM & _).
destruct (drv_secs_post_le 65536 S (q, S') (HM 65536 trc S tr (q, S') Hp)) as [N T]. cbn [snd] in N, T.
assert (N0 : PresetRoomPos.rp_nsec S = 0) by (unfold PresetRoomPos.rp_nsec, YGcfNames.nsec_cf; rewrite E; reflexivity).
assert (T0 : YGcfNames.sec_T_cf S = 0) by (unfold YGcfNames.sec_T_cf; rewrite E; reflexivity).
rewrite (drv_sec_map_size_pages 65536) in T by (lia || reflexivity).
change (Z.log2 65536) with 16. lia.
Qed.

(* one grow of the read buffer: malloc_cf (2 * cap), then free_cf of the old buffer *)
Lemma drv_secs_grow : forall S S1 S2 cap trc tr (q : sptr) (p : sptr) trc' tr',
  drv_secs_cf S cap -> 65536 <= cap < 2 ^ 26 -> (exists e, cap = 2 ^ e) ->
  apath (malloc_cf (2 * cap) trc S) tr (q, S1) -> apath (free_cf p trc' S1) tr' (tt, S2) ->
  drv_secs_cf S2 (2 * cap).
Proof.
intros S S1 S2 cap trc tr q p trc' tr' H0 Hc (e & He) Hp1 Hp2 Hss.
destruct (H0 Hss) as [N0 T0].
destruct (Hss ci) as (HM & HF & _).
destruct (drv_secs_post_le (2 * cap) S (q, S1) (HM _ _ _ _ _ Hp1)) as [N1 T1]. cbn [snd] in N1, T1.
destruct (HF _ _ _ _ _ Hp2) as [N2 T2].
assert (He16 : 16 <= e).
{ destruct (Z.lt_ge_cases e 16) as [Hlt|]; [|lia]. exfalso.
  destruct (Z.lt_ge_cases e 0) as [Hneg|Hnn].
  - rewrite (Z.pow_neg_r 2 e Hneg) in He. lia.
  - pose proof (Z.pow_lt_mono_r 2 e 16 ltac:(lia) ltac:(lia) Hlt). change (2 ^ 16) with 65536 in *. lia. }
assert (Hk : cap = 65536 * 2 ^ (e - 16)).
{ rewrite He. change 65536 with (2 ^ 16). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
assert (Hm : (2 * cap) mod 4096 = 0).
{ replace (2 * cap) with (32 * 2 ^ (e - 16) * 4096) by lia. apply Z.mod_mul. lia. }
rewrite (drv_sec_map_size_pages (2 * cap)) in T1 by (lia || exact Hm).
rewrite Z.log2_double by lia.
unfold PresetRoomPos.rp_nsec in *. rewrite N2, T2. lia.
Qed.

(* the rp base (lib/Spec/PresetRoomPos.v rp_base, rp_NB = 64, rp_TB = 2 ^ 30) at a driver state with cap <= 2 ^ 26,
   and after one more malloc_cf of at most 2 ^ 26 bytes from it: the two loop entries (the empty-payload arm's tail
   state and the state after the payload malloc) *)
Lemma drv_secs_rp_base : forall S cap, drv_secs_cf S cap -> 65536 <= cap <= 2 ^ 26 ->
  PresetRoomPos.rp_base S /\
  (forall n trc tr (q : sptr) S', 0 <= n <= 2 ^ 26 -> apath (malloc_cf n trc S) tr (q, S') -> PresetRoomPos.rp_base S').
Proof.
intros S cap H Hc.
assert (L : Z.log2 cap <= Z.log2 (2 ^ 26)) by (apply Z.log2_le_mono; lia).
rewrite Z.log2_pow2 in L by lia.
unfold PresetRoomPos.rp_base, PresetRoomPos.rp_NB, PresetRoomPos.rp_TB.
change (2 ^ 26) with 67108864 in *. change (2 ^ 30) with 1073741824.
split.
- intros Hss. destruct (H Hss) as [N T]. split; lia.
- intros n trc tr q S' Hn Hp Hss. destruct (H Hss) as [N T].
  destruct (Hss ci) as (HM & _).
  destruct (drv_secs_post_le n S (q, S') (HM _ _ _ _ _ Hp)) as [N1 T1]. cbn [snd] in N1, T1.
  pose proof (drv_sec_map_size_le n) as Hs. split; lia.
Qed.
End steps.
