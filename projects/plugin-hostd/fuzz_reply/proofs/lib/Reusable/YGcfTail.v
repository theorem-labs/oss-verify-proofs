(* CARRIED from a working branch 3dd49fa29fa14b99e3c465cacbfe79a09756bb26,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfTail.v, sha256 4a18b8107e86b0e7adbf30308a5ccf933004acc074ca6c1263d86c51adcebbd3.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the ALLOCATION TAIL.
   A live block's bytes up to the end of its last 8-byte granule are VISIBLE (aview <> None). AR_blocks_law_cf
   gives presence only on [p, p + req_size m); the granule tail [p + req_size m, roundup8 (p + req_size m))
   lies inside the block's CHUNK, because the chunk's user part is rounded: needed_size m includes
   rounded_size m = round_up (max m 8) 8 after the left redzone, and the chunk's extent covers needed_size m
   (a primary chunk is a whole class slot, a secondary chunk the whole mapping past its first page). ARmcf's
   amc_areas (cgif's am_areas) keeps every class's mapped user region and every live-or-quarantined
   secondary's mapping visible in every state (aareas, YG0n.v:133-139), so the chunk is visible.
   The bound is roundup8, never "+ a whole granule": when p + req_size m is 8-aligned the tail is empty, and the
   next granule can be the end of a full class mapping. Visibility only, not ownership or writability.
   No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK13 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0s.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

Lemma round_up8_mono_cf : forall x y, x <= y -> round_up x 8 <= round_up y 8.
Proof. intros x y H. unfold round_up. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. Qed.

(* The chunk's extent covers the left redzone plus the rounded user part. *)
Lemma ck_extent_tail_cf : forall k, 0 <= ck_req k -> ck_rz k + round_up (Z.max (ck_req k) 1) 8 <= ck_extent k.
Proof.
intros k Hn. unfold ck_extent, ck_rz. set (n := ck_req k).
assert (R : round_up (Z.max n 1) 8 <= rounded_size n) by (unfold rounded_size; apply round_up8_mono_cf; lia).
assert (Z0 : 0 <= rz_size n) by (unfold rz_size; apply Z.shiftl_nonneg; lia).
pose proof (rounded_size_bounds n Hn) as [[RB1 _] _].
destruct (from_primary n) eqn:Fp.
- pose proof Fp as Hk. unfold from_primary in Hk. apply Z.leb_le in Hk. unfold needed_primary in Hk.
  destruct (class_id_ok (rounded_size n + rz_size n) ltac:(lia)) as [_ Hc].
  unfold chunk_class, needed_size. rewrite Fp. unfold needed_primary in *. lia.
- unfold sec_map_size, needed_size. rewrite Fp.
  pose proof (round_up_ge (needed_primary n + rz_size n) kPage ltac:(unfold kPage; lia)) as [[H1 _] _].
  unfold needed_primary in *. lia.
Qed.

Theorem amalloc_tail_vis_cf : forall segs B ly S Hp W mem md p m a,
ARcf segs B ly S Hp W mem md -> In (p, m) (ablocks B ly S) ->
p <= a < p + round_up (Z.max m 1) 8 -> aview segs (w_H W) mem a <> None.
Proof.
intros segs B ly S Hp W mem md p m a (M & _ & _) Hin Ha.
apply YG0s.In_ablocks in Hin as (k & Hk & _ & Hu & Hr). subst p m.
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
rewrite G4 in Ha.
pose proof (ck_extent_tail_cf k ltac:(lia)) as EG.
assert (Hext : ck_base B ly k <= a < ck_base B ly k + ck_extent k) by lia.
pose proof (amc_areas _ _ _ _ _ M) as AR.
destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; try (exfalso; exact GG).
- destruct GG as (C1 & _ & _ & EX & EB & X0 & _ & XA & A1 & A2).
  assert (Hel : In (ASp (region_off (prim_class off)), rg_mapped_user (reg S (prim_class off))) (aareas S)).
  { unfold aareas. apply in_or_app. left. apply in_flat_map. exists (prim_class off).
    split; [apply YG0s.In_zseq; lia | left; reflexivity]. }
  pose proof (proj1 (Forall_forall _ _) AR _ Hel) as V. unfold range_vis in V. cbn [fst snd aeval] in V.
  unfold region_base in EB.
  replace a with (ly_space ly + region_off (prim_class off) + (a - (ly_space ly + region_off (prim_class off)))) by lia.
  apply V. lia.
- destruct GG as (O & _ & EB & EX & _ & _).
  assert (Hel : In (ASec r 0, sec_map_size (ck_req k)) (aareas S)).
  { unfold aareas. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    apply in_flat_map. exists k. split; [exact Hk | rewrite Eb; left; reflexivity]. }
  pose proof (proj1 (Forall_forall _ _) AR _ Hel) as V. unfold range_vis in V. cbn [fst snd aeval] in V.
  replace a with (ly_sec ly r + 0 + (a - ly_sec ly r)) by lia.
  apply V. unfold kPage in *. lia.
Qed.

(* A live block's start is 8-aligned (base and left redzone are 16-aligned). *)
Lemma ablock_al8_cf : forall segs B ly S Hp W mem md p m,
ARcf segs B ly S Hp W mem md -> In (p, m) (ablocks B ly S) -> p mod 8 = 0 /\ 0 <= m.
Proof.
intros segs B ly S Hp W mem md p m (M & _ & _) Hin.
apply YG0s.In_ablocks in Hin as (k & Hk & _ & Hu & Hr). subst p m.
pose proof (chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
split; [|lia]. rewrite G4.
apply Z.mod_divide in G3 as [q1 Hq1]; [|lia]. apply Z.mod_divide in G6 as [q2 Hq2]; [|lia].
rewrite Hq1, Hq2. replace (q1 * 16 + q2 * 16) with ((2 * q1 + 2 * q2) * 8) by ring. apply Z_mod_mult.
Qed.

(* The same in the granule-end form: the tail [p + req_size m, roundup8 (p + req_size m)). *)
Corollary amalloc_tail_vis_end_cf : forall segs B ly S Hp W mem md p m a,
ARcf segs B ly S Hp W mem md -> In (p, m) (ablocks B ly S) ->
p + req_size m <= a < (p + req_size m + 7) / 8 * 8 -> aview segs (w_H W) mem a <> None.
Proof.
intros segs B ly S Hp W mem md p m a HA Hin Ha.
destruct (ablock_al8_cf segs B ly S Hp W mem md p m HA Hin) as [P8 Hm].
pose proof (req_size_bounds m Hm) as (RQ & RQ1 & _).
apply (amalloc_tail_vis_cf segs B ly S Hp W mem md p m a HA Hin).
rewrite RQ. unfold round_up.
apply Z.mod_divide in P8 as [q Hq]; [|lia]. subst p.
replace (q * 8 + req_size m + 7) with (q * 8 + (req_size m + 8 - 1)) in Ha by lia.
rewrite Z.div_add_l in Ha by lia. lia.
Qed.

End T.
