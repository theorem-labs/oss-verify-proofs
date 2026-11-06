(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the writer's tree visibility, NARROWED to the granule end, as an every-state consequence
   of ARcf for a tree whose strings are the user parts, past the hidden head, of live hidden blocks.
   tree_vis_cf is the narrowed prhWriter_tree_vis of a Theorem Labs lane's internal file HSMAP-DESIGN.md section 4(b) (its proposal
   text, the last conjunct ending at the last granule (a + k + 7) / 8 * 8 instead of a + k + 8), word for word,
   so that PRH_FnWriter.v's text, once narrowed, is it. A Reusable file may not import lib/A, so it is restated here and not
   taken from PRH_FnWriter.v.
   tree_vis_of_blocks_cf proves it from ARcf, one source per conjunct, for a string (a, k) whose block is
   (a - cf_head, k + cf_head) with base in Hp:
   - 4096 <= a, and the granule end below alloc_ceiling and in one application range: AR_blocks_law_ok_cf
     (4096 <= p, p + req_size n <= alloc_ceiling, in_app p (req_size n)), with alloc_ceiling and kLowShadowBeg
     page-aligned, so rounding the end up to its granule cannot cross either bound (tv_gran_le);
   - 0 <= k: the hidden head fits in the block (hd_bound_cf, YG0sshcf.v, at hd_skip Hp p = cf_head), and
     cf_head mod 8 = 0 excludes cf_head = 1 for the empty block; k < 2 ^ 32: cf_sizes_ok at n
     (n <= sec_map_size n <= cf_nob <= 2 ^ 30);
   - range_addressable: AR_head_shadow_cf (YGcfHeadSh.v) through block_shadow_range (YG0v.v);
   - the hull: AR_shadow_law_ok_cf's hull on (p, req_size n), restricted by shadow_hull_vis_sub_cf;
   - visibility to the granule end: amalloc_tail_vis_cf (YGcfTail.v); the block start is 16-aligned, so
     (a + k + 7) / 8 * 8 ends inside p + round_up (max n 1) 8.
   No address, no unit numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0scf YG0sshcf YG0lawscf YGcfHeadSh YGcfTail.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0s.
(* stdpp, through the LPS modules, shadows several list names; the lemmas here are Stdlib's. *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section TV. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* the internal file HSMAP-DESIGN.md section 4(b), lines 650-656, the body word for word. *)
Definition tree_vis_cf (segs : list Segment) (W : world segs) (mem : word -> option byte) (D : list (Z * Z)) : Prop :=
  forall a k, In (a, k) D ->
    4096 <= a /\ 0 <= k < 2 ^ 32 /\ (a + k + 7) / 8 * 8 <= alloc_ceiling /\
    amem_range a ((a + k + 7) / 8 * 8 - a) /\
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF a k /\
    (0 < k -> shadow_hull_vis (aview segs (w_H W) mem) a k) /\
    (forall x, a <= x < (a + k + 7) / 8 * 8 -> aview segs (w_H W) mem x <> None).

(* Rounding up to the granule cannot cross a page-aligned bound. *)
Lemma tv_gran_le : forall e C, e <= C -> C mod 4096 = 0 -> (e + 7) / 8 * 8 <= C.
Proof.
intros e C H HC. apply Z.mod_divide in HC as [c Hc]; [|lia]. subst C.
assert (D : (e + 7) / 8 < 512 * c + 1) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Theorem tree_vis_of_blocks_cf : forall segs B ly S Hp W mem md D,
ARcf segs B ly S Hp W mem md ->
(forall a k, In (a, k) D -> In (a - cf_head, k + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp) ->
tree_vis_cf segs W mem D.
Proof.
intros segs B ly S Hp W mem md D H HD a k Hin.
destruct (HD a k Hin) as [Hb Hh].
pose proof (AR_blocks_law_ok_cf segs B ly S Hp W mem md _ _ H Hb) as (B16 & B4096 & BC & BA & _ & _ & BN).
pose proof cf_head_nonneg as C0. pose proof cf_head_al as C8.
pose proof alloc_ceiling_value as CR.
assert (RS : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
(* the hidden head fits in the block *)
assert (HN : cf_head <= k + cf_head).
{ pose proof H as (M & _). pose proof Hb as Hb'.
  apply YG0s.In_ablocks in Hb' as (c & Hc & _ & Hu & Hr).
  pose proof (hd_bound_cf B ly S Hp _ c (a - cf_head) M Hc Hu) as [_ HB].
  rewrite (hd_skip_in_cf Hp (a - cf_head) Hh) in HB. unfold ck_n in HB. rewrite Hr in HB.
  revert HB. unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); intros HB; lia. }
(* the request is at most cf_nob <= 2 ^ 30 *)
assert (HK : k + cf_head <= 2 ^ 30).
{ pose proof (cf_sizes_ok (k + cf_head) ltac:(lia)) as SZ. pose proof cf_nob_ok as NB.
  pose proof (needed_primary_bounds (k + cf_head) ltac:(lia)) as [NP _].
  assert (RZ : 0 <= rz_size (k + cf_head)) by (unfold rz_size; apply Z.shiftl_nonneg; lia).
  pose proof (round_up_ge (needed_size (k + cf_head)) kPage ltac:(unfold kPage; lia)) as [[RU _] _].
  assert (NS : needed_primary (k + cf_head) <= needed_size (k + cf_head))
  by (unfold needed_size; destruct (from_primary (k + cf_head)); lia).
  unfold sec_map_size in SZ. clear - SZ NB NP RZ RU NS RS BN. unfold kPage in *. lia. }
split; [lia|]. split; [lia|]. split.
{ apply tv_gran_le; [lia | exact (proj2 CR)]. }
split.
{ unfold amem_range. unfold in_app in BA. destruct BA as [_ [BL | [BH1 BH2]]].
  - assert (G : (a + k + 7) / 8 * 8 <= kLowShadowBeg) by (apply tv_gran_le; [lia | unfold kLowShadowBeg; reflexivity]).
    left. unfold kLowMemEnd, kLowShadowBeg in *. lia.
  - unfold ASAN_CEIL in BH2.
    assert (G : (a + k + 7) / 8 * 8 <= alloc_ceiling) by (apply tv_gran_le; [lia | exact (proj2 CR)]).
    right. unfold kHighMemEnd, kHighMemBeg in *. lia. }
split.
{ pose proof (AR_head_shadow_cf segs B ly S Hp W mem md (a - cf_head) (k + cf_head) (AR_laws_ok_cf segs B) H Hb Hh)
  as [BS _].
  replace (a - cf_head + cf_head) with a in BS by lia.
  eapply block_shadow_range; [exact BS | lia | lia]. }
split.
{ intros _. pose proof (proj2 (AR_shadow_law_ok_cf segs B ly S Hp W mem md _ _ H Hb)) as HV.
  eapply shadow_hull_vis_sub_cf; [exact HV | lia | lia]. }
intros x Hx. apply (amalloc_tail_vis_cf segs B ly S Hp W mem md (a - cf_head) (k + cf_head) x H Hb).
apply Z.mod_divide in B16 as [q Hq]; [|lia].
assert (E : (a + k + 7) / 8 = 2 * q + (k + cf_head + 7) / 8).
{ replace (a + k + 7) with ((k + cf_head + 7) + (2 * q) * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (M1 : (k + cf_head + 7) / 8 <= (Z.max (k + cf_head) 1 + 8 - 1) / 8) by (apply Z.div_le_mono; lia).
unfold round_up. lia.
Qed.

End TV.
