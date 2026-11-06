(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (route (B''): the call memory in the call rules): the cf forms are YGcallx's at
   QMm := QMm_cf, acall_pre_cf's trailing conjuncts verbatim (since the cf layer's field round 3 they end with
   cf_hull_ok S /\ arodata_ok_cf segs B mem; part 3c took memnorm out), so acall_pre_cf_x / afree_realizes_cf_x stay BY
   REFLEXIVITY; QM := QM_cf, their STATE part (the new FA_GROW headroom + FA_GROW_MAX / 8, and cf_hull_ok), for the model
   laws; QMQ_cf (QMm_cf S mem -> QM_cf S) is a projection. QM_cf_of_room takes cf_hull_ok, as the layer's
   acall_pre_cf_intro does (abudget_room_cf and mroom_cf_of_live need it); QMm_cf_of_room adds the memory fact. *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): the cf call post under the re-hide
   (YGcfRehidePost.acall_post_cf_rh, the post of the primed free and realloc rows) as the generic rules' callee post
   APOST_cf, with its two laws POST_AR_cf / POST_J_cf (YGcallx's apost_ar_law / apost_j_law) at the world relation
   wle' segs RZ_cf; ajournal_x_of_rh_off is the fact POST_J_cf rests on: a call's dead set misses each view-frame
   domain of a journal around the call. Additive: no existing statement changes. *)
(* Modified by Theorem Labs, 2026-10-30 (the call memory's RELRO fact): arodata_ok_cf_of_journal carries the call
   memory's arodata_ok_cf (QMm_cf's last conjunct) across a journal at any world relation R; arodata_ok_cf_of_journal_P
   starts it from a walk entry's reader form arodata_okP (YGcfAroBridge.arodata_ok_cf_of_P). Additive. *)
(* Modified by Theorem Labs, 2026-10-31 (field round 3 part 3c: aro_addr_cf covers the RELRO range and cf_ro_reads):
   arodata_ok_cf_of_journal and arodata_ok_cf_of_journal_P take YGcfAroBridge.ro_reads_nw_t (a segment inside 2^64
   holds each cf_ro_reads range), as YGcfAroBridge.arodata_ok_cf_of_P does, and their PST premise covers every
   aro_addr_cf address. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcallcf.v, with its module paths and module names changed; 45 of its 104 lines of code are new or changed and 535 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane WalkB2, route R; integrator ReallocPrimary).
   rule 24: no function proved here (a lemma on a call's dead shadow set and the journal's view-frame domains).
   L2 at fuzz_reply image A: the cf dead set of a call, dead_shadow_new lyc Sc S2 (lib/A/YGcfRehidePost.v:70), misses
   each of the five view-frame domains of the journal YCbqG.ajournal_xR (lib/Reusable/YCbqG.v): above alloc_ceiling,
   the user bytes of the blocks live at the journal's end, the image, the journal start's frames and their shadow, and
   ly_extra. So a journal whose frames hold off the dead set gives the frames of the journal itself. The statement is
   the shared text of ajournal_x_of_rh_off (CfR, 2026-10-30; first built as the R4 probe, a working branch
   cb17f1003ddf lib/A/R4ProbeROff.v:89). Per domain:
   - above the ceiling: dead_shadow_new_below_ceiling (YGcfRehidePost.v:231);
   - block bytes: AR_laws_x's alx_blocks at the journal's end puts them in application memory; dead_shadow_new_app;
   - image: segs_low puts it below kLowMemEnd; dead_shadow_new_not_low (YGcfRehidePost.v:236);
   - frame bytes: frame_facts_cf at the CALL state (the start's frames are live there) puts them in the fake stack
     (ly_F, kFakeStackSize), application memory; dead_shadow_new_app. Frame shadow: dsn_frame_shadow_off below, from
     dead_shadow_new_off (YGcfRehidePost.v:123) at the static extent (ly_F lyc, kFakeStackSize) with sec_placed;
   - ly_extra: ARx_extra_law_ok_ARcf (Reusable/YGcfExtra.v) at the call state; dead_shadow_new_app.
   The lib/B twin is lib/B/AjxRhOff.v, the same text with lib/B's YGcfRehidePost. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG0ncf YG0scf YGcfExtra.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfRehidePost.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* A value in both halves of a pairwise list is related to itself. *)
Lemma pairwise_app_dup {X : Type} (R : X -> X -> Prop) : forall (l1 l2 : list X) x,
  pairwise R (l1 ++ l2) -> In x l1 -> In x l2 -> R x x.
Proof.
induction l1 as [|y l1 IH]; intros l2 x P H1 H2; [destruct H1|].
cbn in P. destruct P as [F P]. destruct H1 as [->|H1].
- exact (proj1 (Forall_forall _ _) F x (in_or_app _ _ _ (or_intror H2))).
- exact (IH l2 x P H1 H2).
Qed.

Section f. Context {rc : YM05.RunCeil}.
(* The shadow of an 8-aligned range inside the fake stack misses a call's dead set: dead_shadow_new_off at the static
   extent e := (ly_F lyc, kFakeStackSize); e is no dead slot, since a value in both halves of sec_placed's pairwise list
   would be disjoint from itself. At the index-keyed core (fa123bc2baa) dead_shadow_new_off also takes
   live_slots_placed at the dead set's entry state, which is Sc here. *)
Lemma dsn_frame_shadow_off : forall lyc Sc S2 fa fb a,
  sec_placed lyc Sc -> live_slots_placed lyc Sc ->
  ly_F lyc <= fa -> fa + fb <= ly_F lyc + kFakeStackSize ->
  fa mod 8 = 0 -> 0 <= fa -> 0 <= fb ->
  shadow_addr fa <= a < shadow_addr fa + fb / 8 ->
  ~ dead_shadow_new lyc Sc S2 a.
Proof.
intros lyc Sc S2 fa fb a HP HL F1 F2 M8 H0 Hb Ha.
set (x := fa + 8 * (a - shadow_addr fa)).
assert (Ex : shadow_addr x = a).
{ unfold x, shadow_addr in *. pose proof (Z.div_mod fa 8 ltac:(lia)) as D. rewrite M8 in D.
  replace (fa + 8 * (a - (SHADOW_OFF + fa / 8))) with ((a - SHADOW_OFF) * 8) by lia.
  rewrite Z.div_mul by lia. lia. }
assert (Hx : fa <= x < fa + fb).
{ unfold x, shadow_addr in *. pose proof (Z.div_mod fb 8 ltac:(lia)). pose proof (Z.mod_pos_bound fb 8 ltac:(lia)). lia. }
rewrite <- Ex.
assert (Hs : In (ly_F lyc, kFakeStackSize) (static_extents lyc)) by (unfold static_extents, owned_extents; cbn; tauto).
apply (dead_shadow_new_off lyc Sc S2 (ly_F lyc, kFakeStackSize) x HP HL).
- apply in_or_app. right. exact Hs.
- cbn [snd]. unfold kFakeStackSize. lia.
- cbn [fst snd]. lia.
- intros r sm Hd Hin Eq. destruct HP as [_ PD]. rewrite <- Eq in Hin.
  pose proof (pairwise_app_dup zdisjoint _ _ _ PD Hin Hs) as Z. unfold zdisjoint in Z. cbn [fst snd] in Z.
  unfold kFakeStackSize in Z. lia.
Qed.
End f.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* The call (lyc, Sc) -> S2 sits inside a journal from (ly, S) to (ly', S'): ARcf at the call (its premise), the call's
   layout and frames reached from the journal's start (layout_le, frames kept), ARx at the end. *)
Theorem ajournal_x_of_rh_off : forall n lyc Sc Hpc Wc memc mdc S2 ly S ly' S' Hp' W' mem' md',
  ARcf segs B lyc Sc Hpc Wc memc mdc ->
  layout_le n ly lyc ->
  (forall f, In f (frames S) -> In f (frames Sc)) ->
  ARx ly' S' Hp' W' mem' md' ->
  (forall a, YM05.alloc_ceiling <= a -> ~ dead_shadow_new lyc Sc S2 a) /\
  (forall p n' i, In (p, n') (ablocks B ly' S') -> 0 <= i < req_size n' -> ~ dead_shadow_new lyc Sc S2 (p + i)) /\
  (forall a, in_img segs a -> ~ dead_shadow_new lyc Sc S2 a) /\
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     ~ dead_shadow_new lyc Sc S2 a) /\
  (forall a, Exists (in_zr a) (ly_extra ly) -> ~ dead_shadow_new lyc Sc S2 a).
Proof.
intros n lyc Sc Hpc Wc memc mdc S2 ly S ly' S' Hp' W' mem' md' HC Hly Hfr HAR.
pose proof HC as [Mc _].
(* the dead set's entry state is the call state: its live slots are placed by the allocator invariant there *)
assert (LSP : live_slots_placed lyc Sc).
{ pose proof (amc_wf _ _ _ _ _ Mc) as WF.
  apply live_slots_placed_of_wf_cf; [eapply wfc_secondary; exact WF | eapply wfc_chunks; exact WF]. }
destruct Hly as (_ & _ & _ & _ & _ & Fc & _ & _ & _ & _ & _ & _ & _ & Xc & _).
split; [|split; [|split; [|split]]].
- intros a Ha Hd. pose proof (dead_shadow_new_below_ceiling lyc Sc S2 a Hd). lia.
- intros p n' i Hin Hi. pose proof (alx_blocks segs B ARx LAWS ly' S' Hp' W' mem' md' p n' HAR Hin) as (_ & _ & _ & IA & _).
  apply dead_shadow_new_app. exact (in_app_addr p (req_size n') (p + i) IA ltac:(lia)).
- intros a Hi Hd. pose proof (segs_low a Hi). pose proof (dead_shadow_new_not_low lyc Sc S2 a Hd). lia.
- intros cid pos a Hin Hr. pose proof (Hfr _ Hin) as Hin'.
  pose proof (frame_facts_cf B lyc Sc Hpc _ cid pos Mc Hin') as (C1 & C2 & [IA1 IA2] & _ & PA & A1 & A2 & A3 & A4 & A5 & _).
  rewrite Fc in IA1, IA2, PA. change (2 ^ 20) with 1048576 in A1. unfold YG0f.page_aligned in PA.
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. unfold frame_addr in *.
  destruct Hr as [Hr | Hr].
  + apply dead_shadow_new_app. apply (in_app_addr (ly_F ly) kFakeStackSize a (conj IA1 IA2)).
    unfold kFakeFramesOff in *. lia.
  + apply (dsn_frame_shadow_off lyc Sc S2 (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) a (amc_placed _ _ _ _ _ Mc) LSP);
      rewrite ?Fc; try exact Hr; unfold kFakeFramesOff, kFakeStackSize in *; lia.
- intros a HX. rewrite <- Xc in HX.
  pose proof (ARx_extra_law_ok_ARcf segs B lyc Sc Hpc Wc memc mdc a HC HX) as (_ & _ & _ & _ & _ & _ & APP).
  apply dead_shadow_new_app. exact APP.
Qed.
End r.

(* The lane's Print Assumptions (toolchain/allowed-axioms.txt). *)
Check dsn_frame_shadow_off. Print Assumptions dsn_frame_shadow_off.
Check ajournal_x_of_rh_off. Print Assumptions ajournal_x_of_rh_off.
