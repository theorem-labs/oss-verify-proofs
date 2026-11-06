(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/YGcallx.v, with its module paths and module names changed; 66 of its 188 lines of code are new or changed and 1110 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane WalkB2, route R; integrator ReallocPrimary).
   rule 24: no function proved here (the call-journal step of a re-hiding call, at the cf instance).
   POST_J_cf at fuzz_reply image A: call_effect_journal_rh_cf, the re-hide twin of Reusable/YGcallx.v's
   call_effect_journal_xw (the step from a callee's post to the journal across the call). Its world and frame premises
   are the two conjuncts that change in a re-hiding post (lib/A/YGcfRehidePost.v acall_post_cf_rh at :292 / :295; the
   primed realloc leaf YG0dcfR.realloc_leaf_cf_rh has the same two), at ly S S' := lyc Sc S2:
   - the world: wle_in segs (dead_shadow_new lyc Sc S2) W W2, so the hidden set grows only inside the call's dead set;
   - the frame: view equality off the owned sets, the call's scratch, Eb AND the dead set.
   Its journal is at the world relation R := wle' segs RZ_cf (YA0nH.v), the re-hide zone: the world conjunct by
   wle_in_mono and dead_shadow_new_RZ (lib/A/YGcfRehidePost.v:199); each of the five frame clauses is
   call_effect_journal_xw's, its extra `~ dead_shadow_new lyc Sc S2 a` given by L2 (lib/A/AjxRhOff.v
   ajournal_x_of_rh_off) with the journal started at the call state. So the premise ARcf at the call state is the only
   one call_effect_journal_xw does not take. Statement agreed with CfR (2026-10-30). The lib/B twin is
   lib/B/AjxCallRh.v, the same text with lib/B's YGcfRehidePost and AjxRhOff. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import FCiface YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfRehidePost AjxRhOff.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Hypothesis OWNLOW : ARx_owned_low_law segs B ARx.
Let ERRIMG : forall a, as_errno B <= a < as_errno B + 4 -> in_img segs a := proj1 (proj2 errno_low).
Local Abbreviation LBLK := (alx_blocks segs B ARx LAWS).
Local Abbreviation LLAY := (alx_layout segs B ARx LAWS).
Local Abbreviation LFRS := (alx_frames segs B ARx LAWS).
Local Abbreviation LOIM := (alx_owned_image segs B ARx LAWS).
Local Abbreviation LEXT := (alx_extra segs B ARx LAWS).

Lemma call_effect_journal_rh_cf : forall stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 (Eb XW : Z -> Prop) FP1 nf k1,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 ->
  wle_in segs (dead_shadow_new lyc Sc S2) W W2 -> same_io mdc md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ ascratch B stk regs a -> ~ Eb a ->
     ~ dead_shadow_new lyc Sc S2 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W2) mem2 a) ->
  ARx lyc Sc Hpc W memc mdc -> ARcf segs B lyc Sc Hpc W memc mdc ->
  astk_ok stk lyc (spZ regs) ->
  frames S2 = nf ++ frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
  (length (st_secs Sc) <= length (st_secs S2))%nat ->
  (forall a, XW a -> a < YM05.alloc_ceiling /\ app_addr a /\ ~ in_img segs a /\
  (forall p n, In (p, n) (ablocks B lyc Sc) -> ~ (p <= a < p + req_size n)) /\
  (forall cid pos, In (cid, pos) (frames Sc) -> ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
  ~ Exists (in_zr a) (ly_extra lyc)) ->
  (forall a, Eb a -> XW a \/ exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
  b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
  (forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
  qtight S2 ->
  ajournal_xR segs B [] ARx (wle' segs RZ_cf) stk (spZ regs) FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1.
Proof.
intros stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 Eb XW FP1 nf k1
HAR2 Hly2 Hwin2 Hio2 Hfr Hpres2 HAR HC Hstk Hfrs Hnev Hk1 Hsecs XWP HE Hgone HQT2.
(* L2 at the journal started at the call state: the call's dead set misses the five view-frame domains *)
pose proof (ajournal_x_of_rh_off segs B ARx LAWS segs_low (length (st_secs Sc)) lyc Sc Hpc W memc mdc S2 lyc Sc
  ly2 S2 Hp2 W2 mem2 md2 HC (layout_le_refl _ lyc) (fun f Hf => Hf) HAR2) as (D1 & D2 & D3 & D4 & D5).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (proj1 errno_low) as [He0 He1].
assert (ASTACK = 16384) as Has by reflexivity.
destruct (LLAY _ _ _ _ _ _ ly2 HAR Hly2) as (Eab & Efa & Eown).
assert (KEEP : forall a, ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a ->
~ (spZ regs - stk <= a < spZ regs) -> ~ (as_errno B <= a < as_errno B + 4) -> ~ Eb a -> 0 <= a < 2 ^ 64 ->
~ dead_shadow_new lyc Sc S2 a ->
aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
{ intros a H1 H2 H3 H4 H5 H6 H7. apply (Hfr a H6 H1 H2); [| exact H5 | exact H7].
  unfold ascratch. intros [H|H]; [exact (H3 H) | exact (H4 H)]. }
assert (BLK : forall b m a, In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
app_addr a).
{ intros b m a [Hb|Hb] Hr.
- destruct (LBLK lyc Sc Hpc W memc mdc b m HAR Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia.
- destruct (LBLK ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hb) as (_ & _ & Hc & [Hh Hh2] & _). zlia. }
split; [exact HAR2|]. split; [exact Hly2|]. split; [exact Hsecs|].
split; [exact (proj2 (wle'_wle_in segs RZ_cf W W2) (wle_in_mono segs _ _ W W2 (dead_shadow_new_RZ lyc Sc S2) Hwin2))|].
split; [apply aos_step_of_same_io, Hio2|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk1|].
split.
{   intros a Ha Hs. apply KEEP.
- intros Ho. pose proof (OWNLOW _ _ _ _ _ _ a HAR Ho). zlia.
- intros Ho. pose proof (OWNLOW _ _ _ _ _ _ a HAR2 Ho). zlia.
- exact Hs.
- zlia.
- intros He. destruct (HE a He) as [Hx | (b & m & Hbm & Hr & _)];
[destruct (XWP a Hx) as (Xc & _); zlia | pose proof (BLK b m a Hbm Hr); zlia].
- zlia.
- exact (D1 a (proj1 Ha)). }
split.
{   intros p n i H1 H2 Hi Hnf. apply KEEP.
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (LBLK lyc Sc Hpc W memc mdc p n HAR H1))))) (p + i) ltac:(zlia))).
- exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (LBLK ly2 S2 Hp2 W2 mem2 md2 p n HAR2 H2))))) (p + i) ltac:(zlia))).
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). zlia.
- intros Herr. exact (blk_img_x segs B ARx LAWS _ _ _ _ _ _ p n (p + i) HAR H1 ltac:(zlia) (ERRIMG _ Herr)).
- intros He. destruct (HE _ He) as [Hx | (b & m & Hbm & Hr & [Hf | Hnot])];
[exact (proj1 (proj2 (proj2 (proj2 (XWP _ Hx)))) p n H1 ltac:(zlia)) | exact (Hnf Hf)|].
destruct Hbm as [Hbm|Hbm]; [exact (Hnot Hbm)|].
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
pose proof (sep_blocks_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m p n HAR2 Hbm H2 Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- pose proof (BLK p n (p + i) (or_introl H1) ltac:(zlia)). pose proof asan_consts. zlia.
- exact (D2 p n i H2 Hi). }
split.
{   intros a Hi Hns He _ _. pose proof (segs_low a Hi). apply KEEP.
- intros Ho. exact (Hns (proj1 (LOIM _ _ _ _ _ _ a HAR Hi) Ho)).
- intros Ho. exact (Hns (proj1 (LOIM _ _ _ _ _ _ a HAR2 Hi) Ho)).
- zlia.
- exact He.
- intros Heb. destruct (HE a Heb) as [Hx | (b & m & Hbm & Hr & _)]; [exact (proj1 (proj2 (proj2 (XWP a Hx))) Hi)|].
destruct Hbm as [Hbm|Hbm];
[exact (blk_img_x segs B ARx LAWS _ _ _ _ _ _ b m a HAR Hbm Hr Hi) | exact (blk_img_x segs B ARx LAWS _ _ _ _ _ _ b m a HAR2 Hbm Hr Hi)].
- zlia.
- exact (D3 a Hi). }
split.
{   intros cid pos a Hin Hr Hnf.
pose proof (D4 cid pos a Hin Hr) as ND.
assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (LFRS lyc Sc Hpc W memc mdc cid pos HAR Hin) as (_ & [Hh1 Hh2] & Hb & Hsh).
destruct (LFRS ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 Hin2) as (_ & _ & Hb2 & Hsh2). rewrite Efa in Hb2, Hsh2.
destruct (frames_bounds_x segs B ARx LAWS lyc Sc Hpc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & Hfh).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(zlia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(zlia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
apply KEEP.
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb a Hr))|].
specialize (Hsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh by zlia. exact (proj2 Hsh).
- destruct Hr as [Hr|Hr]; [exact (proj2 (Hb2 a Hr))|].
specialize (Hsh2 (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh2 by zlia. exact (proj2 Hsh2).
- destruct Hr as [Hr|Hr]; zlia.
- intros Herr. destruct Hr as [Hr|Hr];
[exact (frm_img_x segs B ARx LAWS _ _ _ _ _ _ cid pos a HAR Hin Hr (ERRIMG _ Herr)) | zlia].
- intros Heb. destruct (HE a Heb) as [Hx | (b & m & Hbm & Hrb & _)].
{ destruct (XWP a Hx) as (Xc & Xa & _ & _ & Xf & _). destruct Hr as [Hr|Hr]; [exact (Xf cid pos Hin Hr) | zlia]. }
pose proof (BLK b m a Hbm Hrb).
destruct Hr as [Hr|Hr]; [|zlia].
destruct Hbm as [Hbm|Hbm].
+ pose proof (sep_block_frame_x segs B ARx LAWS lyc Sc Hpc W memc mdc b m cid pos HAR Hbm Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
+ pose proof (sep_block_frame_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m cid pos HAR2 Hbm Hin2) as Hd. rewrite Efa in Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. zlia.
- destruct Hr as [Hr|Hr]; zlia.
- exact ND. }
split; [exact Hgone|]. split; [exact Hpres2|]. split; [exact Hstk|]. split; [|exact HQT2].
{   intros a HXa He.
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
pose proof (LEXT lyc Sc Hpc W memc mdc a HAR HXa) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
pose proof (LEXT ly2 S2 Hp2 W2 mem2 md2 a HAR2 ltac:(rewrite Eextra; exact HXa)) as (Yo & Yb & _).
apply KEEP.
- exact Xo.
- exact Yo.
- intros Hs. apply Xs. zlia.
- exact He.
- intros Heb. destruct (HE a Heb) as [Hx | (b & m & [Hbm|Hbm] & Hr & _)];
[exact (proj2 (proj2 (proj2 (proj2 (proj2 (XWP a Hx))))) HXa) | exact (Xb b m Hbm Hr) | exact (Yb b m Hbm Hr)].
- unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp. zlia.
- exact (D5 a HXa). }
Qed.
(* the same step at a general PST (the harness callers' journal): call_effect_journal_rh_cf, then the [] -> PST lift
   ajournal_x_nil_pstR (Reusable/YGcallx.v) *)
Lemma call_effect_journal_rh_cf_pst : forall PST stk lyc Sc Hpc W regs memc mdc ly2 S2 Hp2 W2 mem2 md2 (Eb XW : Z -> Prop) FP1 nf k1,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> layout_le (length (st_secs Sc)) lyc ly2 ->
  wle_in segs (dead_shadow_new lyc Sc S2) W W2 -> same_io mdc md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a -> ~ ascratch B stk regs a -> ~ Eb a ->
     ~ dead_shadow_new lyc Sc S2 a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W2) mem2 a) ->
  ARx lyc Sc Hpc W memc mdc -> ARcf segs B lyc Sc Hpc W memc mdc ->
  astk_ok stk lyc (spZ regs) ->
  frames S2 = nf ++ frames Sc -> st_nev S2 <= st_nev Sc + k1 -> 0 <= k1 ->
  (length (st_secs Sc) <= length (st_secs S2))%nat ->
  (forall a, XW a -> a < YM05.alloc_ceiling /\ app_addr a /\ ~ in_img segs a /\
  (forall p n, In (p, n) (ablocks B lyc Sc) -> ~ (p <= a < p + req_size n)) /\
  (forall cid pos, In (cid, pos) (frames Sc) -> ~ (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)) /\
  ~ Exists (in_zr a) (ly_extra lyc)) ->
  (forall a, Eb a -> XW a \/ exists b m, (In (b, m) (ablocks B lyc Sc) \/ In (b, m) (ablocks B ly2 S2)) /\
  b <= a < b + req_size m /\ (inFP FP1 a \/ ~ In (b, m) (ablocks B lyc Sc))) ->
  (forall p n i, In (p, n) (ablocks B lyc Sc) -> ~ In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n -> inFP FP1 (p + i)) ->
  qtight S2 ->
  ajournal_xR segs B PST ARx (wle' segs RZ_cf) stk (spZ regs) FP1 lyc Sc Hpc W memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1.
Proof.
intros PST. intros. eapply ajournal_x_nil_pstR. eapply call_effect_journal_rh_cf; eassumption.
Qed.
End r.

(* The lane's Print Assumptions (toolchain/allowed-axioms.txt). *)
Check call_effect_journal_rh_cf. Print Assumptions call_effect_journal_rh_cf.
Check call_effect_journal_rh_cf_pst. Print Assumptions call_effect_journal_rh_cf_pst.
