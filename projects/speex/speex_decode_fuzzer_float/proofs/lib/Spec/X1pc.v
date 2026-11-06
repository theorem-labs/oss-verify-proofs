(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1nw X1qz X1r0 X1nt X1nv X1rb X1r1 X1pa X1qt.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section OggSafeM.
Context {St ptr : Type}.
Variable own : list ptr -> assn St.
Variable lib_malloc : Z -> M St (option ptr).
Variable lib_realloc : ptr -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.

Variable reall : ptr -> Prop.
Variable KROOM : nat.
Hypothesis Hmal_big : forall X n, REALL_MIN <= n -> n < MMAP_THRESHOLD -> (length X < KROOM)%nat ->
mspec (own X) (lib_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ reall p | None => own X s mo end).
Hypothesis Hrea : forall X p n, reall p -> REALL_MIN <= n < MMAP_THRESHOLD -> (length X + 1 < KROOM)%nat ->
mspec (own (p :: X)) (lib_realloc p n) (fun r s mo => match r with Some q => own (q :: X) s mo /\ reall q | None => own (p :: X) s mo end).
Hypothesis Hfree : forall X p, mspec (own (p :: X)) (lib_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.

Implicit Types sy : sync_st ptr.
Implicit Types os : stream_st ptr.

#[using="Type"] Lemma sync_inv2_set_block : forall sy (d : option ptr) st, sync_inv2 sy ->
sync_inv2 (mkSync d (sy_buf sy) st (sy_fill sy) (sy_returned sy) (sy_unsynced sy) (sy_headerbytes sy) (sy_bodybytes sy)).
Proof. intros sy d st [[A B] C]. unfold sync_inv2, sync_inv, sync_hdr in *; cbn in *. tauto. Qed.

Definition sync_ok sy : Prop := sync_inv2 sy /\ 0 <= sy_storage sy /\ (sy_data sy = None -> sy_storage sy = 0) /\ sy_reall reall sy.

#[using="Type"] Lemma ogg_sync_init_ok : sync_ok ogg_sync_init.
Proof. split; [apply ogg_sync_init_inv2|]. cbn. split; [lia|]. split; [lia|]. intros q E. discriminate E. Qed.

#[using="Hmal_big Hrea Hfree"] Lemma ogg_sync_buffer_spec2 : forall X sy size, 0 <= size -> sync_ok sy ->
size + (sy_fill sy - sy_returned sy) + 4096 < MMAP_THRESHOLD -> (length X + 2 <= KROOM)%nat ->
mspec (own (sy_ptrs sy ++ X)) (ogg_sync_buffer lib_malloc lib_realloc lib_free sy size)
(fun r s mo => let '(res, sy') := r in own (sy_ptrs sy' ++ X) s mo /\ sync_ok sy' /\
((res = None /\ sy' = ogg_sync_init) \/
(sy_returned sy' = 0 /\ sy_fill sy' = sy_fill sy - sy_returned sy /\
match res with
| Some (q, off) => off = sy_fill sy' /\ sy_data sy' = Some q /\ sy_fill sy' + size <= sy_storage sy'
| None => size = 0
end))).
Proof.
intros X sy size Hsz (Hinv & Hst & Hnul & Hrl) Hbound HR. pose proof Hinv as [[R1 R2] _]. unfold ogg_sync_buffer.
apply mspec_if; intros Hck. { unfold ogg_sync_check in Hck. apply Z.ltb_lt in Hck. lia. }
set (sy1 := if negb (sy_returned sy =? 0) then _ else sy).
assert (E1 : sync_inv2 sy1 /\ sy_data sy1 = sy_data sy /\ sy_fill sy1 = sy_fill sy - sy_returned sy /\ sy_storage sy1 = sy_storage sy /\
sy_returned sy1 = 0).
{ subst sy1. destruct (Z.eqb_spec (sy_returned sy) 0) as [Ez|Ez]; cbn [negb].
- split; [exact Hinv|]. repeat split; auto; lia.
- pose proof (sync_compact_inv2 sy Hinv) as C. cbn in C. split; [exact C|]. repeat split; auto. }
destruct E1 as (I1 & Ed & Ef & Es & Er).
assert (EP : sy_ptrs sy1 = sy_ptrs sy) by (unfold sy_ptrs; rewrite Ed; reflexivity).
assert (RL1 : sy_reall reall sy1) by (intros q E; apply Hrl; rewrite <- Ed; exact E).
rewrite <- EP.
apply mspec_if; intros Hgrow.
- apply mspec_if; intros Hbig. { apply Z.ltb_lt in Hbig. unfold INT_MAX, MMAP_THRESHOLD in *. lia. }
apply Z.ltb_lt in Hgrow.
eapply mspec_bind with (Q1 := fun ret s mo => match ret with Some q => own (q :: X) s mo /\ reall q | None => own (sy_ptrs sy1 ++ X) s mo end).
{ unfold sy_ptrs. destruct (sy_data sy1) as [p|] eqn:Edd; cbn.
- eapply mspec_post; [apply Hrea|]. 4:{ intros [q|] s mo H; exact H. } { apply RL1. exact Edd. } { rewrite Ef. unfold REALL_MIN. lia. } lia.
- eapply mspec_post; [apply Hmal_big; unfold REALL_MIN, INT_MAX, MMAP_THRESHOLD in *; lia|]. intros [q|] s mo H; exact H. }
intros [q|]; cbn beta iota.
+ apply mspec_pure. intros Hq. apply mspec_ret. intros s mo H. cbn. split; [exact H|]. split.
{ split; [apply sync_inv2_set_block; exact I1|]. cbn. split; [lia|]. split; [intros; discriminate|]. intros q' E; injection E as <-; exact Hq. }
right. cbn. rewrite Er, Ef. repeat split; try lia.
+ eapply mspec_bind; [apply X1pa.ogg_sync_clear_spec; eauto|]. intros sy'. apply mspec_ret. intros s mo [H ->]. cbn.
split; [exact H|]. split; [apply ogg_sync_init_ok|]. left. auto.
- apply mspec_ret. intros s mo H. cbn beta iota. apply Z.ltb_ge in Hgrow.
assert (OK1 : sync_ok sy1). { split; [exact I1|]. rewrite Es, Ed. split; [exact Hst|]. split; [exact Hnul| exact RL1]. }
destruct (sy_data sy1) as [p|] eqn:Edd.
+ split; [exact H|]. split; [exact OK1|]. right. repeat split; auto; lia.
+ split; [exact H|]. split; [exact OK1|]. right. repeat split; auto.
assert (Hz : sy_storage sy = 0) by (apply Hnul; congruence). lia.
Qed.

#[using="Hrea Hfree"] Lemma os_body_expand_spec2 : forall X os needed, os_has_blocks os -> os_reall reall os -> 0 <= needed -> 0 <= os_body_storage os ->
(os_body_storage os - needed <= os_body_fill os -> os_body_storage os + needed + 1024 < MMAP_THRESHOLD) -> (length X + 4 <= KROOM)%nat ->
mspec (own (os_ptrs os ++ X)) (os_body_expand lib_realloc lib_free os needed)
(fun r s mo => let '(rc, os') := r in own (os_ptrs os' ++ X) s mo /\ os_reall reall os' /\
((rc = 0 /\ os_has_blocks os' /\ exists b bs, 0 <= bs /\ bs <= Z.max (os_body_storage os) (os_body_fill os + 2 * needed + 1024) /\
os' = set_blocks os b bs (os_lacing_vals os) (os_granule_vals os) (os_lacing_storage os))
\/ (rc = -1 /\ os' = stream_zero))).
Proof.
intros X os needed (b & l & g & Hb & Hl & Hg) HR Hn Hs Hbound HRM. pose proof HR as (R1 & R2 & R3 & R4). unfold os_body_expand.
destruct (R4 ltac:(rewrite Hb; discriminate)) as [S16 S10].
apply mspec_if; intros Hfit.
{ apply mspec_ret. intros s mo H. split; [exact H|]. split; [exact HR|]. left. split; [reflexivity|]. split; [exists b, l, g; auto|].
exists (os_body_data os), (os_body_storage os). split; [exact Hs|]. split; [lia|]. destruct os; reflexivity. }
apply Z.ltb_ge in Hfit. specialize (Hbound Hfit).
apply mspec_if; intros _.
{ eapply mspec_bind; [apply X1pa.ogg_sync_clear_spec || apply X1pa.ogg_stream_clear_spec; eauto|]. intros os'. apply mspec_ret. intros s mo [H ->]. cbn. split; [exact H|]. split; [apply stream_zero_reall| right; auto]. }
rewrite Hb. unfold os_ptrs at 1. rewrite Hb, Hl, Hg. cbn.
eapply mspec_bind.
{ eapply mspec_pre; [apply Hrea|]. 4:{ intros s mo H. exact H. } { apply R1. exact Hb. }
{ destruct (Z.ltb_spec (os_body_storage os + needed) (LONG_MAX - 1024)); unfold MMAP_THRESHOLD, LONG_MAX, REALL_MIN in *; lia. }
cbn [length]. lia. }
intros [q|]; cbn beta iota.
- apply mspec_pure. intros Hq. apply mspec_ret. intros s mo H. split; [|split].
+ unfold os_ptrs, set_blocks; cbn. first [exact H | rewrite Hl, Hg; exact H].
+ unfold os_reall, set_blocks; cbn. split; [intros b0 E; injection E as <-; exact Hq|]. split; [intros l0 E; injection E as <-; apply R2; exact Hl|].
split; [intros g0 E; injection E as <-; apply R3; exact Hg|]. intros _. split; [destruct (os_body_storage os + needed <? LONG_MAX - 1024); lia| exact S10].
+ left. split; [reflexivity|]. split; [exists q, l, g; unfold set_blocks; cbn; auto|]. eexists _, _. split; [|split; [|reflexivity]].
* destruct (os_body_storage os + needed <? LONG_MAX - 1024); lia.
* destruct (os_body_storage os + needed <? LONG_MAX - 1024); lia.
- eapply mspec_bind. { eapply mspec_pre; [apply X1pa.ogg_stream_clear_spec; eauto|]. intros s mo H. unfold os_ptrs. rewrite Hb, Hl, Hg. exact H. }
intros os'. apply mspec_ret. intros s mo [H ->]. split; [exact H|]. split; [apply stream_zero_reall| right; auto].
Qed.

#[using="Hrea Hfree Hperm"] Lemma os_lacing_expand_spec2 : forall X os needed, os_has_blocks os -> os_reall reall os -> 0 <= needed -> 0 <= os_lacing_storage os ->
(os_lacing_storage os - needed <= os_lacing_fill os -> (os_lacing_storage os + needed + 32) * 8 < MMAP_THRESHOLD) -> (length X + 4 <= KROOM)%nat ->
mspec (own (os_ptrs os ++ X)) (os_lacing_expand lib_realloc lib_free os needed)
(fun r s mo => let '(rc, os') := r in own (os_ptrs os' ++ X) s mo /\ os_reall reall os' /\
((rc = 0 /\ os_has_blocks os' /\ exists l g ls, 0 <= ls /\ ls <= Z.max (os_lacing_storage os) (os_lacing_fill os + 2 * needed + 32) /\
os' = set_blocks os (os_body_data os) (os_body_storage os) l g ls)
\/ (rc = -1 /\ os' = stream_zero))).
Proof.
intros X os needed (b & l & g & Hb & Hl & Hg) HR Hn Hs Hbound HRM. pose proof HR as (R1 & R2 & R3 & R4). unfold os_lacing_expand.
destruct (R4 ltac:(rewrite Hb; discriminate)) as [S16 S10].
apply mspec_if; intros Hfit.
{ apply mspec_ret. intros s mo H. split; [exact H|]. split; [exact HR|]. left. split; [reflexivity|]. split; [exists b, l, g; auto|].
exists (os_lacing_vals os), (os_granule_vals os), (os_lacing_storage os). split; [exact Hs|]. split; [lia|]. destruct os; reflexivity. }
apply Z.ltb_ge in Hfit. specialize (Hbound Hfit).
apply mspec_if; intros _.
{ eapply mspec_bind; [apply X1pa.ogg_stream_clear_spec; eauto|]. intros os'. apply mspec_ret. intros s mo [H ->]. cbn. split; [exact H|]. split; [apply stream_zero_reall| right; auto]. }
rewrite Hl, Hg. unfold os_ptrs at 1. rewrite Hb, Hl, Hg. cbn.
set (ls := if os_lacing_storage os + needed <? LONG_MAX - 32 then _ else _).
assert (Hls : 0 <= ls /\ ls * 8 < MMAP_THRESHOLD /\ ls <= os_lacing_fill os + 2 * needed + 32 /\ os_lacing_storage os <= ls).
{ subst ls. destruct (Z.ltb_spec (os_lacing_storage os + needed) (LONG_MAX - 32)); unfold MMAP_THRESHOLD, LONG_MAX in *; lia. }
destruct Hls as (Hls & Hls8 & HlsB & HlsM).
eapply mspec_bind.
{ eapply (X1pa.own_perm_pre own Hperm); [apply (perm_swap b l)|]. eapply mspec_pre; [apply (Hrea (b :: g :: X)); [apply R2; exact Hl| unfold SIZEOF_INT, REALL_MIN; lia| cbn [length]; lia]|]. intros s mo H; exact H. }
intros [l'|]; cbn beta iota.
- apply mspec_pure. intros Hl'. eapply mspec_bind.
{ eapply (X1pa.own_perm_pre own Hperm) with (Y := g :: l' :: b :: X).
{ eapply Permutation_trans; [apply (perm_swap l' g) | apply perm_skip; apply (perm_swap b g)]. }
eapply mspec_pre; [apply (Hrea (l' :: b :: X)); [apply R3; exact Hg| unfold SIZEOF_INT64, REALL_MIN; lia| cbn [length]; lia]|]. intros s mo H; exact H. }
intros [g'|]; cbn beta iota.
+ apply mspec_pure. intros Hg'. apply mspec_ret. intros s mo H. split; [|split].
* unfold os_ptrs, set_blocks; cbn. rewrite ?Hb. cbn. eapply Hperm; [|exact H].
eapply Permutation_trans; [apply (perm_swap l' g')|]. eapply Permutation_trans; [apply perm_skip; apply (perm_swap b g')|]. apply (perm_swap b l').
* unfold os_reall, set_blocks; cbn. split; [intros b0 E; apply R1; rewrite <- E; first [exact Hb | reflexivity]|]. split; [intros l0 E; injection E as <-; exact Hl'|].
split; [intros g0 E; injection E as <-; exact Hg'|]. intros NE. split; [exact S16| lia].
* left. split; [reflexivity|]. split; [exists b, l', g'; unfold set_blocks; cbn; auto|]. eexists _, _, _.
split; [exact Hls|]. split; [lia| reflexivity].
+ eapply mspec_bind.
{ eapply mspec_pre; [apply X1pa.ogg_stream_clear_spec; eauto|]. intros s mo H. unfold os_ptrs, set_blocks; cbn. rewrite ?Hb, ?Hg; cbn.
eapply Hperm; [|exact H].
eapply Permutation_trans; [apply (perm_swap l' g)|]. eapply Permutation_trans; [apply perm_skip; apply (perm_swap b g)|]. apply (perm_swap b l'). }
intros os'. apply mspec_ret. intros s mo [H ->]. split; [exact H|]. split; [apply stream_zero_reall| right; auto].
- eapply mspec_bind. { eapply mspec_pre; [apply X1pa.ogg_stream_clear_spec; eauto|]. intros s mo H. unfold os_ptrs. rewrite ?Hb, ?Hl, ?Hg. cbn.
eapply Hperm; [|exact H]. apply (perm_swap b l). }
intros os'. apply mspec_ret. intros s mo [H ->]. split; [exact H|]. split; [apply stream_zero_reall| right; auto].
Qed.

Definition pagein_post (os : stream_st ptr) (hdr body : list Z) (os' : stream_st ptr) : Prop :=
os_ok reall os' /\ body_inv os' /\
0 <= os_lacing_fill os' <= os_lacing_fill os + znth hdr 26 + 1 /\
0 <= os_body_fill os' <= os_body_fill os + zlength body /\
0 <= os_lacing_storage os' <= Z.max (os_lacing_storage os) (os_lacing_fill os + 2 * (znth hdr 26 + 1) + 32) /\
0 <= os_body_storage os' <= Z.max (os_body_storage os) (os_body_fill os + 2 * zlength body + 1024).

#[using="Type"] Lemma pagein_post_zero : forall os hdr body, os_ok reall os -> body_inv os -> 0 <= znth hdr 26 ->
pagein_post os hdr body stream_zero.
Proof.
intros os hdr body (Hbl & Hinv & Hbs & Hls & HRl) Hb Hn. pose proof (body_inv_fill_nonneg os Hb).
destruct Hinv as (A & B & _). pose proof (zlength_nonneg body).
unfold pagein_post. split; [apply (stream_zero_ok reall)|]. split; [apply stream_zero_body_inv|]. unfold stream_zero; simpl. lia.
Qed.

#[using="Type"] Lemma pagein_post_same : forall os hdr body, os_ok reall os -> body_inv os -> 0 <= znth hdr 26 ->
pagein_post os hdr body os.
Proof.
intros os hdr body Hok Hb Hn. pose proof Hok as (Hbl & Hinv & Hbs & Hls & HRl). pose proof (body_inv_fill_nonneg os Hb).
destruct Hinv as (A & B & _). pose proof (zlength_nonneg body).
unfold pagein_post. split; [exact Hok|]. split; [exact Hb|]. lia.
Qed.

#[using="Hrea Hfree Hperm"] Theorem ogg_stream_pagein_spec2 : forall X os hdr body,
os_ok reall os -> body_inv os -> bytes_ok (lacing_of hdr) -> 0 <= znth hdr 26 -> zsum (lacing_of hdr) = zlength body ->
(os_lacing_storage os + znth hdr 26 + 33) * 8 < MMAP_THRESHOLD ->
os_body_storage os + zlength body + 1024 < MMAP_THRESHOLD -> (length X + 4 <= KROOM)%nat ->
mspec (own (os_ptrs os ++ X)) (ogg_stream_pagein lib_realloc lib_free os hdr body)
(fun r s mo => let '(rc, os') := r in own (os_ptrs os' ++ X) s mo /\ pagein_post os hdr body os').
Proof.
intros X os hdr body Hok0 Hbody Hlac Hseg Hsum HboundL HboundB HRM. pose proof Hok0 as (Hbl & Hinv & Hbs & Hls & HRl). unfold ogg_stream_pagein.
apply mspec_if; intros Hck.
{ apply mspec_ret. intros s mo H. split; [exact H|]. apply pagein_post_same; auto. }
assert (Hhas : os_has_blocks os).
{ unfold ogg_stream_check in Hck. unfold os_blocks_ok in Hbl. unfold os_has_blocks.
destruct (os_body_data os) as [b|] eqn:Eb; [|discriminate].
destruct (os_lacing_vals os) as [l|] eqn:El; [|destruct (os_granule_vals os); contradiction].
destruct (os_granule_vals os) as [g|] eqn:Eg; [|contradiction]. exists b, l, g; auto. }
pose proof (pagein_returned_inv os Hinv) as (Hinv1 & Hret1 & Elv & Egv & Ebd & Els & Ebs & Esn & Epn).
pose proof (pagein_returned_body_inv os Hinv Hbody) as (Hbody1 & Hbr1 & Hbf1 & Hlf1).
pose proof (body_inv_fill_nonneg os Hbody) as Hbf0. pose proof (body_inv_returned_le_fill os Hbody) as Hbr0.
pose proof Hinv as (SA & SB & _). pose proof Hbody as (_ & HbrNN & _).
set (os1 := pagein_returned os) in *.
assert (Eptrs1 : os_ptrs os1 = os_ptrs os) by (unfold os_ptrs; rewrite Elv, Egv, Ebd; reflexivity).
assert (Hhas1 : os_has_blocks os1).
{ destruct Hhas as (b & l & g & Hb & Hl & Hg). exists b, l, g. rewrite Ebd, Elv, Egv. auto. }
assert (HRl1 : os_reall reall os1) by (eapply os_reall_frame; [exact Ebd| exact Elv| exact Egv| rewrite Ebs; lia| rewrite Els; lia| exact HRl]).
assert (Hok1 : os_ok reall os1).
{ unfold os_ok. split; [apply os_has_blocks_ok; exact Hhas1|]. split; [exact Hinv1|]. rewrite Ebs, Els. split; [lia|]. split; [lia| exact HRl1]. }
assert (Hpost1 : pagein_post os hdr body os1).
{ unfold pagein_post. split; [exact Hok1|]. split; [exact Hbody1|]. rewrite Hlf1, Hbf1, Els, Ebs. pose proof (zlength_nonneg body). lia. }
apply mspec_if; intros _. { apply mspec_ret. intros s mo H. rewrite Eptrs1. split; [exact H| exact Hpost1]. }
apply mspec_if; intros _. { apply mspec_ret. intros s mo H. rewrite Eptrs1. split; [exact H| exact Hpost1]. }
eapply mspec_bind.
{ rewrite <- Eptrs1. apply os_lacing_expand_spec2; [exact Hhas1| exact HRl1| lia| rewrite Els; exact Hls| | exact HRM]. intros _. rewrite Els. lia. }
intros [r os2]. cbn beta iota.
apply mspec_pointwise. intros s0 mo0 (Hown2 & HRl2 & Hcase).
destruct Hcase as [(-> & Hhas2 & (l2 & g2 & ls2 & Hls2 & Hls2B & Eos2)) | (-> & ->)].
2:{ cbn. apply mspec_ret. intros s mo [-> ->]. split; [exact Hown2| apply pagein_post_zero; auto]. }
cbn [negb Z.eqb].

assert (Hinv2 : stream_inv os2 /\ os_lacing_returned os2 = 0 /\ 0 <= os_body_storage os2 /\ 0 <= os_lacing_storage os2 /\
body_inv os2 /\ os_lacing_fill os2 = os_lacing_fill os1 /\ os_body_fill os2 = os_body_fill os1 /\
os_body_storage os2 = os_body_storage os /\ os_lacing_storage os2 = ls2).
{ rewrite Eos2. pose proof (set_blocks_inv os1 (os_body_data os1) (os_body_storage os1) l2 g2 ls2 Hinv1) as [A B].
split; [exact A|]. split; [rewrite B; exact Hret1|]. split; [unfold set_blocks; cbn; rewrite Ebs; lia|]. split; [unfold set_blocks; cbn; lia|].
split; [apply set_blocks_body_inv; exact Hbody1|]. unfold set_blocks; cbn. rewrite Ebs. repeat split; reflexivity. }
destruct Hinv2 as (Hinv2 & Hret2 & Hbs2 & Hls2' & Hbody2 & Hlf2 & Hbf2 & Ebs2 & Els2).
pose proof (pagein_unroll_inv os2 (ogg_page_pageno hdr) Hinv2 Hret2) as (Hinv3 & Hret3 & Elv3 & Egv3 & Ebd3 & Els3 & Ebs3 & Hlf3).
pose proof (pagein_unroll_body_inv os2 (ogg_page_pageno hdr) Hinv2 Hret2 Hbody2) as (Hbody3 & Hbf3 & Hbr3).
set (os3 := pagein_unroll os2 (ogg_page_pageno hdr)) in *.
assert (Eptrs3 : os_ptrs os3 = os_ptrs os2) by (unfold os_ptrs; rewrite Elv3, Egv3, Ebd3; reflexivity).
assert (HRl3 : os_reall reall os3) by (eapply os_reall_frame; [exact Ebd3| exact Elv3| exact Egv3| rewrite Ebs3; lia| rewrite Els3; lia| exact HRl2]).
assert (Hhas3 : os_has_blocks os3).
{ destruct Hhas2 as (b & l & g & Hb & Hl & Hg). exists b, l, g. rewrite Ebd3, Elv3, Egv3. auto. }
pose proof (pagein_skip_sum os3 hdr Hlac) as Bsk.
destruct (pagein_skip os3 hdr) as [[bos segptr] skipped]. destruct Bsk as [Hsegptr Hskipped].
pose proof (zsum_split segptr (lacing_of hdr) ltac:(lia)) as Hzs.
pose proof (zsum_bytes_nonneg _ (bytes_ok_ztake segptr _ Hlac)) as N1.
pose proof (zsum_bytes_nonneg _ (bytes_ok_zdrop segptr _ Hlac)) as N2.
assert (Hbsz : 0 <= zlength body - skipped <= zlength body) by lia.
pose proof Hinv3 as (TA & TB & _). pose proof (body_inv_fill_nonneg os3 Hbody3) as Hbf3nn.

eapply mspec_bind with
(Q1 := fun r s mo => let '(rc, os4) := r in own (os_ptrs os4 ++ X) s mo /\
((rc = 0 /\ exists os3', stream_inv os3' /\ os_lacing_returned os3' = 0 /\ os_has_blocks os3' /\ body_inv os3' /\ os_reall reall os3' /\
os_lacing os3' = os_lacing os3 /\ os_lacing_fill os3' = os_lacing_fill os3 /\ os_lacing_packet os3' = os_lacing_packet os3 /\
os_body_fill os3' = os_body_fill os3 /\ os_lacing_storage os3' = os_lacing_storage os3 /\
0 <= os_body_storage os3' <= Z.max (os_body_storage os) (os_body_fill os + 2 * zlength body + 1024) /\
os4 = (if negb (zlength body - skipped =? 0) then pagein_body os3' body skipped (zlength body - skipped) else os3'))
\/ (rc <> 0 /\ os4 = stream_zero))).
{ apply mspec_if; intros Hnz.
- eapply mspec_bind.
{ eapply mspec_pre; [apply os_body_expand_spec2; [exact Hhas3| exact HRl3| lia| rewrite Ebs3; exact Hbs2| | exact HRM]|].
{ intros _. rewrite Ebs3, Ebs2. lia. }
intros s mo [-> ->]. rewrite Eptrs3. exact Hown2. }
intros [rc os4]. cbn beta iota. apply mspec_pointwise. intros s1 mo1 (Hown4 & HRl4 & Hc4).
destruct Hc4 as [(-> & Hhas4 & (b4 & bs4 & Hbs4 & Hbs4B & Eos4)) | (-> & ->)].
+ cbn [negb Z.eqb]. apply mspec_ret. intros s mo [-> ->]. split.
* subst os4. unfold os_ptrs, pagein_body, set_blocks in *; cbn in *. exact Hown4.
* left. split; [reflexivity|]. exists os4. subst os4.
pose proof (set_blocks_inv os3 b4 bs4 (os_lacing_vals os3) (os_granule_vals os3) (os_lacing_storage os3) Hinv3) as [A4 B4].
split; [exact A4|]. split; [rewrite B4; exact Hret3|]. split; [exact Hhas4|]. split; [apply set_blocks_body_inv; exact Hbody3|]. split; [exact HRl4|].
unfold set_blocks; cbn. rewrite Ebs3, Ebs2 in Hbs4B. repeat split; try reflexivity; try lia.
rewrite Hnz. reflexivity.
+ cbn. apply mspec_ret. intros s mo [-> ->]. split; [exact Hown4|]. right. split; [lia| reflexivity].
- apply mspec_ret. intros s mo [-> ->]. rewrite Eptrs3. split; [exact Hown2|]. left. split; [reflexivity|].
exists os3. split; [exact Hinv3|]. split; [exact Hret3|]. split; [exact Hhas3|]. split; [exact Hbody3|]. split; [exact HRl3|].
rewrite Ebs3, Ebs2. repeat split; try reflexivity; try lia. rewrite Hnz. reflexivity. }
intros [rc os4]. cbn beta iota. apply mspec_pointwise. intros s1 mo1 [Hown4 Hc4].
destruct Hc4 as [(-> & (os3' & I3' & R3' & Hhas3' & B3' & RL3' & L3' & LF3' & LP3' & BF3' & LS3' & BS3' & ->)) | (Hne & ->)].
- cbn [negb Z.eqb]. apply mspec_ret. intros s mo [-> ->].
pose proof (pagein_body_segments_body_inv os3' hdr body bos segptr skipped I3' R3' B3' Hlac Hsum Hsegptr Hskipped) as PBS.
cbv zeta in PBS. destruct PBS as (Hbody5 & Hbf5 & _ & Hbr5).
set (os4 := if negb (zlength body - skipped =? 0) then pagein_body os3' body skipped (zlength body - skipped) else os3') in *.
assert (H4 : stream_inv os4 /\ os_lacing_returned os4 = 0 /\ os_has_blocks os4 /\ os_lacing_fill os4 = os_lacing_fill os3 /\
os_lacing_packet os4 = os_lacing_packet os3 /\ os_lacing_storage os4 = os_lacing_storage os3 /\
os_body_storage os4 = os_body_storage os3' /\ os_ptrs os4 = os_ptrs os3').
{ subst os4. destruct (negb (zlength body - skipped =? 0)).
- pose proof (pagein_body_inv os3' body skipped (zlength body - skipped) I3') as [A B].
split; [exact A|]. split; [rewrite B; exact R3'|].
split. { destruct Hhas3' as (b & l & g & Hb & Hl & Hg). exists b, l, g. unfold pagein_body, set_body; cbn. auto. }
unfold pagein_body, set_body, os_ptrs; cbn. rewrite LF3', LP3', LS3'. repeat split; reflexivity.
- rewrite <- LF3', <- LP3', <- LS3'. split; [exact I3'|]. split; [exact R3'|]. split; [exact Hhas3'|]. repeat split; reflexivity. }
destruct H4 as (I4 & R4 & Hhas4 & LF4 & LP4 & LS4 & BS4 & P4).
assert (HRl4 : os_reall reall os4).
{ subst os4. destruct (negb (zlength body - skipped =? 0)); [| exact RL3']. unfold pagein_body, set_body. eapply os_reall_frame; [..| exact RL3']; cbn; try reflexivity; lia. }
pose proof I4 as (U1 & U2 & _).
pose proof (pagein_segments_frame os4 hdr bos segptr Hlac Hsegptr U2) as FR. cbv zeta in FR.
destruct FR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
split.
+ assert (EQ : os_ptrs (pagein_segments os4 hdr bos segptr) = os_ptrs os4) by (unfold os_ptrs; rewrite F1, F2, F3; reflexivity).
rewrite EQ. exact Hown4.
+ unfold pagein_post. split.
{ unfold os_ok. split.
{ apply os_has_blocks_ok. destruct Hhas4 as (b & l & g & Hb & Hl & Hg). exists b, l, g. rewrite F1, F2, F3. auto. }
split; [apply pagein_segments_inv; auto; lia|]. rewrite F4, F5, LS4, BS4, Els3, Els2. split; [lia|]. split; [lia|].
eapply os_reall_frame; [exact F1| exact F2| exact F3| rewrite F4; lia| rewrite F5; lia| exact HRl4]. }
split; [exact Hbody5|].
rewrite Hbf5, BF3', F8, F5, F4, LF4, LS4, BS4, Els3, Els2.
pose proof (zlength_ztake_le_n (znth hdr 26) (zdrop 27 hdr) Hseg) as ZL. change (ztake (znth hdr 26) (zdrop 27 hdr)) with (lacing_of hdr) in ZL.
pose proof (zlength_nonneg body). pose proof (zlength_nonneg (lacing_of hdr)). lia.
- destruct (negb (rc =? 0)) eqn:En.
+ apply mspec_ret. intros s mo [-> ->]. split; [exact Hown4| apply pagein_post_zero; auto].
+ apply Bool.negb_false_iff in En. apply Z.eqb_eq in En. lia.
Qed.
End OggSafeM.
