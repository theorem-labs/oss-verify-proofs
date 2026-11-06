(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1nw X1qz X1r0 X1nt X1rg.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Definition MSG_MAX : Z := 4096.
Definition msg_ok (msg : list Z) : Prop := zlength msg <= MSG_MAX.
Ltac msg_ok_tac := unfold msg_ok, MSG_MAX; apply Z.leb_le; vm_compute; reflexivity.

Section CoreSafe.
Context {St ptr : Type}.
Variable own : list ptr -> assn St.
Variable lib_malloc : Z -> M St (option ptr).
Variable lib_calloc : Z -> Z -> M St (option ptr).
Variable lib_realloc : ptr -> Z -> M St (option ptr).
Variable lib_free : ptr -> M St unit.
Variable spx_notify : list Z -> M St unit.
Variable spx_warning : list Z -> M St unit.

Hypothesis Hmal : forall X n, 0 <= n ->
mspec (own X) (lib_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo | None => own X s mo end).
Hypothesis Hcal : forall X n m, 0 <= n -> 0 <= m ->
mspec (own X) (lib_calloc n m) (fun r s mo => match r with Some p => own (p :: X) s mo | None => own X s mo end).

Variable reall : ptr -> Prop.
Definition REALL_MIN : Z := 1024.
Hypothesis Hmal_big : forall X n, REALL_MIN <= n ->
mspec (own X) (lib_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ reall p | None => own X s mo end).
Hypothesis Hcal_big : forall X n m, 0 <= n -> 0 <= m -> REALL_MIN <= n * m ->
mspec (own X) (lib_calloc n m) (fun r s mo => match r with Some p => own (p :: X) s mo /\ reall p | None => own X s mo end).
Hypothesis Hrea : forall X p n, reall p -> REALL_MIN <= n < MMAP_THRESHOLD ->
mspec (own (p :: X)) (lib_realloc p n) (fun r s mo => match r with Some q => own (q :: X) s mo /\ reall q | None => own (p :: X) s mo end).
Hypothesis Hfree : forall X p, mspec (own (p :: X)) (lib_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hnotify : forall X msg, msg_ok msg -> mspec (own X) (spx_notify msg) (fun _ => own X).
Hypothesis Hwarning : forall X msg, msg_ok msg -> mspec (own X) (spx_warning msg) (fun _ => own X).

Definition SOME_MAX : Z := 2^62.
Hypothesis Hmal_some : forall n, 0 <= n < SOME_MAX -> mspecA (lib_malloc n) (fun r => r <> None).
Hypothesis Hcal_some : forall n m, 0 <= n -> 0 <= m -> n * m < SOME_MAX -> mspecA (lib_calloc n m) (fun r => r <> None).
Hypothesis Hrea_some : forall p n, 0 <= n < SOME_MAX -> mspecA (lib_realloc p n) (fun r => r <> None).

Definition olist {A} (o : option A) : list A := match o with Some x => [x] | None => [] end.

#[using="Hperm"] Lemma own_perm_pre {A} (X Y : list ptr) (m : M St A) Q :
Permutation Y X -> mspec (own Y) m Q -> mspec (own X) m Q.
Proof. intros HP Hm. eapply mspec_pre; [exact Hm|]. intros s mo H. eapply Hperm; [apply Permutation_sym; exact HP| exact H]. Qed.

Definition sy_ptrs (sy : sync_st ptr) : list ptr := olist (sy_data sy).

#[using="Hfree"] Lemma ogg_sync_clear_spec : forall X sy,
mspec (own (sy_ptrs sy ++ X)) (ogg_sync_clear lib_free sy) (fun sy' s mo => own X s mo /\ sy' = ogg_sync_init).
Proof.
intros X sy. unfold ogg_sync_clear, sy_ptrs. destruct (sy_data sy) as [p|]; cbn.
- eapply mspec_seq; [apply Hfree|]. intros _. apply mspec_ret. auto.
- apply mspec_ret. auto.
Qed.

Definition sy_reall (sy : sync_st ptr) : Prop := forall q, sy_data sy = Some q -> reall q.

#[using="Hmal_big Hrea Hfree"] Lemma ogg_sync_buffer_spec : forall X sy size, 0 <= size -> 0 <= sy_returned sy <= sy_fill sy -> sy_reall sy ->

(sy_data sy <> None -> sy_storage sy - (sy_fill sy - sy_returned sy) < size ->
size + (sy_fill sy - sy_returned sy) + 4096 < MMAP_THRESHOLD) ->
mspec (own (sy_ptrs sy ++ X)) (ogg_sync_buffer lib_malloc lib_realloc lib_free sy size)
(fun r s mo => let '(res, sy') := r in own (sy_ptrs sy' ++ X) s mo /\ sy_reall sy' /\
match res with Some (q, off) => sy_data sy' = Some q | None => True end).
Proof.
intros X sy size Hsz Hfill Hrl Hbound. unfold ogg_sync_buffer.
assert (RL0 : sy_reall ogg_sync_init) by (intros q E; discriminate E).
apply mspec_if; intros _. { apply mspec_ret. intros s mo H. cbn. auto. }
set (sy1 := if negb (sy_returned sy =? 0) then _ else sy).
assert (E1 : sy_data sy1 = sy_data sy /\ sy_fill sy1 = sy_fill sy - sy_returned sy /\ sy_storage sy1 = sy_storage sy).
{ subst sy1. destruct (Z.eqb_spec (sy_returned sy) 0) as [Ez|Ez]; cbn; repeat split; auto; lia. }
destruct E1 as (E1 & F1 & S1).
assert (EP : sy_ptrs sy1 = sy_ptrs sy) by (unfold sy_ptrs; rewrite E1; reflexivity).
assert (RL1 : sy_reall sy1) by (intros q E; apply Hrl; rewrite <- E1; exact E).
apply mspec_if; intros Hgrow.
- apply mspec_if; intros _.
+ eapply mspec_bind. { rewrite <- EP. apply (ogg_sync_clear_spec X sy1). }
intros sy'. apply mspec_ret. intros s mo [H ->]. cbn. auto.
+ apply Z.ltb_lt in Hgrow. rewrite F1, S1 in Hgrow.
eapply mspec_bind with (Q1 := fun ret s mo => match ret with Some q => own (q :: X) s mo /\ reall q | None => own (sy_ptrs sy1 ++ X) s mo end).
{ unfold sy_ptrs. rewrite E1. destruct (sy_data sy) as [p|] eqn:Ed; cbn.
- eapply mspec_post; [apply Hrea|]. 3:{ intros [q|] s mo H; exact H. }
{ apply Hrl. exact Ed. }
rewrite F1. unfold REALL_MIN. split; [lia|]. apply Hbound; [congruence| lia].
- eapply mspec_post; [apply Hmal_big; unfold REALL_MIN; lia|]. intros [q|] s mo H; exact H. }
intros [q|]; cbn beta iota.
* apply mspec_pure. intros Hq. apply mspec_ret. intros s mo H. cbn. split; [exact H|]. split; [| reflexivity]. intros q' E. injection E as <-. exact Hq.
* eapply mspec_bind; [apply ogg_sync_clear_spec|]. intros sy'. apply mspec_ret. intros s mo [H ->]. cbn. auto.
- apply mspec_ret. intros s mo H. cbn beta iota. rewrite EP. split; [exact H|]. split; [exact RL1|]. destruct (sy_data sy1); auto.
Qed.

Definition os_ptrs (os : stream_st ptr) : list ptr :=
olist (os_body_data os) ++ olist (os_lacing_vals os) ++ olist (os_granule_vals os).

Definition os_blocks_ok (os : stream_st ptr) : Prop :=
match os_body_data os, os_lacing_vals os, os_granule_vals os with
| Some _, Some _, Some _ => True
| None, None, None => True
| _, _, _ => False
end.

#[using="Hfree"] Lemma ogg_stream_clear_spec : forall X os,
mspec (own (os_ptrs os ++ X)) (ogg_stream_clear lib_free os) (fun os' s mo => own X s mo /\ os' = stream_zero).
Proof.
intros X os. unfold ogg_stream_clear, os_ptrs.
destruct (os_body_data os) as [b|]; destruct (os_lacing_vals os) as [l|]; destruct (os_granule_vals os) as [g|]; cbn;
repeat (eapply mspec_seq; [first [apply Hfree | apply mspec_ret; intros s mo H; exact H] | intros _]);
apply mspec_ret; auto.
Qed.

Definition os_reall (os : stream_st ptr) : Prop :=
(forall b, os_body_data os = Some b -> reall b) /\ (forall l, os_lacing_vals os = Some l -> reall l) /\
(forall g, os_granule_vals os = Some g -> reall g) /\
(os_body_data os <> None -> 16384 <= os_body_storage os /\ 1024 <= os_lacing_storage os).

#[using="Type"] Lemma stream_zero_reall : os_reall stream_zero.
Proof. unfold os_reall, stream_zero; cbn. repeat split; intros; try discriminate; congruence. Qed.

#[using="Type"] Lemma os_reall_frame : forall os os',
os_body_data os' = os_body_data os -> os_lacing_vals os' = os_lacing_vals os -> os_granule_vals os' = os_granule_vals os ->
os_body_storage os <= os_body_storage os' -> os_lacing_storage os <= os_lacing_storage os' ->
os_reall os -> os_reall os'.
Proof.
intros os os' E1 E2 E3 E4 E5 (R1 & R2 & R3 & R4). unfold os_reall. rewrite E1, E2, E3.
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. intros NE. destruct (R4 NE). lia.
Qed.

Definition oreall (o : option ptr) : Prop := forall p, o = Some p -> reall p.

#[using="Hmal_big Hfree Hperm"] Lemma ogg_stream_init_spec : forall X sn,
mspec (own X) (ogg_stream_init lib_malloc lib_free sn)
(fun r s mo => let '(rc, os) := r in own (os_ptrs os ++ X) s mo /\ os_blocks_ok os /\ stream_inv os /\
os_lacing_returned os = 0 /\ os_reall os /\
((rc = 0 /\ exists b l g, os_body_data os = Some b /\ os_lacing_vals os = Some l /\ os_granule_vals os = Some g)
\/ (rc = -1 /\ os = stream_zero))).
Proof.
intros X sn. unfold ogg_stream_init.
eapply mspec_bind with (Q1 := fun b s mo => own (olist b ++ X) s mo /\ oreall b).
{ eapply mspec_post; [apply Hmal_big; unfold REALL_MIN; lia|]. intros [b|] s mo H; cbn; [destruct H as [H Hb]; split; [exact H| intros p E; injection E as <-; exact Hb]| split; [exact H| intros p E; discriminate E]]. }
intros b. apply mspec_pure. intros Rb.
eapply mspec_bind with (Q1 := fun l s mo => own (olist l ++ olist b ++ X) s mo /\ oreall l).
{ destruct b as [b|]; cbn; (eapply mspec_post; [apply Hmal_big; unfold REALL_MIN; lia|]); intros [l|] s mo H; cbn;
first [destruct H as [H Hl]; split; [exact H| intros p E; injection E as <-; exact Hl] | split; [exact H| intros p E; discriminate E]]. }
intros l. apply mspec_pure. intros Rl.
eapply mspec_bind with (Q1 := fun g s mo => own (olist g ++ olist l ++ olist b ++ X) s mo /\ oreall g).
{ destruct l as [l|]; destruct b as [b|]; cbn; (eapply mspec_post; [apply Hmal_big; unfold REALL_MIN; lia|]); intros [g|] s mo H; cbn;
first [destruct H as [H Hg]; split; [exact H| intros p E; injection E as <-; exact Hg] | split; [exact H| intros p E; discriminate E]]. }
intros g. apply mspec_pure. intros Rg.
destruct b as [b|]; destruct l as [l|]; destruct g as [g|]; cbn -[stream_zero ogg_stream_clear].
1: { apply mspec_ret. intros s mo H. split.
- unfold os_ptrs; cbn. eapply Hperm; [|exact H].
eapply Permutation_trans; [apply (perm_swap l g)|].
eapply Permutation_trans; [apply perm_skip; apply (perm_swap b g)|]. apply (perm_swap b l).
- split; [exact I|]. split; [unfold stream_inv; cbn; repeat split; lia|]. split; [reflexivity|].
split; [unfold os_reall; cbn; split; [exact Rb|]; split; [exact Rl|]; split; [exact Rg|]; intros _; lia|].
left. split; [reflexivity|]. exists b, l, g. auto. }
all: eapply mspec_bind; [eapply mspec_pre; [apply ogg_stream_clear_spec|]; intros s mo H; unfold os_ptrs; cbn;
first [exact H | eapply Hperm; [|exact H]] | intros os'; apply mspec_ret; intros s mo [H ->];
split; [exact H|]; split; [exact I|]; split; [apply stream_zero_inv|]; split; [reflexivity|]; split; [apply stream_zero_reall|]; right; auto].
all: try apply Permutation_refl.
all: match goal with |- Permutation (?x :: ?y :: ?r) _ => apply (perm_swap y x) end.
Qed.

Definition os_has_blocks (os : stream_st ptr) : Prop :=
exists b l g, os_body_data os = Some b /\ os_lacing_vals os = Some l /\ os_granule_vals os = Some g.

#[using="Type"] Lemma os_has_blocks_ok : forall os, os_has_blocks os -> os_blocks_ok os.
Proof. intros os (b & l & g & Hb & Hl & Hg). unfold os_blocks_ok. rewrite Hb, Hl, Hg. exact I. Qed.

#[using="Hrea Hfree"] Lemma os_body_expand_spec : forall X os needed, os_has_blocks os -> os_reall os -> 0 <= needed -> 0 <= os_body_storage os ->
(os_body_storage os - needed <= os_body_fill os -> os_body_storage os + needed + 1024 < MMAP_THRESHOLD) ->
mspec (own (os_ptrs os ++ X)) (os_body_expand lib_realloc lib_free os needed)
(fun r s mo => let '(rc, os') := r in own (os_ptrs os' ++ X) s mo /\ os_reall os' /\
((rc = 0 /\ os_has_blocks os' /\ exists b bs, 0 <= bs /\ os' = set_blocks os b bs (os_lacing_vals os) (os_granule_vals os) (os_lacing_storage os))
\/ (rc = -1 /\ os' = stream_zero))).
Proof.
intros X os needed (b & l & g & Hb & Hl & Hg) HR Hn Hs Hbound. pose proof HR as (R1 & R2 & R3 & R4). unfold os_body_expand.
destruct (R4 ltac:(rewrite Hb; discriminate)) as [S16 S10].
apply mspec_if; intros Hfit.
{ apply mspec_ret. intros s mo H. split; [exact H|]. split; [exact HR|]. left. split; [reflexivity|]. split; [exists b, l, g; auto|].
exists (os_body_data os), (os_body_storage os). split; [exact Hs|]. destruct os; reflexivity. }
apply Z.ltb_ge in Hfit. specialize (Hbound Hfit).
apply mspec_if; intros _.
{ eapply mspec_bind; [apply ogg_stream_clear_spec|]. intros os'. apply mspec_ret. intros s mo [H ->]. cbn. split; [exact H|]. split; [apply stream_zero_reall| right; auto]. }
rewrite Hb. unfold os_ptrs at 1. rewrite Hb, Hl, Hg. cbn.
eapply mspec_bind.
{ eapply mspec_pre; [apply Hrea|]. 3:{ intros s mo H. exact H. } { apply R1. exact Hb. }
destruct (Z.ltb_spec (os_body_storage os + needed) (LONG_MAX - 1024)); unfold MMAP_THRESHOLD, LONG_MAX, REALL_MIN in *; lia. }
intros [q|]; cbn beta iota.
- apply mspec_pure. intros Hq. apply mspec_ret. intros s mo H. split; [|split].
+ unfold os_ptrs, set_blocks; cbn. first [exact H | rewrite Hl, Hg; exact H].
+ unfold os_reall, set_blocks; cbn. split; [intros b0 E; injection E as <-; exact Hq|]. split; [intros l0 E; injection E as <-; apply R2; exact Hl|].
split; [intros g0 E; injection E as <-; apply R3; exact Hg|]. intros _. split; [destruct (os_body_storage os + needed <? LONG_MAX - 1024); lia| exact S10].
+ left. split; [reflexivity|]. split; [exists q, l, g; unfold set_blocks; cbn; auto|]. eexists _, _. split; [|reflexivity].
destruct (os_body_storage os + needed <? LONG_MAX - 1024); lia.
- eapply mspec_bind. { eapply mspec_pre; [apply ogg_stream_clear_spec|]. intros s mo H. unfold os_ptrs. rewrite Hb, Hl, Hg. exact H. }
intros os'. apply mspec_ret. intros s mo [H ->]. split; [exact H|]. split; [apply stream_zero_reall| right; auto].
Qed.

#[using="Hrea Hfree Hperm"] Lemma os_lacing_expand_spec : forall X os needed, os_has_blocks os -> os_reall os -> 0 <= needed -> 0 <= os_lacing_storage os ->
(os_lacing_storage os - needed <= os_lacing_fill os -> (os_lacing_storage os + needed + 32) * 8 < MMAP_THRESHOLD) ->
mspec (own (os_ptrs os ++ X)) (os_lacing_expand lib_realloc lib_free os needed)
(fun r s mo => let '(rc, os') := r in own (os_ptrs os' ++ X) s mo /\ os_reall os' /\
((rc = 0 /\ os_has_blocks os' /\ exists l g ls, 0 <= ls /\ os' = set_blocks os (os_body_data os) (os_body_storage os) l g ls)
\/ (rc = -1 /\ os' = stream_zero))).
Proof.
intros X os needed (b & l & g & Hb & Hl & Hg) HR Hn Hs Hbound. pose proof HR as (R1 & R2 & R3 & R4). unfold os_lacing_expand.
destruct (R4 ltac:(rewrite Hb; discriminate)) as [S16 S10].
apply mspec_if; intros Hfit.
{ apply mspec_ret. intros s mo H. split; [exact H|]. split; [exact HR|]. left. split; [reflexivity|]. split; [exists b, l, g; auto|].
exists (os_lacing_vals os), (os_granule_vals os), (os_lacing_storage os). split; [exact Hs|]. destruct os; reflexivity. }
apply Z.ltb_ge in Hfit. specialize (Hbound Hfit).
apply mspec_if; intros _.
{ eapply mspec_bind; [apply ogg_stream_clear_spec|]. intros os'. apply mspec_ret. intros s mo [H ->]. cbn. split; [exact H|]. split; [apply stream_zero_reall| right; auto]. }
rewrite Hl, Hg. unfold os_ptrs at 1. rewrite Hb, Hl, Hg. cbn.
set (ls := if os_lacing_storage os + needed <? LONG_MAX - 32 then _ else _).
assert (Hls : 0 <= ls /\ ls * 8 < MMAP_THRESHOLD /\ os_lacing_storage os <= ls).
{ subst ls. destruct (Z.ltb_spec (os_lacing_storage os + needed) (LONG_MAX - 32)); unfold MMAP_THRESHOLD, LONG_MAX in *; lia. }
destruct Hls as (Hls & Hls8 & HlsM).
eapply mspec_bind.
{ eapply own_perm_pre; [apply (perm_swap b l)|]. eapply mspec_pre; [apply Hrea; [apply R2; exact Hl| unfold SIZEOF_INT, REALL_MIN; lia]|]. intros s mo H; exact H. }
intros [l'|]; cbn beta iota.
- apply mspec_pure. intros Hl'. eapply mspec_bind.
{ eapply own_perm_pre with (Y := g :: l' :: b :: X).
{ eapply Permutation_trans; [apply (perm_swap l' g) | apply perm_skip; apply (perm_swap b g)]. }
eapply mspec_pre; [apply Hrea; [apply R3; exact Hg| unfold SIZEOF_INT64, REALL_MIN; lia]|]. intros s mo H; exact H. }
intros [g'|]; cbn beta iota.
+ apply mspec_pure. intros Hg'. apply mspec_ret. intros s mo H. split; [|split].
* unfold os_ptrs, set_blocks; cbn. rewrite ?Hb. cbn. eapply Hperm; [|exact H].
eapply Permutation_trans; [apply (perm_swap l' g')|]. eapply Permutation_trans; [apply perm_skip; apply (perm_swap b g')|]. apply (perm_swap b l').
* unfold os_reall, set_blocks; cbn. split; [intros b0 E; apply R1; rewrite <- E; first [exact Hb | reflexivity]|]. split; [intros l0 E; injection E as <-; exact Hl'|].
split; [intros g0 E; injection E as <-; exact Hg'|]. intros NE. split; [exact S16| lia].
* left. split; [reflexivity|]. split; [exists b, l', g'; unfold set_blocks; cbn; auto|]. eexists _, _, _. split; [exact Hls| reflexivity].
+ eapply mspec_bind.
{ eapply mspec_pre; [apply ogg_stream_clear_spec|]. intros s mo H. unfold os_ptrs, set_blocks; cbn. rewrite ?Hb, ?Hg; cbn.
eapply Hperm; [|exact H].
eapply Permutation_trans; [apply (perm_swap l' g)|]. eapply Permutation_trans; [apply perm_skip; apply (perm_swap b g)|]. apply (perm_swap b l'). }
intros os'. apply mspec_ret. intros s mo [H ->]. split; [exact H|]. split; [apply stream_zero_reall| right; auto].
- eapply mspec_bind. { eapply mspec_pre; [apply ogg_stream_clear_spec|]. intros s mo H. unfold os_ptrs. rewrite ?Hb, ?Hl, ?Hg. cbn.
eapply Hperm; [|exact H]. apply (perm_swap b l). }
intros os'. apply mspec_ret. intros s mo [H ->]. split; [exact H|]. split; [apply stream_zero_reall| right; auto].
Qed.

Definition os_ok (os : stream_st ptr) : Prop :=
os_blocks_ok os /\ stream_inv os /\ 0 <= os_body_storage os /\ 0 <= os_lacing_storage os /\ os_reall os.

#[using="Type"] Lemma stream_zero_ok : os_ok stream_zero.
Proof. unfold os_ok. split; [exact I|]. split; [apply stream_zero_inv|]. split; [cbn; lia|]. split; [cbn; lia| apply stream_zero_reall]. Qed.

#[using="Type"] Lemma skip_continued_bounds : forall l, Forall (fun v => 0 <= v < 256) l ->
let '(n, sk) := skip_continued l in 0 <= n <= zlength l /\ 0 <= sk <= zsum l.
Proof.
induction l as [|v l IH]; intros Hl; cbn [skip_continued].
- rewrite zlength_nil. cbn. lia.
- inversion Hl as [|v' l' Hv Hl']; subst. specialize (IH Hl'). destruct (skip_continued l) as [n sk].
rewrite zlength_cons. cbn [zsum]. pose proof (zsum_nonneg l ltac:(eapply Forall_impl; [|exact Hl']; cbv beta; intros; lia)).
pose proof (zlength_nonneg l).
destruct (Z.ltb_spec v 255); lia.
Qed.

#[using="Type"] Lemma pagein_skip_bounds : forall (os : stream_st ptr) hdr, Forall (fun v => 0 <= v < 256) (lacing_of hdr) ->
let '(bos, segptr, skipped) := pagein_skip os hdr in 0 <= segptr /\ 0 <= skipped <= zsum (lacing_of hdr).
Proof.
intros os hdr Hl. unfold pagein_skip.
pose proof (zsum_nonneg (lacing_of hdr) ltac:(eapply Forall_impl; [|exact Hl]; cbv beta; intros; lia)).
destruct (negb (ogg_page_continued hdr =? 0)); [|cbn; lia].
destruct (_ || _ || _); [|cbn; lia].
pose proof (skip_continued_bounds _ Hl) as B. destruct (skip_continued (lacing_of hdr)) as [n sk]. cbn. lia.
Qed.

#[using="Hcal_big"] Lemma speex_bits_init_spec : forall X,
mspec (own X) (speex_bits_init lib_calloc)
(fun r s mo => match r with
| Some b => own (sb_chars b :: X) s mo /\ bits_ok b /\ sb_owner b = 1 /\ sb_nbBits b = 0 /\
reall (sb_chars b) /\ sb_buf_size b = MAX_CHARS_PER_FRAME
| None => own X s mo
end).
Proof.
intros X. unfold speex_bits_init.
eapply mspec_bind; [apply Hcal_big; unfold MAX_CHARS_PER_FRAME, REALL_MIN; lia|]. intros [p|]; cbn beta iota.
- apply mspec_pure. intros Hp. apply mspec_ret. intros s mo H. cbn. split; [exact H|]. split; [|split; [reflexivity| split; [reflexivity| split; [exact Hp| reflexivity]]]].
unfold bits_ok, speex_bits_reset, bits_pos; cbn -[zupd zrepeat MAX_CHARS_PER_FRAME Z.mul Z.add].
rewrite zlength_zupd. rewrite zlength_zrepeat by (unfold MAX_CHARS_PER_FRAME; lia).
unfold MAX_CHARS_PER_FRAME. lia.
- apply mspec_ret. intros s mo H. exact H.
Qed.

#[using="Hcal_some"] Lemma speex_bits_init_some : mspecA (speex_bits_init lib_calloc) (fun r => r <> None).
Proof.
unfold speex_bits_init. eapply mspecA_bind; [apply Hcal_some; unfold MAX_CHARS_PER_FRAME, SOME_MAX; lia|].
intros [p|] Hp; [apply mspecA_ret; discriminate| contradiction].
Qed.

#[using="Hfree"] Lemma speex_bits_destroy_spec : forall X b, sb_owner b <> 0 ->
mspec (own (sb_chars b :: X)) (speex_bits_destroy lib_free b) (fun _ => own X).
Proof.
intros X b Ho. unfold speex_bits_destroy. destruct (Z.eqb_spec (sb_owner b) 0); [lia|]. cbn. apply Hfree.
Qed.

#[using="Hrea Hnotify Hwarning"] Lemma speex_bits_read_from_spec : forall X b pkt len, bits_ok b -> 0 <= len <= zlength pkt ->
reall (sb_chars b) -> REALL_MIN <= sb_buf_size b ->
(sb_buf_size b < len -> len < MMAP_THRESHOLD) ->
mspec (own (sb_chars b :: X)) (speex_bits_read_from lib_realloc spx_notify spx_warning b pkt len)
(fun b' s mo => own (sb_chars b' :: X) s mo /\ (reall (sb_chars b') /\ sb_buf_size b <= sb_buf_size b') /\ bits_ok b' /\ sb_owner b' = sb_owner b /\
bits_pos b' = 0 /\ sb_overflow b' = 0 /\
(sb_nbBits b' = len * 8 \/ (sb_nbBits b' = sb_buf_size b * 8 /\ sb_buf_size b < len))).
Proof.
intros X b pkt len Hok Hlen Hrl Hbig Hbound. pose proof Hok as (L & S1 & N & C & B & P & O). unfold speex_bits_read_from.
eapply mspec_bind with
(Q1 := fun r s mo => let '(b1, nchars) := r in own (sb_chars b1 :: X) s mo /\ reall (sb_chars b1) /\ sb_owner b1 = sb_owner b /\
0 <= nchars <= zlength pkt /\ sb_data b1 = sb_data b /\
((nchars = len /\ sb_buf_size b1 = len /\ sb_buf_size b < len) \/ (nchars = len /\ sb_buf_size b1 = sb_buf_size b /\ len <= sb_buf_size b)
\/ (nchars = sb_buf_size b /\ sb_buf_size b1 = sb_buf_size b /\ sb_buf_size b < len))).
{ apply mspec_if; intros Hgt.
- apply Z.ltb_lt in Hgt. eapply mspec_seq; [apply Hnotify; msg_ok_tac|]. intros _.
apply mspec_if; intros _.
+ eapply mspec_bind; [apply Hrea; [exact Hrl| split; [lia| apply Hbound; lia]]|]. intros [q|]; cbn beta iota.
* apply mspec_pure. intros Hq. apply mspec_ret. intros s mo H. cbn. repeat split; auto; try lia.
* eapply mspec_seq; [apply Hwarning; msg_ok_tac|]. intros _. apply mspec_ret. intros s mo H. cbn. repeat split; auto; try lia.
+ eapply mspec_seq; [apply Hwarning; msg_ok_tac|]. intros _. apply mspec_ret. intros s mo H. cbn. repeat split; auto; try lia.
- apply Z.ltb_ge in Hgt. apply mspec_ret. intros s mo H. cbn. repeat split; auto; try lia. }
intros [b1 nchars]. cbn beta iota. apply mspec_pointwise. intros s0 mo0 (Hown & Hrl1 & Eo & Hn & Ed & Hcases).
apply mspec_ret. intros s mo [-> ->]. cbn. split; [exact Hown|].
split. { split; [exact Hrl1|]. destruct Hcases as [(_ & E2 & ?)|[(_ & E2 & ?)|(_ & E2 & ?)]]; rewrite E2; lia. }
assert (HL : zlength (ztake nchars pkt ++ zdrop nchars (sb_data b1)) = sb_buf_size b1).
{ rewrite zlength_app, zlength_ztake by lia. rewrite Ed.
destruct Hcases as [(-> & -> & ?)|[(-> & -> & ?)|(-> & -> & ?)]].
- unfold zdrop, zlength in *. rewrite length_skipn. lia.
- rewrite zlength_zdrop by lia. lia.
- rewrite zlength_zdrop by lia. lia. }
split.
{ unfold bits_ok, bits_pos; cbn. rewrite HL. destruct Hcases as [(-> & -> & ?)|[(-> & -> & ?)|(-> & -> & ?)]]; repeat split; try lia. }
unfold bits_pos; cbn. repeat split; auto; try lia.
all: destruct Hcases as [(-> & E2 & ?)|[(-> & E2 & ?)|(-> & E2 & ?)]]; first [left; lia | right; lia].
Qed.

#[using="Hcal Hfree Hnotify Hcal_some"] Lemma speex_packet_to_header_spec : forall X pkt size,
mspec (own X) (speex_packet_to_header lib_calloc lib_free spx_notify pkt size)
(fun r s mo => match r with Some (blk, h) => own (blk :: X) s mo /\ 0 <= hd_mode h < SPEEX_NB_MODES | None => own X s mo end).
Proof.
intros X pkt size. unfold speex_packet_to_header.
apply mspec_if; intros _. { eapply mspec_seq; [apply Hnotify; msg_ok_tac|]. intros _. apply mspec_ret. intros s mo H; exact H. }
apply mspec_if; intros _. { apply mspec_ret. intros s mo H; exact H. }
eapply mspec_bind; [apply mspec_some; [apply Hcal| apply Hcal_some]; unfold SIZEOF_SPEEX_HEADER, SOME_MAX; lia|]. intros [blk|]; cbn beta iota.
- destruct ((SPEEX_NB_MODES <=? hd_mode (header_of_bytes pkt)) || (hd_mode (header_of_bytes pkt) <? 0)) eqn:E.
+ eapply mspec_seq; [apply Hnotify; msg_ok_tac|]. intros _. eapply mspec_seq; [apply Hfree|]. intros _. apply mspec_ret. intros s mo H; exact H.
+ apply mspec_ret. intros s mo H. split; [exact H|]. unfold set_nb_channels; cbn -[SPEEX_NB_MODES Z.le Z.lt].
apply Bool.orb_false_iff in E. destruct E as [E1 E2]. apply Z.leb_gt in E1. apply Z.ltb_ge in E2. unfold SPEEX_NB_MODES in *.
cbn in E1, E2. lia.
- apply mspec_munr.
Qed.
End CoreSafe.
