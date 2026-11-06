(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: rk_free_inner's restated tree takes free_cf's size test; its recycle side from rk_rchunk_fr; statement of rk_free unchanged. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfRoomStep.v, with its module paths changed; 433 of its 650 lines of code are new or changed and 791 lines of the source are left out. *)
(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfSecsStep.v, sha256 8c21e650f2ea681f7c8c92abb0992ce6486cb1fe7e507ba5c6bf2d5cfe46eba4 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Taken by path from a working branch 459411b31098 (proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfSecsStep.v).
   Modified by Theorem Labs, 2026-10: module paths changed from fuzz_preset lib.Reusable to cgif_file_fuzzer lib; the
   local nsec_cf / sec_T_cf and the local test ss_real are dropped for the layer's nsec_cf / sec_T_cf (YG0ncf.v, Z-valued) and
   sec_user_cf (YGcfNames.v), so secs_step / secs_same carry no Z.of_nat and the two bridges nsec_cf_def /
   sec_T_cf_def are restated; ss_free_inner takes this tree's free_cf size test (YG00cf.v, DeallocNmaxA). Every other
   statement is unchanged. *)
(* Theorem Labs, 2026-10: the event-free second allocator instance (suffix cf), the PER-CALL STEPS of the two
   secondary counts a Theorem Labs lane's layer reads at preset's driver (cf_hull_ok), the layer's own (YG0ncf.v):
     nsec_cf S = the number of entries of st_secs S that are sec_user_cf (sm_size >= 0),
     sec_T_cf S = the sum of sm_len over those entries.
   An errbuf (control) entry has a negative sm_size (YG00cf.v's is_errb_any; the tags ERRB_CAP_TAG, ERRB_SZ_TAG,
   ERRB_DEAD_TAG are -1, -2, -3), so both counts drop it; a real secondary has sm_size = needed_size n > 0.
   YGcfCount.v proves the list-level forms of three of the steps below over the same counts (nsec_cf_alloc,
   nsec_cf_kill, nsec_cf_errb, for nsec_cf only); this file keeps its own proofs and adds sec_T_cf and the
   model-level posts.
   Model lemmas only; no function is proved (rule 24). No address.
   Every statement holds on EVERY returning path of the model (YGcfAmx.v's ipost; ipost_apath turns it into a
   statement about apath), with no gflag and NO STATE PREMISE: the lemmas are implications over model steps, so
   each is satisfiable at preset's real start (any path of the model from init_state).
   The rule (secs_call_post n s r, r = (result, state)): one malloc_cf n, realloc tree or realloc(NULL, n)
   - with result PNull (a refused secondary, a primary that found no chunk, the refused realloc arm): d = 0, t = 0;
   - with a block and a secondary request (from_primary n = false): d = 1, t = sec_map_size n. sec_alloc appends
     exactly one entry, mkSec (sec_map_size n) (needed_size n) true (YG00.v:358; secs_sec_alloc_entry): its sm_len
     is sec_map_size n itself, with no overhead;
   - with a block and a primary request: d = 0, t = 0. A primary call's only st_secs writes are the class-full
     report's (map_more_user_cf, YG00cf.v:176), and those are errbuf entries.
   free_cf (any pointer, so also the realloc tree's free of the old block) keeps both counts (secs_same): sec_dealloc
   rewrites the entry in place with the same sm_len and sm_size (YG00.v:493), on both sides of free_cf's size test
   (enqueue, or recycle_chunk at once). free_cf PNull keeps st_secs itself.
   The errbuf steps (errb_map_cf's append at YG00cf.v:126 after errb_retire, errb_set_size's in-place update at
   YG00cf.v:93 or append at :94, errb_append_cf, errb_report_cf) keep both counts.
   secs_steps_cf bundles the call steps as one closed Prop; secs_steps_cf_holds proves it.
   The ordering: section 1 the counts and the rule, section 2 the list facts, section 3 the errbuf, section 4
   malloc_cf, section 5 free_cf, section 6 the realloc forms, section 7 the apath forms and the bundle. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG02 YG04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG00cf YG01cf YGcfPath YGcfAmx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoomPre YGcfRoomKeep YGcfRoomStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YG0dcf ReallocP YGcfRealloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The counts and the rule.                                                    *)
Definition sum_len (l : list secmap) : Z := fold_right (fun sm acc => sm_len sm + acc) 0 l.

(* nsec_cf / sec_T_cf and the call rule secs_step / secs_call_d / secs_call_t / secs_call_post are the layer's
   YGcfNames.v (moved there, unchanged, so that CfParams's admission law can name secs_call_post). *)

(* Both counts unchanged. *)
Definition secs_same (s s' : astate) : Prop := nsec_cf s' = nsec_cf s /\ sec_T_cf s' = sec_T_cf s.

Lemma secs_same_refl : forall s, secs_same s s.
Proof. intros s. split; reflexivity. Qed.
Lemma secs_same_trans : forall s1 s2 s3, secs_same s1 s2 -> secs_same s2 s3 -> secs_same s1 s3.
Proof. intros s1 s2 s3 [A1 B1] [A2 B2]. split; congruence. Qed.
Lemma secs_same_of_secs : forall s s', st_secs s' = st_secs s -> secs_same s s'.
Proof. intros s s' H. unfold secs_same, nsec_cf, sec_T_cf. rewrite H. split; reflexivity. Qed.
Lemma secs_step_of_same : forall s s', secs_same s s' -> secs_step 0 0 s s'.
Proof. intros s s' [A B]. unfold secs_step. rewrite A, B. split; lia. Qed.
Lemma secs_step_same_l : forall d t s s1 s2, secs_same s s1 -> secs_step d t s1 s2 -> secs_step d t s s2.
Proof. intros d t s s1 s2 [A B] [C D]. unfold secs_step. rewrite <- A, <- B. split; assumption. Qed.
Lemma secs_step_same_r : forall d t s s1 s2, secs_step d t s s1 -> secs_same s1 s2 -> secs_step d t s s2.
Proof. intros d t s s1 s2 [C D] [A B]. unfold secs_step. rewrite A, B. split; assumption. Qed.

Lemma secs_post_same_l : forall n s s1 r, st_secs s1 = st_secs s -> secs_call_post n s1 r -> secs_call_post n s r.
Proof. intros n s s1 r E H. exact (secs_step_same_l _ _ s s1 _ (secs_same_of_secs _ _ E) H). Qed.
Lemma secs_post_same_r : forall n s q s2 s3, secs_call_post n s (q, s2) -> secs_same s2 s3 -> secs_call_post n s (q, s3).
Proof. intros n s q s2 s3 H E. exact (secs_step_same_r _ _ _ _ _ H E). Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. List facts. The two bridges and secs_same_of_secs are the only places that  *)
(*    read the bodies of the layer's nsec_cf / sec_T_cf.                           *)
Lemma nsec_cf_def : forall S, Z.of_nat (length (filter sec_user_cf (st_secs S))) = nsec_cf S.
Proof.
intros S. unfold nsec_cf. induction (st_secs S) as [|a t IH]; cbn [filter fold_right]; [reflexivity|].
destruct (sec_user_cf a); cbn [length]; lia.
Qed.
Lemma sec_T_cf_def : forall S, sum_len (filter sec_user_cf (st_secs S)) = sec_T_cf S.
Proof.
intros S. unfold sec_T_cf, sum_len. induction (st_secs S) as [|a t IH]; cbn [filter fold_right]; [reflexivity|].
destruct (sec_user_cf a); cbn [fold_right]; lia.
Qed.
Lemma secs_same_of_filter : forall s s', filter sec_user_cf (st_secs s') = filter sec_user_cf (st_secs s) -> secs_same s s'.
Proof. intros s s' H. unfold secs_same. rewrite <- !nsec_cf_def, <- !sec_T_cf_def, H. split; reflexivity. Qed.

Lemma sum_len_cons : forall a l, sum_len (a :: l) = sm_len a + sum_len l.
Proof. reflexivity. Qed.
Lemma sum_len_app : forall l1 l2, sum_len (l1 ++ l2) = sum_len l1 + sum_len l2.
Proof. induction l1 as [|x t IH]; intros l2; cbn [app]; [reflexivity|]. rewrite !sum_len_cons, IH. lia. Qed.
Lemma sum_len_one : forall x, sum_len [x] = sm_len x.
Proof. intros x. unfold sum_len. cbn [fold_right]. lia. Qed.

(* errb_retire's map (YG00cf.v:98) *)
Definition ss_retire (sm : secmap) : secmap := if is_errb_cap sm then mkSec (sm_len sm) ERRB_DEAD_TAG false else sm.
Lemma ss_retire_cap : forall sm, is_errb_cap sm = true -> ss_retire sm = mkSec (sm_len sm) ERRB_DEAD_TAG false.
Proof. intros sm H. unfold ss_retire. rewrite H. reflexivity. Qed.
Lemma ss_retire_ncap : forall sm, is_errb_cap sm = false -> ss_retire sm = sm.
Proof. intros sm H. unfold ss_retire. rewrite H. reflexivity. Qed.

Lemma ss_filter_retire : forall l, filter sec_user_cf (map ss_retire l) = filter sec_user_cf l.
Proof.
induction l as [|sm t IH]; [reflexivity|]. cbn [map filter].
destruct (is_errb_cap sm) eqn:Ec.
- rewrite (ss_retire_cap sm Ec).
  assert (R : sec_user_cf sm = false).
  { unfold sec_user_cf, is_errb_cap in *. apply Z.eqb_eq in Ec. rewrite Ec. reflexivity. }
  rewrite R. replace (sec_user_cf (mkSec (sm_len sm) ERRB_DEAD_TAG false)) with false by reflexivity. exact IH.
- rewrite (ss_retire_ncap sm Ec), IH. reflexivity.
Qed.

Lemma ss_filter_app_ctl : forall l x, sec_user_cf x = false -> filter sec_user_cf (l ++ [x]) = filter sec_user_cf l.
Proof.
intros l x H. rewrite filter_app.
replace (filter sec_user_cf [x]) with (@nil secmap) by (cbn [filter]; rewrite H; reflexivity). apply app_nil_r.
Qed.

Lemma ss_filter_app_real : forall l x, sec_user_cf x = true -> filter sec_user_cf (l ++ [x]) = filter sec_user_cf l ++ [x].
Proof.
intros l x H. rewrite filter_app.
replace (filter sec_user_cf [x]) with [x] by (cbn [filter]; rewrite H; reflexivity). reflexivity.
Qed.

(* An in-place rewrite of one entry that keeps its kind, and its sm_len when it is a real entry. *)
Lemma ss_lupd_filter : forall l i x y, nth_error l i = Some y -> sec_user_cf x = sec_user_cf y ->
(sec_user_cf y = true -> sm_len x = sm_len y) ->
length (filter sec_user_cf (lupd l i x)) = length (filter sec_user_cf l) /\
sum_len (filter sec_user_cf (lupd l i x)) = sum_len (filter sec_user_cf l).
Proof.
induction l as [|z t IH]; intros [|i] x y H Hr Hl; cbn [nth_error lupd] in H |- *; try discriminate H.
- injection H as Hzy. subst y. cbn [filter]. rewrite Hr. destruct (sec_user_cf z) eqn:Ez.
  + cbn [length]. rewrite !sum_len_cons, (Hl eq_refl). split; reflexivity.
  + split; reflexivity.
- cbn [filter]. destruct (IH i x y H Hr Hl) as [A B]. destruct (sec_user_cf z).
  + cbn [length]. rewrite !sum_len_cons, A, B. split; reflexivity.
  + split; assumption.
Qed.

Lemma secs_same_of_lupd : forall s s' i x y, st_secs s' = lupd (st_secs s) i x -> nth_error (st_secs s) i = Some y ->
sec_user_cf x = sec_user_cf y -> (sec_user_cf y = true -> sm_len x = sm_len y) -> secs_same s s'.
Proof.
intros s s' i x y E Hy Hr Hl. destruct (ss_lupd_filter (st_secs s) i x y Hy Hr Hl) as [A B].
unfold secs_same. rewrite <- !nsec_cf_def, <- !sec_T_cf_def, E, A, B. split; reflexivity.
Qed.

Lemma ss_find_sz_ge : forall l j i, find_sz l j = Some i -> (j <= i)%nat.
Proof.
induction l as [|sm t IH]; intros j i H; cbn [find_sz] in H; [discriminate H|].
destruct (is_errb_sz sm); [injection H as <-; lia | specialize (IH _ _ H); lia].
Qed.

Lemma ss_find_sz_nth : forall l j i, find_sz l j = Some i ->
exists y, nth_error l (i - j) = Some y /\ is_errb_sz y = true.
Proof.
induction l as [|sm t IH]; intros j i H; cbn [find_sz] in H; [discriminate H|].
destruct (is_errb_sz sm) eqn:E.
- injection H as <-. exists sm. rewrite Nat.sub_diag. split; [reflexivity | exact E].
- destruct (IH (S j) i H) as (y & Hy & Sy). pose proof (ss_find_sz_ge t (S j) i H) as G.
  exists y. replace (i - j)%nat with (S (i - S j)) by lia. split; [exact Hy | exact Sy].
Qed.

Lemma ss_sz_not_real : forall y, is_errb_sz y = true -> sec_user_cf y = false.
Proof.
intros y H. unfold sec_user_cf, is_errb_sz in *. apply Z.eqb_eq in H. rewrite H. reflexivity.
Qed.

Section SS. Context {ci : CfImg}.

(* ---------------------------------------------------------------------------- *)
(* 3. The errbuf: no step of it changes either count.                            *)
(* The append of a capacity entry (YG00cf.v:126), after errb_retire. *)
Lemma secs_errb_map : forall w s, ipost (errb_map_cf w s) (fun r => secs_same s (snd r)).
Proof.
intros w s. unfold errb_map_cf. cbv zeta. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
rk_if; [apply rk_spin|].
apply rk_bind. unfold errb_retire. apply rk_modify. cbn [fst snd]. apply rk_modify. cbn [snd].
apply secs_same_of_filter. cbn [st_secs set_secs set_nev].
rewrite ss_filter_app_ctl by reflexivity. exact (ss_filter_retire (st_secs s)).
Qed.

(* The size entry (YG00cf.v:93-94): an in-place update of an errbuf entry, or an append. *)
Lemma secs_errb_set : forall ns s, ipost (errb_set_size ns s) (fun r => secs_same s (snd r)).
Proof.
intros ns s. unfold errb_set_size. apply rk_modify. cbn [snd].
destruct (find_sz (st_secs s) 0) as [i|] eqn:Ef.
- destruct (ss_find_sz_nth _ _ _ Ef) as (y & Hy & Sy). rewrite Nat.sub_0_r in Hy.
  pose proof (ss_sz_not_real y Sy) as Ry.
  apply (secs_same_of_lupd s _ i (mkSec ns ERRB_SZ_TAG false) y); [reflexivity | exact Hy | |].
  + rewrite Ry. reflexivity.
  + intros H. rewrite Ry in H. discriminate H.
- apply secs_same_of_filter. cbn [st_secs set_secs]. apply ss_filter_app_ctl. reflexivity.
Qed.

Lemma secs_errb_append : forall len s, ipost (errb_append_cf len s) (fun r => secs_same s (snd r)).
Proof.
intros len s. unfold errb_append_cf. cbv zeta. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (negb (errb_mapped_cf s)); cbv beta iota.
- apply rk_bind. eapply ipost_mono; [|apply secs_errb_map]. intros [u s1] H1. cbn [fst snd] in *.
  apply rk_bind. apply rk_get. cbn [fst snd].
  apply rk_bind. eapply ipost_mono with (P := fun r => secs_same s1 (snd r)).
  2:{ destruct (errb_cap_cf s1 <? len); cbv beta iota;
      [apply secs_errb_map | apply rk_ret; cbn [snd]; apply secs_same_refl]. }
  intros [u2 s2] H2. cbn [fst snd] in *.
  eapply ipost_mono; [|apply secs_errb_set]. intros [u3 s3] H3. cbn [snd] in *.
  exact (secs_same_trans _ _ _ H1 (secs_same_trans _ _ _ H2 H3)).
- apply rk_bind. eapply ipost_mono with (P := fun r => secs_same s (snd r)).
  2:{ destruct (errb_cap_cf s <? errb_size_cf s + len); cbv beta iota;
      [apply secs_errb_map | apply rk_ret; cbn [snd]; apply secs_same_refl]. }
  intros [u2 s2] H2. cbn [fst snd] in *.
  eapply ipost_mono; [|apply secs_errb_set]. intros [u3 s3] H3. cbn [snd] in *.
  exact (secs_same_trans _ _ _ H2 H3).
Qed.

Lemma secs_errb_report : forall c s, ipost (errb_report_cf c s) (fun r => secs_same s (snd r)).
Proof.
intros c s. unfold errb_report_cf. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (exh_mem_cf s c); cbv beta iota.
- apply rk_ret. cbn [snd]. apply secs_same_refl.
- apply rk_bind. eapply ipost_mono; [|apply secs_errb_append]. intros [u s1] H1. cbn [fst snd] in *.
  eapply ipost_mono; [|apply secs_errb_append]. intros [u2 s2] H2. cbn [snd] in *.
  exact (secs_same_trans _ _ _ H1 H2).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. malloc_cf.                                                                   *)
Lemma ss_init_cache : forall s, ipost (init_cache_if_needed s) (fun r => st_secs (snd r) = st_secs s).
Proof.
intros s. unfold init_cache_if_needed. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (st_cache_inited s); cbv beta iota; [apply rk_ret | apply rk_put]; reflexivity.
Qed.

Lemma ss_efa : forall c need sof s, ipost (ensure_free_array c need sof s) (fun r => st_secs (snd r) = st_secs s).
Proof.
intros c need sof s. unfold ensure_free_array. cbv zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if.
- apply rk_ret. reflexivity.
- apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
  destruct (aGranted z); cbv beta iota.
  + apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. reflexivity.
  + apply rk_bind. eapply ipost_mono with (P := fun r => st_secs (snd r) = st_secs s).
    2:{ destruct (aDestroyed z); cbv beta iota; [apply rk_set_region; reflexivity | apply rk_ret; reflexivity]. }
    intros [u s1] H1. cbn [fst snd] in *. destruct sof; cbv beta iota; [apply rk_spin | apply rk_ret; exact H1].
Qed.

(* cgif's chain (YG00.v:260-348), which class kBatchClass runs and enqueue calls: no st_secs write. *)
Lemma ss_mmu0 : forall c need s, ipost (map_more_user c need s) (fun r => st_secs (snd r) = st_secs s).
Proof.
intros c need s. unfold map_more_user. cbv zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if.
- apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. destruct (aGranted z); cbv beta iota.
  + apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. reflexivity.
  + apply rk_bind. eapply ipost_mono with (P := fun r => st_secs (snd r) = st_secs s).
    2:{ destruct (aDestroyed z); cbv beta iota; [apply rk_set_region; reflexivity | apply rk_ret; reflexivity]. }
    intros [u s1] H1. cbn [fst snd] in *. apply rk_ret. exact H1.
- apply rk_ret. reflexivity.
Qed.

Lemma ss_populate0 : forall c need s, ipost (populate c need s) (fun r => st_secs (snd r) = st_secs s).
Proof.
intros c need s. unfold populate. cbv zeta. apply rk_bind. eapply ipost_mono; [|apply ss_mmu0].
intros [ok s1] H1. cbn [fst snd] in *.
destruct ok; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd].
  apply rk_bind. eapply ipost_mono; [|apply ss_efa]. intros [ok2 s2] H2. cbn [fst snd] in *.
  destruct ok2; cbn [negb]; cbv beta iota.
  + apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_bind. apply rk_set_region. cbn [fst snd].
    apply rk_ret. cbn [snd st_secs set_regions]. congruence.
  + apply rk_ret. cbn [snd]. congruence.
- apply rk_ret. cbn [snd]. exact H1.
Qed.

Lemma ss_gfa0 : forall c n s, ipost (get_from_allocator c n s) (fun r => st_secs (snd r) = st_secs s).
Proof.
intros c n s. unfold get_from_allocator. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => st_secs (snd r) = st_secs s).
2:{ rk_if; [apply ss_populate0 | apply rk_ret; reflexivity]. }
intros [ok s1] H1. cbn [fst snd] in *.
destruct ok; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd]. rk_if.
  + apply rk_ret. exact H1.
  + match goal with |- context [fa_pop_n ?f ?a ?b ?l ?acc] => destruct (fa_pop_n f a b l acc) as [[tops rest]|] end;
    cbv beta iota.
    * apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. exact H1.
    * apply rk_fail.
- apply rk_ret. exact H1.
Qed.

Lemma ss_refill0 : forall c s, ipost (refill_if_empty c s) (fun r => st_secs (snd r) = st_secs s).
Proof.
intros c s. unfold refill_if_empty. apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s c)) as [|x l]; cbv beta iota.
- apply rk_bind. eapply ipost_mono; [|apply ss_gfa0]. intros [got s1] H1. cbn [fst snd] in *.
  destruct got as [tops|]; cbv beta iota; [apply rk_set_pc; exact H1 | apply rk_ret; exact H1].
- apply rk_ret. reflexivity.
Qed.

Lemma ss_cache_alloc0 : forall c s, ipost (cache_alloc c s) (fun r => st_secs (snd r) = st_secs s).
Proof.
intros c s. unfold cache_alloc. apply rk_bind. eapply ipost_mono; [|apply ss_init_cache].
intros [u s1] S1. cbn [fst snd] in *.
apply rk_bind. eapply ipost_mono; [|apply ss_refill0]. intros [u2 s2] S2. cbn [fst snd] in *.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s2 c)) as [|x l]; cbv beta iota zeta.
- apply rk_ret. cbn [snd]. congruence.
- apply rk_bind. apply rk_set_pc. cbn [fst snd]. apply rk_ret. cbn [snd st_secs set_cache]. congruence.
Qed.

(* The cf chain (YG00cf.v:158-233): the class-full report writes only errbuf entries. *)
Lemma ss_mmu : forall c need s, ipost (map_more_user_cf c need s) (fun r => secs_same s (snd r)).
Proof.
intros c need s. unfold map_more_user_cf. destruct (Z.eqb_spec c kBatchClass) as [E|_]; cbv beta iota zeta.
{ eapply ipost_mono; [|apply ss_mmu0]. intros r H. apply secs_same_of_secs. exact H. }
apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if.
- rk_if.
  + apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. destruct (aGranted z); cbv beta iota.
    * apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
      apply secs_same_of_secs. reflexivity.
    * apply rk_bind. eapply ipost_mono with (P := fun r => st_secs (snd r) = st_secs s).
      2:{ destruct (aDestroyed z); cbv beta iota; [apply rk_set_region; reflexivity | apply rk_ret; reflexivity]. }
      intros [u s1] H1. cbn [fst snd] in *. apply rk_ret. cbn [snd]. apply secs_same_of_secs. exact H1.
  + apply rk_bind. eapply ipost_mono; [|apply secs_errb_report]. intros [u s1] H1. cbn [fst snd] in *.
    apply rk_bind. unfold set_exh_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
    apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
    eapply secs_same_trans; [exact H1 | apply secs_same_of_secs; reflexivity].
- apply rk_ret. cbn [snd]. apply secs_same_refl.
Qed.

Lemma ss_populate : forall c need s, ipost (populate_cf c need s) (fun r => secs_same s (snd r)).
Proof.
intros c need s. unfold populate_cf. destruct (Z.eqb_spec c kBatchClass) as [E|_]; cbv beta iota zeta.
{ eapply ipost_mono; [|apply ss_populate0]. intros r H. apply secs_same_of_secs. exact H. }
apply rk_bind. eapply ipost_mono; [|apply ss_mmu]. intros [ok s1] H1. cbn [fst snd] in *.
destruct ok; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd].
  apply rk_bind. eapply ipost_mono; [|apply ss_efa]. intros [ok2 s2] S2. cbn [fst snd] in *.
  destruct ok2; cbn [negb]; cbv beta iota.
  + apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_bind. apply rk_set_region. cbn [fst snd].
    apply rk_bind. unfold clear_exh_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
    apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
    eapply secs_same_trans; [exact H1 | apply secs_same_of_secs; cbn [st_secs set_regions]; exact S2].
  + apply rk_ret. cbn [snd]. eapply secs_same_trans; [exact H1 | apply secs_same_of_secs; exact S2].
- apply rk_ret. cbn [snd]. exact H1.
Qed.

Lemma ss_gfa : forall c n s, ipost (get_from_allocator_cf c n s) (fun r => secs_same s (snd r)).
Proof.
intros c n s. unfold get_from_allocator_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => secs_same s (snd r)).
2:{ rk_if; [apply ss_populate | apply rk_ret; cbn [snd]; apply secs_same_refl]. }
intros [ok s1] H1. cbn [fst snd] in *.
destruct ok; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd]. rk_if.
  + apply rk_ret. cbn [snd]. exact H1.
  + match goal with |- context [fa_pop_n ?f ?a ?b ?l ?acc] => destruct (fa_pop_n f a b l acc) as [[tops rest]|] end;
    cbv beta iota.
    * apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
      eapply secs_same_trans; [exact H1 | apply secs_same_of_secs; reflexivity].
    * apply rk_fail.
- apply rk_ret. cbn [snd]. exact H1.
Qed.

Lemma ss_refill : forall c s, ipost (refill_if_empty_cf c s) (fun r => secs_same s (snd r)).
Proof.
intros c s. unfold refill_if_empty_cf. apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s c)) as [|x l]; cbv beta iota.
- apply rk_bind. eapply ipost_mono; [|apply ss_gfa]. intros [got s1] H1. cbn [fst snd] in *.
  destruct got as [tops|]; cbv beta iota.
  + apply rk_set_pc. cbn [snd]. eapply secs_same_trans; [exact H1 | apply secs_same_of_secs; reflexivity].
  + apply rk_ret. cbn [snd]. exact H1.
- apply rk_ret. cbn [snd]. apply secs_same_refl.
Qed.

Lemma ss_cache_alloc : forall c s, ipost (cache_alloc_cf c s) (fun r => secs_same s (snd r)).
Proof.
intros c s. unfold cache_alloc_cf. apply rk_bind. eapply ipost_mono; [|apply ss_init_cache].
intros [u s1] S1. cbn [fst snd] in *.
apply rk_bind. eapply ipost_mono; [|apply ss_refill]. intros [u2 s2] H2. cbn [fst snd] in *.
pose proof (secs_same_trans _ _ _ (secs_same_of_secs _ _ S1) H2) as H12.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s2 c)) as [|x l]; cbv beta iota zeta.
- apply rk_ret. cbn [snd]. exact H12.
- apply rk_bind. apply rk_set_pc. cbn [fst snd]. apply rk_ret. cbn [snd].
  eapply secs_same_trans; [exact H12 | apply secs_same_of_secs; reflexivity].
Qed.

(* sec_alloc (YG00.v:349-365): either a refused map (None, st_secs kept), or exactly one appended entry whose
   sm_len is sec_map_size n itself (no overhead) and whose sm_size is needed_size n. *)
Lemma secs_sec_alloc_entry : forall n s, ipost (sec_alloc n s) (fun r =>
(fst r = None /\ st_secs (snd r) = st_secs s) \/
(fst r = Some (PSec (length (st_secs s)) kPage) /\
 st_secs (snd r) = st_secs s ++ [mkSec (sec_map_size n) (needed_size n) true])).
Proof.
intros n s. unfold sec_alloc. cbv zeta.
apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
rk_if.
- apply rk_ret. cbn [fst snd]. left. split; reflexivity.
- apply rk_bind. apply rk_get. cbn [fst snd].
  apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
  apply rk_bind. apply rk_put. cbn [fst snd].
  apply rk_bind. eapply ipost_mono with
    (P := fun r => st_secs (snd r) = st_secs s ++ [mkSec (sec_map_size n) (needed_size n) true]).
  2:{ rk_if.
      - apply rk_bind. apply rk_askz. intros z2. cbn [fst snd]. rk_if.
        + apply rk_modify. cbn [snd]. reflexivity.
        + apply rk_spin.
      - apply rk_ret. cbn [snd]. reflexivity. }
  intros [u s3] S3. cbn [fst snd] in *.
  apply rk_bind. apply rk_modify. cbn [fst snd]. apply rk_ret. cbn [fst snd]. right. split; [reflexivity | exact S3].
Qed.

Lemma ss_sec_alloc : forall n s, from_primary n = false -> ipost (sec_alloc n s) (fun r =>
match fst r with
| None => secs_same s (snd r)
| Some beg => beg <> PNull /\ secs_step 1 (sec_map_size n) s (snd r)
end).
Proof.
intros n s Fp. pose proof (rk_needed_pos n Fp) as Np.
assert (R : sec_user_cf (mkSec (sec_map_size n) (needed_size n) true) = true).
{ unfold sec_user_cf. cbn [sm_size]. destruct (Z.leb_spec 0 (needed_size n)); [reflexivity | lia]. }
eapply ipost_mono; [|apply secs_sec_alloc_entry]. intros [ob s2] [[E S2] | [E S2]]; cbn [fst snd] in *; subst ob;
cbv beta iota.
- apply secs_same_of_secs. exact S2.
- split; [discriminate|]. unfold secs_step. rewrite <- !nsec_cf_def, <- !sec_T_cf_def, S2.
  rewrite (ss_filter_app_real _ _ R), length_app, sum_len_app, sum_len_one. cbn [length sm_len]. split; lia.
Qed.

(* A block returned from a non-null start pointer is not PNull. *)
Lemma ss_post_some : forall n s s' beg d, beg <> PNull ->
secs_step (if from_primary n then 0 else 1) (if from_primary n then 0 else sec_map_size n) s s' ->
secs_call_post n s (padd beg d, s').
Proof. intros n s s' beg d Hb H. destruct beg; [contradiction Hb; reflexivity | exact H | exact H | exact H]. Qed.

Theorem secs_malloc : forall n tr s, ipost (malloc_cf n tr s) (secs_call_post n s).
Proof.
intros n tr s.
unfold malloc_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r =>
  match fst r with
  | None => secs_same s (snd r)
  | Some beg => beg <> PNull /\
      secs_step (if from_primary n then 0 else 1) (if from_primary n then 0 else sec_map_size n) s (snd r)
  end).
- intros [ob s2] H2. cbn [fst snd] in *. cbv zeta.
  destruct ob as [beg|]; cbv beta iota.
  + destruct H2 as [Hb H2].
    apply rk_bind. eapply ipost_mono; [|apply rk_depot]. intros [u3 s3] N3. cbn [fst snd] in *.
    apply rk_bind. eapply ipost_mono with (P := fun r => snd r = s3).
    2:{ rk_if.
        - apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. rk_if; [apply rk_ret; reflexivity | apply rk_spin].
        - apply rk_ret. reflexivity. }
    intros [u4 s4] E4. cbn [fst snd] in *. subst s4.
    apply rk_bind. apply rk_modify. cbn [fst snd]. apply rk_ret.
    pose proof N3 as (_ & _ & _ & S3 & _).
    unfold ck_user. apply ss_post_some; [exact Hb|].
    apply (secs_step_same_r _ _ s s2); [exact H2 | apply secs_same_of_secs; cbn [st_secs set_chunks]; exact S3].
  + apply rk_ret. unfold secs_call_post, secs_call_d, secs_call_t. cbn [fst snd].
    apply secs_step_of_same. exact H2.
- destruct (from_primary n) eqn:Fp; cbv beta iota.
  + apply rk_bind. eapply ipost_mono; [|apply ss_cache_alloc].
    intros [o s2] H2. cbn [fst snd] in *. apply rk_ret. cbn [fst snd].
    destruct o as [off|]; cbv beta iota.
    * split; [discriminate | apply secs_step_of_same; exact H2].
    * exact H2.
  + eapply ipost_mono; [|apply ss_sec_alloc; exact Fp]. intros [ob s2] H2. exact H2.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. free_cf: sec_dealloc rewrites one entry in place (same sm_len, same kind);   *)
(*    nothing else on the free path writes st_secs.                               *)
Lemma ss_rta : forall c offs s, ipost (return_to_allocator c offs s) (fun r => st_secs (snd r) = st_secs s).
Proof.
intros c offs s. unfold return_to_allocator. cbv zeta. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono; [|apply ss_efa]. intros [u s1] H1. cbn [fst snd] in *.
apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_set_region. cbn [snd]. exact H1.
Qed.

Lemma ss_cdealloc : forall c off s, ipost (cache_dealloc c off s) (fun r => st_secs (snd r) = st_secs s).
Proof.
intros c off s. unfold cache_dealloc. cbv zeta. apply rk_bind. eapply ipost_mono; [|apply ss_init_cache].
intros [u s1] H1. cbn [fst snd] in *.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => st_secs (snd r) = st_secs s1).
2:{ rk_if.
    - apply rk_bind. eapply ipost_mono; [|apply ss_rta]. intros [u2 s2] H2. cbn [fst snd] in *.
      apply rk_set_pc. cbn [snd]. exact H2.
    - apply rk_ret. reflexivity. }
intros [u3 s3] H3. cbn [fst snd] in *.
apply rk_bind. apply rk_get_pc. cbn [fst snd]. apply rk_set_pc. cbn [snd st_secs set_cache]. congruence.
Qed.

Lemma ss_sdealloc : forall r s, ipost (sec_dealloc r s) (fun x => secs_same s (snd x)).
Proof.
intros r s. unfold sec_dealloc. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (nth_error (st_secs s) r) as [sm|] eqn:En; cbv beta iota; [|apply rk_fail].
destruct (index_of (st_sec_arr s) r 0%nat) as [i|]; cbv beta iota; [|apply rk_fail].
apply rk_bind. eapply ipost_mono with (P := fun x => snd x = s).
2:{ rk_if.
    - apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. rk_if; [apply rk_ret; reflexivity | apply rk_spin].
    - apply rk_ret. reflexivity. }
intros [u s1] E1. cbn [fst snd] in *. subst s1.
apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. apply rk_modify. cbn [snd]. cbv zeta.
apply (secs_same_of_lupd s _ r (mkSec (sm_len sm) (sm_size sm) false) sm);
[reflexivity | exact En | reflexivity | intros _; reflexivity].
Qed.

Lemma ss_rchunk : forall k s, ipost (recycle_chunk k s) (fun r => secs_same s (snd r)).
Proof.
intros k s. unfold recycle_chunk. apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
apply rk_bind. apply rk_put. cbn [fst snd].
destruct (ck_beg k) as [|off|r o|cid pos]; cbv beta iota.
- apply rk_fail.
- eapply ipost_mono; [|apply ss_cdealloc]. intros [u s1] H1. cbn [snd] in *. apply secs_same_of_secs. exact H1.
- eapply ipost_mono; [|apply ss_sdealloc]. intros [u s1] H1. cbn [snd] in *.
  eapply secs_same_trans; [apply secs_same_of_secs; reflexivity | exact H1].
- apply rk_fail.
Qed.

Lemma ss_ritems : forall fuel items s, ipost (recycle_items fuel items s) (fun r => secs_same s (snd r)).
Proof.
induction fuel as [|f IH]; intros [|k t] s; cbn [recycle_items].
- apply rk_ret. cbn [snd]. apply secs_same_refl.
- apply rk_fail.
- apply rk_ret. cbn [snd]. apply secs_same_refl.
- apply rk_bind. eapply ipost_mono; [|apply ss_rchunk]. intros [u s1] H1. cbn [fst snd] in *.
  eapply ipost_mono; [|apply IH]. intros [u2 s2] H2. cbn [snd] in *. exact (secs_same_trans _ _ _ H1 H2).
Qed.

Lemma ss_drecycle : forall fuel bs s, ipost (do_recycle fuel bs s) (fun r => secs_same s (snd r)).
Proof.
induction fuel as [|f IH]; intros [|b t] s; cbn [do_recycle].
- apply rk_ret. cbn [snd]. apply secs_same_refl.
- apply rk_fail.
- apply rk_ret. cbn [snd]. apply secs_same_refl.
- apply rk_bind. eapply ipost_mono; [|apply ss_ritems]. intros [u s1] H1. cbn [fst snd] in *.
  apply rk_bind. eapply ipost_mono; [|apply ss_cdealloc]. intros [u2 s2] H2. cbn [fst snd] in *.
  eapply ipost_mono; [|apply IH]. intros [u3 s3] H3. cbn [snd] in *.
  exact (secs_same_trans _ _ _ H1 (secs_same_trans _ _ _ (secs_same_of_secs _ _ H2) H3)).
Qed.

Lemma ss_drain : forall s, ipost (maybe_drain_cf s) (fun r => secs_same s (snd r)).
Proof.
intros s. unfold maybe_drain_cf. cbv zeta. apply rk_bind. apply rk_get. cbn [fst snd].
rk_if.
- apply rk_ret. cbn [snd]. apply secs_same_refl.
- apply rk_bind. apply rk_put. cbn [fst snd].
  rk_if.
  + apply rk_ret. cbn [snd]. apply secs_same_of_secs. reflexivity.
  + do 2 (match goal with |- context [match ?x with _ => _ end] => destruct x end).
    apply rk_bind. apply rk_modify. cbn [fst snd].
    eapply ipost_mono; [|apply ss_drecycle]. intros [u s3] H3. cbn [snd] in *.
    eapply secs_same_trans; [apply secs_same_of_secs; reflexivity | exact H3].
Qed.

Lemma ss_enqueue : forall k s, ipost (enqueue k s) (fun r => st_secs (snd r) = st_secs s).
Proof.
intros k s. unfold enqueue. apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => st_secs (snd r) = st_secs s).
2:{ rk_if.
    - apply rk_bind. eapply ipost_mono; [|apply ss_cache_alloc0]. intros [ob s1] H1. cbn [fst snd] in *.
      destruct ob as [off|]; cbv beta iota; [apply rk_ret; exact H1 | apply rk_spin].
    - apply rk_ret. reflexivity. }
intros [nb s2] H2. cbn [fst snd] in *. apply rk_modify. cbn [snd st_secs set_qthread]. exact H2.
Qed.

Lemma ss_free_inner : forall p tr s,
ipost ((s0 <- get ;;
  match find_user (st_chunks s0) p with
  | None => fail (FModel 11)
  | Some k =>
    (if match ck_state k with CAllocated => true | _ => false end then ret tt else fail (FModel 12)) ;;
    depot_put tr ;;
    let k' := mkChunk (ck_beg k) (ck_req k) CQuarantined in
    modify (fun s1 => set_chunks (upd_chunk (st_chunks s1) k') s1) ;;
    (if ck_n k' <=? kQuarantineMax then enqueue k' else recycle_chunk k') ;;
    maybe_drain_cf
  end) s)
(fun r => secs_same s (snd r)).
Proof.
intros p tr s. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (find_user (st_chunks s) p) as [k|]; cbv beta iota; [|apply rk_fail].
apply rk_bind. eapply ipost_mono with (P := fun r => snd r = s).
2:{ destruct (ck_state k); cbv beta iota; [apply rk_ret; reflexivity | apply rk_fail]. }
intros [u3 s3] E3. cbn [fst snd] in *. subst s3.
apply rk_bind. eapply ipost_mono; [|apply rk_depot]. intros [u4 s4] N4. cbn [fst snd] in *. cbv zeta.
pose proof N4 as (_ & _ & _ & S4 & _).
apply rk_bind. apply rk_modify. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => secs_same s (snd r)).
2:{ match goal with |- context [if ?c then _ else _] => destruct c end; cbv beta iota.
    - eapply ipost_mono; [|apply ss_enqueue]. intros [u6 s6] S6. cbn [snd st_secs set_chunks] in *.
      apply secs_same_of_secs. congruence.
    - eapply ipost_mono; [|apply ss_rchunk]. intros [u6 s6] H6. cbn [snd] in *.
      eapply secs_same_trans; [|exact H6]. apply secs_same_of_secs. cbn [st_secs set_chunks]. exact S4. }
intros [u6 s6] H6. cbn [fst snd] in *.
eapply ipost_mono; [|apply ss_drain]. intros [u7 s7] H7. cbn [snd] in *.
exact (secs_same_trans _ _ _ H6 H7).
Qed.

Theorem secs_free : forall p tr s, ipost (free_cf p tr s) (fun r => secs_same s (snd r)).
Proof.
intros p tr s.
unfold free_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => st_secs (snd r) = st_secs s).
2:{ rk_if; [apply rk_ret; reflexivity | apply rk_modify; reflexivity]. }
intros [u s2] S2. cbn [fst snd] in *.
pose proof (secs_same_of_secs _ _ S2) as H2.
destruct p as [|off|r o|cid pos]; cbv beta iota.
- apply rk_ret. cbn [snd]. exact H2.
- eapply ipost_mono; [|apply (ss_free_inner (PPrim off) tr s2)]. intros [u3 s3] H3. cbn [snd] in *.
  exact (secs_same_trans _ _ _ H2 H3).
- eapply ipost_mono; [|apply (ss_free_inner (PSec r o) tr s2)]. intros [u3 s3] H3. cbn [snd] in *.
  exact (secs_same_trans _ _ _ H2 H3).
- eapply ipost_mono; [|apply (ss_free_inner (PFake cid pos) tr s2)]. intros [u3 s3] H3. cbn [snd] in *.
  exact (secs_same_trans _ _ _ H2 H3).
Qed.

(* free_cf PNull, the entry step of the realloc forms: st_secs itself is kept. *)
Theorem secs_free_null : forall tr s, ipost (free_cf PNull tr s) (fun r => st_secs (snd r) = st_secs s).
Proof.
intros tr s. unfold free_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_get. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => st_secs (snd r) = st_secs s).
2:{ rk_if; [apply rk_ret; reflexivity | apply rk_modify; reflexivity]. }
intros [u s2] S2. cbn [fst snd] in *. apply rk_ret. exact S2.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 6. The realloc tree (free_cf PNull, malloc_cf, free_cf of the old block when   *)
(*    malloc_cf returns a block) and realloc(NULL, n) (free_cf PNull, malloc_cf).  *)
Theorem secs_realloc : forall p n tr s, ipost (realloc_tree_with malloc_cf free_cf p n tr s) (secs_call_post n s).
Proof.
intros p n tr s. unfold realloc_tree_with. apply rk_bind. eapply ipost_mono; [|apply secs_free_null].
intros [u s1] S1. cbn [fst snd] in *.
apply rk_bind. eapply ipost_mono; [|apply secs_malloc]. intros [q s2] H2. cbn [fst snd] in *.
pose proof (secs_post_same_l n s s1 (q, s2) S1 H2) as H2'.
destruct q as [|off|r o|cid pos]; cbv beta iota.
- apply rk_ret. exact H2'.
- apply rk_bind. eapply ipost_mono; [|apply secs_free]. intros [u3 s3] H3. cbn [fst snd] in *.
  apply rk_ret. exact (secs_post_same_r n s _ s2 s3 H2' H3).
- apply rk_bind. eapply ipost_mono; [|apply secs_free]. intros [u3 s3] H3. cbn [fst snd] in *.
  apply rk_ret. exact (secs_post_same_r n s _ s2 s3 H2' H3).
- apply rk_bind. eapply ipost_mono; [|apply secs_free]. intros [u3 s3] H3. cbn [fst snd] in *.
  apply rk_ret. exact (secs_post_same_r n s _ s2 s3 H2' H3).
Qed.

Theorem secs_realloc_null : forall n tr s, ipost (realloc_null_tree_with malloc_cf free_cf n tr s) (secs_call_post n s).
Proof.
intros n tr s. unfold realloc_null_tree_with. apply rk_bind. eapply ipost_mono; [|apply secs_free_null].
intros [u s1] S1. cbn [fst snd] in *.
eapply ipost_mono; [|apply secs_malloc]. intros r H. exact (secs_post_same_l n s s1 r S1 H).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 7. The same over apath, and the bundle.                                         *)
Theorem secs_malloc_step : forall n tr s trc r, apath (malloc_cf n tr s) trc r -> secs_call_post n s r.
Proof. intros n tr s trc r Hp. exact (ipost_apath _ _ _ _ (secs_malloc n tr s) Hp). Qed.

Theorem secs_free_step : forall p tr s trc s', apath (free_cf p tr s) trc (tt, s') -> secs_same s s'.
Proof. intros p tr s trc s' Hp. exact (ipost_apath _ _ _ _ (secs_free p tr s) Hp). Qed.

Theorem secs_free_null_step : forall tr s trc s', apath (free_cf PNull tr s) trc (tt, s') -> st_secs s' = st_secs s.
Proof. intros tr s trc s' Hp. exact (ipost_apath _ _ _ _ (secs_free_null tr s) Hp). Qed.

Theorem secs_realloc_step : forall p n tr s trc r,
apath (realloc_tree_with malloc_cf free_cf p n tr s) trc r -> secs_call_post n s r.
Proof. intros p n tr s trc r Hp. exact (ipost_apath _ _ _ _ (secs_realloc p n tr s) Hp). Qed.

Theorem secs_realloc_null_step : forall n tr s trc r,
apath (realloc_null_tree_with malloc_cf free_cf n tr s) trc r -> secs_call_post n s r.
Proof. intros n tr s trc r Hp. exact (ipost_apath _ _ _ _ (secs_realloc_null n tr s) Hp). Qed.

(* The refused arm (ReallocP's mt_refused): the entry free_cf PNull, then a malloc_cf returning PNull. *)
Theorem secs_refused_step : forall n tr s s', mt_refused malloc_cf free_cf n tr s s' -> secs_call_post n s (PNull, s').
Proof.
intros n tr s s' (S1 & t1 & t2 & Hp1 & _ & Hp2 & _).
exact (secs_post_same_l n s S1 (PNull, s') (secs_free_null_step tr s t1 S1 Hp1) (secs_malloc_step n tr S1 t2 (PNull, s') Hp2)).
Qed.

End SS.

(* The call steps as one closed Prop, for the count clause's interface (secs_steps_cf -> counts). *)
Definition secs_steps_cf : Prop :=
forall (ci : CfImg),
(forall n tr s trc r, apath (malloc_cf n tr s) trc r -> secs_call_post n s r) /\
(forall p tr s trc s', apath (free_cf p tr s) trc (tt, s') -> secs_same s s') /\
(forall p n tr s trc r, apath (realloc_tree_with malloc_cf free_cf p n tr s) trc r -> secs_call_post n s r) /\
(forall n tr s trc r, apath (realloc_null_tree_with malloc_cf free_cf n tr s) trc r -> secs_call_post n s r) /\
(forall n tr s s', mt_refused malloc_cf free_cf n tr s s' -> secs_call_post n s (PNull, s')).

Theorem secs_steps_cf_holds : secs_steps_cf.
Proof.
intros ci. split; [|split; [|split; [|split]]].
- exact secs_malloc_step.
- exact secs_free_step.
- exact secs_realloc_step.
- exact secs_realloc_null_step.
- exact secs_refused_step.
Qed.

(* From a Theorem Labs lane (01a18c1f), envoy 2026-10-30T11:50:05Z. All Qed; Print Assumptions closed; checked against af140f9f320 appended after YGcfSecsStep.v (its box: wt/hwd-rep.logs/build-20261030T114310Z.log rc=0). For AbudgetRestate: append at the END of YGcfSecsStep.v (drop the Require block, which repeats the file's own :35-41 plus YGcfSecsStep itself). *)

(* errb_map_cf's st_secs step (YG00cf.v:124-128: errb_retire, then the new capacity entry): a secs_errb_grow. *)
Lemma secs_grow_remap : forall l ncap, 0 <= ncap ->
  secs_errb_grow l (map ss_retire l ++ [mkSec ncap ERRB_CAP_TAG false]).
Proof.
intros l ncap Hn. split; [|split].
- rewrite length_app, length_map. cbn [length]. lia.
- intros i sm H. exists (ss_retire sm). split.
  + assert (Hi : (i < length l)%nat) by (apply nth_error_Some; rewrite H; discriminate).
    rewrite nth_error_app1 by (rewrite length_map; exact Hi). rewrite nth_error_map, H. reflexivity.
  + unfold ss_retire. destruct (is_errb_cap sm) eqn:E; unfold is_errb_cap, ERRB_CAP_TAG in E.
    * apply Z.eqb_eq in E. split; intros Hs; [lia|]. cbn [sm_size sm_len]. unfold ERRB_DEAD_TAG. lia.
    * split; intros Hs; [reflexivity | lia].
- intros i sm' Hi H. rewrite nth_error_app2 in H by (rewrite length_map; exact Hi). rewrite length_map in H.
  destruct (i - length l)%nat as [|k]; cbn in H.
  + injection H as <-. cbn [sm_size sm_len]. unfold ERRB_CAP_TAG. lia.
  + destruct k; discriminate H.
Qed.

(* errb_set_size's st_secs step (YG00cf.v:93-98: the size entry rewritten in place or appended): a secs_errb_grow
   when the size does not shrink (errb_size_cf s <= ns) and is non-negative. *)
Lemma secs_grow_setsize : forall s ns, errb_size_cf s <= ns -> 0 <= ns ->
  secs_errb_grow (st_secs s) (st_secs (match find_sz (st_secs s) 0 with
    | Some i => set_secs (lupd (st_secs s) i (mkSec ns ERRB_SZ_TAG false)) s
    | None => set_secs (st_secs s ++ [mkSec ns ERRB_SZ_TAG false]) s end)).
Proof.
intros s ns Hle H0. set (new := mkSec ns ERRB_SZ_TAG false).
unfold errb_size_cf in Hle.
destruct (find_sz (st_secs s) 0) as [i|] eqn:E; cbn [st_secs set_secs].
- destruct (ss_find_sz_nth _ _ _ E) as (smz & Ez & Sz). rewrite Nat.sub_0_r in Ez. rewrite Ez in Hle.
  unfold is_errb_sz, ERRB_SZ_TAG in Sz. apply Z.eqb_eq in Sz.
  assert (Hi : (i < length (st_secs s))%nat) by (apply nth_error_Some; rewrite Ez; discriminate).
  split; [|split].
  + rewrite lupd_length. lia.
  + intros j sm Hj. destruct (Nat.eq_dec i j) as [<-|Hne].
    * rewrite Ez in Hj. injection Hj as <-. exists new. split; [exact (nth_error_lupd_same _ _ _ Hi)|].
      unfold new. cbn [sm_size sm_len]. unfold ERRB_SZ_TAG. split; intros Hs; lia.
    * exists sm. rewrite (nth_error_lupd_other _ _ _ _ Hne). split; [exact Hj|]. split; intros Hs; [reflexivity | lia].
  + intros j sm' Hj Hs. exfalso.
    assert (Hlt : (j < length (lupd (st_secs s) i new))%nat) by (apply nth_error_Some; rewrite Hs; discriminate).
    rewrite lupd_length in Hlt. lia.
- split; [|split].
  + rewrite length_app. cbn [length]. lia.
  + intros j sm Hj. exists sm. split; [|split; intros Hs; [reflexivity | lia]].
    rewrite nth_error_app1; [exact Hj|]. apply nth_error_Some. rewrite Hj. discriminate.
  + intros j sm' Hj Hs. rewrite nth_error_app2 in Hs by exact Hj.
    destruct (j - length (st_secs s))%nat as [|k]; cbn in Hs.
    * injection Hs as <-. unfold new. cbn [sm_size sm_len]. unfold ERRB_SZ_TAG. lia.
    * destruct k; discriminate Hs.
Qed.

(* The two as posts of the model steps (the ipost form of secs_errb_map / secs_errb_set above). *)
Lemma secs_errb_set_grow : forall ns s, errb_size_cf s <= ns -> 0 <= ns ->
  ipost (errb_set_size ns s) (fun r => secs_errb_grow (st_secs s) (st_secs (snd r))).
Proof.
intros ns s Hle H0. unfold errb_set_size. apply rk_modify. cbn [snd]. exact (secs_grow_setsize s ns Hle H0).
Qed.

Section SG. Context {ci : CfImg}.
Lemma secs_errb_map_grow : forall w s, 0 <= round_up w kPage ->
  ipost (errb_map_cf w s) (fun r => secs_errb_grow (st_secs s) (st_secs (snd r))).
Proof.
intros w s Hn. unfold errb_map_cf. cbv zeta. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
rk_if; [apply rk_spin|].
apply rk_bind. unfold errb_retire. apply rk_modify. cbn [fst snd]. apply rk_modify. cbn [snd].
cbn [st_secs set_secs set_nev]. exact (secs_grow_remap (st_secs s) _ Hn).
Qed.
End SG.

(* The IRet form a walk uses (errb_set_size is a modify, so always IRet). *)
Lemma secs_errb_set_grow_ret : forall ns s s', errb_set_size ns s = IRet (tt, s') -> errb_size_cf s <= ns -> 0 <= ns ->
  secs_errb_grow (st_secs s) (st_secs s').
Proof.
intros ns s s' H Hle H0. pose proof (secs_errb_set_grow ns s Hle H0) as P. rewrite H in P. exact P.
Qed.
