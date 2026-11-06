(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30: the two NULL calls of the free move (rows A20b / A20c; a Theorem Labs lane's texts, 2026-10-30).
   Model lemmas and one contract implication; no function is proved (rule 24). No address.
   (A20c) What one malloc_cf does to st_secs, on EVERY path of the model (YG00.apath, any trace, gflag or not):
   - malloc_cf_secs_keep (any result): every real entry of S (sec_user_cf, sm_size >= 0) is unchanged at S', at its
     index, and every errbuf (control) entry stays a control entry. The only st_secs writes of malloc_cf are
     sec_alloc's append (YG00.v:351-367) and the errbuf steps (YG00cf.v: errb_retire re-tags capacity entries,
     errb_map_cf appends one, errb_set_size rewrites the size entry in place or appends it), which touch control
     entries only.
   - malloc_cf_null_live_keep: a live REAL slot of S is live at S' with its length. The premise sec_real is needed: a
     live control entry (a capacity entry with sm_live = true, which wf_errb_cf forbids but shape_cf allows) dies at
     errb_retire on a class-full NULL path.
   - malloc_cf_null_dead_empty: the dead set of a NULL malloc is empty (no premise), since dead_shadow_new counts
     real slots only. dead_shadow_new_of_keep gives the same for any result.
   - malloc_cf_null_no_new_live: every live entry of S' is S's entry at its index (the errbuf entries appended are
     dead; a NULL secondary request appends nothing, since sec_alloc's refused map keeps st_secs).
   The walk follows YGcfSecsStep.v's (sections 3 and 4), with the relation nk_cf in place of secs_same.
   (A20b) afree_null_realizes_cf: the free(NULL) contract in the released form (plain amreal, free_leaf_cf), with the
   model fact rcc_same, from the PRIMED free row YG0dcfR.afree_realizes_cf_rh. free_cf PNull is one IRet (tick, the
   internal-init flag, no ask), and it keeps st_secs (YGcfSecsStep.secs_free_null_step), so dead_shadow_new is empty
   at its exit (YGcfRehidePost.dead_shadow_new_same_secs_empty): the primed post's wle_in at the empty set is wle, and
   its view premise is discharged; rcc_same is YGcfRealloc.cfr_free_null_gpost. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG02 YG04 YG0f YG0v YG0n YG0d YG0dH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfPath YGcfAmx YGcfRoomPre YGcfRoomKeep YGcfRoomStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRehidePost ReallocP YGcfRealloc YGcfSecsStep YG0dcfR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The relations and their list facts.                                         *)
(* Every real entry of s is unchanged at s', and every control entry of s stays a control entry. *)
Definition secs_keep_cf (s s' : astate) : Prop :=
forall r sm, nth_error (st_secs s) r = Some sm -> exists sm', nth_error (st_secs s') r = Some sm' /\
  (sec_user_cf sm = true -> sm' = sm) /\ (sec_user_cf sm = false -> sec_user_cf sm' = false).

(* Every live entry of s' is s's entry at its index: no entry revived, none added live. *)
Definition no_new_live_cf (s s' : astate) : Prop :=
forall r sm', nth_error (st_secs s') r = Some sm' -> sm_live sm' = true -> nth_error (st_secs s) r = Some sm'.

Definition nk_cf (s s' : astate) : Prop := secs_keep_cf s s' /\ no_new_live_cf s s'.

Lemma nk_refl : forall s, nk_cf s s.
Proof.
intros s. split.
- intros r sm H. exists sm. split; [exact H|]. split; [intros _; reflexivity | intros F; exact F].
- intros r sm' H _. exact H.
Qed.

Lemma nk_of_secs : forall s s', st_secs s' = st_secs s -> nk_cf s s'.
Proof.
intros s s' E. split.
- intros r sm H. exists sm. rewrite E. split; [exact H|]. split; [intros _; reflexivity | intros F; exact F].
- intros r sm' H _. rewrite E in H. exact H.
Qed.

Lemma nk_trans : forall s1 s2 s3, nk_cf s1 s2 -> nk_cf s2 s3 -> nk_cf s1 s3.
Proof.
intros s1 s2 s3 [K12 N12] [K23 N23]. split.
- intros r sm H1. destruct (K12 r sm H1) as (sm2 & H2 & U2 & C2).
  destruct (K23 r sm2 H2) as (sm3 & H3 & U3 & C3).
  exists sm3. split; [exact H3|]. split.
  + intros U. pose proof (U2 U) as E2. subst sm2. exact (U3 U).
  + intros F. exact (C3 (C2 F)).
- intros r sm3 H3 L3. exact (N12 r sm3 (N23 r sm3 H3 L3) L3).
Qed.

Lemma sk_secs_r : forall s s1 s2, secs_keep_cf s s1 -> st_secs s2 = st_secs s1 -> secs_keep_cf s s2.
Proof. intros s s1 s2 K E r sm H. rewrite E. exact (K r sm H). Qed.

Lemma sk_app : forall s s' l, st_secs s' = st_secs s ++ l -> secs_keep_cf s s'.
Proof.
intros s s' l E r sm H. exists sm. rewrite E, nth_error_app1 by (apply nth_error_Some; rewrite H; discriminate).
split; [exact H|]. split; [intros _; reflexivity | intros F; exact F].
Qed.

(* An append of dead entries. *)
Lemma nk_app_dead : forall s s' l, st_secs s' = st_secs s ++ l -> Forall (fun x => sm_live x = false) l -> nk_cf s s'.
Proof.
intros s s' l E D. split; [exact (sk_app s s' l E)|].
intros r sm' H L. rewrite E in H. destruct (Nat.lt_ge_cases r (length (st_secs s))) as [Lt|Ge].
- rewrite nth_error_app1 in H by exact Lt. exact H.
- rewrite nth_error_app2 in H by exact Ge. apply nth_error_In in H. rewrite Forall_forall in D.
  rewrite (D _ H) in L. discriminate L.
Qed.

(* errb_retire's map (YGcfSecsStep.ss_retire) keeps a real entry, keeps a control entry a control entry, and leaves
   live only an entry it did not change. *)
Lemma nk_rt_user : forall sm, sec_user_cf sm = true -> ss_retire sm = sm.
Proof.
intros sm U. apply ss_retire_ncap. unfold sec_user_cf, is_errb_cap in *. apply Z.leb_le in U.
apply Z.eqb_neq. unfold ERRB_CAP_TAG. lia.
Qed.

Lemma nk_rt_ctl : forall sm, sec_user_cf sm = false -> sec_user_cf (ss_retire sm) = false.
Proof. intros sm U. unfold ss_retire. destruct (is_errb_cap sm); [reflexivity | exact U]. Qed.

Lemma nk_rt_live : forall sm, sm_live (ss_retire sm) = true -> ss_retire sm = sm.
Proof. intros sm L. unfold ss_retire in *. destruct (is_errb_cap sm); [cbn in L; discriminate L | reflexivity]. Qed.

(* errb_map_cf's write (YG00cf.v): the retire, then one dead capacity entry appended. *)
Lemma nk_retire_app : forall s s' x, st_secs s' = map ss_retire (st_secs s) ++ [x] -> sm_live x = false -> nk_cf s s'.
Proof.
intros s s' x E Dx. split.
- intros r sm H. exists (ss_retire sm).
  rewrite E, nth_error_app1 by (rewrite length_map; apply nth_error_Some; rewrite H; discriminate).
  rewrite nth_error_map, H. split; [reflexivity|]. split; [exact (fun U => nk_rt_user sm U) | exact (nk_rt_ctl sm)].
- intros r sm' H L. rewrite E in H. destruct (Nat.lt_ge_cases r (length (map ss_retire (st_secs s)))) as [Lt|Ge].
  + rewrite nth_error_app1 in H by exact Lt. rewrite nth_error_map in H.
    destruct (nth_error (st_secs s) r) as [sm|] eqn:Hs; cbn [option_map] in H; [|discriminate H].
    injection H as <-. rewrite (nk_rt_live sm L). reflexivity.
  + rewrite nth_error_app2 in H by exact Ge. apply nth_error_In in H. destruct H as [<- | []].
    rewrite Dx in L. discriminate L.
Qed.

(* errb_set_size's in-place write of the size entry (YG00cf.v): a dead control entry over a control entry. *)
Lemma nk_lupd_ctl : forall s s' i x y, st_secs s' = lupd (st_secs s) i x -> nth_error (st_secs s) i = Some y ->
sec_user_cf y = false -> sec_user_cf x = false -> sm_live x = false -> nk_cf s s'.
Proof.
intros s s' i x y E Hy Uy Ux Lx.
assert (Li : (i < length (st_secs s))%nat) by (apply nth_error_Some; rewrite Hy; discriminate).
split.
- intros r sm H. rewrite E. destruct (Nat.eq_dec i r) as [<-|Ne].
  + exists x. rewrite (nth_error_lupd_same (st_secs s) i x Li). rewrite Hy in H. injection H as <-.
    split; [reflexivity|]. split; [intros U; rewrite Uy in U; discriminate U | intros _; exact Ux].
  + exists sm. rewrite (nth_error_lupd_other (st_secs s) i r x Ne). split; [exact H|].
    split; [intros _; reflexivity | intros F; exact F].
- intros r sm' H L. rewrite E in H. destruct (Nat.eq_dec i r) as [<-|Ne].
  + rewrite (nth_error_lupd_same (st_secs s) i x Li) in H. injection H as <-. rewrite Lx in L. discriminate L.
  + rewrite (nth_error_lupd_other (st_secs s) i r x Ne) in H. exact H.
Qed.

Lemma nk_padd_not_null : forall p d, p <> PNull -> padd p d <> PNull.
Proof. intros [|o|r o|c q] d H; cbn [padd]; [contradiction H; reflexivity | discriminate | discriminate | exact H]. Qed.

Lemma nk_user_of_real : forall sm, sec_real sm -> sec_user_cf sm = true.
Proof. intros sm H. unfold sec_real in H. unfold sec_user_cf. apply Z.leb_le. exact H. Qed.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* A relation that keeps every real entry and every control entry's kind hides nothing new. *)
Lemma dead_shadow_new_of_keep : forall ly S S' a, secs_keep_cf S S' -> ~ dead_shadow_new ly S S' a.
Proof.
intros ly S S' a K (r & sm & sm0 & (Hn & Hl & Hr & _) & Hn0 & Hl0 & _ & _).
destruct (K r sm0 Hn0) as (sm' & Hn' & U & C). rewrite Hn in Hn'. injection Hn' as <-.
destruct (sec_user_cf sm0) eqn:E0.
- specialize (U eq_refl). subst sm. rewrite Hl in Hl0. discriminate Hl0.
- specialize (C eq_refl). rewrite (nk_user_of_real sm Hr) in C. discriminate C.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The errbuf (YGcfSecsStep.v section 3, with nk_cf).                          *)
Lemma nk_errb_map : forall w s, ipost (errb_map_cf w s) (fun r => nk_cf s (snd r)).
Proof.
intros w s. unfold errb_map_cf. cbv zeta. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_askz. intros z. cbn [fst snd].
rk_if; [apply rk_spin|].
apply rk_bind. unfold errb_retire. apply rk_modify. cbn [fst snd]. apply rk_modify. cbn [snd].
apply (nk_retire_app _ _ (mkSec (round_up w kPage) ERRB_CAP_TAG false)); reflexivity.
Qed.

Lemma nk_errb_set : forall ns s, ipost (errb_set_size ns s) (fun r => nk_cf s (snd r)).
Proof.
intros ns s. unfold errb_set_size. apply rk_modify. cbn [snd].
destruct (find_sz (st_secs s) 0) as [i|] eqn:Ef.
- destruct (ss_find_sz_nth _ _ _ Ef) as (y & Hy & Sy). rewrite Nat.sub_0_r in Hy.
  apply (nk_lupd_ctl s _ i (mkSec ns ERRB_SZ_TAG false) y); [reflexivity | exact Hy | exact (ss_sz_not_real y Sy)
  | reflexivity | reflexivity].
- apply (nk_app_dead s _ [mkSec ns ERRB_SZ_TAG false]); [reflexivity | constructor; [reflexivity | constructor]].
Qed.

Lemma nk_errb_append : forall len s, ipost (errb_append_cf len s) (fun r => nk_cf s (snd r)).
Proof.
intros len s. unfold errb_append_cf. cbv zeta. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (negb (errb_mapped_cf s)); cbv beta iota.
- apply rk_bind. eapply ipost_mono; [|apply nk_errb_map]. intros [u s1] H1. cbn [fst snd] in *.
  apply rk_bind. apply rk_get. cbn [fst snd].
  apply rk_bind. eapply ipost_mono with (P := fun r => nk_cf s1 (snd r)).
  2:{ destruct (errb_cap_cf s1 <? len); cbv beta iota;
      [apply nk_errb_map | apply rk_ret; cbn [snd]; apply nk_refl]. }
  intros [u2 s2] H2. cbn [fst snd] in *.
  eapply ipost_mono; [|apply nk_errb_set]. intros [u3 s3] H3. cbn [snd] in *.
  exact (nk_trans _ _ _ H1 (nk_trans _ _ _ H2 H3)).
- apply rk_bind. eapply ipost_mono with (P := fun r => nk_cf s (snd r)).
  2:{ destruct (errb_cap_cf s <? errb_size_cf s + len); cbv beta iota;
      [apply nk_errb_map | apply rk_ret; cbn [snd]; apply nk_refl]. }
  intros [u2 s2] H2. cbn [fst snd] in *.
  eapply ipost_mono; [|apply nk_errb_set]. intros [u3 s3] H3. cbn [snd] in *.
  exact (nk_trans _ _ _ H2 H3).
Qed.

Lemma nk_errb_report : forall c s, ipost (errb_report_cf c s) (fun r => nk_cf s (snd r)).
Proof.
intros c s. unfold errb_report_cf. apply rk_bind. apply rk_get. cbn [fst snd].
destruct (exh_mem_cf s c); cbv beta iota.
- apply rk_ret. cbn [snd]. apply nk_refl.
- apply rk_bind. eapply ipost_mono; [|apply nk_errb_append]. intros [u s1] H1. cbn [fst snd] in *.
  eapply ipost_mono; [|apply nk_errb_append]. intros [u2 s2] H2. cbn [snd] in *.
  exact (nk_trans _ _ _ H1 H2).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3. malloc_cf (YGcfSecsStep.v section 4, with nk_cf; cgif's chain keeps st_secs). *)
Lemma nk_mmu : forall c need s, ipost (map_more_user_cf c need s) (fun r => nk_cf s (snd r)).
Proof.
intros c need s. unfold map_more_user_cf. destruct (Z.eqb_spec c kBatchClass) as [E|_]; cbv beta iota zeta.
{ eapply ipost_mono; [|apply ss_mmu0]. intros r H. apply nk_of_secs. exact H. }
apply rk_bind. apply rk_get_region. cbn [fst snd].
rk_if.
- rk_if.
  + apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. destruct (aGranted z); cbv beta iota.
    * apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
      apply nk_of_secs. reflexivity.
    * apply rk_bind. eapply ipost_mono with (P := fun r => st_secs (snd r) = st_secs s).
      2:{ destruct (aDestroyed z); cbv beta iota; [apply rk_set_region; reflexivity | apply rk_ret; reflexivity]. }
      intros [u s1] H1. cbn [fst snd] in *. apply rk_ret. cbn [snd]. apply nk_of_secs. exact H1.
  + apply rk_bind. eapply ipost_mono; [|apply nk_errb_report]. intros [u s1] H1. cbn [fst snd] in *.
    apply rk_bind. unfold set_exh_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
    apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
    eapply nk_trans; [exact H1 | apply nk_of_secs; reflexivity].
- apply rk_ret. cbn [snd]. apply nk_refl.
Qed.

Lemma nk_populate : forall c need s, ipost (populate_cf c need s) (fun r => nk_cf s (snd r)).
Proof.
intros c need s. unfold populate_cf. destruct (Z.eqb_spec c kBatchClass) as [E|_]; cbv beta iota zeta.
{ eapply ipost_mono; [|apply ss_populate0]. intros r H. apply nk_of_secs. exact H. }
apply rk_bind. eapply ipost_mono; [|apply nk_mmu]. intros [ok s1] H1. cbn [fst snd] in *.
destruct ok; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd].
  apply rk_bind. eapply ipost_mono; [|apply ss_efa]. intros [ok2 s2] S2. cbn [fst snd] in *.
  destruct ok2; cbn [negb]; cbv beta iota.
  + apply rk_bind. apply rk_get_region. cbn [fst snd]. apply rk_bind. apply rk_set_region. cbn [fst snd].
    apply rk_bind. unfold clear_exh_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
    apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
    eapply nk_trans; [exact H1 | apply nk_of_secs; cbn [st_secs set_regions]; exact S2].
  + apply rk_ret. cbn [snd]. eapply nk_trans; [exact H1 | apply nk_of_secs; exact S2].
- apply rk_ret. cbn [snd]. exact H1.
Qed.

Lemma nk_gfa : forall c n s, ipost (get_from_allocator_cf c n s) (fun r => nk_cf s (snd r)).
Proof.
intros c n s. unfold get_from_allocator_cf. apply rk_bind. apply rk_get_region. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => nk_cf s (snd r)).
2:{ rk_if; [apply nk_populate | apply rk_ret; cbn [snd]; apply nk_refl]. }
intros [ok s1] H1. cbn [fst snd] in *.
destruct ok; cbn [negb]; cbv beta iota.
- apply rk_bind. apply rk_get_region. cbn [fst snd]. rk_if.
  + apply rk_ret. cbn [snd]. exact H1.
  + match goal with |- context [fa_pop_n ?f ?a ?b ?l ?acc] => destruct (fa_pop_n f a b l acc) as [[tops rest]|] end;
    cbv beta iota.
    * apply rk_bind. apply rk_set_region. cbn [fst snd]. apply rk_ret. cbn [snd].
      eapply nk_trans; [exact H1 | apply nk_of_secs; reflexivity].
    * apply rk_fail.
- apply rk_ret. cbn [snd]. exact H1.
Qed.

Lemma nk_refill : forall c s, ipost (refill_if_empty_cf c s) (fun r => nk_cf s (snd r)).
Proof.
intros c s. unfold refill_if_empty_cf. apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s c)) as [|x l]; cbv beta iota.
- apply rk_bind. eapply ipost_mono; [|apply nk_gfa]. intros [got s1] H1. cbn [fst snd] in *.
  destruct got as [tops|]; cbv beta iota.
  + apply rk_set_pc. cbn [snd]. eapply nk_trans; [exact H1 | apply nk_of_secs; reflexivity].
  + apply rk_ret. cbn [snd]. exact H1.
- apply rk_ret. cbn [snd]. apply nk_refl.
Qed.

Lemma nk_cache_alloc : forall c s, ipost (cache_alloc_cf c s) (fun r => nk_cf s (snd r)).
Proof.
intros c s. unfold cache_alloc_cf. apply rk_bind. eapply ipost_mono; [|apply ss_init_cache].
intros [u s1] S1. cbn [fst snd] in *.
apply rk_bind. eapply ipost_mono; [|apply nk_refill]. intros [u2 s2] H2. cbn [fst snd] in *.
pose proof (nk_trans _ _ _ (nk_of_secs _ _ S1) H2) as H12.
apply rk_bind. apply rk_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s2 c)) as [|x l]; cbv beta iota zeta.
- apply rk_ret. cbn [snd]. exact H12.
- apply rk_bind. apply rk_set_pc. cbn [fst snd]. apply rk_ret. cbn [snd].
  eapply nk_trans; [exact H12 | apply nk_of_secs; reflexivity].
Qed.

(* sec_alloc: a refused map keeps st_secs; a granted one appends one entry and returns a non-null pointer. *)
Lemma nk_sec_alloc : forall n s, ipost (sec_alloc n s) (fun r => secs_keep_cf s (snd r) /\
match fst r with None => no_new_live_cf s (snd r) | Some beg => beg <> PNull end).
Proof.
intros n s. eapply ipost_mono; [|apply secs_sec_alloc_entry]. intros [ob s2] [[E S2] | [E S2]]; cbn [fst snd] in *;
subst ob; cbv beta iota.
- exact (nk_of_secs s s2 S2).
- split; [exact (sk_app s s2 _ S2) | discriminate].
Qed.

Theorem nk_malloc : forall n tr s, ipost (malloc_cf n tr s) (fun r =>
secs_keep_cf s (snd r) /\ (fst r = PNull -> no_new_live_cf s (snd r))).
Proof.
intros n tr s.
unfold malloc_cf. apply rk_bind. apply rk_tick. cbn [fst snd].
apply rk_bind. apply rk_mcheck. intros _. cbn [fst snd].
apply rk_bind. eapply ipost_mono with (P := fun r => secs_keep_cf s (snd r) /\
  match fst r with None => no_new_live_cf s (snd r) | Some beg => beg <> PNull end).
- intros [ob s2] [K2 N2]. cbn [fst snd] in *. cbv zeta.
  destruct ob as [beg|]; cbv beta iota.
  + apply rk_bind. eapply ipost_mono; [|apply rk_depot]. intros [u3 s3] N3. cbn [fst snd] in *.
    apply rk_bind. eapply ipost_mono with (P := fun r => snd r = s3).
    2:{ rk_if.
        - apply rk_bind. apply rk_askz. intros z. cbn [fst snd]. rk_if; [apply rk_ret; reflexivity | apply rk_spin].
        - apply rk_ret. reflexivity. }
    intros [u4 s4] E4. cbn [fst snd] in *. subst s4.
    apply rk_bind. apply rk_modify. cbn [fst snd]. apply rk_ret. cbn [fst snd].
    pose proof N3 as (_ & _ & _ & S3 & _).
    split.
    * apply (sk_secs_r s s2); [exact K2 | cbn [st_secs set_chunks]; exact S3].
    * intros Hp. exfalso. unfold ck_user in Hp. exact (nk_padd_not_null beg _ N2 Hp).
  + apply rk_ret. cbn [fst snd]. split; [exact K2 | intros _; exact N2].
- destruct (from_primary n) eqn:Fp; cbv beta iota.
  + apply rk_bind. eapply ipost_mono; [|apply nk_cache_alloc].
    intros [o s2] [K2 N2]. cbn [fst snd] in *. apply rk_ret. cbn [fst snd].
    destruct o as [off|]; cbv beta iota.
    * split; [exact K2 | discriminate].
    * split; [exact K2 | exact N2].
  + eapply ipost_mono; [|apply nk_sec_alloc]. intros r Hr. exact Hr.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The apath forms (A20c).                                                     *)
Theorem malloc_cf_secs_keep : forall n tr S t r, apath (malloc_cf n tr S) t r -> secs_keep_cf S (snd r).
Proof. intros n tr S t r Hp. exact (proj1 (ipost_apath _ _ _ _ (nk_malloc n tr S) Hp)). Qed.

Theorem malloc_cf_null_live_keep : forall n tr S t S', apath (malloc_cf n tr S) t (PNull, S') ->
forall r sm, nth_error (st_secs S) r = Some sm -> sm_live sm = true -> sec_real sm ->
exists sm', nth_error (st_secs S') r = Some sm' /\ sm_live sm' = true /\ sm_len sm' = sm_len sm.
Proof.
intros n tr S t S' Hp r sm H L R.
destruct (malloc_cf_secs_keep n tr S t (PNull, S') Hp r sm H) as (sm' & H' & U & _).
rewrite (U (nk_user_of_real sm R)) in H'. exists sm. split; [exact H'|]. split; [exact L | reflexivity].
Qed.

Theorem malloc_cf_null_dead_empty : forall ly n tr S t S' a, apath (malloc_cf n tr S) t (PNull, S') ->
~ dead_shadow_new ly S S' a.
Proof.
intros ly n tr S t S' a Hp. exact (dead_shadow_new_of_keep ly S S' a (malloc_cf_secs_keep n tr S t (PNull, S') Hp)).
Qed.

Theorem malloc_cf_null_no_new_live : forall n tr S t S', apath (malloc_cf n tr S) t (PNull, S') ->
forall r sm', nth_error (st_secs S') r = Some sm' -> sm_live sm' = true -> nth_error (st_secs S) r = Some sm'.
Proof. intros n tr S t S' Hp. exact (proj2 (ipost_apath _ _ _ _ (nk_malloc n tr S) Hp) eq_refl). Qed.

(* ---------------------------------------------------------------------------- *)
(* 5. free(NULL) in the released form, from the primed free row (A20b).          *)
Definition afree_null_realizes_cf (segs : list Segment) (B : asyms) : Prop :=
forall ly S Hp W regs mem md n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch ->
getr regs 10 = w64 (sptr_addr B ly PNull) -> ~ In (sptr_addr B ly PNull) Hp ->
admits (as_universe B) (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S ->
amreal segs (free_cf PNull (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S) W
(cfg_at segs (pc_wrap_free (as_code B)) regs mem md)
(fun r W' c' => free_leaf_cf segs B ly S Hp W regs mem md PNull n r W' c' /\ rcc_same S (snd r)).

(* free_cf PNull asks nothing: it is one IRet. *)
Lemma free_cf_null_ret : forall tr S, exists S1, free_cf PNull tr S = IRet (tt, S1).
Proof.
intros tr S. unfold free_cf. cbn.
match goal with |- context [if ?b then _ else _] => destruct b end; eexists; reflexivity.
Qed.

Theorem afree_null_realizes_cf_of_rh : forall segs B, afree_realizes_cf_rh segs B -> afree_null_realizes_cf segs B.
Proof.
intros segs B H ly S Hp W regs mem md n ch PRE Hr Hh Htr.
pose proof (H ly S Hp W regs mem md PNull n ch PRE (or_introl eq_refl) Hr Hh Htr) as A.
destruct (free_cf_null_ret (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S) as [S1 E].
assert (SS : st_secs S1 = st_secs S).
{ apply (secs_free_null_step (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S []). rewrite E. cbn. reflexivity. }
assert (RC : rcc_same S S1).
{ apply (cfr_free_null_gpost (call_trace ly (pc_free_ra0 (as_code B)) regs ch) S [] (tt, S1));
  [rewrite E; cbn; reflexivity | reflexivity]. }
assert (DN : forall a, ~ dead_shadow_new ly S S1 a) by (intros a; exact (dead_shadow_new_same_secs_empty ly S S1 a SS)).
rewrite E in A |- *. unfold amreal' in A. cbn [amrealG] in A. cbn [amreal].
intros HI T HK. apply (A HI T). intros W' c' _ HI' HL.
destruct HL as (ly' & regs' & mem' & md' & HC & HP & REST).
rewrite acall_post_cf_rh_unfold in HP. destruct HP as (AR & LL & WI & AP & IO & VW & ST).
apply (HK W' c'); [hnf; intros a Ha; destruct (WI a Ha) as [H1 | H2]; [exact H1 | destruct (DN _ H2)] | exact HI' |].
split; [| exact RC].
exists ly', regs', mem', md'. split; [exact HC|]. split; [|exact REST].
red. refine (conj AR (conj LL (conj _ (conj AP (conj IO (conj _ ST)))))).
- hnf. intros a Ha. destruct (WI a Ha) as [H1 | H2]; [exact H1 | destruct (DN _ H2)].
- intros a Ha N1 N2 N3 N4. exact (VW a Ha N1 N2 N3 N4 (DN a)).
Qed.
End G.
