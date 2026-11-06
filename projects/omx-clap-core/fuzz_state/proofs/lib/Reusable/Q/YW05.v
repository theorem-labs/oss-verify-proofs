(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0g YO0e.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c.
Variable N : nat.
Definition IDn (s : astate) : Prop := (N <= length (st_regions s))%nat.
Ltac idn_close := unfold IDn in *; cbn;
repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn;
rewrite ?length_app, ?length_lupd; cbn; first [assumption | reflexivity | lia].
Ltac setter := intros ? ?; idn_close.
Ltac pgo0 :=
repeat first
[ assumption
| solve [eauto 3]
| apply presI_ret | apply presI_get | apply presI_ask | apply presI_askz | apply presI_fail
| apply presI_massert | apply presI_mcheck
| apply presI_modify; [solve [setter] ]
| apply presI_bind_get; intros ? ?
| apply presI_bind; [ | intros ? ]
| lazymatch goal with
| |- IDn _ => solve [idn_close]
| |- tall _ (IRet _) => cbn [tall snd fst]
| |- presI _ (match ?x with _ => _ end) => destruct x
| |- presI _ (if ?x then _ else _) => destruct x
| |- tall _ (match ?x with _ => _ end ?s) => destruct x
| |- tall _ ((if ?b then _ else _) ?s) => destruct b
| |- tall _ (put _ _) => apply tall_put; solve [idn_close]
| |- tall _ (bind (put _) _ _) => apply tall_bind_put
| |- tall _ (bind get _ _) => apply tall_bind_get
| |- tall _ (bind (modify _) _ _) => apply tall_bind_modify
| |- tall _ (?m ?s) => apply tall_of_presI; [ | solve [assumption | idn_close] ]
| H : presI _ ?f |- presI _ (?f _) => apply H
| H : presI _ ?f |- presI _ (?f _ _) => apply H
| H : presI _ ?f |- presI _ (?f _ _ _) => apply H
| H : presI _ ?f |- presI _ (?f _ _ _ _) => apply H
| H : presI _ ?f |- presI _ (?f _ _ _ _ _) => apply H
| H : presI _ ?f |- presI _ (?f _ _ _ _ _ _ _) => apply H
end ].
Ltac pgo := pgo0; try solve [idn_close].
Lemma p_getm p : presI IDn (getm p). Proof. unfold getm. pgo. Qed.
Lemma p_setm p am : presI IDn (setm p am). Proof. unfold setm. pgo. Qed.
Lemma p_setslot p x : presI IDn (setslot p x). Proof. unfold setslot. pgo. Qed.
Lemma p_get_links p : presI IDn (get_links p). Proof. unfold get_links. pgo. Qed.
Lemma p_set_links p a b : presI IDn (set_links p a b). Proof. unfold set_links. pose proof p_setslot. pgo. Qed.
Lemma p_set_prev p a : presI IDn (set_prev p a). Proof. unfold set_prev. pose proof p_get_links. pose proof p_set_links. pgo. Qed.
Lemma p_set_next p a : presI IDn (set_next p a). Proof. unfold set_next. pose proof p_get_links. pose proof p_set_links. pgo. Qed.
Lemma p_get_head h : presI IDn (get_head h). Proof. unfold get_head. pgo. Qed.
Lemma p_set_head h v : presI IDn (set_head h v). Proof. unfold set_head. pgo. Qed.
Lemma p_queue h m : presI IDn (queue h m).
Proof. unfold queue. pose proof p_get_links. pose proof p_set_links. pose proof p_set_next. pose proof p_set_prev. pose proof p_get_head. pose proof p_set_head. pgo. Qed.
Lemma p_dequeue h m : presI IDn (dequeue h m).
Proof. unfold dequeue. pose proof p_get_links. pose proof p_set_links. pose proof p_set_next. pose proof p_set_prev. pose proof p_get_head. pose proof p_set_head. pgo. Qed.
Lemma p_dequeue_head h : presI IDn (dequeue_head h). Proof. unfold dequeue_head. pose proof p_get_head. pose proof p_dequeue. pgo. Qed.
Lemma p_free_meta m : presI IDn (free_meta m). Proof. unfold free_meta. pose proof p_setslot. pose proof p_queue. pgo. Qed.
Lemma p_set_usage_of sc v : presI IDn (set_usage_of sc v). Proof. unfold set_usage_of. pgo. Qed.
Lemma p_step_seq : presI IDn step_seq. Proof. unfold step_seq. pgo. Qed.
Lemma p_record_seq sc : presI IDn (record_seq sc). Proof. unfold record_seq. pgo. Qed.
Lemma p_account_bounce sc : presI IDn (account_bounce sc). Proof. unfold account_bounce. pgo. Qed.
Lemma p_decay_bounces sc : presI IDn (decay_bounces sc). Proof. unfold decay_bounces. pgo. Qed.
Lemma p_new_region k len : presI IDn (new_region k len). Proof. unfold new_region. pgo. Qed.
Lemma p_upd_region r f : presI IDn (upd_region r f). Proof. unfold upd_region. pgo. Qed.
Lemma p_area_from_brk : presI IDn area_from_brk. Proof. unfold area_from_brk. pose proof p_new_region. pose proof p_upd_region. pgo. Qed.
Lemma p_area_from_mmap : presI IDn area_from_mmap. Proof. unfold area_from_mmap. pose proof p_new_region. pose proof p_upd_region. pgo. Qed.
Lemma p_open_area b : presI IDn (open_area b). Proof. unfold open_area. pose proof p_new_region. pose proof p_upd_region. pgo. Qed.
Lemma p_alloc_meta : presI IDn alloc_meta.
Proof. unfold alloc_meta. pose proof p_dequeue_head. pose proof p_area_from_brk. pose proof p_area_from_mmap. pose proof p_open_area. pose proof p_setslot. pgo. Qed.
Lemma p_activate_group m : presI IDn (activate_group m). Proof. unfold activate_group. pose proof p_getm. pose proof p_setm. pgo. Qed.
Lemma p_try_avail sc : presI IDn (try_avail sc).
Proof. unfold try_avail. pose proof p_getm. pose proof p_setm. pose proof p_get_head. pose proof p_set_head. pose proof p_dequeue.
pose proof p_activate_group. pose proof p_decay_bounces. pgo. Qed.
Lemma p_enframe g idx n ctr k : presI IDn (enframe g idx n ctr k).
Proof. unfold enframe. pose proof p_getm. pose proof p_setm. pgo. Qed.
Lemma p_install_group m sc cnt aidx maplen mem sl : presI IDn (install_group m sc cnt aidx maplen mem sl).
Proof. unfold install_group. pose proof p_getm. pose proof p_setm. pose proof p_setslot. pose proof p_queue. pose proof p_set_head. pose proof p_set_usage_of. pgo. Qed.
Lemma p_alloc_slot_group fuel : (forall sc req, presI IDn (alloc_slot fuel sc req)) /\ (forall sc req, presI IDn (alloc_group fuel sc req)).
Proof.
induction fuel as [|fuel [IHs IHg]]; (split; intros sc req; [cbn [alloc_slot] | cbn [alloc_group]]).
- apply presI_fail. - apply presI_fail.
- pose proof p_try_avail. pgo.
- pose proof p_alloc_meta. pose proof p_account_bounce. pose proof p_step_seq. pose proof p_free_meta. pose proof p_new_region.
pose proof p_install_group. pose proof p_get_head. pose proof p_getm. pose proof p_enframe. pgo.
Qed.
Lemma p_alloc_slot fuel sc req : presI IDn (alloc_slot fuel sc req). Proof. apply (proj1 (p_alloc_slot_group fuel)). Qed.
Lemma p_malloc n : presI IDn (malloc n).
Proof. unfold malloc. pose proof p_alloc_meta. pose proof p_step_seq. pose proof p_new_region. pose proof p_upd_region. pose proof p_setm. pose proof p_getm.
pose proof p_enframe. pose proof p_set_usage_of. pose proof p_get_head. pose proof p_alloc_slot. pose proof p_free_meta. pgo. Qed.
Lemma p_find_frame p : presI IDn (find_frame p). Proof. unfold find_frame. pgo. Qed.
Lemma p_forget_frame g i : presI IDn (forget_frame g i). Proof. unfold forget_frame. pose proof p_getm. pose proof p_setm. pgo. Qed.
Lemma p_release_slot g i : presI IDn (release_slot g i). Proof. unfold release_slot. pose proof p_getm. pose proof p_setm. pgo. Qed.
Lemma p_nontrivial_free fuel : forall g i, presI IDn (nontrivial_free fuel g i).
Proof.
induction fuel as [|fuel IH]; intros g i; cbn [nontrivial_free]; [apply presI_fail|].
pose proof p_getm. pose proof p_setm. pose proof p_get_head. pose proof p_dequeue. pose proof p_activate_group.
pose proof p_set_usage_of. pose proof p_step_seq. pose proof p_record_seq. pose proof p_find_frame. pose proof p_forget_frame.
pose proof p_free_meta. pose proof p_queue. pgo.
Qed.
Lemma p_free p : presI IDn (free p).
Proof. unfold free. pose proof p_find_frame. pose proof p_getm. pose proof p_setm. pose proof p_release_slot. pose proof p_nontrivial_free.
pose proof p_upd_region. pgo. Qed.
End c.


Theorem malloc_regions_tall : forall n s,
tall (fun r => (length (st_regions s) <= length (st_regions (snd r)))%nat) (malloc n s).
Proof. intros n s. exact (p_malloc (length (st_regions s)) n s (le_n _)). Qed.
Theorem free_regions_tall : forall p s,
tall (fun r => (length (st_regions s) <= length (st_regions (snd r)))%nat) (free p s).
Proof. intros p s. exact (p_free (length (st_regions s)) p s (le_n _)). Qed.
