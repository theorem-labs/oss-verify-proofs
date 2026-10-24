(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Fixpoint tall {A : Type} (P : A -> Prop) (t : itree astate A) : Prop :=
match t with
| IRet a => P a
| IAsk _ _ k => forall z, tall P (k z)
| IFail _ => True
end.
Lemma tall_ibind {A B} (t : itree astate A) (k : A -> itree astate B) (P : A -> Prop) (Q : B -> Prop) :
tall P t -> (forall a, P a -> tall Q (k a)) -> tall Q (ibind t k).
Proof. revert k. induction t as [a | q s c IH | f]; intros k Ht Hk; cbn in *; auto. Qed.
Lemma tall_mono {A} (t : itree astate A) (P Q : A -> Prop) : (forall a, P a -> Q a) -> tall P t -> tall Q t.
Proof. induction t; cbn; intros; auto. Qed.
Lemma tall_yields {A} (t : itree astate A) P tr a : tall P t -> yields t tr a -> P a.
Proof.
revert tr. induction t as [a' | q s c IH | f]; intros tr Ht Hy; cbn in *.
- destruct tr; [subst; exact Ht | destruct Hy].
- destruct tr as [|[q' z] tr']; [destruct Hy|]. destruct Hy as (_ & _ & Hy). eapply IH; eauto.
- destruct tr; destruct Hy.
Qed.
Section d.
Variable ID : astate -> Prop.
Definition presI {A} (m : M A) : Prop := forall s, ID s -> tall (fun r => ID (snd r)) (m s).
Lemma presI_bind {A B} (m : M A) (k : A -> M B) : presI m -> (forall a, presI (k a)) -> presI (bind m k).
Proof. intros Hm Hk s Hs. unfold bind. eapply tall_ibind; [apply Hm, Hs|]. intros [a s'] H'. cbn in H'. apply Hk, H'. Qed.
Lemma presI_bind_get {B} (k : astate -> M B) : (forall s, ID s -> tall (fun r => ID (snd r)) (k s s)) -> presI (bind get k).
Proof. intros Hk s Hs. unfold bind, get. cbn. apply Hk, Hs. Qed.
Lemma presI_ret {A} (a : A) : presI (ret a). Proof. intros s Hs; exact Hs. Qed.
Lemma presI_get : presI get. Proof. intros s Hs; exact Hs. Qed.
Lemma presI_modify f : (forall s, ID s -> ID (f s)) -> presI (modify f). Proof. intros Hf s Hs. cbn. apply Hf, Hs. Qed.
Lemma presI_ask q : presI (ask q). Proof. intros s Hs z. exact Hs. Qed.
Lemma presI_askz q : presI (askz q). Proof. intros s Hs z. exact Hs. Qed.
Lemma presI_fail {A} f : presI (@fail A f). Proof. intros s Hs. exact I. Qed.
Lemma presI_massert b site : presI (massert b site). Proof. unfold massert. destruct b; [apply presI_ret | apply presI_fail]. Qed.
Lemma presI_mcheck b tag : presI (mcheck b tag). Proof. unfold mcheck. destruct b; [apply presI_ret | apply presI_fail]. Qed.
Lemma tall_of_presI {A} (m : M A) s : presI m -> ID s -> tall (fun r => ID (snd r)) (m s).
Proof. intros H Hs. apply H, Hs. Qed.
Lemma tall_put s0 s1 : ID s1 -> tall (fun r : unit * astate => ID (snd r)) (put s1 s0).
Proof. intros H. exact H. Qed.
Lemma tall_bind_put {B} (k : unit -> M B) s0 s1 P : tall P (k tt s1) -> tall P (bind (put s1) k s0).
Proof. intros H. exact H. Qed.
Lemma tall_bind_get {B} (k : astate -> M B) s0 P : tall P (k s0 s0) -> tall P (bind get k s0).
Proof. intros H. exact H. Qed.
Lemma tall_bind_modify {B} f (k : unit -> M B) s0 P : tall P (k tt (f s0)) -> tall P (bind (modify f) k s0).
Proof. intros H. exact H. Qed.
End d.
Definition IDn (s : astate) : Prop := st_init_done s = true.
Ltac idn_close := unfold IDn in *; cbn;
repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn; first [assumption | reflexivity].
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
Theorem malloc_keeps_init_done : forall n s tr r s',
st_init_done s = true -> yields (malloc n s) tr (r, s') -> st_init_done s' = true.
Proof. intros n s tr r s' Hs Hy. exact (tall_yields _ _ _ _ (p_malloc n s Hs) Hy). Qed.
Theorem free_keeps_init_done : forall p s tr r s',
st_init_done s = true -> yields (free p s) tr (r, s') -> st_init_done s' = true.
Proof. intros p s tr r s' Hs Hy. exact (tall_yields _ _ _ _ (p_free p s Hs) Hy). Qed.
Definition Jn (s : astate) : Prop := st_init_done s = true \/ st_metas s = [].
Lemma Jn_of_IDn s : IDn s -> Jn s. Proof. intros H; left; exact H. Qed.
Lemma presJ_of_presI_IDn {A} (m : M A) s : presI IDn m -> IDn s -> tall (fun r => Jn (snd r)) (m s).
Proof. intros H Hs. eapply tall_mono; [| apply H, Hs]. intros a Ha. left. exact Ha. Qed.
Lemma presJ_bind_getm {B} p (k : ameta -> M B) : (forall am, presI IDn (k am)) -> presI Jn (bind (getm p) k).
Proof.
intros Hk s [Hs|Hs]; unfold bind, getm, get; cbn.
- destruct (mlookup (st_metas s) p) as [[| |am]|]; cbn; try exact I. apply presJ_of_presI_IDn; [apply Hk | exact Hs].
- rewrite Hs. cbn. exact I.
Qed.
Lemma presJ_bind_get_links {B} p (k : _ -> M B) : (forall l, presI IDn (k l)) -> presI Jn (bind (get_links p) k).
Proof.
intros Hk s [Hs|Hs]; unfold bind, get_links, get; cbn.
- destruct (mlookup (st_metas s) p) as [x|]; cbn; try exact I. apply presJ_of_presI_IDn; [apply Hk | exact Hs].
- rewrite Hs. cbn. exact I.
Qed.
Lemma find_frame_in_nil p : find_frame_in [] p = None. Proof. reflexivity. Qed.
Lemma presJ_bind_find_frame {B} p (k : _ -> M B) : (forall x, presI IDn (k x)) -> presI Jn (bind (find_frame p) k).
Proof.
intros Hk s [Hs|Hs]; unfold bind, find_frame, get; cbn.
- destruct (find_frame_in (st_metas s) p) as [x|]; cbn; try exact I. apply presJ_of_presI_IDn; [apply Hk | exact Hs].
- rewrite Hs. cbn. exact I.
Qed.
Lemma presJ_bind_set_init {B} (k : unit -> M B) : presI IDn (k tt) -> presI Jn (bind (modify (set_init_done true)) k).
Proof. intros Hk s Hs. unfold bind, modify. cbn. apply presJ_of_presI_IDn; [exact Hk | reflexivity]. Qed.
Definition presJI {A} (m : M A) : Prop := forall s, Jn s -> tall (fun r => IDn (snd r)) (m s).
Lemma presJI_presJ {A} (m : M A) : presJI m -> presI Jn m.
Proof. intros H s Hs. eapply tall_mono; [|apply H, Hs]. intros a Ha; left; exact Ha. Qed.
Lemma presJI_bind {A B} (m : M A) (k : A -> M B) : presJI m -> (forall a, presI IDn (k a)) -> presJI (bind m k).
Proof. intros Hm Hk s Hs. unfold bind. eapply tall_ibind; [apply Hm, Hs|]. intros [a s'] H'. apply Hk, H'. Qed.
Lemma presJ_bind_JI {A B} (m : M A) (k : A -> M B) : presJI m -> (forall a, presI IDn (k a)) -> presI Jn (bind m k).
Proof. intros Hm Hk. apply presJI_presJ. apply presJI_bind; assumption. Qed.
Ltac jn_close := unfold Jn, IDn in *; cbn;
repeat (match goal with |- context [if ?b then _ else _] => destruct b end); cbn; first [assumption | tauto].
Ltac jsetter := intros ? ?; jn_close.
Ltac jgo0 :=
repeat first
[ assumption
| solve [eauto 3]
| apply presJ_bind_set_init
| apply presJ_bind_JI; [ solve [eauto 2] | intros ? ]
| apply presJ_bind_getm; intros ?
| apply presJ_bind_get_links; intros ?
| apply presJ_bind_find_frame; intros ?
| apply presI_ret | apply presI_get | apply presI_ask | apply presI_askz | apply presI_fail
| apply presI_massert | apply presI_mcheck
| apply presI_modify; [ solve [jsetter | setter] ]
| apply presI_bind_get; intros ? ?
| apply presI_bind; [ | intros ? ]
| lazymatch goal with
| |- Jn _ => solve [jn_close]
| |- IDn _ => solve [idn_close]
| |- tall _ (IRet _) => cbn [tall snd fst]
| |- presI _ (match ?x with _ => _ end) => destruct x
| |- presI _ (if ?x then _ else _) => destruct x
| |- tall _ (match ?x with _ => _ end ?s) => destruct x
| |- tall _ ((if ?b then _ else _) ?s) => destruct b
| |- tall _ (put _ _) => apply tall_put; solve [jn_close | idn_close]
| |- tall _ (bind (put _) _ _) => apply tall_bind_put
| |- tall _ (bind get _ _) => apply tall_bind_get
| |- tall _ (bind (modify _) _ _) => apply tall_bind_modify
| |- tall _ (?m ?s) => apply tall_of_presI; [ | solve [assumption | jn_close | idn_close] ]
end ].
Ltac jgo := jgo0; try solve [jn_close | idn_close].
Lemma j_set_links p a b : presI Jn (set_links p a b). Proof. unfold set_links. intros s [Hs|Hs]; unfold bind, get; cbn; [|rewrite Hs; exact I].
destruct (mlookup (st_metas s) p); cbn; [|exact I]. left. exact Hs. Qed.
Lemma j_set_prev p a : presI Jn (set_prev p a). Proof. unfold set_prev. pose proof p_set_links. jgo. Qed.
Lemma j_set_next p a : presI Jn (set_next p a). Proof. unfold set_next. pose proof p_set_links. jgo. Qed.
Lemma j_get_head h : presI Jn (get_head h). Proof. unfold get_head. jgo. Qed.
Lemma j_set_head h v : presI Jn (set_head h v). Proof. unfold set_head. jgo. Qed.
Lemma j_queue h m : presI Jn (queue h m).
Proof. unfold queue. pose proof p_get_links. pose proof p_set_links. pose proof p_set_next. pose proof p_set_prev. pose proof p_get_head. pose proof p_set_head. jgo. Qed.
Lemma j_dequeue h m : presI Jn (dequeue h m).
Proof. unfold dequeue. pose proof p_get_links. pose proof p_set_links. pose proof p_set_next. pose proof p_set_prev. pose proof p_get_head. pose proof p_set_head. jgo. Qed.
Lemma j_dequeue_head h : presI Jn (dequeue_head h). Proof. unfold dequeue_head. pose proof j_get_head. pose proof j_dequeue. jgo. Qed.
Lemma j_new_region k len : presI Jn (new_region k len). Proof. unfold new_region. jgo. Qed.
Lemma j_upd_region r f : presI Jn (upd_region r f). Proof. unfold upd_region. jgo. Qed.
Lemma j_area_from_brk : presI Jn area_from_brk. Proof. unfold area_from_brk. pose proof j_new_region. pose proof j_upd_region. jgo. Qed.
Lemma j_area_from_mmap : presI Jn area_from_mmap. Proof. unfold area_from_mmap. pose proof j_new_region. pose proof j_upd_region. jgo. Qed.
Lemma j_open_area b : presI Jn (open_area b). Proof. unfold open_area. pose proof j_new_region. pose proof j_upd_region. jgo. Qed.
Lemma j_alloc_meta : presI Jn alloc_meta.
Proof. unfold alloc_meta. pose proof p_dequeue_head. pose proof p_area_from_brk. pose proof p_area_from_mmap. pose proof p_open_area. pose proof p_setslot. jgo. Qed.
Lemma j_decay_bounces sc : presI Jn (decay_bounces sc). Proof. unfold decay_bounces. jgo. Qed.
Lemma j_account_bounce sc : presI Jn (account_bounce sc). Proof. unfold account_bounce. jgo. Qed.
Lemma j_step_seq : presI Jn step_seq. Proof. unfold step_seq. jgo. Qed.
Lemma j_activate_group m : presI Jn (activate_group m). Proof. unfold activate_group. pose proof p_setm. jgo. Qed.
Lemma j_try_avail sc : presI Jn (try_avail sc).
Proof. unfold try_avail. pose proof p_getm. pose proof p_setm. pose proof p_get_head. pose proof p_set_head. pose proof p_dequeue.
pose proof p_activate_group. pose proof p_decay_bounces. pose proof j_get_head. jgo. Qed.
Lemma ji_alloc_meta : presJI alloc_meta.
Proof. unfold alloc_meta. intros s Hs. unfold bind at 1. unfold modify. cbn [ibind].
pose proof p_dequeue_head. pose proof p_area_from_brk. pose proof p_area_from_mmap. pose proof p_open_area. pose proof p_setslot.
match goal with |- tall _ (?m ?s1) => apply (tall_of_presI IDn m s1); [| reflexivity] end. pgo.
Qed.
Lemma j_alloc_slot_group fuel : (forall sc req, presI Jn (alloc_slot fuel sc req)) /\ (forall sc req, presI Jn (alloc_group fuel sc req)).
Proof.
induction fuel as [|fuel [IHs IHg]]; (split; intros sc req; [cbn [alloc_slot] | cbn [alloc_group]]).
- apply presI_fail. - apply presI_fail.
- pose proof j_try_avail. jgo.
- apply presJ_bind_JI; [apply ji_alloc_meta|]. intros om.
pose proof p_account_bounce. pose proof p_step_seq. pose proof p_free_meta. pose proof p_new_region.
pose proof p_install_group. pose proof p_get_head. pose proof p_getm. pose proof p_enframe. pose proof (proj1 (p_alloc_slot_group fuel)).
pgo.
Qed.
Lemma j_malloc n : presI Jn (malloc n).
Proof. unfold malloc. pose proof ji_alloc_meta. pose proof j_step_seq. pose proof p_step_seq. pose proof p_new_region. pose proof j_new_region.
pose proof p_upd_region. pose proof j_upd_region. pose proof p_setm. pose proof p_getm.
pose proof p_enframe. pose proof p_set_usage_of. pose proof p_get_head. pose proof j_get_head. pose proof (proj1 (j_alloc_slot_group NEST_FUEL)). pose proof p_free_meta.
jgo.
Qed.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
Lemma user_blocks_nil_metas s : st_metas s = [] -> user_blocks s = [].
Proof. intros H. unfold user_blocks, used_metas. rewrite H. reflexivity. Qed.
Theorem malloc_some_init_done : forall n s tr q s',
WF s -> 0 <= n -> (st_init_done s = true \/ st_metas s = []) ->
yields (malloc n s) tr (Some q, s') -> st_init_done s' = true.
Proof.
intros n s tr q s' HW Hn HJ Hy.
pose proof (tall_yields _ _ _ _ (j_malloc n s HJ) Hy) as HJ'. cbn [snd] in HJ'.
destruct HJ' as [H|H]; [exact H|].
pose proof (malloc_blocks s n tr (Some q) s' HW Hn Hy) as (l1 & l2 & E & _).
rewrite (user_blocks_nil_metas s' H) in E. destruct l1; discriminate.
Qed.
Corollary malloc_init_state_init_done : forall n tr q s',
0 <= n -> yields (malloc n init_state) tr (Some q, s') -> st_init_done s' = true.
Proof. intros n tr q s' Hn Hy. eapply malloc_some_init_done; [apply wf_init | exact Hn | right; reflexivity | exact Hy]. Qed.
