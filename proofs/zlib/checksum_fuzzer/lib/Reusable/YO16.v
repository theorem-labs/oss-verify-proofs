(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition shp (rs : list region) : list (rkind * bool) := map (fun rg => (rg_kind rg, rg_live rg)) rs.
Lemma same_shape_shp a b : same_shape_regions a b <-> shp a = shp b.
Proof.
unfold same_shape_regions, shp. split.
- revert b. induction a as [|x a IH]; intros [|y b] [H1 H2]; cbn in *; try discriminate; [reflexivity|].
injection H1 as E1 T1. injection H2 as E2 T2. rewrite E1, E2. f_equal. apply IH. split; assumption.
- revert b. induction a as [|x a IH]; intros [|y b] H; cbn in *; try discriminate; [split; reflexivity|].
injection H as E1 E2 T. destruct (IH b T) as [IH1 IH2]. rewrite E1, E2, IH1, IH2. split; reflexivity.
Qed.
Lemma shp_app a b : shp (a ++ b) = shp a ++ shp b.
Proof. unfold shp. apply map_app. Qed.
Lemma shp_lupd l r x : shp (lupd l r x) = lupd (shp l) r (rg_kind x, rg_live x).
Proof. revert r. induction l as [|y l IH]; intros [|r]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma lupd_nth_same {T} (l : list T) r (f : T -> T) d :
(forall x, f x = x) -> lupd l r (f (nth r l d)) = l.
Proof. intros Hf. rewrite Hf. revert r. induction l as [|y l IH]; intros [|r]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma shp_lupd_keep l r (f : region -> region) d :
(forall rg, rg_kind (f rg) = rg_kind rg /\ rg_live (f rg) = rg_live rg) ->
shp (lupd l r (f (nth r l d))) = shp l.
Proof.
intros Hf. revert r. induction l as [|y l IH]; intros [|r]; cbn [lupd nth]; try reflexivity.
- destruct (Hf y) as [E1 E2]. unfold shp. cbn [map]. rewrite E1, E2. reflexivity.
- unfold shp in *. cbn [map]. f_equal. apply IH.
Qed.
Lemma shp_length a b : shp a = shp b -> length a = length b.
Proof. intros H. rewrite <- (length_map (fun rg => (rg_kind rg, rg_live rg)) a), <- (length_map (fun rg => (rg_kind rg, rg_live rg)) b). unfold shp in H. rewrite H. reflexivity. Qed.
Definition ra1 (rs : list region) (e : kreq * Z) : list region :=
match e with
| (KMmapRW len, z) => if z =? 0 then rs else rs ++ [mkRegion RkMap (page_round len) [] true]
| (KMmapNone len, z) => if z =? 0 then rs else rs ++ [mkRegion RkMetaRes len [] true]
| (KBrkGrow 2, z) => if z =? 0 then rs else rs ++ [mkRegion RkBrk (2 * PGSZ) [] true]
| (KMunmap r len, _) => lupd rs r (mkRegion RkMap (rg_len (nth r rs (mkRegion RkMap 0 [] false))) [] false)
| (KMremap r ol nl, z) =>
if z =? 0 then rs
else lupd (rs ++ [mkRegion RkMap nl [] true]) r (mkRegion RkMap (rg_len (nth r rs (mkRegion RkMap 0 [] false))) [] false)
| _ => rs
end.
Lemma regions_after_cons rs e t : regions_after rs (e :: t) = regions_after (ra1 rs e) t.
Proof. destruct e as [q z]. destruct q; try reflexivity. cbn [regions_after ra1]. destruct npages as [|p|p]; try reflexivity. destruct p as [p|p|]; try reflexivity. destruct p; reflexivity. Qed.
Fixpoint rt {A : Type} (rs : list region) (t : itree astate A) (Q : list region -> A -> Prop) : Prop :=
match t with
| IRet a => Q rs a
| IFail _ => True
| IAsk q snap k => req_ok snap q -> forall z, rt (ra1 rs (q, z)) (k z) Q
end.
Lemma rt_yields {A} rs (t : itree astate A) Q tr a :
rt rs t Q -> reqs_ok t -> yields t tr a -> Q (regions_after rs tr) a.
Proof.
revert rs tr. induction t as [a' | q sp k IH | f]; intros rs tr H RQ Y; destruct tr as [|[q' z] tr]; cbn in Y; try contradiction.
- subst a'. exact H.
- destruct Y as (-> & Az & Y). cbn in RQ. destruct RQ as [Rq RQ]. rewrite regions_after_cons. apply (IH z). + apply H. exact Rq. + apply RQ. exact Az. + exact Y.
Qed.
Lemma rt_conseq {A} rs (t : itree astate A) (Q Q' : list region -> A -> Prop) :
rt rs t Q -> (forall rs' a, Q rs' a -> Q' rs' a) -> rt rs t Q'.
Proof. revert rs. induction t as [a | q sp k IH | f]; intros rs H HQ; cbn in *; [apply HQ, H | | exact I]. intros Rq z. apply IH; [apply H; exact Rq | exact HQ]. Qed.
Lemma rt_ibind {A B} rs (x : itree astate A) (K : A -> itree astate B) Q :
rt rs x (fun rs' a => rt rs' (K a) Q) -> rt rs (ibind x K) Q.
Proof. revert rs. induction x as [a | q sp k IH | f]; intros rs H; cbn in *; [exact H | | exact I]. intros Rq z. apply IH. apply H. exact Rq. Qed.
Section c.
Context {A B : Type}.
Implicit Types (s : astate) (rs : list region).
Lemma rt_ret rs (a : A) s Q : Q rs (a, s) -> rt rs (ret a s) Q.
Proof. intros H. exact H. Qed.
Lemma rt_bind rs (m : M B) (k : B -> M A) s Q :
rt rs (m s) (fun rs' r => rt rs' (k (fst r) (snd r)) Q) -> rt rs (bind m k s) Q.
Proof. intros H. unfold bind. apply rt_ibind. eapply rt_conseq; [exact H|]. intros rs' [b s']. cbn. intros X; exact X. Qed.
Lemma rt_fail rs f s Q : rt rs (@fail A f s) Q.
Proof. exact I. Qed.
Lemma rt_get rs s (Q : list region -> astate * astate -> Prop) : Q rs (s, s) -> rt rs (get s) Q.
Proof. intros H; exact H. Qed.
Lemma rt_put rs s s' (Q : list region -> unit * astate -> Prop) : Q rs (tt, s') -> rt rs (put s' s) Q.
Proof. intros H; exact H. Qed.
Lemma rt_modify rs f s (Q : list region -> unit * astate -> Prop) : Q rs (tt, f s) -> rt rs (modify f s) Q.
Proof. intros H; exact H. Qed.
Lemma rt_ask rs q s (Q : list region -> bool * astate -> Prop) :
(req_ok s q -> forall z, Q (ra1 rs (q, z)) (negb (z =? 0), s)) -> rt rs (ask q s) Q.
Proof. intros H Rq z. cbn. apply H. exact Rq. Qed.
Lemma rt_askz rs q s (Q : list region -> Z * astate -> Prop) :
(req_ok s q -> forall z, Q (ra1 rs (q, z)) (z, s)) -> rt rs (askz q s) Q.
Proof. intros H Rq z. cbn. apply H. exact Rq. Qed.
Lemma rt_massert rs (b : bool) i s (Q : list region -> unit * astate -> Prop) :
(b = true -> Q rs (tt, s)) -> rt rs (massert b i s) Q.
Proof. intros H. unfold massert. destruct b; [apply H; reflexivity | exact I]. Qed.
Lemma rt_mcheck rs (b : bool) i s (Q : list region -> unit * astate -> Prop) :
(b = true -> Q rs (tt, s)) -> rt rs (mcheck b i s) Q.
Proof. intros H. unfold mcheck. destruct b; [apply H; reflexivity | exact I]. Qed.
End c.
Lemma rt_getm rs p s (Q : list region -> ameta * astate -> Prop) :
(forall am, MT s p = Some (MUsed am) -> Q rs (am, s)) -> rt rs (getm p s) Q.
Proof.
intros H. unfold getm. apply rt_bind. apply rt_get. cbn [fst snd]. unfold MT in H.
destruct (mlookup (st_metas s) p) as [[| |am]|]; try exact I. apply H. reflexivity.
Qed.
Lemma rt_get_links rs p s (Q : list region -> (option sptr * option sptr) * astate -> Prop) :
(forall l, Q rs (l, s)) -> rt rs (get_links p s) Q.
Proof. intros H. unfold get_links. apply rt_bind. apply rt_get. cbn [fst snd]. destruct (mlookup (st_metas s) p); [apply H | exact I]. Qed.
Lemma rt_set_links rs p pr nx s (Q : list region -> unit * astate -> Prop) :
(forall ms, Q rs (tt, set_metas ms s)) -> rt rs (set_links p pr nx s) Q.
Proof. intros H. unfold set_links. apply rt_bind. apply rt_get. cbn [fst snd]. destruct (mlookup (st_metas s) p); [apply H | exact I]. Qed.
Definition sq {A} (rs : list region) (r : A * astate) : Prop := shp (st_regions (snd r)) = shp rs.
Create HintDb rt.
Ltac rq := cbn [st_regions st_metas set_init_done set_mmap_counter set_free_meta_head set_avail_meta set_avail_meta_count
set_avail_meta_area_count set_meta_alloc_shift set_area_head set_area_tail set_avail_meta_areas
set_active set_usage set_unmap_seq set_bounces set_seq set_brk set_metas set_regions set_areas fst snd] in *.
Ltac rtstep :=
lazymatch goal with
| |- rt _ (bind _ _ _) _ => apply rt_bind
| |- rt _ (ret _ _) _ => apply rt_ret
| |- rt _ (get _) _ => apply rt_get
| |- rt _ (put _ _) _ => apply rt_put
| |- rt _ (modify _ _) _ => apply rt_modify
| |- rt _ (setm _ _ _) _ => unfold setm at 1; apply rt_modify
| |- rt _ (setslot _ _ _) _ => unfold setslot at 1; apply rt_modify
| |- rt _ (set_usage_of _ _ _) _ => unfold set_usage_of at 1; apply rt_modify
| |- rt _ (set_head _ _ _) _ => unfold set_head at 1
| |- rt _ (get_head _ _) _ => unfold get_head at 1
| |- rt _ (getm _ _) _ => apply rt_getm; intros ? ?
| |- rt _ (get_links _ _) _ => apply rt_get_links; intros ?
| |- rt _ (set_links _ _ _ _) _ => apply rt_set_links; intros ?
| |- rt _ (set_prev _ _ _) _ => unfold set_prev at 1
| |- rt _ (set_next _ _ _) _ => unfold set_next at 1
| |- rt _ (massert _ _ _) _ => apply rt_massert; intros _
| |- rt _ (mcheck _ _ _) _ => apply rt_mcheck; intros ?
| |- rt _ (ask _ _) _ => let z := fresh "z" in apply rt_ask; intros ?RQ z; cbn [ra1]; destruct (z =? 0); cbn [negb]
| |- rt _ (askz _ _) _ => apply rt_askz; intros ?RQ ?; cbn [ra1]
| |- rt _ (fail _ _) _ => apply rt_fail
| |- rt _ (IFail _) _ => exact I
| |- rt _ (IRet _) _ => cbn [rt]
| |- rt _ (match ?x with _ => _ end _) _ => destruct x eqn:?
| |- rt _ (match ?x with _ => _ end) _ => destruct x eqn:?
| |- rt _ _ (fun _ _ => rt _ _ _) =>
let HQ := fresh "HQ" in
eapply rt_conseq; [solve [eauto 4 with rt nocore] | intros ? [? ?] HQ;
lazymatch type of HQ with
| _ /\ _ => let EQ := fresh "EQ" in destruct HQ as [HQ EQ]; cbn [fst snd] in EQ; try subst
| _ => idtac
end; unfold sq in HQ; cbn [fst snd] in HQ ]
| |- rt _ _ _ => solve [eauto 3 with rt nocore]
| |- sq _ _ => unfold sq; rq; solve [assumption | congruence | auto]
| |- True => exact I
| |- forall _, _ => intros ?
end.
Ltac rtauto := repeat (cbn beta iota zeta delta [fst snd negb andb orb]; rtstep).
Section j.
Implicit Types (s : astate) (rs : list region).
Lemma rt_queue rs h m s : shp (st_regions s) = shp rs -> rt rs (queue h m s) sq.
Proof. intros E. unfold queue. rtauto. all: destruct h; rtauto. Qed.
Hint Resolve rt_queue : rt.
Lemma rt_dequeue rs h m s : shp (st_regions s) = shp rs -> rt rs (dequeue h m s) sq.
Proof. intros E. unfold dequeue. rtauto; destruct h; rtauto. Qed.
Hint Resolve rt_dequeue : rt.
Lemma rt_dequeue_head rs h s : shp (st_regions s) = shp rs -> rt rs (dequeue_head h s) sq.
Proof. intros E. unfold dequeue_head. destruct h; rtauto. Qed.
Hint Resolve rt_dequeue_head : rt.
Lemma rt_free_meta rs m s : shp (st_regions s) = shp rs -> rt rs (free_meta m s) sq.
Proof. intros E. unfold free_meta. rtauto. Qed.
Hint Resolve rt_free_meta : rt.
Lemma rt_step_seq rs s : shp (st_regions s) = shp rs -> rt rs (step_seq s) sq.
Proof. intros E. unfold step_seq. rtauto. destruct (st_seq s =? 255); rq; exact E. Qed.
Hint Resolve rt_step_seq : rt.
Lemma rt_record_seq rs sc s : shp (st_regions s) = shp rs -> rt rs (record_seq sc s) sq.
Proof. intros E. unfold record_seq. destruct (bounce_idx sc); rtauto. Qed.
Hint Resolve rt_record_seq : rt.
Lemma rt_account_bounce rs sc s : shp (st_regions s) = shp rs -> rt rs (account_bounce sc s) sq.
Proof. intros E. unfold account_bounce. destruct (bounce_idx sc); rtauto. destruct (negb _ && _); rq; exact E. Qed.
Hint Resolve rt_account_bounce : rt.
Lemma rt_decay_bounces rs sc s : shp (st_regions s) = shp rs -> rt rs (decay_bounces sc s) sq.
Proof. intros E. unfold decay_bounces. destruct (bounce_idx sc); rtauto. destruct (_ =? 0); rq; exact E. Qed.
Hint Resolve rt_decay_bounces : rt.
Lemma rt_new_region rs k len len' s :
shp (st_regions s) = shp rs ->
rt (rs ++ [mkRegion k len' [] true]) (new_region k len s) (fun rs' r => sq rs' r /\ fst r = length (st_regions s)).
Proof. intros E. unfold new_region. rtauto. split; [|reflexivity]. unfold sq. rq. rewrite !shp_app, E. reflexivity. Qed.
Lemma rt_upd_region_keep rs r f s :
shp (st_regions s) = shp rs -> (forall rg, rg_kind (f rg) = rg_kind rg /\ rg_live (f rg) = rg_live rg) ->
rt rs (upd_region r f s) sq.
Proof. intros E Hf. unfold upd_region. rtauto. unfold sq. rq. rewrite (shp_lupd_keep _ _ _ _ Hf). exact E. Qed.
Lemma rt_upd_region_kill rs r len s :
shp (st_regions s) = shp rs ->
rt (lupd rs r (mkRegion RkMap len [] false)) (upd_region r (fun rg => mkRegion RkMap (rg_len rg) [] false) s) sq.
Proof. intros E. unfold upd_region. rtauto. unfold sq. rq. rewrite !shp_lupd, E. reflexivity. Qed.
Lemma shp_lupd_nth l r x rg :
nth_error l r = Some rg -> rg_kind x = rg_kind rg -> rg_live x = rg_live rg -> shp (lupd l r x) = shp l.
Proof.
revert r. induction l as [|y l IH]; intros [|r] Hn Hk Hl; cbn [lupd nth_error] in *; try reflexivity.
- injection Hn as ->. unfold shp. cbn [map]. rewrite Hk, Hl. reflexivity.
- unfold shp in *. cbn [map]. f_equal. apply IH; assumption.
Qed.
Lemma rt_upd_region_brk rs r pages s :
shp (st_regions s) = shp rs -> req_ok s (KBrkGrow 1) -> st_brk s = BrkCur r pages ->
rt rs (upd_region r (fun rg => mkRegion RkBrk (rg_len rg + PGSZ) [] true) s) sq.
Proof.
intros E RQ Hb. unfold upd_region. rtauto. unfold sq. rq.
destruct RQ as [[H _] | (_ & r0 & p0 & rg & Hb0 & Hrg & Hk & Hl & _)]; [lia|].
rewrite Hb in Hb0. injection Hb0 as <- <-. unfold region_of in Hrg.
rewrite <- E. apply (shp_lupd_nth _ _ _ rg); [exact Hrg | cbn; congruence | cbn; congruence].
Qed.
Hint Resolve rt_new_region rt_upd_region_keep rt_upd_region_kill rt_upd_region_brk : rt.
Hint Extern 1 (forall rg, _ = _ /\ _ = _) => intros; split; reflexivity : rt.
Lemma rt_area_from_brk rs s : shp (st_regions s) = shp rs -> rt rs (area_from_brk s) sq.
Proof.
intros E. unfold area_from_brk. rtauto. Qed.
Hint Resolve rt_area_from_brk : rt.
Lemma rt_area_from_mmap rs s : shp (st_regions s) = shp rs -> rt rs (area_from_mmap s) sq.
Proof. intros E. unfold area_from_mmap. rtauto. Qed.
Hint Resolve rt_area_from_mmap : rt.
Lemma rt_open_area rs nu s : shp (st_regions s) = shp rs -> rt rs (open_area nu s) sq.
Proof. intros E. unfold open_area. rtauto. Qed.
Hint Resolve rt_open_area : rt.
Lemma rt_alloc_meta rs s : shp (st_regions s) = shp rs -> rt rs (alloc_meta s) sq.
Proof. intros E. unfold alloc_meta. rtauto. Qed.
Hint Resolve rt_alloc_meta : rt.
Lemma rt_activate_group rs m s : shp (st_regions s) = shp rs -> rt rs (activate_group m s) sq.
Proof. intros E. unfold activate_group. rtauto. Qed.
Hint Resolve rt_activate_group : rt.
Lemma rt_try_avail rs sc s : shp (st_regions s) = shp rs -> rt rs (try_avail sc s) sq.
Proof. intros E. unfold try_avail. rtauto. Qed.
Hint Resolve rt_try_avail : rt.
Lemma rt_enframe rs g idx n ctr k s : shp (st_regions s) = shp rs -> rt rs (enframe g idx n ctr k s) sq.
Proof. intros E. unfold enframe. rtauto. Qed.
Hint Resolve rt_enframe : rt.
Lemma rt_install_group rs m sc cnt aidx maplen mem sl s :
shp (st_regions s) = shp rs -> rt rs (install_group m sc cnt aidx maplen mem sl s) sq.
Proof. intros E. unfold install_group. rtauto. Qed.
Hint Resolve rt_install_group : rt.
Lemma rt_forget_frame rs g i s : shp (st_regions s) = shp rs -> rt rs (forget_frame g i s) sq.
Proof. intros E. unfold forget_frame. rtauto. Qed.
Hint Resolve rt_forget_frame : rt.
Lemma rt_release_slot rs g i s : shp (st_regions s) = shp rs -> rt rs (release_slot g i s) sq.
Proof. intros E. unfold release_slot. rtauto. Qed.
Hint Resolve rt_release_slot : rt.
Lemma rt_find_frame rs p s : shp (st_regions s) = shp rs -> rt rs (find_frame p s) sq.
Proof. intros E. unfold find_frame. rtauto. Qed.
Hint Resolve rt_find_frame : rt.
Lemma rt_alloc_mutual fuel :
(forall rs sc req s, shp (st_regions s) = shp rs -> rt rs (alloc_slot fuel sc req s) sq) /\
(forall rs sc req s, shp (st_regions s) = shp rs -> rt rs (alloc_group fuel sc req s) sq).
Proof.
induction fuel as [|f [IHs IHg]]; [split; intros; cbn; exact I|]. split.
- intros rs sc req s E. cbn fix beta iota delta [alloc_slot]. rtauto.
- intros rs sc req s E. cbn fix beta iota delta [alloc_group]. rtauto.
Qed.
Lemma rt_alloc_slot fuel rs sc req s : shp (st_regions s) = shp rs -> rt rs (alloc_slot fuel sc req s) sq.
Proof. apply (proj1 (rt_alloc_mutual fuel)). Qed.
Hint Resolve rt_alloc_slot : rt.
Lemma rt_malloc rs n s : shp (st_regions s) = shp rs -> rt rs (malloc n s) sq.
Proof. intros E. unfold malloc. rtauto. Qed.
Lemma rt_nontrivial_free fuel rs g i s : shp (st_regions s) = shp rs -> rt rs (nontrivial_free fuel g i s) sq.
Proof.
revert rs g i s. induction fuel as [|f IH]; intros rs g i s E; [cbn; exact I|].
cbn fix beta iota delta [nontrivial_free]. rtauto.
Qed.
Hint Resolve rt_nontrivial_free : rt.
Lemma rt_free rs p s : shp (st_regions s) = shp rs -> rt rs (free p s) sq.
Proof. intros E. unfold free. rtauto. Qed.
End j.
