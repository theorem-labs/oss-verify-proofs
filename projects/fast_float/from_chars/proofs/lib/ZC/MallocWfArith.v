(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocLemmasBase.
Import ListNotations.

Module MallocWfTrace.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import
  MallocModel MallocInv MallocLemmasBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)
Definition ra1 (rs : list region) (e : kreq * Z) : list region :=
  match e with
  | (KMmapRW len, z) => if z =? 0 then rs else rs ++ [mkRegion RkMap (page_round len) [] true]
  | (KMmapNone len, z) => if z =? 0 then rs else rs ++ [mkRegion RkMetaRes len [] true]
  | (KBrkGrow 2, z) => if z =? 0 then rs else rs ++ [mkRegion RkBrk (2 * PGSZ) [] true]
  | (KMunmap r len, _) => lupd rs r (mkRegion RkMap (rg_len (nth r rs (mkRegion RkMap 0 [] false))) [] false)
  | _ => rs
  end.

Lemma regions_after_cons rs e t : regions_after rs (e :: t) = regions_after (ra1 rs e) t.
Proof. destruct e as [q z]. destruct q; try reflexivity. cbn [regions_after ra1]. destruct npages as [|p|p]; try reflexivity. destruct p as [p|p|]; try reflexivity. destruct p; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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

Section MonadRules.
  Context {A B : Type}.
  Implicit Types (s : astate) (rs : list region).

  #[using="Type"] Lemma rt_ret rs (a : A) s Q : Q rs (a, s) -> rt rs (ret a s) Q.
  Proof. intros H. exact H. Qed.
  #[using="Type"] Lemma rt_bind rs (m : M B) (k : B -> M A) s Q :
    rt rs (m s) (fun rs' r => rt rs' (k (fst r) (snd r)) Q) -> rt rs (bind m k s) Q.
  Proof. intros H. unfold bind. apply rt_ibind. eapply rt_conseq; [exact H|]. intros rs' [b s']. cbn. intros X; exact X. Qed.
  #[using="Type"] Lemma rt_fail rs f s Q : rt rs (@fail A f s) Q.
  Proof. exact I. Qed.
  #[using="Type"] Lemma rt_get rs s (Q : list region -> astate * astate -> Prop) : Q rs (s, s) -> rt rs (get s) Q.
  Proof. intros H; exact H. Qed.
  #[using="Type"] Lemma rt_put rs s s' (Q : list region -> unit * astate -> Prop) : Q rs (tt, s') -> rt rs (put s' s) Q.
  Proof. intros H; exact H. Qed.
  #[using="Type"] Lemma rt_modify rs f s (Q : list region -> unit * astate -> Prop) : Q rs (tt, f s) -> rt rs (modify f s) Q.
  Proof. intros H; exact H. Qed.
  #[using="Type"] Lemma rt_ask rs q s (Q : list region -> bool * astate -> Prop) :
    (req_ok s q -> forall z, Q (ra1 rs (q, z)) (negb (z =? 0), s)) -> rt rs (ask q s) Q.
  Proof. intros H Rq z. cbn. apply H. exact Rq. Qed.
  #[using="Type"] Lemma rt_askz rs q s (Q : list region -> Z * astate -> Prop) :
    (req_ok s q -> forall z, Q (ra1 rs (q, z)) (z, s)) -> rt rs (askz q s) Q.
  Proof. intros H Rq z. cbn. apply H. exact Rq. Qed.
  #[using="Type"] Lemma rt_massert rs (b : bool) i s (Q : list region -> unit * astate -> Prop) :
    (b = true -> Q rs (tt, s)) -> rt rs (massert b i s) Q.
  Proof. intros H. unfold massert. destruct b; [apply H; reflexivity | exact I]. Qed.
  #[using="Type"] Lemma rt_mcheck rs (b : bool) i s (Q : list region -> unit * astate -> Prop) :
    (b = true -> Q rs (tt, s)) -> rt rs (mcheck b i s) Q.
  Proof. intros H. unfold mcheck. destruct b; [apply H; reflexivity | exact I]. Qed.
End MonadRules.

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

(* [comment removed for export] *)
Definition sq {A} (rs : list region) (r : A * astate) : Prop := shp (st_regions (snd r)) = shp rs.

Create HintDb rt.

Ltac rq := cbn [st_regions st_metas set_init_done set_mmap_counter set_free_meta_head set_avail_meta set_avail_meta_count
               set_avail_meta_area_count set_meta_alloc_shift set_area_head set_area_tail set_avail_meta_areas
               set_active set_usage set_unmap_seq set_bounces set_seq set_brk set_metas set_regions set_areas fst snd] in *.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Fns.
  Implicit Types (s : astate) (rs : list region).

  #[using="Type"] Lemma rt_queue rs h m s : shp (st_regions s) = shp rs -> rt rs (queue h m s) sq.
  Proof. intros E. unfold queue. rtauto. all: destruct h; rtauto. Qed.
  Hint Resolve rt_queue : rt.

  #[using="Type"] Lemma rt_dequeue rs h m s : shp (st_regions s) = shp rs -> rt rs (dequeue h m s) sq.
  Proof. intros E. unfold dequeue. rtauto; destruct h; rtauto. Qed.
  Hint Resolve rt_dequeue : rt.

  #[using="Type"] Lemma rt_dequeue_head rs h s : shp (st_regions s) = shp rs -> rt rs (dequeue_head h s) sq.
  Proof. intros E. unfold dequeue_head. destruct h; rtauto. Qed.
  Hint Resolve rt_dequeue_head : rt.

  #[using="Type"] Lemma rt_free_meta rs m s : shp (st_regions s) = shp rs -> rt rs (free_meta m s) sq.
  Proof. intros E. unfold free_meta. rtauto. Qed.
  Hint Resolve rt_free_meta : rt.

  #[using="Type"] Lemma rt_step_seq rs s : shp (st_regions s) = shp rs -> rt rs (step_seq s) sq.
  Proof. intros E. unfold step_seq. rtauto. destruct (st_seq s =? 255); rq; exact E. Qed.
  Hint Resolve rt_step_seq : rt.

  #[using="Type"] Lemma rt_record_seq rs sc s : shp (st_regions s) = shp rs -> rt rs (record_seq sc s) sq.
  Proof. intros E. unfold record_seq. destruct (bounce_idx sc); rtauto. Qed.
  Hint Resolve rt_record_seq : rt.

  #[using="Type"] Lemma rt_account_bounce rs sc s : shp (st_regions s) = shp rs -> rt rs (account_bounce sc s) sq.
  Proof. intros E. unfold account_bounce. destruct (bounce_idx sc); rtauto. destruct (negb _ && _); rq; exact E. Qed.
  Hint Resolve rt_account_bounce : rt.

  #[using="Type"] Lemma rt_decay_bounces rs sc s : shp (st_regions s) = shp rs -> rt rs (decay_bounces sc s) sq.
  Proof. intros E. unfold decay_bounces. destruct (bounce_idx sc); rtauto. destruct (_ =? 0); rq; exact E. Qed.
  Hint Resolve rt_decay_bounces : rt.

  (* [comment removed for export] *)
  #[using="Type"] Lemma rt_new_region rs k len len' s :
    shp (st_regions s) = shp rs ->
    rt (rs ++ [mkRegion k len' [] true]) (new_region k len s) (fun rs' r => sq rs' r /\ fst r = length (st_regions s)).
  Proof. intros E. unfold new_region. rtauto. split; [|reflexivity]. unfold sq. rq. rewrite !shp_app, E. reflexivity. Qed.

  #[using="Type"] Lemma rt_upd_region_keep rs r f s :
    shp (st_regions s) = shp rs -> (forall rg, rg_kind (f rg) = rg_kind rg /\ rg_live (f rg) = rg_live rg) ->
    rt rs (upd_region r f s) sq.
  Proof. intros E Hf. unfold upd_region. rtauto. unfold sq. rq. rewrite (shp_lupd_keep _ _ _ _ Hf). exact E. Qed.

  #[using="Type"] Lemma rt_upd_region_kill rs r len s :
    shp (st_regions s) = shp rs ->
    rt (lupd rs r (mkRegion RkMap len [] false)) (upd_region r (fun rg => mkRegion RkMap (rg_len rg) [] false) s) sq.
  Proof. intros E. unfold upd_region. rtauto. unfold sq. rq. rewrite !shp_lupd, E. reflexivity. Qed.

  #[using="Type"] Lemma shp_lupd_nth l r x rg :
    nth_error l r = Some rg -> rg_kind x = rg_kind rg -> rg_live x = rg_live rg -> shp (lupd l r x) = shp l.
  Proof.
    revert r. induction l as [|y l IH]; intros [|r] Hn Hk Hl; cbn [lupd nth_error] in *; try reflexivity.
    - injection Hn as ->. unfold shp. cbn [map]. rewrite Hk, Hl. reflexivity.
    - unfold shp in *. cbn [map]. f_equal. apply IH; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma rt_upd_region_brk rs r pages s :
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

  #[using="Type"] Lemma rt_area_from_brk rs s : shp (st_regions s) = shp rs -> rt rs (area_from_brk s) sq.
  Proof.
    intros E. unfold area_from_brk. rtauto. Qed.
  Hint Resolve rt_area_from_brk : rt.

  #[using="Type"] Lemma rt_area_from_mmap rs s : shp (st_regions s) = shp rs -> rt rs (area_from_mmap s) sq.
  Proof. intros E. unfold area_from_mmap. rtauto. Qed.
  Hint Resolve rt_area_from_mmap : rt.

  #[using="Type"] Lemma rt_open_area rs nu s : shp (st_regions s) = shp rs -> rt rs (open_area nu s) sq.
  Proof. intros E. unfold open_area. rtauto. Qed.
  Hint Resolve rt_open_area : rt.

  #[using="Type"] Lemma rt_alloc_meta rs s : shp (st_regions s) = shp rs -> rt rs (alloc_meta s) sq.
  Proof. intros E. unfold alloc_meta. rtauto. Qed.
  Hint Resolve rt_alloc_meta : rt.

  #[using="Type"] Lemma rt_activate_group rs m s : shp (st_regions s) = shp rs -> rt rs (activate_group m s) sq.
  Proof. intros E. unfold activate_group. rtauto. Qed.
  Hint Resolve rt_activate_group : rt.

  #[using="Type"] Lemma rt_try_avail rs sc s : shp (st_regions s) = shp rs -> rt rs (try_avail sc s) sq.
  Proof. intros E. unfold try_avail. rtauto. Qed.
  Hint Resolve rt_try_avail : rt.

  #[using="Type"] Lemma rt_enframe rs g idx n ctr k s : shp (st_regions s) = shp rs -> rt rs (enframe g idx n ctr k s) sq.
  Proof. intros E. unfold enframe. rtauto. Qed.
  Hint Resolve rt_enframe : rt.

  #[using="Type"] Lemma rt_install_group rs m sc cnt aidx maplen mem sl s :
    shp (st_regions s) = shp rs -> rt rs (install_group m sc cnt aidx maplen mem sl s) sq.
  Proof. intros E. unfold install_group. rtauto. Qed.
  Hint Resolve rt_install_group : rt.

  #[using="Type"] Lemma rt_forget_frame rs g i s : shp (st_regions s) = shp rs -> rt rs (forget_frame g i s) sq.
  Proof. intros E. unfold forget_frame. rtauto. Qed.
  Hint Resolve rt_forget_frame : rt.

  #[using="Type"] Lemma rt_release_slot rs g i s : shp (st_regions s) = shp rs -> rt rs (release_slot g i s) sq.
  Proof. intros E. unfold release_slot. rtauto. Qed.
  Hint Resolve rt_release_slot : rt.

  #[using="Type"] Lemma rt_find_frame rs p s : shp (st_regions s) = shp rs -> rt rs (find_frame p s) sq.
  Proof. intros E. unfold find_frame. rtauto. Qed.
  Hint Resolve rt_find_frame : rt.

  #[using="Type"] Lemma rt_alloc_mutual fuel :
    (forall rs sc req s, shp (st_regions s) = shp rs -> rt rs (alloc_slot fuel sc req s) sq) /\
    (forall rs sc req s, shp (st_regions s) = shp rs -> rt rs (alloc_group fuel sc req s) sq).
  Proof.
    induction fuel as [|f [IHs IHg]]; [split; intros; cbn; exact I|]. split.
    - intros rs sc req s E. cbn fix beta iota delta [alloc_slot]. rtauto.
    - intros rs sc req s E. cbn fix beta iota delta [alloc_group]. rtauto.
  Qed.
  #[using="Type"] Lemma rt_alloc_slot fuel rs sc req s : shp (st_regions s) = shp rs -> rt rs (alloc_slot fuel sc req s) sq.
  Proof. apply (proj1 (rt_alloc_mutual fuel)). Qed.
  Hint Resolve rt_alloc_slot : rt.

  #[using="Type"] Lemma rt_malloc rs n s : shp (st_regions s) = shp rs -> rt rs (malloc n s) sq.
  Proof. intros E. unfold malloc. rtauto. Qed.

  #[using="Type"] Lemma rt_nontrivial_free fuel rs g i s : shp (st_regions s) = shp rs -> rt rs (nontrivial_free fuel g i s) sq.
  Proof.
    revert rs g i s. induction fuel as [|f IH]; intros rs g i s E; [cbn; exact I|].
    cbn fix beta iota delta [nontrivial_free]. rtauto.
  Qed.
  Hint Resolve rt_nontrivial_free : rt.

  #[using="Type"] Lemma rt_free rs p s : shp (st_regions s) = shp rs -> rt rs (free p s) sq.
  Proof. intros E. unfold free. rtauto. Qed.
End Fns.
End MallocWfTrace.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Infix "==>" := implb (at level 55, right associativity).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zseq_In lo n k : 0 <= n -> lo <= k < lo + n -> In k (zseq lo n).
Proof.
  intros Hn Hk. unfold zseq. apply in_map_iff. exists (Z.to_nat (k - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Tactic Notation "brute" constr(H) constr(k) "as" ident(T) :=
  pose proof H as T; rewrite forallb_forall in T; specialize (T k);
  match type of T with In _ (zseq ?lo ?n) -> _ =>
    specialize (T (zseq_In lo n k ltac:(lia) ltac:(lia))); cbn beta in T end.

Lemma class_size_mono_tab :
  forallb (fun a => forallb (fun b => (a <=? b) ==> (znth a size_classes <=? znth b size_classes)) (zseq 0 48)) (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma class_size_mono a b : 0 <= a -> a <= b -> b < 48 -> class_size a <= class_size b.
Proof.
  intros Ha Hab Hb. brute class_size_mono_tab a as H. rewrite forallb_forall in H.
  specialize (H b (zseq_In 0 48 b ltac:(lia) ltac:(lia))). cbn beta in H.
  unfold implb in H. destruct (a <=? b) eqn:E; [|apply Z.leb_gt in E; lia]. cbn [negb orb] in H.
  apply Z.leb_le in H. unfold class_size, UNIT. lia.
Qed.

Lemma class_size_tab :
  forallb (fun a => (1 <=? znth a size_classes) && (znth a size_classes <=? 8191) &&
                    ((znth a size_classes <=? 127) ==> (a <=? 23))) (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma class_size_bounds sc : 0 <= sc < 48 -> 16 <= class_size sc <= 131056.
Proof.
  intros H. brute class_size_tab sc as H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [A B].
  apply Z.leb_le in A. apply Z.leb_le in B. unfold class_size, UNIT. lia.
Qed.

Lemma class_le_23 sc : 0 <= sc < 48 -> class_size sc <= 2032 -> sc <= 23.
Proof.
  intros H Hs. brute class_size_tab sc as H0. apply andb_prop in H0 as [_ C]. unfold implb in C.
  destruct (znth sc size_classes <=? 127) eqn:E; cbn [negb orb] in C; [apply Z.leb_le in C; lia|].
  apply Z.leb_gt in E. unfold class_size, UNIT in Hs. lia.
Qed.

Lemma class_of_units_small_tab :
  forallb (fun k => class_of_units k <=? 24) (zseq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma size_to_class_small n : 0 <= n <= 2044 -> size_to_class n <= 24.
Proof.
  intros Hn. unfold size_to_class.
  set (k := Z.shiftr (n + IB - 1) 4).
  assert (Hk : 0 <= k < 128).
  { subst k. rewrite Z.shiftr_div_pow2 by lia. unfold IB.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  brute class_of_units_small_tab k as H. apply Z.leb_le in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_round_ge x : x <= page_round x.
Proof. unfold page_round, PGSZ. pose proof (Z_div_mod_eq_full (x + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)). lia. Qed.

Lemma page_round_lt x : page_round x < x + PGSZ.
Proof. unfold page_round, PGSZ. pose proof (Z_div_mod_eq_full (x + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (x + 4096 - 1) 4096 ltac:(lia)). lia. Qed.

Lemma page_round_mod x : page_round x mod PGSZ = 0.
Proof. unfold page_round. apply Z_mod_mult. Qed.

Lemma page_round_pages x : page_round x = page_round x / PGSZ * PGSZ.
Proof. unfold page_round, PGSZ. rewrite Z_div_mult by lia. reflexivity. Qed.

Lemma page_round_mono x y : x <= y -> page_round x <= page_round y.
Proof. intros H. unfold page_round, PGSZ. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. Qed.

Lemma page_round_fixed x : x mod PGSZ = 0 -> page_round x = x.
Proof.
  intros H. unfold page_round. unfold PGSZ in *.
  pose proof (Z_div_mod_eq_full x 4096). rewrite H in H0.
  replace (x + 4096 - 1) with (4096 * (x / 4096) + 4095) by lia.
  rewrite (Z.mul_comm 4096 (x / 4096)), Z.div_add_l by lia. replace (4095 / 4096) with 0 by reflexivity. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint htrail (f : nat) (c : Z) : list Z :=
  c :: match f with O => [] | S f' => if Z.even c then htrail f' (c / 2) else [] end.

Lemma halve_while_even_In f c u : In (halve_while_even f c u) (htrail f c).
Proof.
  revert c. induction f as [|f IH]; intros c; cbn [halve_while_even htrail]; [left; reflexivity|].
  destruct (Z.even c) eqn:E; cbn [andb].
  - destruct (u <? 4 * c); [right; apply IH | left; reflexivity].
  - left; reflexivity.
Qed.

Lemma small_cnt_In sc u :
  In (small_cnt sc u) (let row := nth (Z.to_nat sc) small_cnt_tab [] in [znth 0 row; znth 1 row; znth 2 row]).
Proof.
  unfold small_cnt. set (row := nth (Z.to_nat sc) small_cnt_tab []).
  destruct (negb (u <? 4 * znth 0 row)); [left; reflexivity|].
  destruct (negb (u <? 4 * znth 1 row)); [right; left; reflexivity|]. right; right; left; reflexivity.
Qed.

Definition icands (sc : Z) : list Z :=
  map (fun cnt => if (cnt =? 1) && (class_size sc * cnt + UNIT <=? PGSZ / 2) then 2 else cnt)
      (if sc <? 9 then (let row := nth (Z.to_nat sc) small_cnt_tab [] in [znth 0 row; znth 1 row; znth 2 row])
       else map (fun c => halve_while_big 8%nat c (class_size sc)) (htrail 8%nat (znth (Z.land sc 3) med_cnt_tab))).

Lemma initial_cnt_In sc u : In (initial_cnt sc u) (icands sc).
Proof.
  unfold initial_cnt, icands. apply in_map_iff. eexists. split; [reflexivity|].
  destruct (sc <? 9).
  - apply small_cnt_In.
  - apply in_map_iff. eexists. split; [reflexivity|]. apply halve_while_even_In.
Qed.

Lemma icands_tab :
  forallb (fun sc => forallb (fun cnt => (1 <=? cnt) && (cnt <=? 32) && (class_size sc * cnt <? 2 ^ 20) &&
                                         ((sc <=? 26) ==> (2 <=? cnt))) (icands sc)) (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma initial_cnt_facts sc u :
  0 <= sc < 48 ->
  1 <= initial_cnt sc u <= 32 /\ class_size sc * initial_cnt sc u < 2 ^ 20 /\ (sc <= 26 -> 2 <= initial_cnt sc u).
Proof.
  intros Hsc. brute icands_tab sc as H. rewrite forallb_forall in H. specialize (H _ (initial_cnt_In sc u)).
  apply andb_prop in H as [H D]. apply andb_prop in H as [H C]. apply andb_prop in H as [A B].
  apply Z.leb_le in A. apply Z.leb_le in B. apply Z.ltb_lt in C. unfold implb in D.
  split; [lia|]. split; [exact C|]. intros H26.
  destruct (sc <=? 26) eqn:E; [|apply Z.leb_gt in E; lia]. cbn [negb orb] in D. apply Z.leb_le in D. exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_plan_facts s sc req cnt0 u cnt needed :
  0 <= sc < 48 -> 1 <= cnt0 <= 32 -> class_size sc * cnt0 < 2 ^ 20 ->
  0 <= req -> req + IB <= class_size sc -> (sc <= 26 -> 2 <= cnt0) ->
  mmap_plan s sc req cnt0 u = (cnt, needed) ->
  1 <= cnt <= 32 /\ class_size sc * cnt < 2 ^ 20 /\ (sc <= 26 -> 2 <= cnt) /\
  needed mod PGSZ = 0 /\ PGSZ <= needed /\ needed <= 2 ^ 20 /\
  (2 <= cnt -> UNIT + class_size sc * cnt <= needed) /\ req + IB + UNIT <= needed /\
  (cnt = 1 -> needed <= page_round (class_size sc + UNIT)).
Proof.
  intros Hsc Hc0 Hsz Hreq Hfit H26 Hp.
  pose proof (class_size_bounds sc Hsc) as [S16 Smax].
  assert (Hz16 : exists z, class_size sc = 16 * z) by (unfold class_size, UNIT; eexists; reflexivity).
  unfold mmap_plan in Hp.
  set (size := class_size sc) in *.
  set (nosmall := is_bouncing s sc) in *.
  set (usage := if Z.even sc && (sc <? 32) then u + usage_of s (sc + 1) else u) in *.
  match type of Hp with context [page_round (size * ?c + UNIT)] => set (cnt1 := c) in Hp end.
  assert (Hc1 : 1 <= cnt1 <= 32 /\ size * cnt1 < 2 ^ 20 /\ (sc <= 26 -> 2 <= cnt1)).
  { subst cnt1.
    destruct ((usage <? 4 * cnt0) && negb nosmall); [|split; [lia|split; [lia|exact H26]]].
    destruct ((Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt0)); [lia|].
    destruct ((Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt0)); [lia|].
    destruct ((Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt0)); [lia|].
    destruct ((Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt0)); [lia|].
    lia. }
  cbv zeta in Hp.
  assert (HN : forall c, 1 <= c <= 32 -> size * c < 2 ^ 20 -> (sc <= 26 -> 2 <= c) ->
            (c, page_round (size * c + UNIT)) = (cnt, needed) ->
            1 <= cnt <= 32 /\ size * cnt < 2 ^ 20 /\ (sc <= 26 -> 2 <= cnt) /\ needed mod PGSZ = 0 /\ PGSZ <= needed /\ needed <= 2 ^ 20 /\
            (2 <= cnt -> UNIT + size * cnt <= needed) /\ req + IB + UNIT <= needed /\
            (cnt = 1 -> needed <= page_round (size + UNIT))).
  { intros c Hc Hcs Hc26 E. injection E as <- <-.
    pose proof (page_round_ge (size * c + UNIT)). pose proof (page_round_lt (size * c + UNIT)).
    pose proof (page_round_mod (size * c + UNIT)).
    unfold UNIT, IB, PGSZ in *.
    assert (A1 : 4096 <= page_round (size * c + 16)).
    { pose proof (Z_div_mod_eq_full (page_round (size * c + 16)) 4096). nia. }
    assert (A2 : page_round (size * c + 16) <= 2 ^ 20).
    { destruct Hz16 as [z Ez]. rewrite Ez in Hcs.
      assert (z * c <= 65535) by nia.
      pose proof (page_round_mono (size * c + 16) (2 ^ 20) ltac:(nia)).
      replace (page_round (2 ^ 20)) with (2 ^ 20) in H3 by reflexivity. lia. }
    assert (A3 : size * 1 <= size * c) by nia.
    repeat split; try lia. intros ->. rewrite Z.mul_1_r. lia. }
  destruct Hc1 as (Hc1 & Hc1s & Hc126).
  destruct (negb nosmall && (cnt1 <=? 7)) eqn:E7; [|exact (HN cnt1 Hc1 Hc1s Hc126 Hp)].
  set (rq := page_round (req + IB + UNIT)) in Hp.
  destruct ((rq <? size + UNIT) || ((4 * PGSZ <=? rq) && (usage <? 2 * cnt1))) eqn:E1; [|exact (HN cnt1 Hc1 Hc1s Hc126 Hp)].
  injection Hp as <- <-. subst rq. unfold UNIT, IB, PGSZ in *.
  pose proof (page_round_ge (req + 4 + 16)). pose proof (page_round_lt (req + 4 + 16)).
  pose proof (page_round_mod (req + 4 + 16)). unfold PGSZ in *.
  assert (Hrq : page_round (req + 4 + 16) <= 131072).
  { pose proof (page_round_mono (req + 4 + 16) 131072 ltac:(lia)).
    replace (page_round 131072) with 131072 in H2 by reflexivity. lia. }
  assert (A1 : 4096 <= page_round (req + 4 + 16)).
  { pose proof (Z_div_mod_eq_full (page_round (req + 4 + 16)) 4096). lia. }
  assert (A2 : page_round (req + 4 + 16) <= page_round (size + 16)) by (apply page_round_mono; lia).
  assert (Hn26 : ~ sc <= 26).
  { intros Hle. assert (size <= 3264).
    { subst size. pose proof (class_size_mono sc 26 ltac:(lia) Hle ltac:(lia)).
      replace (class_size 26) with 3264 in H2 by reflexivity. lia. }
    assert (page_round (req + 4 + 16) <= 4096).
    { pose proof (page_round_mono (req + 4 + 16) 4096 ltac:(lia)).
      replace (page_round 4096) with 4096 in H3 by reflexivity. lia. }
    apply orb_prop in E1. destruct E1 as [E1|E1].
    - apply Z.ltb_lt in E1. lia.
    - apply andb_prop in E1 as [E1 _]. apply Z.leb_le in E1. lia. }
  repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nested_facts sc cnt0 :
  0 <= sc < 48 -> 1 <= cnt0 -> (sc <= 26 -> 2 <= cnt0) ->
  class_size sc * cnt0 + UNIT <= PGSZ / 2 ->
  let total := UNIT + cnt0 * class_size sc - IB in
  let j := size_to_class total in
  sc <= 23 /\ 2 <= cnt0 /\ 0 <= total <= 2044 /\ sc < j <= 24 /\ 0 <= j < 48 /\ total + IB <= class_size j /\
  class_size sc < class_size j.
Proof.
  intros Hsc Hc H26 Hsmall total j.
  replace (PGSZ / 2) with 2048 in Hsmall by reflexivity. unfold UNIT in Hsmall.
  pose proof (class_size_bounds sc Hsc) as [S16 Smax].
  assert (H23 : sc <= 23).
  { apply class_le_23; [exact Hsc|]. nia. }
  assert (H2 : 2 <= cnt0) by (apply H26; lia).
  assert (Ht : 0 <= total <= 2044).
  { subst total. unfold UNIT, IB. split; nia. }
  pose proof (size_to_class_range total ltac:(unfold MMAP_THRESHOLD; lia)) as [Hj Hfit]. fold j in Hj, Hfit.
  pose proof (size_to_class_small total Ht) as Hj24. fold j in Hj24.
  assert (Hlt : class_size sc < class_size j).
  { subst total. unfold UNIT, IB in *. nia. }
  assert (sc < j).
  { destruct (Z_lt_dec sc j) as [|Hge]; [assumption|]. exfalso.
    pose proof (class_size_mono j sc ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
  repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition need (sc : Z) : nat := if sc <? 24 then Z.to_nat (2 * (24 - sc) + 2) else 2%nat.

Lemma need_ge2 sc : (2 <= need sc)%nat.
Proof. unfold need. destruct (sc <? 24) eqn:E; [apply Z.ltb_lt in E; lia | lia]. Qed.

Lemma need_nested sc j : sc <= 23 -> sc < j -> (need j + 2 <= need sc)%nat.
Proof.
  intros H23 Hlt. unfold need. destruct (sc <? 24) eqn:E; [|apply Z.ltb_ge in E; lia].
  destruct (j <? 24) eqn:Ej; [apply Z.ltb_lt in Ej | apply Z.ltb_ge in Ej]; lia.
Qed.

Lemma need_le_fuel sc : 0 <= sc -> (need sc <= NEST_FUEL)%nat.
Proof. intros H. unfold need, NEST_FUEL. destruct (sc <? 24); lia. Qed.
