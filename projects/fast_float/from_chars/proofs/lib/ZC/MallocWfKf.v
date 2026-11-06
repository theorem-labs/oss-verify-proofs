(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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

(* [comment removed for export] *)
Definition kf : Type := (list region * brkst * list sptr)%type.
Definition kf_of (s : astate) : kf := (st_regions s, st_brk s, st_areas s).

Definition rg_dflt : region := mkRegion RkMap 0 [] false.

(* [comment removed for export] *)
Definition kstep (x : kf) (q : kreq) (z : Z) : kf :=
  let '(rs, b, ars) := x in
  match q with
  | KBrkGrow _ =>
      if z =? 0 then (rs, BrkDead, ars) else
      match b with
      | BrkNever => (rs ++ [mkRegion RkBrk (2 * PGSZ) [] true], BrkCur (length rs) 2, ars)   (* [comment removed for export] *)
      | BrkCur r p => (lupd rs r (mkRegion RkBrk (rg_len (nth r rs rg_dflt) + PGSZ) [] true), BrkCur r (p + 1),
                       ars ++ [SP r (PGSZ * p)])
      | BrkDead => (rs, b, ars)
      end
  | KGuard => match b with BrkCur r _ => (rs, b, ars ++ [SP r PGSZ]) | _ => (rs, b, ars) end
  | KMmapRW len => if z =? 0 then (rs, b, ars) else (rs ++ [mkRegion RkMap (page_round len) [] true], b, ars)
  | KMmapNone len => if z =? 0 then (rs, b, ars) else (rs ++ [mkRegion RkMetaRes len [] true], b, ars)
  | KMprotect p =>
      if z =? 0 then (rs, b, ars)
      else (lupd rs (prid p) (let rg := nth (prid p) rs rg_dflt in
                              mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [poff p]) (rg_live rg)), b, ars ++ [p])
  | KMunmap r len => (lupd rs r (mkRegion RkMap (rg_len (nth r rs rg_dflt)) [] false), b, ars)
  | _ => (rs, b, ars)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint rk {A : Type} (x : kf) (t : itree astate A) (Q : kf -> A -> Prop) : Prop :=
  match t with
  | IRet a => Q x a
  | IFail _ => True
  | IAsk (KJunk _) _ k => forall z, rk x (k z) Q
  | IAsk q snap k => kf_of snap = x /\ (req_ok snap q -> forall z, rk (kstep x q z) (k z) Q)
  end.

Definition is_junk (q : kreq) : bool := match q with KJunk _ => true | _ => false end.

Lemma rk_ask_inv {A} x q sp k (Q : kf -> A -> Prop) :
  rk x (IAsk q sp k) Q ->
  (is_junk q = true /\ forall z, rk x (k z) Q)
  \/ (is_junk q = false /\ kf_of sp = x /\ (req_ok sp q -> forall z, rk (kstep x q z) (k z) Q)).
Proof. intros H. destruct q; cbn in H; first [right; split; [reflexivity | exact H] | left; split; [reflexivity | exact H]]. Qed.

Lemma rk_ask_intro {A} x q sp k (Q : kf -> A -> Prop) :
  (is_junk q = true /\ forall z, rk x (k z) Q)
  \/ (is_junk q = false /\ kf_of sp = x /\ (req_ok sp q -> forall z, rk (kstep x q z) (k z) Q)) ->
  rk x (IAsk q sp k) Q.
Proof. intros [[J H] | [J H]]; destruct q; cbn in J |- *; first [discriminate | exact H]. Qed.

Lemma rk_conseq {A} x (t : itree astate A) (Q Q' : kf -> A -> Prop) :
  rk x t Q -> (forall x' a, Q x' a -> Q' x' a) -> rk x t Q'.
Proof.
  revert x. induction t as [a | q sp k IH | f]; intros x H HQ; [cbn in *; apply HQ, H | | exact I].
  apply rk_ask_inv in H. apply rk_ask_intro. destruct H as [[J H] | (J & E & H)].
  - left. split; [exact J|]. intros z. apply IH; [apply H | exact HQ].
  - right. split; [exact J|]. split; [exact E|]. intros Rq z. apply IH; [apply H; exact Rq | exact HQ].
Qed.

Lemma rk_ibind {A B} x (t : itree astate A) (K : A -> itree astate B) Q :
  rk x t (fun x' a => rk x' (K a) Q) -> rk x (ibind t K) Q.
Proof.
  revert x. induction t as [a | q sp k IH | f]; intros x H; [cbn in *; exact H | | exact I].
  cbn [ibind]. apply rk_ask_inv in H. apply rk_ask_intro. destruct H as [[J H] | (J & E & H)].
  - left. split; [exact J|]. intros z. apply IH. apply H.
  - right. split; [exact J|]. split; [exact E|]. intros Rq z. apply IH. apply H. exact Rq.
Qed.

Section MonadRules.
  Context {A B : Type}.
  Implicit Types (s : astate) (x : kf).

  #[using="Type"] Lemma rk_ret x (a : A) s Q : Q x (a, s) -> rk x (ret a s) Q.
  Proof. intros H. exact H. Qed.
  #[using="Type"] Lemma rk_bind x (m : M B) (k : B -> M A) s Q :
    rk x (m s) (fun x' r => rk x' (k (fst r) (snd r)) Q) -> rk x (bind m k s) Q.
  Proof. intros H. unfold bind. apply rk_ibind. eapply rk_conseq; [exact H|]. intros x' [b s']. cbn. intros X; exact X. Qed.
  #[using="Type"] Lemma rk_fail x f s Q : rk x (@fail A f s) Q.
  Proof. exact I. Qed.
  #[using="Type"] Lemma rk_get x s (Q : kf -> astate * astate -> Prop) : Q x (s, s) -> rk x (get s) Q.
  Proof. intros H; exact H. Qed.
  #[using="Type"] Lemma rk_put x s s' (Q : kf -> unit * astate -> Prop) : Q x (tt, s') -> rk x (put s' s) Q.
  Proof. intros H; exact H. Qed.
  #[using="Type"] Lemma rk_modify x f s (Q : kf -> unit * astate -> Prop) : Q x (tt, f s) -> rk x (modify f s) Q.
  Proof. intros H; exact H. Qed.
  #[using="Type"] Lemma rk_ask x q s (Q : kf -> bool * astate -> Prop) :
    is_junk q = false -> kf_of s = x -> (req_ok s q -> forall z, Q (kstep x q z) (negb (z =? 0), s)) -> rk x (ask q s) Q.
  Proof.
    intros J E H. unfold ask. apply rk_ask_intro. right. split; [exact J|]. split; [exact E|]. intros Rq z. cbn. apply H. exact Rq.
  Qed.
  #[using="Type"] Lemma rk_askz_junk x c s (Q : kf -> Z * astate -> Prop) :
    (forall z, Q x (z, s)) -> rk x (askz (KJunk c) s) Q.
  Proof. intros H z. cbn. apply H. Qed.
  #[using="Type"] Lemma rk_massert x (b : bool) i s (Q : kf -> unit * astate -> Prop) :
    (b = true -> Q x (tt, s)) -> rk x (massert b i s) Q.
  Proof. intros H. unfold massert. destruct b; [apply H; reflexivity | exact I]. Qed.
  #[using="Type"] Lemma rk_mcheck x (b : bool) i s (Q : kf -> unit * astate -> Prop) :
    (b = true -> Q x (tt, s)) -> rk x (mcheck b i s) Q.
  Proof. intros H. unfold mcheck. destruct b; [apply H; reflexivity | exact I]. Qed.
End MonadRules.

Lemma rk_getm x p s (Q : kf -> ameta * astate -> Prop) :
  (forall am, MT s p = Some (MUsed am) -> Q x (am, s)) -> rk x (getm p s) Q.
Proof.
  intros H. unfold getm. apply rk_bind. apply rk_get. cbn [fst snd]. unfold MT in H.
  destruct (mlookup (st_metas s) p) as [[| |am]|]; try exact I. apply H. reflexivity.
Qed.

Lemma rk_get_links x p s (Q : kf -> (option sptr * option sptr) * astate -> Prop) :
  (forall l, Q x (l, s)) -> rk x (get_links p s) Q.
Proof. intros H. unfold get_links. apply rk_bind. apply rk_get. cbn [fst snd]. destruct (mlookup (st_metas s) p); [apply H | exact I]. Qed.

Lemma rk_set_links x p pr nx s (Q : kf -> unit * astate -> Prop) :
  (forall ms, Q x (tt, set_metas ms s)) -> rk x (set_links p pr nx s) Q.
Proof. intros H. unfold set_links. apply rk_bind. apply rk_get. cbn [fst snd]. destruct (mlookup (st_metas s) p); [apply H | exact I]. Qed.

(* [comment removed for export] *)
Definition kq {A} (x : kf) (r : A * astate) : Prop := kf_of (snd r) = x.
Definition kt {A} (x : kf) (s : astate) (x' : kf) (r : A * astate) : Prop := x' = x /\ kf_of (snd r) = kf_of s.

Create HintDb rk.

Ltac rq := cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas
               set_init_done set_mmap_counter set_free_meta_head set_avail_meta set_avail_meta_count set_avail_meta_area_count set_meta_alloc_shift set_area_head set_area_tail set_avail_meta_areas set_active set_usage set_unmap_seq set_bounces set_seq set_brk set_metas set_regions set_areas fst snd prid poff] in *.

(* [comment removed for export] *)
Ltac kfsolve :=
  unfold kq, kt, kf_of in *; rq;
  solve [ reflexivity | assumption | congruence | split; congruence ].

(* [comment removed for export] *)
Ltac kre E :=
  lazymatch type of E with
  | st_regions _ = _ => try rewrite <- E in *
  | st_brk _ = _ => try rewrite <- E in *
  | st_areas _ = _ => try rewrite <- E in *
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac kpairs :=
  repeat match goal with
         | E : (_, _) = (_, _) |- _ =>
             injection E; clear E;
             repeat lazymatch goal with
                    | |- _ = _ -> _ => let E1 := fresh "KE" in intros E1; try subst; try kre E1
                    end
         end.
Ltac kpost HQ :=
  unfold kq, kt, kf_of in HQ; cbn [fst snd] in HQ;
  repeat match type of HQ with
         | _ /\ _ => let E := fresh "KE" in destruct HQ as [E HQ]; cbn [fst snd] in E; try subst; try kre E
         end;
  try subst; try kre HQ; kpairs.

(* [comment removed for export] *)
Ltac kdisc H :=
  cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas
       set_init_done set_mmap_counter set_free_meta_head set_avail_meta set_avail_meta_count set_avail_meta_area_count set_meta_alloc_shift set_area_head set_area_tail set_avail_meta_areas set_active set_usage set_unmap_seq set_bounces set_seq set_brk set_metas set_regions set_areas fst snd negb andb orb Z.eqb Z.leb Z.ltb Pos.eqb] in H; discriminate H.

Ltac rkstep :=
  lazymatch goal with
  | |- rk _ (bind _ _ _) _ => apply rk_bind
  | |- rk _ (ret _ _) _ => apply rk_ret
  | |- rk _ (get _) _ => apply rk_get
  | |- rk _ (put _ _) _ => apply rk_put
  | |- rk _ (modify _ _) _ => apply rk_modify
  | |- rk _ (setm _ _ _) _ => unfold setm at 1; apply rk_modify
  | |- rk _ (setslot _ _ _) _ => unfold setslot at 1; apply rk_modify
  | |- rk _ (set_usage_of _ _ _) _ => unfold set_usage_of at 1; apply rk_modify
  | |- rk _ (set_head _ _ _) _ => unfold set_head at 1
  | |- rk _ (get_head _ _) _ => unfold get_head at 1
  | |- rk _ (getm _ _) _ => apply rk_getm; intros ? ?
  | |- rk _ (get_links _ _) _ => apply rk_get_links; intros ?
  | |- rk _ (set_links _ _ _ _) _ => apply rk_set_links; intros ?
  | |- rk _ (set_prev _ _ _) _ => unfold set_prev at 1
  | |- rk _ (set_next _ _ _) _ => unfold set_next at 1
  | |- rk _ (massert _ _ _) _ => apply rk_massert; intros _
  | |- rk _ (mcheck _ _ _) _ => apply rk_mcheck; intros ?
  | |- rk _ (ask _ _) _ => let z := fresh "z" in apply rk_ask; [reflexivity | kfsolve | intros ?RQ z; cbn [kstep]; destruct (z =? 0); cbn [negb]]
  | |- rk _ (askz (KJunk _) _) _ => apply rk_askz_junk; intros ?
  | |- rk _ (fail _ _) _ => apply rk_fail
  | |- rk _ (IFail _) _ => exact I
  | |- rk _ (IRet _) _ => cbn [rk]
  | |- rk _ (match ?y with _ => _ end _) _ => let H := fresh "Hc" in destruct y eqn:H; try (exfalso; kdisc H)
  | |- rk _ (match ?y with _ => _ end) _ => let H := fresh "Hc" in destruct y eqn:H; try (exfalso; kdisc H)
  | |- rk _ _ (fun _ _ => rk _ _ _) =>
      let HQ := fresh "HQ" in
      eapply rk_conseq; [solve [eauto 4 with rk nocore] | intros [[? ?] ?] [? ?] HQ; kpost HQ]
  | |- rk _ _ _ =>
      first [ solve [eauto 4 with rk nocore]
            | let HQ := fresh "HQ" in
              eapply rk_conseq; [solve [eauto 4 with rk nocore] | intros [[? ?] ?] [? ?] HQ; kpost HQ; kfsolve] ]
  | |- kq _ _ => kfsolve
  | |- kt _ _ _ _ => kfsolve
  | |- True => exact I
  | |- forall _, _ => intros ?
  end.
Ltac rkauto := repeat (cbn beta iota zeta delta [fst snd negb andb orb]; rkstep).
(* [comment removed for export] *)
Ltac kfE E := unfold kf_of in E; injection E as ?ER ?EB ?EA; try subst.
Global Hint Extern 0 (kf_of _ = _) => kfsolve : rk.
Global Hint Extern 0 (st_regions _ = _) => kfsolve : rk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Fns.
  Implicit Types (s : astate) (rs : list region) (b : brkst) (ars : list sptr) (x : kf).

  (* [comment removed for export] *)
  #[using="Type"] Lemma rk_queue x h m s : rk x (queue h m s) (kt x s).
  Proof. unfold queue. rkauto. all: destruct h; rkauto. Qed.
  Hint Resolve rk_queue : rk.

  #[using="Type"] Lemma rk_dequeue x h m s : rk x (dequeue h m s) (kt x s).
  Proof. unfold dequeue. rkauto; destruct h; rkauto. Qed.
  Hint Resolve rk_dequeue : rk.

  #[using="Type"] Lemma rk_dequeue_head x h s : rk x (dequeue_head h s) (kt x s).
  Proof. unfold dequeue_head. destruct h; rkauto. Qed.
  Hint Resolve rk_dequeue_head : rk.

  #[using="Type"] Lemma rk_free_meta x m s : rk x (free_meta m s) (kt x s).
  Proof. unfold free_meta. rkauto. Qed.
  Hint Resolve rk_free_meta : rk.

  #[using="Type"] Lemma rk_set_usage_of x sc v s : rk x (set_usage_of sc v s) (kt x s).
  Proof. unfold set_usage_of. rkauto. Qed.
  Hint Resolve rk_set_usage_of : rk.

  #[using="Type"] Lemma rk_step_seq x s : rk x (step_seq s) (kt x s).
  Proof. unfold step_seq. rkauto. destruct (st_seq s =? 255); kfsolve. Qed.
  Hint Resolve rk_step_seq : rk.

  #[using="Type"] Lemma rk_record_seq x sc s : rk x (record_seq sc s) (kt x s).
  Proof. unfold record_seq. destruct (bounce_idx sc); rkauto. Qed.
  Hint Resolve rk_record_seq : rk.

  #[using="Type"] Lemma rk_account_bounce x sc s : rk x (account_bounce sc s) (kt x s).
  Proof. unfold account_bounce. destruct (bounce_idx sc); rkauto. destruct (negb _ && _); kfsolve. Qed.
  Hint Resolve rk_account_bounce : rk.

  #[using="Type"] Lemma rk_decay_bounces x sc s : rk x (decay_bounces sc s) (kt x s).
  Proof. unfold decay_bounces. destruct (bounce_idx sc); rkauto. destruct (_ =? 0); kfsolve. Qed.
  Hint Resolve rk_decay_bounces : rk.

  #[using="Type"] Lemma rk_activate_group x m s : rk x (activate_group m s) (kt x s).
  Proof. unfold activate_group. rkauto. Qed.
  Hint Resolve rk_activate_group : rk.

  #[using="Type"] Lemma rk_try_avail x sc s : rk x (try_avail sc s) (kt x s).
  Proof. unfold try_avail. rkauto. Qed.
  Hint Resolve rk_try_avail : rk.

  #[using="Type"] Lemma rk_enframe x g idx n ctr k s : rk x (enframe g idx n ctr k s) (kt x s).
  Proof. unfold enframe. rkauto. Qed.
  Hint Resolve rk_enframe : rk.

  #[using="Type"] Lemma rk_install_group x m sc cnt aidx maplen mem sl s :
    rk x (install_group m sc cnt aidx maplen mem sl s) (kt x s).
  Proof. unfold install_group. rkauto. Qed.
  Hint Resolve rk_install_group : rk.

  #[using="Type"] Lemma rk_forget_frame x g i s : rk x (forget_frame g i s) (kt x s).
  Proof. unfold forget_frame. rkauto. Qed.
  Hint Resolve rk_forget_frame : rk.

  #[using="Type"] Lemma rk_release_slot x g i s : rk x (release_slot g i s) (kt x s).
  Proof. unfold release_slot. rkauto. Qed.
  Hint Resolve rk_release_slot : rk.

  #[using="Type"] Lemma rk_find_frame x p s : rk x (find_frame p s) (kt x s).
  Proof. unfold find_frame. rkauto. Qed.
  Hint Resolve rk_find_frame : rk.

  #[using="Type"] Lemma rk_nontrivial_free fuel x g i s : rk x (nontrivial_free fuel g i s) (kt x s).
  Proof.
    revert x g i s. induction fuel as [|f IH]; intros x g i s; [cbn; exact I|].
    cbn fix beta iota delta [nontrivial_free]. rkauto.
  Qed.
  Hint Resolve rk_nontrivial_free : rk.

  (* [comment removed for export] *)
  #[using="Type"] Lemma rk_new_region rs b ars k len s :
    st_regions s = rs ->
    rk (rs ++ [mkRegion k len [] true], b, ars) (new_region k len s)
       (fun x' r => x' = (rs ++ [mkRegion k len [] true], b, ars) /\ st_regions (snd r) = rs ++ [mkRegion k len [] true]
                    /\ st_brk (snd r) = st_brk s /\ st_areas (snd r) = st_areas s /\ fst r = length rs).
  Proof. intros E. unfold new_region. rkauto. subst rs. repeat split; reflexivity. Qed.

  #[using="Type"] Lemma rk_upd_region rs b ars r f y s :
    st_regions s = rs -> y = f (nth r rs rg_dflt) ->
    rk (lupd rs r y, b, ars) (upd_region r f s)
       (fun x' r' => x' = (lupd rs r y, b, ars) /\ st_regions (snd r') = lupd rs r y /\ st_brk (snd r') = st_brk s
                     /\ st_areas (snd r') = st_areas s).
  Proof. intros E ->. unfold upd_region. rkauto. subst rs. repeat split; reflexivity. Qed.
  Hint Resolve rk_new_region rk_upd_region : rk.
  Hint Extern 0 (_ = _ :> region) => reflexivity : rk.

  (* [comment removed for export] *)
  #[using="Type"] Lemma rk_alloc_meta rs b ars s : kf_of s = (rs, b, ars) -> rk (rs, b, ars) (alloc_meta s) kq.
  Proof. intros E. kfE E. unfold alloc_meta, area_from_brk, area_from_mmap, open_area. rkauto. Qed.
  Hint Resolve rk_alloc_meta : rk.

  #[using="Type"] Lemma rk_alloc_mutual fuel :
    (forall rs b ars sc req s, kf_of s = (rs, b, ars) -> rk (rs, b, ars) (alloc_slot fuel sc req s) kq) /\
    (forall rs b ars sc req s, kf_of s = (rs, b, ars) -> rk (rs, b, ars) (alloc_group fuel sc req s) kq).
  Proof.
    induction fuel as [|f [IHs IHg]]; [split; intros; cbn; exact I|]. split.
    - intros rs b ars sc req s E. kfE E. cbn fix beta iota delta [alloc_slot]. rkauto.
    - intros rs b ars sc req s E. kfE E. cbn fix beta iota delta [alloc_group]. rkauto.
  Qed.
  #[using="Type"] Lemma rk_alloc_slot fuel rs b ars sc req s : kf_of s = (rs, b, ars) -> rk (rs, b, ars) (alloc_slot fuel sc req s) kq.
  Proof. apply (proj1 (rk_alloc_mutual fuel)). Qed.
  Hint Resolve rk_alloc_slot : rk.

  #[using="Type"] Lemma rk_malloc rs b ars n s : kf_of s = (rs, b, ars) -> rk (rs, b, ars) (malloc n s) kq.
  Proof. intros E. kfE E. unfold malloc. rkauto. Qed.

  #[using="Type"] Lemma rk_free rs b ars p s : kf_of s = (rs, b, ars) -> rk (rs, b, ars) (free p s) kq.
  Proof. intros E. kfE E. unfold free. rkauto. Qed.
End Fns.

(* [comment removed for export] *)
Theorem malloc_kf : forall s n, rk (kf_of s) (malloc n s) kq.
Proof. intros s n. apply (rk_malloc (st_regions s) (st_brk s) (st_areas s)). reflexivity. Qed.

Theorem free_kf : forall s p, rk (kf_of s) (free p s) kq.
Proof. intros s p. apply (rk_free (st_regions s) (st_brk s) (st_areas s)). reflexivity. Qed.
