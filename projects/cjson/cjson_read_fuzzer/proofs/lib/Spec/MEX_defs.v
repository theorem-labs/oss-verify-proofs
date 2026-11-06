(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Bool.
From Stdlib Require Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require STree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Malloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MallocCtrl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require KInv.
Module MI_Tree.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.KInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Definition rejects {R} (t : M R) : Prop :=
  match t with SVis (EUndef _) _ => True | _ => False end.

Definition is_peek (e : ev) : bool := match e with EPeek _ _ _ => true | _ => false end.
Definition is_undef (e : ev) : bool := match e with EUndef _ => true | _ => false end.

Lemma rejects_inv {R} (t : M R) : rejects t -> exists w k, t = SVis (EUndef w) k.
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e; cbn; try tauto. intros _. eauto. Qed.

Lemma rejects_bind {R S} (t : M R) (f : R -> M S) : rejects t -> rejects (sbind t f).
Proof. destruct t as [|e k]; cbn; [tauto|]. destruct e; cbn; tauto. Qed.

Fixpoint ftree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (EPeek _ _ _) k => forall v, 0 <= v < 256 -> ftree L (k v) Post
  | SVis (EUndef _) _ => False
  | SVis e k => event_pre L e /\ forall a, if answer_ok L e a then ftree (event_post L e a) (k a) Post else rejects (k a)
  end.

(* [comment removed for export] *)
Fixpoint ptree {R} (L : mled) (t : M R) (Post : mled -> R -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post L r
  | SVis (EPeek _ _ _) k => False
  | SVis (EUndef _) _ => False
  | SVis e k => event_pre L e /\ forall a, if answer_ok L e a then ptree (event_post L e a) (k a) Post else rejects (k a)
  end.

Ltac case_ans :=
  match goal with
  | |- context [if answer_ok ?L ?e ?a then _ else _] => destruct (answer_ok L e a) eqn:?
  | H : context [if answer_ok ?L ?e ?a then _ else _] |- _ => destruct (answer_ok L e a) eqn:?
  end.

Lemma ftree_ret {R} L (r : R) Post : Post L r -> ftree L (SRet r) Post.
Proof. intros H. exact H. Qed.

Lemma ftree_vis {R} L e (k : Z -> M R) Post :
  is_peek e = false -> is_undef e = false ->
  event_pre L e ->
  (forall a, answer_ok L e a = true -> ftree (event_post L e a) (k a) Post) ->
  (forall a, answer_ok L e a = false -> rejects (k a)) ->
  ftree L (SVis e k) Post.
Proof.
  intros Hp Hu He Hk Hr. destruct e; cbn in Hp, Hu; try discriminate; cbn [ftree]; split; auto;
  intros a; case_ans; auto.
Qed.

Lemma ftree_peek {R} L p c h (k : Z -> M R) Post :
  (forall v, 0 <= v < 256 -> ftree L (k v) Post) -> ftree L (SVis (EPeek p c h) k) Post.
Proof. intros H. exact H. Qed.

Lemma ftree_mono {R} (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall t L, ftree L t Post -> ftree L t Post'.
Proof.
  intros HP. induction t as [r|e k IH]; intros L H; cbn [ftree ptree follow sbind] in *; [auto|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
    case_ans; [apply IH; exact Hk| exact Hk]).
  - intros v Hv. apply IH. apply H. exact Hv.
  - exact H.
Qed.

Lemma ftree_bind {R S} (t : M R) (f : R -> M S) Post Q L :
  ftree L t Post -> (forall L' r, Post L' r -> ftree L' (f r) Q) -> ftree L (sbind t f) Q.
Proof.
  revert L. induction t as [r|e k IH]; intros L H Hf; cbn [ftree ptree follow sbind] in *.
  - apply Hf. exact H.
  - destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
      case_ans; [apply IH; [exact Hk| exact Hf]|];
      apply rejects_bind; exact Hk).
    + intros v Hv. apply IH; [apply H; exact Hv| exact Hf].
    + destruct H.
Qed.

Lemma rejects_bad_answer {R} (b : M R) : rejects (bad_answer b).
Proof. exact I. Qed.

Lemma ftree_guard {R} L tag (c : bool) (k bail : M R) Post :
  c = true -> ftree L k Post -> ftree L (guard tag c k bail) Post.
Proof. intros -> H. exact H. Qed.

Lemma ftree_guard_inv {R} L tag (c : bool) (k bail : M R) Post :
  ftree L (guard tag c k bail) Post -> c = true /\ ftree L k Post.
Proof. unfold guard. destruct c; cbn; [auto| intros H; destruct H]. Qed.

(* [comment removed for export] *)
Lemma ptree_mono {R} (Post Post' : mled -> R -> Prop) :
  (forall L r, Post L r -> Post' L r) -> forall t L, ptree L t Post -> ptree L t Post'.
Proof.
  intros HP. induction t as [r|e k IH]; intros L H; cbn [ftree ptree follow sbind] in *; [auto|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
    case_ans; [apply IH; exact Hk| exact Hk]); exact H.
Qed.

Lemma ptree_bind {R S} (t : M R) (f : R -> M S) Post Q L :
  ptree L t Post -> (forall L' r, Post L' r -> ptree L' (f r) Q) -> ptree L (sbind t f) Q.
Proof.
  revert L. induction t as [r|e k IH]; intros L H Hf; cbn [ftree ptree follow sbind] in *.
  - apply Hf. exact H.
  - destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
      case_ans; [apply IH; [exact Hk| exact Hf]|];
      apply rejects_bind; exact Hk); exact H.
Qed.

(* [comment removed for export] *)
Lemma ptree_ctree_ok {R} : forall (t : M R) L Post, ptree L t Post -> ctree_ok L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post H; cbn [ftree ptree follow sbind] in *; [exact H|].
  destruct e; try (destruct H as [He Hk]; split; [exact He|]; intros z Hz; specialize (Hk z); rewrite Hz in Hk; apply IH; exact Hk);
    destruct H.
Qed.

(* [comment removed for export] *)
Lemma ptree_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall L (P1 : mled -> R1 -> Prop) (P2 : mled -> R2 -> Prop),
  (forall L' r1 r2, RR r1 r2 -> P1 L' r1 -> P2 L' r2) ->
  ptree L t1 P1 -> ptree L t2 P2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L P1 P2 HP H; cbn [ftree ptree follow sbind] in *.
  - eapply HP; eauto.
  - destruct e; try exact H. all: destruct H as [He H]; split; [exact He|]; intros a; specialize (H a);
      case_ans; [eapply IH; eauto|].
    all: specialize (Hk a); destruct (rejects_inv _ H) as (w & k' & E); rewrite E in Hk; inversion Hk; subst; exact I.
Qed.

(* [comment removed for export] *)
Section PRUN.
Context {O : Type} (pans : O -> aptr -> Z -> Z -> Z) (pupd : O -> ev -> Z -> O).
Hypothesis Hpans : forall o p c h, 0 <= pans o p c h < 256.

Lemma ftree_prun {R} : forall (t : M R) L Post o,
  ftree L t Post -> ptree L (prun pans pupd o t) (fun L' x => Post L' (snd x)).
Proof.
  induction t as [r|e k IH]; intros L Post o H; cbn [ftree ptree follow sbind] in *.
  - exact H.
  - unfold prun. destruct e; cbn [eruns psel];
      try (destruct H as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
           case_ans; [apply IH; exact Hk|];
           destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E; exact I).
    + apply IH. apply H. apply Hpans.
    + destruct H.
Qed.
End PRUN.

(* [comment removed for export] *)
Lemma ptree_follow {R} : forall (t : M R) L Post ans r,
  ptree L t Post -> follow t ans = Some r -> exists L', cpath L t L' r /\ Post L' r.
Proof.
  induction t as [r0|e k IH]; intros L Post ans r H Hf; cbn [ftree ptree follow sbind] in *.
  - inversion Hf; subst. exists L. split; [constructor| exact H].
  - destruct e; try (destruct H; fail); try contradiction.
    all: destruct H as [He Hk]; destruct ans as [|a ans']; [discriminate|];
      specialize (Hk a); case_ans;
      [ destruct (IH a _ _ _ _ Hk Hf) as (L' & Hp & HP); exists L'; split; [econstructor; eauto| exact HP]
      | destruct (rejects_inv _ Hk) as (w & k' & E); rewrite E in Hf; cbn in Hf; discriminate ].
Qed.

Lemma ptree_cpath {R} : forall (t : M R) L Post L' r,
  ptree L t Post -> cpath L t L' r -> Post L' r.
Proof.
  induction t as [r0|e k IH]; intros L Post L' r H Hp; cbn [ftree ptree follow sbind] in *.
  - inversion Hp; subst. exact H.
  - inversion Hp; subst. destruct e; try contradiction.
    all: destruct H as [He Hk];
      match goal with Ha : answer_ok _ _ ?z = true |- _ => specialize (Hk z); rewrite Ha in Hk; eapply IH; eauto end.
Qed.

(* [comment removed for export] *)
Lemma strel_cpath {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall L L' r2, cpath L t2 L' r2 -> exists r1, cpath L t1 L' r1 /\ RR r1 r2.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros L L' r Hp.
  - inversion Hp; subst. exists r1. split; [constructor| exact Hr].
  - inversion Hp; subst.
    match goal with Hc : cpath _ (k2 ?z) _ _ |- _ =>
      destruct (IH z _ _ _ Hc) as (r1 & Hp1 & Hr1); exists r1; split; [econstructor; eauto| exact Hr1] end.
Qed.

Lemma strel_follow {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : M R1) (t2 : M R2) :
  strel RR t1 t2 -> forall ans,
  match follow t1 ans, follow t2 ans with
  | Some r1, Some r2 => RR r1 r2
  | None, None => True
  | _, _ => False
  end.
Proof.
  induction 1 as [r1 r2 Hr|e k1 k2 Hk IH]; intros ans; cbn.
  - exact Hr.
  - destruct e; destruct ans; cbn; auto; apply IH.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac case_ans :=
  match goal with
  | |- context [if answer_ok ?L ?e ?a then _ else _] => destruct (answer_ok L e a) eqn:?
  | H : context [if answer_ok ?L ?e ?a then _ else _] |- _ => destruct (answer_ok L e a) eqn:?
  end.
End MI_Tree.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require MI_Kit.
Module MEX_lib.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import stdpp.gmap.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.STree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Malloc OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MallocCtrl MI_Tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.MI_Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tnode {R} (t : M R) : option ev :=
  match t with SVis e _ => Some e | SRet _ => None end.
Definition tsub {R} (t : M R) (a : Z) : M R :=
  match t with SVis _ k => k a | SRet _ => t end.
Definition tleaf {R} (t : M R) : option R :=
  match t with SRet r => Some r | SVis _ _ => None end.
Fixpoint tsubs {R} (t : M R) (ans : list Z) : M R :=
  match ans with [] => t | a :: ans' => tsubs (tsub t a) ans' end.

Lemma tnode_vis {R} e (k : Z -> M R) : tnode (SVis e k) = Some e. Proof. reflexivity. Qed.
Lemma tsub_vis {R} e (k : Z -> M R) a : tsub (SVis e k) a = k a. Proof. reflexivity. Qed.
Lemma tleaf_ret {R} (r : R) : tleaf (ret r) = Some r. Proof. reflexivity. Qed.
Lemma tsubs_app {R} (t : M R) l1 l2 : tsubs t (l1 ++ l2) = tsubs (tsubs t l1) l2.
Proof. revert t; induction l1; intros; cbn; auto. Qed.

Lemma tnode_Some {R} (t : M R) e : tnode t = Some e -> exists k, t = SVis e k /\ forall a, tsub t a = k a.
Proof. destruct t as [r|e' k]; cbn; [discriminate|]. intros H; inversion H; subst. exists k. auto. Qed.
Lemma tleaf_Some {R} (t : M R) r : tleaf t = Some r -> t = SRet r.
Proof. destruct t; cbn; [intros H; inversion H; reflexivity| discriminate]. Qed.

(* [comment removed for export] *)
Lemma tnode_sbind {R S} (t : M R) (f : R -> M S) e : tnode t = Some e -> tnode (sbind t f) = Some e.
Proof. destruct t; cbn; [discriminate| auto]. Qed.
Lemma tsub_sbind {R S} (t : M R) (f : R -> M S) a : tnode t <> None -> tsub (sbind t f) a = sbind (tsub t a) f.
Proof. destruct t; cbn; [congruence| auto]. Qed.
Lemma sbind_ret {R S} (r : R) (f : R -> M S) : sbind (ret r) f = f r.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rejects_bad {R} (b : M R) : rejects (bad_answer b).
Proof. exact I. Qed.
Lemma rejects_sbind {R S} (t : M R) (f : R -> M S) : rejects t -> rejects (sbind t f).
Proof. apply rejects_bind. Qed.

(* [comment removed for export] *)
Lemma follow_vis_cons {R} (t : M R) e a ans :
  tnode t = Some e -> match e with EUndef _ => False | _ => True end ->
  follow t (a :: ans) = follow (tsub t a) ans.
Proof. destruct t as [r|e' k]; cbn; [discriminate|]. intros H; inversion H; subst. destruct e; cbn; intros F; try reflexivity; destruct F. Qed.
Lemma follow_vis_nil {R} (t : M R) e : tnode t = Some e -> follow t [] = None.
Proof. destruct t as [r|e' k]; cbn; [discriminate|]. intros _. destruct e'; reflexivity. Qed.
Lemma follow_rejects {R} (t : M R) ans : rejects t -> follow t ans = None.
Proof. destruct t as [r|e k]; cbn; [intros F; destruct F|]. destruct e; cbn; intros F; try destruct F. destruct ans; reflexivity. Qed.
Lemma follow_leaf {R} (t : M R) r ans : tleaf t = Some r -> follow t ans = Some r.
Proof. destruct t; cbn; [intros H; inversion H; subst; destruct ans; reflexivity| discriminate]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_small_ones v k : 0 <= v < 2 ^ k -> 0 <= k -> Z.land v (2 ^ k - 1) = v.
Proof.
  intros Hv Hk. replace (2 ^ k - 1) with (Z.pred (2 ^ k)) by lia. rewrite <- Z.ones_equiv, Z.land_ones by lia.
  apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition q_post (h : lhead) (m : aptr) (st : mstate) : mstate :=
  match get_head st h with
  | Some head =>
      let hprev := m_prev (get_meta_rec st head) in
      let st1 := upd_meta m (fun r => m_set_prev hprev (m_set_next (Some head) r)) st in
      let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some m)) st1 | None => st1 end in
      upd_meta head (m_set_prev (Some m)) st2
  | None =>
      set_head h (Some m) (upd_meta m (fun r => m_set_prev (Some m) (m_set_next (Some m) r)) st)
  end.

Lemma queue_eq {R} h m st (k : mstate -> M R) bail :
  m_next (get_meta_rec st m) = None -> m_prev (get_meta_rec st m) = None ->
  queue h m st k bail = k (q_post h m st).
Proof.
  intros HN HP. unfold queue, q_post. rewrite HN, HP. cbn [optr_eqb guard].
  destruct (get_head st h); reflexivity.
Qed.

(* [comment removed for export] *)
Definition fm_post (m : aptr) (st : mstate) : mstate := q_post LFree m (put_meta m meta0 st).

Lemma free_meta_eq {R} m st (k : mstate -> M R) bail : free_meta m st k bail = k (fm_post m st).
Proof. unfold free_meta, fm_post. apply queue_eq; rewrite get_meta_rec_put_same; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition am_init (st : mstate) : mstate :=
  if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.

(* [comment removed for export] *)
Definition am_ok (st : mstate) : Prop :=
  c_free_meta_head (ctx st) <> None \/ (c_avail_meta_count (ctx st) <> 0 /\ c_avail_meta (ctx st) <> None).

Definition am_post (st : mstate) : mstate * aptr :=
  let st := am_init st in
  match c_free_meta_head (ctx st) with
  | Some m => (dequeue LFree m st, m)
  | None =>
      match c_avail_meta (ctx st) with
      | Some m =>
          (upd_meta m (fun r => m_set_prev None (m_set_next None r))
             (upd_ctx (fun c => set_avail_meta (Some (aadd m META_SIZE)) (set_avail_meta_count (c_avail_meta_count c - 1) c)) st), m)
      | None => (st, (0%N, 0))
      end
  end.

Lemma am_init_fields st :
  c_free_meta_head (ctx (am_init st)) = c_free_meta_head (ctx st)
  /\ c_avail_meta_count (ctx (am_init st)) = c_avail_meta_count (ctx st)
  /\ c_avail_meta (ctx (am_init st)) = c_avail_meta (ctx st).
Proof. unfold am_init. destruct (c_init_done (ctx st) =? 0); repeat split; reflexivity. Qed.

Lemma alloc_meta_silent {R} st (k : mstate -> optr -> M R) bail :
  am_ok st -> alloc_meta st k bail = k (fst (am_post st)) (Some (snd (am_post st))).
Proof.
  intros AM. unfold alloc_meta, am_post. change (if c_init_done (ctx st) =? 0 then _ else st) with (am_init st).
  destruct (am_init_fields st) as (F1 & F2 & F3).
  destruct (c_free_meta_head (ctx (am_init st))) as [m|] eqn:FH; [reflexivity|].
  destruct AM as [AM|[AC AV]]; [congruence|].
  rewrite F2. replace (c_avail_meta_count (ctx st) =? 0) with false by (symmetry; apply Z.eqb_neq; exact AC).
  cbn [negb]. unfold am_take. rewrite F3. destruct (c_avail_meta (ctx st)) as [m|]; [reflexivity| congruence].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition big_tail (lay : layout_hook) (st3 : mstate) (g : aptr) (rid : N) (needed : Z) : mstate :=
  let st4 := upd_meta g (fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
               (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
  let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr lay st4 (rid, 0)) in
  let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
  upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6.

Section BIG.
Variables (lay : layout_hook) (st : mstate) (n : Z).
Hypothesis Hn : MMAP_THRESHOLD <= n.
Hypothesis Hov : size_overflows n = false.
Let needed := n + IB + UNIT.

Lemma malloc_core_big_node :
  tnode (malloc_core lay st n) = Some (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)).
Proof. unfold malloc_core. rewrite Hov. rewrite (proj2 (Z.leb_le _ _) Hn). reflexivity. Qed.

Lemma malloc_core_big_bad r :
  mmap_answer_ok (live_ranges st) needed r = false -> rejects (tsub (malloc_core lay st n) r).
Proof. intros Hr. unfold malloc_core. rewrite Hov, (proj2 (Z.leb_le _ _) Hn). cbn [tsub]. fold needed. rewrite Hr. exact I. Qed.

Lemma malloc_core_big_err r :
  mmap_answer_ok (live_ranges st) needed r = true -> is_err r = true ->
  tsub (malloc_core lay st n) r = ret (st, None).
Proof. intros Hr He. unfold malloc_core. rewrite Hov, (proj2 (Z.leb_le _ _) Hn). cbn [tsub]. fold needed. rewrite Hr, He. reflexivity. Qed.

Lemma malloc_core_big_ok r :
  mmap_answer_ok (live_ranges st) needed r = true -> is_err r = false ->
  am_ok (step_seq (fst (new_region RKGroup r needed st))) ->
  let st2 := step_seq (fst (new_region RKGroup r needed st)) in
  let '(st3, g) := am_post st2 in
  tsub (malloc_core lay st n) r = ret (big_tail lay st3 g (s_next_rid st) needed, Some (g, 0)).
Proof.
  intros Hr He AM. unfold malloc_core. rewrite Hov, (proj2 (Z.leb_le _ _) Hn). cbn [tsub]. fold needed. rewrite Hr, He. cbn [negb].
  unfold new_region. cbn [fst snd]. rewrite (alloc_meta_silent _ _ _ AM).
  destruct (am_post _) as [st3 g]. reflexivity.
Qed.
End BIG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dequeue_self h m st :
  m_next (get_meta_rec st m) = Some m ->
  dequeue h m st = upd_meta m (fun r => m_set_prev None (m_set_next None r)) (set_head h None st).
Proof. intros H. unfold dequeue. rewrite H, optr_eqb_refl. reflexivity. Qed.

Lemma okay_to_free_blk st g rid sc ml l :
  get_meta_rec st g = mkMeta l l (Some (rid,0)) 0 0 0 1 sc ml -> 0 < ml ->
  (sc = 63 \/ (sc = 44 /\ ml = 17)) ->
  okay_to_free st g = true.
Proof.
  intros MR Hml Hsc. unfold okay_to_free. rewrite MR. cbn [m_freeable m_sizeclass m_maplen m_next get_stride m_last_idx Z.eqb andb negb].
  destruct Hsc as [->|[-> ->]]; [reflexivity|].
  replace (17 =? 0) with false by reflexivity. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Definition free_pre (st : mstate) (g : aptr) (sc : Z) : mstate :=
  let st1 := if sc =? 44 then dequeue (LActive 44) g st else st in
  if sc <? 48 then set_usage sc (usage st1 sc - 1) st1 else st1.

(* [comment removed for export] *)
Definition free_post0 (st : mstate) (g : aptr) (rid : N) (sc ml : Z) : mstate :=
  let st1 := free_pre st g sc in
  let st2 := del_slots (rid, 0) (ml * 4096 - UNIT) 1 (del_group (rid, 0) st1) in
  fm_post g (record_seq sc (step_seq st2)).

(* [comment removed for export] *)
Definition blk_meta (g : aptr) (rid : N) (sc ml : Z) : meta :=
  let l := if sc =? 44 then Some g else None in
  mkMeta l l (Some (rid, 0)) 0 0 0 1 sc ml.

Definition blk_class_ok (st : mstate) (g : aptr) (sc ml : Z) : Prop :=
  sc = 63 \/ (sc = 44 /\ ml = 17 /\ active st 44 = Some g).

Lemma ntf_blk {R} dec f st g rid sc ml (k : mstate -> mapinfo -> M R) bail :
  get_meta_rec st g = blk_meta g rid sc ml -> 0 < ml -> blk_class_ok st g sc ml ->
  nontrivial_free dec (S f) st g 0 k bail = k (free_post0 st g rid sc ml) (Some ((rid, 0), ml * 4096)).
Proof.
  intros MR Hml CL. cbn [nontrivial_free].
  assert (OK : okay_to_free st g = true).
  { eapply okay_to_free_blk; [exact MR| exact Hml|]. destruct CL as [A|(A & B & _)]; [left; exact A| right; split; assumption]. }
  rewrite OK, MR. unfold blk_meta. cbn [m_freed m_avail m_last_idx m_sizeclass m_next].
  change (Z.lor 0 0 + bit 0 =? mask_upto 0) with true. cbn [andb].
  assert (NZ : (ml =? 0) = false) by (apply Z.eqb_neq; lia).
  destruct CL as [->|(-> & -> & HA)].
  - change (63 =? 44) with false. cbv iota.
    unfold free_group. rewrite MR. unfold blk_meta. change (63 =? 44) with false. cbn [m_sizeclass m_last_idx m_mem m_maplen].
    change (63 <? 48) with false. cbv iota. rewrite NZ. cbn [negb].
    rewrite free_meta_eq. unfold free_post0, free_pre. change (63 =? 44) with false. change (63 <? 48) with false. cbv iota. cbv zeta.
    unfold get_stride. cbn [m_last_idx m_maplen]. rewrite NZ. reflexivity.
  - change (44 =? 44) with true. cbv iota. unfold guard. change (44 <? 48) with true. cbv iota.
    rewrite HA, optr_eqb_refl.
    assert (DQ := dequeue_self (LActive 44) g st). rewrite MR in DQ. unfold blk_meta in DQ. change (44 =? 44) with true in DQ. cbn [m_next] in DQ.
    specialize (DQ eq_refl). rewrite DQ.
    rewrite active_upd_meta. change (set_head (LActive 44) None st) with (set_active 44 None st). rewrite active_set_active, Z.eqb_refl.
    unfold free_group. rewrite get_meta_rec_upd_same. unfold set_active. rewrite get_meta_rec_upd_ctx, MR. unfold blk_meta. change (44 =? 44) with true.
    cbn [m_sizeclass m_last_idx m_mem m_maplen m_set_prev m_set_next m_prev m_next m_avail m_freed m_freeable].
    change (44 <? 48) with true. change (negb (17 =? 0)) with true. cbv iota.
    rewrite free_meta_eq. unfold free_post0, free_pre. change (44 =? 44) with true. change (44 <? 48) with true. cbv iota. cbv zeta.
    rewrite DQ. unfold get_stride. cbn [m_last_idx m_maplen]. change ((0 =? 0) && negb (17 =? 0)) with true. cbv iota.
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma free_tail_blk st g rid sc ml :
  get_meta_rec st g = blk_meta g rid sc ml -> 0 < ml -> blk_class_ok st g sc ml ->
  let st3 := free_post0 st g rid sc ml in
  free_tail dec_slots st g 0 =
    SVis (EMunmap (conc st3 (rid, 0)) (ml * 4096))
         (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3) else bad_answer (ret st)).
Proof.
  intros MR Hml CL. cbn zeta. unfold free_tail. rewrite MR. unfold blk_meta. cbn [m_freed m_avail m_last_idx].
  unfold guard. change (negb (testbit (Z.lor 0 0) 0)) with true. cbv iota.
  change (negb ((0 =? 0) || (Z.lor 0 0 + bit 0 =? mask_upto 0))) with false. cbv iota.
  unfold FUEL. rewrite (ntf_blk dec_slots 63 st g rid sc ml _ _ MR Hml CL). cbv beta iota.
  replace (negb (ml * 4096 =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition free_post (st : mstate) (g : aptr) (rid : N) (sc ml : Z) : mstate :=
  strip (drop_region rid (free_post0 st g rid sc ml)).

Lemma cfree_blk st c g rid sc ml :
  s_slots st !! c = Some (g, 0) ->
  get_meta_rec st g = blk_meta g rid sc ml -> 0 < ml -> blk_class_ok st g sc ml ->
  let T := cfree st (Some c) in
  tnode T = Some (EMunmap (conc (free_post0 st g rid sc ml) (rid, 0)) (ml * 4096))
  /\ (forall ru, munmap_answer_ok ru = true -> tsub T ru = ret (free_post st g rid sc ml))
  /\ (forall ru, munmap_answer_ok ru = false -> rejects (tsub T ru)).
Proof.
  intros HS MR Hml CL. cbn zeta. unfold cfree. rewrite HS. rewrite (free_tail_blk st g rid sc ml MR Hml CL).
  cbn [sbind tnode tsub]. split; [reflexivity|]. split; intros ru Hru; rewrite Hru; [reflexivity| exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint spine {R} (t : M R) (ans : list Z) : Prop :=
  match ans with
  | [] => True
  | a :: ans' => tnode t <> None /\ spine (tsub t a) ans'
  end.

Lemma tsubs_sbind {R S} (f : R -> M S) : forall ans (t : M R),
  spine t ans -> tsubs (sbind t f) ans = sbind (tsubs t ans) f.
Proof.
  induction ans as [|a ans IH]; intros t Hs; cbn; [reflexivity|].
  destruct Hs as [Hn Hs]. rewrite (tsub_sbind t f a Hn). apply IH. exact Hs.
Qed.

Lemma tnode_sbind_eq {R S} (t : M R) (f : R -> M S) e : tnode t = Some e -> tnode (sbind t f) = Some e.
Proof. apply tnode_sbind. Qed.

Lemma tleaf_sbind {R S} (t : M R) (f : R -> M S) r : tleaf t = Some r -> sbind t f = f r.
Proof. intros H. rewrite (tleaf_Some t r H). reflexivity. Qed.

Lemma spine_snoc {R} (t : M R) ans a : spine t ans -> tnode (tsubs t ans) <> None -> spine t (ans ++ [a]).
Proof.
  revert t. induction ans as [|b ans IH]; intros t Hs Hn; cbn in *.
  - split; [exact Hn| exact I].
  - destruct Hs as [H1 H2]. split; [exact H1|]. apply IH; assumption.
Qed.



End CeilWrap.
End MEX_lib.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl.
Import MEX_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Record dblk : Type := mkDB {
  db_rid : N;        (* [comment removed for export] *)
  db_base : Z;       (* [comment removed for export] *)
  db_len : Z;        (* [comment removed for export] *)
  db_meta : aptr;    (* [comment removed for export] *)
  db_sc : Z          (* [comment removed for export] *)
}.

Definition db_slot (d : dblk) : cptr := (db_rid d, 16).
Definition db_ml (d : dblk) : Z := (db_len d + 4095) / 4096.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition find44 (D : list dblk) : option dblk := find (fun d => db_sc d =? 44) D.

(* [comment removed for export] *)
Definition blk_ok (cs : mstate) (d : dblk) : Prop :=
  s_regions cs !! db_rid d = Some (mkRegion RKGroup (db_base d) (db_len d))
  /\ s_slots cs !! db_slot d = Some (db_meta d, 0)
  /\ get_meta_rec cs (db_meta d) = blk_meta (db_meta d) (db_rid d) (db_sc d) (db_ml d)
  /\ 0 < db_len d <= 2 ^ 26 + 20
  /\ (db_sc d = 63 \/ (db_sc d = 44 /\ db_len d = 69632))
  /\ db_rid d <> 0%N /\ fst (db_meta d) = 0%N.

(* [comment removed for export] *)
Definition freelist_ok (cs : mstate) (fl : optr) (PM : list aptr) (p : aptr) : Prop :=
  c_free_meta_head (ctx cs) = fl /\
  forall f, fl = Some f ->
    get_meta_rec cs f = mkMeta (Some f) (Some f) None 0 0 0 0 0 0 /\ fst f = 0%N /\ snd f < snd p /\ ~ In f PM.

Definition RP (cs : mstate) (D : list dblk) (fl : optr) (lo : Z) : Prop :=
  Forall (blk_ok cs) D
  /\ (forall sc, active cs sc = match find44 D with Some d => if sc =? 44 then Some (db_meta d) else None | None => None end)
  /\ (forall sc, usage cs sc = match find44 D with Some _ => if sc =? 44 then 1 else 0 | None => 0 end)
  /\ (forall i, bounces cs i = 0) /\ (forall i, unmap_seq cs i = 0)
  /\ (exists p, c_avail_meta (ctx cs) = Some p /\ fst p = 0%N /\ 0 <= snd p /\ 50 <= lo <= c_avail_meta_count (ctx cs)
        /\ (forall d, In d D -> snd (db_meta d) < snd p)
        /\ freelist_ok cs fl (map db_meta D) p)
  /\ (exists r0, s_regions cs !! 0%N = Some r0 /\ r_kind r0 <> RKGroup /\ r_len r0 = 2 * PGSZ)
  /\ (forall rid r, s_regions cs !! rid = Some r -> rid = 0%N \/ In rid (map db_rid D))
  /\ (forall rid r, s_regions cs !! rid = Some r -> (rid < s_next_rid cs)%N)
  /\ (forall b h, s_groups cs !! b = Some h -> (fst b < s_next_rid cs)%N)
  /\ List.NoDup (map db_rid D) /\ List.NoDup (map db_meta D) /\ (length D <= 2)%nat
  /\ s_shadow cs = ∅ /\ s_tick cs = 0%N.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RP1 (cs : mstate) (d : dblk) : Prop :=
  exists fl, RP cs [d] fl (match fl with None => 51 | Some _ => 50 end).
(* [comment removed for export] *)
Definition RP2 (cs : mstate) (dold dnew : dblk) : Prop := RP cs [dold; dnew] None 50 /\ db_sc dnew = 63.

(* [comment removed for export] *)
Definition big_blk (cs : mstate) (a n : Z) (g : aptr) : dblk := mkDB (s_next_rid cs) a (n + IB + UNIT) g 63.


End CeilWrap.
