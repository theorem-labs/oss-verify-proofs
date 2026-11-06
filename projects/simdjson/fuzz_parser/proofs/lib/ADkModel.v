(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType.
Import ITree.Exc.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition dk (st : astate) : Z := Z.of_N (a_next st) - Z.of_nat (size (a_live st)).
(* [comment removed for export] *)
Definition DWMAX : Z := 1024.
Definition DKF : Z := 64.

(* [comment removed for export] *)
Fixpoint sallA {R} (P : R -> Prop) (t : AM R) : Prop :=
  match t with
  | SRet r => P r
  | SVis e k => match e with AUndef _ => True | _ => forall z, sallA P (k z) end
  end.

Lemma sallA_mono : forall {R} (P Q : R -> Prop) t, (forall r, P r -> Q r) -> sallA P t -> sallA Q t.
Proof.
  intros R P Q t H. induction t as [r|e k IH]; cbn; [apply H|]. destruct e; try exact (fun H0 z => IH z (H0 z)). intros _; exact I.
Qed.

Lemma sallA_and : forall {R} (P Q : R -> Prop) t, sallA P t -> sallA Q t -> sallA (fun r => P r /\ Q r) t.
Proof.
  intros R P Q t. induction t as [r|e k IH]; cbn; [intros; split; assumption|]. destruct e; try exact (fun H1 H2 z => IH z (H1 z) (H2 z)).
  intros _ _; exact I.
Qed.

(* [comment removed for export] *)
Fixpoint iall {N R} (P : R -> Prop) (t : itree N R) : Prop :=
  match t with Ret r => P r | Vis n k => forall rsp, iall P (k rsp) end.

Lemma iall_bind_all : forall {N A B} (P : B -> Prop) (t : itree N A) (g : A -> itree N B),
  (forall x, iall P (g x)) -> iall P (bind N t g).
Proof. intros N A B P t g H. induction t as [r|n k IH]; cbn; [apply H| intros rsp; apply IH]. Qed.

Definition eprop {R} (P : R -> Prop) (x : exc R) : Prop := match x with Unr => True | Ok r => P r end.

Lemma sallA_embed : forall atop {R} (P : R -> Prop) (t : AM R), sallA P t -> iall (eprop P) (aembed atop t).
Proof.
  intros atop R P t. induction t as [r|e k IH]; intros H; [exact H|].
  destruct e as [a|a|a l p f|a l|a l p|a l|w];
    try (rewrite aembed_vis; unfold ebind; apply iall_bind_all; intros [|z]; cbn; [exact I| apply IH; apply H]).
  rewrite aembed_undef. exact I.
Qed.

Section ImplF.
  Variables (node : Type) (segs : list MemImageType.Segment) (at_node : node -> footprint -> RiscvSemantics.machine_state -> Prop)
            (fstep : node -> resp -> footprint -> footprint -> Prop).
  Lemma implF_iall : forall {R} RNG (t : itree node R) (Q : R -> footprint -> RiscvSemantics.machine_state -> Prop) (P : R -> Prop) ms,
    @implF node segs at_node fstep R RNG t Q ms -> iall P t ->
    @implF node segs at_node fstep R RNG t (fun r RNG' ms' => Q r RNG' ms' /\ P r) ms.
  Proof.
    intros R RNG t; revert RNG. induction t as [r|n k IH]; intros RNG Q P ms H HP; cbn in *.
    - eapply evtF_mono; [exact H|]. intros ms' H'. split; [exact H'| exact HP].
    - eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp RNG' HF. apply IH; [exact (Hk rsp RNG' HF)| exact (HP rsp)].
  Qed.
End ImplF.

Lemma implF_embed_sallA : forall (segs : list MemImageType.Segment) (at_node : Nodes.node -> footprint -> RiscvSemantics.machine_state -> Prop)
    (fstep : Nodes.node -> resp -> footprint -> footprint -> Prop) atop {R} RNG (t : AM R) (Q : R -> footprint -> RiscvSemantics.machine_state -> Prop) (P : R -> Prop) ms,
    @implF Nodes.node segs at_node fstep (exc R) RNG (aembed atop t) (epostF Q) ms -> sallA P t ->
    @implF Nodes.node segs at_node fstep (exc R) RNG (aembed atop t) (epostF (fun r RNG' ms' => Q r RNG' ms' /\ P r)) ms.
  Proof.
    intros segs at_node fstep atop R RNG t Q P ms H HS. pose proof (sallA_embed atop P t HS) as HI.
    eapply implF_mono; [exact (implF_iall Nodes.node segs at_node fstep _ _ _ _ _ H HI)|]. intros [|r] RNG' ms'; cbn; [auto| intros [A B]; split; assumption].
  Qed.

(* [comment removed for export] *)
Definition LN (st st' : astate) : Prop := a_live st' = a_live st /\ a_next st' = a_next st.
Lemma LN_refl : forall st, LN st st. Proof. intros; split; reflexivity. Qed.
Lemma LN_trans : forall a b c, LN a b -> LN b c -> LN a c. Proof. intros a b c [A1 A2] [B1 B2]. split; congruence. Qed.

Ltac ln_solve := unfold LN, init_cache; cbn [a_live a_next put_cls set_cls set_cinit set_nsec set_nres set_qloc set_qglob];
                 try (destruct (a_cinit _)); cbn [a_live a_next put_cls set_cls set_cinit set_nsec set_nres set_qloc set_qglob];
                 split; reflexivity.
Ltac sall_leaf Hk := first [exact I | (apply Hk; ln_solve) | (apply Hk; eapply LN_trans; [| eassumption]; ln_solve)
                            | (apply Hk; eapply LN_trans; [eassumption|]; ln_solve) | (apply Hk; assumption)].
Ltac sall_go Hk :=
  repeat (first [ progress (unfold ev, aundef_, aret, poison0)
                | progress cbn [sallA]
                | match goal with
                  | |- _ -> _ => intro
                  | |- forall _, _ => intro
                  | |- True => exact I
                  | |- sallA _ (if ?b then _ else _) => destruct b
                  | |- sallA _ (match ?x with _ => _ end) => destruct x
                  end ]).

Section Pres.
Context {R : Type} (P : R -> Prop).

Lemma ensure_free_array_pres : forall st c nf (k : astate -> bool -> AM R),
  (forall st' x, LN st st' -> sallA P (k st' x)) -> sallA P (ensure_free_array st c nf k).
Proof. intros st c nf k Hk. unfold ensure_free_array. cbv zeta. sall_go Hk; sall_leaf Hk. Qed.

Lemma populate_free_array_pres : forall st c req (k : astate -> bool -> AM R),
  (forall st' x, LN st st' -> sallA P (k st' x)) -> sallA P (populate_free_array st c req k).
Proof.
  intros st c req k Hk. unfold populate_free_array. cbv zeta.
  destruct (_ <=? _).
  - apply ensure_free_array_pres. intros st' x E. destruct (negb x); [sall_leaf Hk|]. apply Hk. eapply LN_trans; [exact E|]. ln_solve.
  - sall_go Hk; try sall_leaf Hk.
    all: apply ensure_free_array_pres; intros st' x E; destruct (negb x); [apply Hk; eapply LN_trans; [| exact E]; ln_solve|].
    all: apply Hk; eapply LN_trans; [| eapply LN_trans; [exact E|]]; ln_solve.
Qed.

Lemma cache_alloc_pres : forall st c (k : astate -> bool -> AM R),
  (forall st' x, LN st st' -> sallA P (k st' x)) -> sallA P (cache_alloc st c k).
Proof.
  intros st c k Hk. unfold cache_alloc. cbv zeta.
  destruct (0 <? _); [sall_leaf Hk|].
  destruct (_ <=? _).
  - sall_go Hk; sall_leaf Hk.
  - apply populate_free_array_pres. intros st' x E. destruct x; [| apply Hk; eapply LN_trans; [| exact E]; ln_solve].
    sall_go Hk; apply Hk; eapply LN_trans; [| eapply LN_trans; [exact E|]]; ln_solve.
Qed.

Lemma cache_dealloc_pres : forall st c (k : astate -> AM R),
  (forall st', LN st st' -> sallA P (k st')) -> sallA P (cache_dealloc st c k).
Proof.
  intros st c k Hk. unfold cache_dealloc. cbv zeta.
  destruct (_ =? _).
  - apply ensure_free_array_pres. intros st' x E. destruct (negb x); cbn [aundef_ sallA]; [exact I|].
    apply Hk. eapply LN_trans; [| eapply LN_trans; [exact E|]]; ln_solve.
  - apply Hk. ln_solve.
Qed.

Lemma large_alloc_pres : forall atop RESV st n (k : astate -> option achunk -> AM R),
  (forall st' x, LN st st' -> sallA P (k st' x)) -> sallA P (large_alloc atop RESV st n k).
Proof. intros atop RESV st n k Hk. unfold large_alloc. cbv zeta. sall_go Hk; sall_leaf Hk. Qed.

Lemma large_dealloc_pres : forall st mb ms (k : astate -> AM R),
  (forall st', LN st st' -> sallA P (k st')) -> sallA P (large_dealloc st mb ms k).
Proof. intros st mb ms k Hk. unfold large_dealloc. cbv zeta. sall_go Hk; sall_leaf Hk. Qed.

Lemma recycle_chunk_pres : forall st ch (k : astate -> AM R),
  (forall st', LN st st' -> sallA P (k st')) -> sallA P (recycle_chunk st ch k).
Proof. intros st ch k Hk. destruct ch; [apply cache_dealloc_pres| apply large_dealloc_pres]; exact Hk. Qed.

Lemma recycle_chunks_pres : forall l st (k : astate -> AM R),
  (forall st', LN st st' -> sallA P (k st')) -> sallA P (recycle_chunks st l k).
Proof.
  induction l as [|ch l IH]; intros st k Hk; cbn [recycle_chunks]; [apply Hk; apply LN_refl|].
  apply recycle_chunk_pres. intros st1 E1. apply IH. intros st2 E2. apply Hk. eapply LN_trans; eassumption.
Qed.

Lemma do_recycle_pres : forall bs st (k : astate -> AM R),
  (forall st', LN st st' -> sallA P (k st')) -> sallA P (do_recycle st bs k).
Proof.
  induction bs as [|b bs IH]; intros st k Hk; cbn [do_recycle]; [apply Hk; apply LN_refl|].
  apply recycle_chunks_pres. intros st1 E1. apply cache_dealloc_pres. intros st2 E2. apply IH. intros st3 E3.
  apply Hk. eapply LN_trans; [exact E1| eapply LN_trans; eassumption].
Qed.

Lemma recycle_pres : forall st mn (k : astate -> AM R),
  (forall st', LN st st' -> sallA P (k st')) -> sallA P (recycle st mn k).
Proof.
  intros st mn k Hk. unfold recycle. cbv zeta.
  destruct (_ <? _); [unfold aundef_; cbn [sallA]; exact I|].
  repeat match goal with |- context [match ?X with pair _ _ => _ end] => destruct X end.
  destruct (_ <? _); [unfold aundef_; cbn [sallA]; exact I|].
  apply do_recycle_pres. intros st' E. apply Hk. eapply LN_trans; [| exact E]. ln_solve.
Qed.

Lemma drain_pres : forall st (k : astate -> AM R),
  (forall st', LN st st' -> sallA P (k st')) -> sallA P (drain st k).
Proof.
  intros st k Hk. unfold drain. cbv zeta. destruct (_ <? _).
  - apply recycle_pres. intros st' E. apply Hk. eapply LN_trans; [| exact E]. ln_solve.
  - apply Hk. ln_solve.
Qed.

Lemma enqueue_pres : forall st ch (k : astate -> AM R),
  (forall st', LN st st' -> sallA P (k st')) -> sallA P (enqueue st ch k).
Proof.
  intros st ch k Hk. unfold enqueue. cbv zeta.
  destruct (rev (a_qloc st)) as [|b rl].
  - apply cache_alloc_pres. intros st1 ok E. destruct (negb ok); cbn [aundef_ sallA]; [exact I|].
    apply Hk. eapply LN_trans; [exact E|]. ln_solve.
  - destruct (b_count b =? Q_BATCH).
    + apply cache_alloc_pres. intros st1 ok E. destruct (negb ok); cbn [aundef_ sallA]; [exact I|].
      apply Hk. eapply LN_trans; [exact E|]. ln_solve.
    + apply Hk. ln_solve.
Qed.
End Pres.

(* [comment removed for export] *)
Theorem afree_leaves : forall st id ch, (a_live st) !! id = Some ch ->
  sallA (fun r => a_live r = delete id (a_live st) /\ a_next r = a_next st) (afree st (Some id)).
Proof.
  intros st id ch Hl. unfold afree. rewrite Hl. cbv zeta.
  set (st1 := set_live (delete id (a_live st)) st).
  assert (K : forall st2, LN st1 st2 ->
     sallA (fun r => a_live r = delete id (a_live st) /\ a_next r = a_next st)
       (if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2)).
  { intros st2 [E1 E2]. destruct (_ <? _).
    - apply drain_pres. intros st3 [F1 F2]. cbn [aret sallA]. split; [rewrite F1, E1; reflexivity| rewrite F2, E2; reflexivity].
    - cbn [aret sallA]. split; [rewrite E1; reflexivity| rewrite E2; reflexivity]. }
  destruct (chunk_size ch <=? Q_MAX); [apply enqueue_pres; exact K| apply recycle_chunk_pres; exact K].
Qed.

Lemma afree_none : forall st, afree st None = aret st. Proof. reflexivity. Qed.

Lemma dk_delete : forall st id ch, (a_live st) !! id = Some ch ->
  forall r, a_live r = delete id (a_live st) -> a_next r = a_next st -> dk r = dk st + 1.
Proof.
  intros st id ch Hl r E1 E2. unfold dk. rewrite E1, E2.
  assert (NZ : (size (a_live st) <> 0)%nat).
  { intros Hs. apply map_size_empty_iff in Hs. rewrite Hs, lookup_empty in Hl. discriminate. }
  rewrite map_size_delete_Some by (eexists; exact Hl). lia.
Qed.

(* [comment removed for export] *)
Theorem afree_dk : forall st id ch, (a_live st) !! id = Some ch -> sallA (fun r => dk r = dk st + 1) (afree st (Some id)).
Proof.
  intros st id ch Hl. eapply sallA_mono; [| exact (afree_leaves st id ch Hl)].
  intros r [E1 E2]. exact (dk_delete st id ch Hl r E1 E2).
Qed.

Lemma dk_insert : forall st1 id ch, Z.of_N (a_next st1) - Z.of_nat (size (a_live st1)) <=
  Z.of_N (N.succ id) - Z.of_nat (size (<[id := ch]> (a_live st1))) + (Z.of_N (a_next st1) - Z.of_N id).
Proof.
  intros st1 id ch. destruct ((a_live st1) !! id) as [c0|] eqn:E.
  - rewrite map_size_insert_Some by (eexists; exact E). lia.
  - rewrite map_size_insert_None by exact E. lia.
Qed.

Theorem amalloc_dk : forall atop RESV st n, sallA (fun r => dk st <= dk (fst r)) (amalloc atop RESV st n).
Proof.
  intros atop RESV st n. unfold amalloc. cbv zeta.
  destruct (_ || _); [unfold aret; cbn [sallA fst]; lia|].
  assert (FIN : forall st1 ch, LN st st1 ->
    sallA (fun r => dk st <= dk (fst r))
      match ch with
      | CPrim _ _ => aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1 := ch]> (a_live st1)) st1), Some (a_next st1))
      | CSec _ _ _ => poison0 (chunk_user_beg ch) (Z.land n (Z.lnot 7))
                        (aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1 := ch]> (a_live st1)) st1), Some (a_next st1)))
      end).
  { intros st1 ch [E1 E2]. pose proof (dk_insert st1 (a_next st1) ch) as D.
    destruct ch; unfold poison0, aret; cbn [sallA fst]; unfold dk; cbn [a_next a_live set_next set_live]; rewrite <- E1, <- E2; lia. }
  destruct (is_primary n).
  - apply cache_alloc_pres. intros st1 ok E. destruct ok; [exact (FIN st1 (CPrim (class_id (needed_size n)) n) E)|].
    unfold aret. cbn [sallA fst]. destruct E as [E1 E2]. unfold dk. rewrite E1, E2. lia.
  - apply large_alloc_pres. intros st1 och E. destruct och as [ch|]; [exact (FIN st1 ch E)|].
    unfold aret. cbn [sallA fst]. destruct E as [E1 E2]. unfold dk. rewrite E1, E2. lia.
Qed.

(* [comment removed for export] *)
Definition AFRESH (st : astate) : Prop := forall id ch, (a_live st) !! id = Some ch -> (id < a_next st)%N.

Lemma afresh_LN : forall st st', LN st st' -> AFRESH st -> AFRESH st'.
Proof. intros st st' [E1 E2] H id ch Hl. rewrite E2. apply (H id ch). rewrite <- E1. exact Hl. Qed.

Lemma afresh_init : forall a b, AFRESH (ainit a b).
Proof. intros a b id ch Hl. cbn [ainit a_live] in Hl. rewrite lookup_empty in Hl. discriminate. Qed.

Lemma afresh_insert_next : forall st1 ch, AFRESH st1 ->
  AFRESH (set_next (N.succ (a_next st1)) (set_live (<[a_next st1 := ch]> (a_live st1)) st1))
  /\ dk (set_next (N.succ (a_next st1)) (set_live (<[a_next st1 := ch]> (a_live st1)) st1)) = dk st1.
Proof.
  intros st1 ch H. split.
  - intros id c Hl. cbn [set_next set_live a_live a_next] in *.
    destruct (N.eq_dec id (a_next st1)) as [->|NE]; [lia|].
    rewrite lookup_insert_ne in Hl by (intros E; apply NE; symmetry; exact E). pose proof (H id c Hl). lia.
  - unfold dk. cbn [set_next set_live a_live a_next].
    destruct ((a_live st1) !! (a_next st1)) as [c0|] eqn:E.
    + pose proof (H _ _ E). lia.
    + rewrite map_size_insert_None by exact E. lia.
Qed.

Theorem amalloc_fresh_dk : forall atop RESV st n, AFRESH st ->
  sallA (fun r => AFRESH (fst r) /\ dk (fst r) = dk st) (amalloc atop RESV st n).
Proof.
  intros atop RESV st n HF. unfold amalloc. cbv zeta.
  destruct (_ || _); [unfold aret; cbn [sallA fst]; split; [exact HF| reflexivity]|].
  assert (FIN : forall st1 ch, LN st st1 ->
    sallA (fun r => AFRESH (fst r) /\ dk (fst r) = dk st)
      match ch with
      | CPrim _ _ => aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1 := ch]> (a_live st1)) st1), Some (a_next st1))
      | CSec _ _ _ => poison0 (chunk_user_beg ch) (Z.land n (Z.lnot 7))
                        (aret (set_next (N.succ (a_next st1)) (set_live (<[a_next st1 := ch]> (a_live st1)) st1), Some (a_next st1)))
      end).
  { intros st1 ch E. pose proof (afresh_LN st st1 E HF) as HF1.
    destruct (afresh_insert_next st1 ch HF1) as [A B].
    assert (D1 : dk st1 = dk st) by (destruct E as [E1 E2]; unfold dk; rewrite E1, E2; reflexivity).
    destruct ch; unfold poison0, aret; cbn [sallA fst]; (split; [exact A| rewrite B; exact D1]). }
  destruct (is_primary n).
  - apply cache_alloc_pres. intros st1 ok E. destruct ok; [exact (FIN st1 (CPrim (class_id (needed_size n)) n) E)|].
    unfold aret. cbn [sallA fst]. split; [exact (afresh_LN st st1 E HF)|]. destruct E as [E1 E2]. unfold dk. rewrite E1, E2. reflexivity.
  - apply large_alloc_pres. intros st1 och E. destruct och as [ch|]; [exact (FIN st1 ch E)|].
    unfold aret. cbn [sallA fst]. split; [exact (afresh_LN st st1 E HF)|]. destruct E as [E1 E2]. unfold dk. rewrite E1, E2. reflexivity.
Qed.

Theorem afree_fresh_dk : forall st o, AFRESH st ->
  sallA (fun r => AFRESH r /\ dk st <= dk r <= dk st + 1) (afree st o).
Proof.
  intros st o HF. destruct o as [id|]; [| rewrite afree_none; cbn [aret sallA]; split; [exact HF| lia]].
  destruct ((a_live st) !! id) as [ch|] eqn:Hl.
  - eapply sallA_mono; [| exact (afree_leaves st id ch Hl)]. intros r [E1 E2].
    pose proof (dk_delete st id ch Hl r E1 E2) as D. split; [| lia].
    intros id' c Hl'. rewrite E2. rewrite E1 in Hl'. destruct (N.eq_dec id' id) as [->|NE].
    + rewrite lookup_delete_eq in Hl'. discriminate.
    + rewrite lookup_delete_ne in Hl' by (intros Ex; apply NE; symmetry; exact Ex). exact (HF id' c Hl').
  - unfold afree. rewrite Hl. unfold aundef_. cbn [sallA]. exact I.
Qed.

(* [comment removed for export] *)
Theorem aannotate_same : forall st p cap old new, sallA (fun r => r = st) (aannotate st p cap old new).
Proof.
  intros st p cap old new. unfold aannotate, aundef_, aret, poison0.
  destruct ((a_live st) !! p) as [ch|]; cbn [sallA]; [| exact I].
  repeat match goal with |- sallA _ (if ?b then _ else _) => destruct b; cbn [sallA] end; try exact I; try reflexivity.
  all: destruct ch; cbn [sallA]; try reflexivity; cbv zeta; destruct (_ <? _); cbn [sallA]; reflexivity.
Qed.

Lemma dk_ainit : forall a b, dk (ainit a b) = 0.
Proof. intros a b. unfold dk, ainit. cbn [a_next a_live]. rewrite map_size_empty. reflexivity. Qed.
