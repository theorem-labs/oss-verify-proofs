(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep KStepC
  MI_Inv MI_Cnt LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Alloc ProgDetIface ProgDetLogic ProgDetMalloc LibProg NLogic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition slotsX (X : list (bptr * Z)) : list cptr := map (fun xb => fst (fst xb)) X.

Definition SBc (c : Z) : Z := if c <? 28 then S_ c else Z.max (S_ c) ((S_ c + 4111) / 4096 * 4096 - UNIT).

Definition realloc_crit (m n : Z) : Prop :=
  0 <= m < MMAP_THRESHOLD /\ Z.max (SBc (size_to_class m)) (SBc (size_to_class m + 1)) - IB < n.
Definition realloc_crit_b (m n : Z) : bool :=
  (0 <=? m) && (m <? MMAP_THRESHOLD) && (Z.max (SBc (size_to_class m)) (SBc (size_to_class m + 1)) - IB <? n).
Lemma realloc_crit_b_ok m n : realloc_crit_b m n = true -> realloc_crit m n.
Proof. unfold realloc_crit_b, realloc_crit. intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. lia. Qed.

Section LWF.
Variable ok : list (bptr * Z) -> Z -> Prop.

Fixpoint lwf {A} (t : lprog A) (X : list (bptr * Z)) (Q : A -> list (bptr * Z) -> Prop) : Prop :=
  match t with
  | LRet a => Q a X
  | LUnr => False
  | LMalloc n k =>
      0 <= n < 2^62 /\ ok X n /\ k None = LUnr
      /\ forall p, ~ In (fst p) (slotsX X) -> lwf (k (Some p)) ((p, n) :: X) Q
  | LFree p k => exists m X', Permutation X ((p, m) :: X') /\ lwf k X' Q
  | LRealloc p n k =>
      exists m X', Permutation X ((p, m) :: X') /\ 0 <= n < 2^62 /\ realloc_crit m n /\ ok X n /\ k None = LUnr
      /\ forall q, ~ In (fst q) (slotsX X) -> lwf (k (Some q)) ((q, n) :: X') Q
  end.

Lemma lwf_mono : forall {A} (t : lprog A) X (Q Q' : A -> list (bptr * Z) -> Prop),
  lwf t X Q -> (forall a X', Q a X' -> Q' a X') -> lwf t X Q'.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH|p n k IH]; intros X Q Q' H HQ; cbn [lwf] in *.
  - apply HQ. exact H.
  - exact H.
  - destruct H as (Hn & Hok & HN & Hk). repeat (split; [assumption|]). intros q Hq. eapply IH; [exact (Hk q Hq)| exact HQ].
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. eapply IH; [exact Hk| exact HQ].
  - destruct H as (m & X' & HP & Hn & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    intros q Hq. eapply IH; [exact (Hk q Hq)| exact HQ].
Qed.

Lemma lwf_bind : forall {A B} (m : lprog A) (f : A -> lprog B) X (Q : B -> list (bptr * Z) -> Prop),
  lwf m X (fun a X' => lwf (f a) X' Q) -> lwf (lbind m f) X Q.
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH|p n k IH]; intros f X Q H; cbn [lwf lbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & Hok & HN & Hk). repeat (split; [assumption|]). split; [rewrite HN; reflexivity|].
    intros q Hq. apply IH. exact (Hk q Hq).
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. apply IH. exact Hk.
  - destruct H as (m & X' & HP & Hn & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    split; [rewrite HN; reflexivity|]. intros q Hq. apply IH. exact (Hk q Hq).
Qed.
End LWF.

Fixpoint lleaves {A} (t : lprog A) (phi : A -> Prop) : Prop :=
  match t with
  | LRet a => phi a
  | LUnr => True
  | LMalloc n k => forall r, lleaves (k r) phi
  | LFree p k => lleaves k phi
  | LRealloc p n k => forall r, lleaves (k r) phi
  end.

Lemma lleaves_true : forall {A} (t : lprog A), lleaves t (fun _ => True).
Proof. intros A t. induction t as [a| |n k IH|p k IH|p n k IH]; cbn [lleaves]; auto. Qed.

Lemma lwf_lleaves : forall ok {A} (t : lprog A) X (Q : A -> list (bptr * Z) -> Prop) (phi : A -> Prop),
  lwf ok t X Q -> lleaves t phi -> lwf ok t X (fun a X' => Q a X' /\ phi a).
Proof.
  intros ok A t. induction t as [a| |n k IH|p k IH|p n k IH]; intros X Q phi H HL; cbn [lwf lleaves] in *.
  - split; assumption.
  - exact H.
  - destruct H as (Hn & Ho & HN & Hk). repeat (split; [assumption|]). intros q Hq. apply IH; [exact (Hk q Hq)| exact (HL (Some q))].
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. apply IH; [exact Hk| exact HL].
  - destruct H as (m & X' & HP & Hn & Hc & Ho & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    intros q Hq. apply IH; [exact (Hk q Hq)| exact (HL (Some q))].
Qed.

Section Alloc.
Context {CE__ : Ceiling}.
Variable G : PState -> Model -> Prop.
Hypothesis HG : frame_ok G.
Variable P : Z -> Z.

Definition mal_okP (X : list (bptr * Z)) (n : Z) : Prop :=
  ROOMX X P n /\ PHI P + R63X X + bigb n <= LBUDGET.

Definition OQ (X : list (bptr * Z)) : assn PState := fun s mo => OWN (map fst X) G s mo /\ QI X P s mo.

Lemma OQ_perm : forall X Y s mo, Permutation X Y -> OQ X s mo -> OQ Y s mo.
Proof.
  intros X Y s mo HP [H1 H2]. split; [eapply OWN_perm; [apply Permutation_map; exact HP| exact H1]| eapply QI_perm; [exact HP| exact H2]].
Qed.

Lemma QI_fresh : forall p n X s mo, QI ((p, n) :: X) P s mo -> ~ In (fst p) (slotsX X).
Proof. intros p n X s mo H. pose proof (QI_nodup _ _ _ _ H) as ND. cbn [map fst] in ND. inversion ND; subst. assumption. Qed.

Lemma OQ_fresh : forall p n X s mo, OQ ((p, n) :: X) s mo -> ~ In (fst p) (slotsX X).
Proof. intros p n X s mo [_ H]. exact (QI_fresh _ _ _ _ _ H). Qed.

Lemma fstable_True : fstable (fun _ _ _ => True).
Proof. intros s mo tr s' mo' _ _ _ _. exact I. Qed.

Lemma size_ok62 : forall n, n < 2^62 -> size_overflows n = false.
Proof. intros n H. unfold size_overflows. apply Z.leb_gt. lia. Qed.

Lemma raw_malloc_N : forall X n, 0 <= n < 2^62 ->
  mspecN (fun s mo => OQ X s mo /\ mal_okP X n) (raw_malloc n)
         (fun r s mo => exists p, r = Some p /\ OQ ((p, n) :: X) s mo).
Proof.
  intros X n Hn.
  eapply mspecN_conseq;
    [eapply (mspecN_combine LBUDGET (fun _ => True));
       [apply (raw_malloc_spec_c (map fst X) G n HG (proj1 Hn))
       |apply (raw_malloc_LQ X P n (proj1 Hn))
       |apply (raw_malloc_E None (fun _ => True) n (fun _ _ _ => True) fstable_True (size_ok62 n (proj2 Hn)))]| |].
  - intros s mo [[HO HQ] [HR HB]]. split; [exact HO|]. split; [auto|]. split; [exists []; exact I|]. exact (QI_minv _ _ _ _ HQ).
  - intros r s mo (H1 & H2 & tr & _ & Hr). destruct r as [p|]; [|contradiction Hr; reflexivity].
    exists p. split; [reflexivity|]. split; [exact (proj1 H1)| exact (proj1 H2)].
Qed.

Lemma raw_free_N : forall X p n, mspecN (OQ ((p, n) :: X)) (raw_free p) (fun _ => OQ X).
Proof.
  intros X p n.
  eapply mspecN_conseq;
    [eapply (mspecN_combine LBUDGET (fun _ => True));
       [apply (raw_free_spec_c (map fst X) G p HG)
       |apply (raw_free_LQ X P p n)
       |apply (raw_free_E None (fun _ => True) p (fun _ _ _ => True) fstable_True)]| |].
  - intros s mo [HO HQ]. split; [exact HO|]. split; [exact HQ|]. split; [exists []; exact I|]. exact (QI_minv _ _ _ _ HQ).
  - intros r s mo (H1 & H2 & _). split; assumption.
Qed.

Lemma SBc_bound : forall mr,
  0 <= m_sizeclass mr < 48 ->
  (get_stride mr <= S_ (m_sizeclass mr) \/ 28 <= m_sizeclass mr) ->
  (m_maplen mr <> 0 -> m_maplen mr * 4096 <= (m_last_idx mr + 1) * S_ (m_sizeclass mr) + 4111) ->
  get_stride mr <= SBc (m_sizeclass mr).
Proof.
  intros mr Hc Hs Hmap. unfold SBc. destruct (Z.ltb_spec (m_sizeclass mr) 28) as [Hlt|Hge]; [destruct Hs; lia|].
  unfold get_stride in *. destruct (Z.eqb_spec (m_last_idx mr) 0) as [E0|NE0]; cbn [andb]; [|unfold S_; lia].
  destruct (Z.eqb_spec (m_maplen mr) 0) as [M0|MN0]; cbn [negb]; [unfold S_; lia|].
  specialize (Hmap MN0). rewrite E0 in Hmap.
  assert (m_maplen mr <= (S_ (m_sizeclass mr) + 4111) / 4096).
  { apply Z.div_le_lower_bound; lia. }
  unfold UNIT. nia.
Qed.

Lemma realloc_moves_of_QI : forall p m X n s mo,
  QI ((p, m) :: X) P s mo -> realloc_crit m n -> realloc_moves (ps_m s) (fst p) n = true.
Proof.
  intros p m X n s mo [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP) _] [Hm Hcrit].
  assert (Hin : In (fst p, m) (map bs BL)). { eapply Permutation_in; [exact HP|]. left. reflexivity. }
  apply in_map_iff in Hin. destruct Hin as (k & Hk & HkBL). unfold bs in Hk. injection Hk as Hslot Hsize.
  destruct (qb_cls _ _ _ SI k HkBL) as (mt & i & Hs & Hlt48 & H63).
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ((b & ai & Hg) & Hi & _).
  pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO.
  assert (Hc : 0 <= m_sizeclass (MR st mt) < 48).
  { destruct (g_sc _ _ _ _ _ _ GO) as [[Hc _]|[Hc _]]; [exact Hc|]. destruct (H63 Hc) as [Hbig _]. lia. }
  destruct (Hlt48 (proj2 Hc)) as [_ Hcls].
  destruct (g_stride _ _ _ _ _ _ GO (proj2 Hc)) as (Hstr & _ & _).
  assert (Hb : get_stride (MR st mt) <= SBc (m_sizeclass (MR st mt))).
  { apply SBc_bound; [exact Hc| exact Hstr|]. intros MN0. exact (qg_map _ _ _ SI _ _ _ Hg (proj2 Hc) MN0). }
  unfold realloc_moves. rewrite <- E. cbn [strip s_slots]. rewrite <- Hslot, Hs.
  unfold MR in *. unfold get_meta_rec in *. cbn [strip s_metas].
  apply andb_true_intro. split; [|apply orb_true_intro; left; apply Z.ltb_lt; exact (proj2 Hc)].
  apply Z.ltb_lt. rewrite Hsize in Hcls.
  destruct Hcls as [Ec|Ec].
  - rewrite <- Ec in Hb. lia.
  - replace (m_sizeclass (default meta0 (s_metas st !! mt))) with (size_to_class m + 1) in Hb by lia. lia.
Qed.

Lemma slotsX_app : forall X Y, slotsX (X ++ Y) = slotsX X ++ slotsX Y.
Proof. intros. unfold slotsX. apply map_app. Qed.

Lemma raw_realloc_N : forall X p m n, 0 <= n < 2^62 -> realloc_crit m n ->
  mspecN (fun s mo => OQ ((p, m) :: X) s mo /\ mal_okP ((p, m) :: X) n) (raw_realloc p n)
         (fun r s mo => exists q, r = Some q /\ OQ ((q, n) :: X) s mo /\ ~ In (fst q) (slotsX ((p, m) :: X))).
Proof.
  intros X p m n Hn Hcrit. unfold raw_realloc.
  eapply mspecN_bind; [apply mspecN_get|]. intros s0.
  apply mspecN_pointwise. intros s1 mo1 [-> [HOQ Hok]].
  rewrite (size_ok62 n (proj2 Hn)). rewrite (realloc_moves_of_QI p m X n s1 mo1 (proj2 HOQ) Hcrit).
  eapply mspecN_bind.
  { eapply mspecN_pre; [apply (raw_malloc_N ((p, m) :: X) n Hn)|]. intros s mo [-> ->]. split; assumption. }
  intros r. apply mspecN_pointwise. intros s2 mo2 (q & -> & HOQ2).
  pose proof (OQ_fresh _ _ _ _ _ HOQ2) as Hfr.
  eapply mspecN_seq with (R := OQ ((q, n) :: X)).
  { eapply mspecN_pre; [apply (raw_free_N ((q, n) :: X) p m)|]. intros s mo [-> ->].
    eapply OQ_perm; [apply perm_swap| exact HOQ2]. }
  intros _. apply mspecN_ret. intros s mo H. exists q. split; [reflexivity|]. split; [exact H| exact Hfr].
Qed.

Lemma raw_realloc_L : forall X p m n, 0 <= n ->
  mspecL LBUDGET (fun s mo => QI ((p, m) :: X) P s mo /\ mal_okP ((p, m) :: X) n) (raw_realloc p n)
         (fun r s mo => match r with
                        | Some q => QI ((q, n) :: X) P s mo /\ ~ In (fst q) (slotsX ((p, m) :: X))
                        | None => True
                        end).
Proof.
  intros X p m n Hn. unfold raw_realloc.
  eapply mspecL_bind; [apply mspecL_get|]. intros s0.
  apply mspecL_pointwise. intros s1 mo1 [-> [HQ Hok]].
  destruct (size_overflows n); [apply mspecL_ret; intros; exact I|].
  destruct (realloc_moves (ps_m s1) (fst p) n); [|apply mspecL_munr].
  eapply mspecL_bind.
  { eapply mspecL_pre; [apply (raw_malloc_LQ ((p, m) :: X) P n Hn)|]. intros s mo [-> ->]. split; [exact HQ| exact Hok]. }
  intros [q|]; [|apply mspecL_ret; intros; exact I].
  apply mspecL_pointwise. intros s2 mo2 [HQ2 _].
  pose proof (QI_fresh _ _ _ _ _ HQ2) as Hfr.
  eapply mspecL_seq with (R := QI ((q, n) :: X) P).
  { eapply mspecL_pre; [apply (raw_free_LQ ((q, n) :: X) P p m)|]. intros s mo [-> ->].
    eapply QI_perm; [apply perm_swap| exact HQ2]. }
  intros _. apply mspecL_ret. intros s mo H. split; [exact H| exact Hfr].
Qed.

End Alloc.

Section AllocE.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable XT : list event -> Prop.

Lemma raw_malloc_E0 : forall n (K : assnE PState), fstable K -> mspecE sel XT K (raw_malloc n) (fun _ => K).
Proof.
  intros n K HK. unfold raw_malloc.
  eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr /\ s = s0);
    [apply mspecE_get; intros s mo tr H; exact (conj H (eq_refl s))|]. intros s0.
  eapply mspecE_bind.
  { eapply mspecE_pre; [apply membed_E; [exact HK| apply oktree_true]| intros s mo tr [H _]; exact H]. }
  intros [st' p]. cbv beta iota.
  eapply mspecE_seq with (R := K).
  { apply mspecE_upd. intros s mo tr [H _]. eapply HK; [exact H| reflexivity| reflexivity| reflexivity]. }
  intros _. apply mspecE_ret. intros s mo tr H. exact H.
Qed.

Lemma raw_realloc_E : forall p n (K : assnE PState), fstable K -> mspecE sel XT K (raw_realloc p n) (fun _ => K).
Proof.
  intros p n K HK. unfold raw_realloc.
  eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr);
    [apply mspecE_get; intros s mo tr H; exact H|]. intros s0.
  destruct (size_overflows n); [apply mspecE_ret; auto|].
  destruct (realloc_moves (ps_m s0) (fst p) n); [|apply mspecE_munr].
  eapply mspecE_bind; [apply raw_malloc_E0; exact HK|].
  intros [q|]; [|apply mspecE_ret; auto].
  eapply mspecE_seq; [apply raw_free_E; exact HK|]. intros _. apply mspecE_ret. auto.
Qed.

Theorem interp_E : forall (K : assnE PState), fstable K ->
  forall {A} (t : lprog A) (phi : A -> Prop), lleaves t phi ->
  mspecE sel XT K (interp t) (fun a s mo tr => K s mo tr /\ phi a).
Proof.
  intros K HK A t. induction t as [a| |n k IH|p k IH|p n k IH]; intros phi H; cbn [interp lleaves] in *.
  - apply mspecE_ret. intros s mo tr HKs. split; [exact HKs| exact H].
  - apply mspecE_munr.
  - eapply mspecE_bind; [apply raw_malloc_E0; exact HK|]. intros r. apply IH. exact (H r).
  - eapply mspecE_seq; [apply raw_free_E; exact HK|]. intros _. apply IH. exact H.
  - eapply mspecE_bind; [apply raw_realloc_E; exact HK|]. intros r. apply IH. exact (H r).
Qed.
End AllocE.

Section Interp.
Context {CE__ : Ceiling}.
Variable G : PState -> Model -> Prop.
Hypothesis HG : frame_ok G.
Variable P : Z -> Z.
Variable ok : list (bptr * Z) -> Z -> Prop.
Variable F : list (bptr * Z).
Hypothesis Hok : forall X n, 0 <= n -> ok X n -> mal_okP P (X ++ F) n.

Lemma fresh_app_l : forall (q : bptr) X, ~ In (fst q) (slotsX (X ++ F)) -> ~ In (fst q) (slotsX X).
Proof. intros q X H Hin. apply H. rewrite slotsX_app. apply in_or_app. left. exact Hin. Qed.

Theorem interp_N : forall {A} (t : lprog A) X (Q : A -> list (bptr * Z) -> Prop),
  lwf ok t X Q ->
  mspecN (OQ G P (X ++ F)) (interp t) (fun a s mo => exists X', Q a X' /\ OQ G P (X' ++ F) s mo).
Proof.
  intros A t. induction t as [a| |n k IH|p k IH|p n k IH]; intros X Q H; cbn [interp lwf] in *.
  - apply mspecN_ret. intros s mo HO. exists X. split; [exact H| exact HO].
  - destruct H.
  - destruct H as (Hn & Ho & HN & Hk).
    eapply mspecN_bind.
    { eapply mspecN_pre; [apply (raw_malloc_N G HG P (X ++ F) n Hn)|]. intros s mo HO. split; [exact HO| apply Hok; [exact (proj1 Hn)| exact Ho]]. }
    intros r. apply mspecN_pointwise. intros s1 mo1 (q & -> & HO1).
    eapply mspecN_pre; [apply (IH (Some q) ((q, n) :: X) Q); apply Hk; apply fresh_app_l; exact (OQ_fresh G P _ _ _ _ _ HO1)|].
    intros s mo [-> ->]. exact HO1.
  - destruct H as (m & X' & HP & Hk).
    eapply mspecN_seq with (R := OQ G P (X' ++ F)).
    { eapply mspecN_pre; [apply (raw_free_N G HG P (X' ++ F) p m)|]. intros s mo HO.
      eapply OQ_perm; [|exact HO]. change ((p, m) :: X' ++ F) with (((p, m) :: X') ++ F). apply Permutation_app_tail. exact HP. }
    intros _. apply IH. exact Hk.
  - destruct H as (m & X' & HP & Hn & Hc & Ho & HN & Hk).
    assert (HPF : Permutation (X ++ F) ((p, m) :: X' ++ F)).
    { change ((p, m) :: X' ++ F) with (((p, m) :: X') ++ F). apply Permutation_app_tail. exact HP. }
    eapply mspecN_bind.
    { eapply mspecN_pre; [apply (raw_realloc_N G HG P (X' ++ F) p m n Hn Hc)|]. intros s mo HO. split.
      - eapply OQ_perm; [exact HPF| exact HO].
      - destruct (Hok X n (proj1 Hn) Ho) as [[R1 R2] HB]. unfold mal_okP, ROOMX.
        unfold LRX, n63X in *. rewrite <- !(zcount_perm _ _ _ HPF). unfold R63X in *.
        rewrite <- (zsum_map_perm _ _ _ HPF). auto. }
    intros r. apply mspecN_pointwise. intros s1 mo1 (q & -> & HO1 & Hfr).
    eapply mspecN_pre; [apply (IH (Some q) ((q, n) :: X') Q); apply Hk|].
    + intros Hin. apply Hfr. unfold slotsX in *.
      assert (Hin' : In (fst q) (map (fun xb : bptr * Z => fst (fst xb)) (X ++ F))) by (rewrite map_app; apply in_or_app; left; exact Hin).
      eapply Permutation_in; [apply Permutation_map; exact HPF| exact Hin'].
    + intros s mo [-> ->]. exact HO1.
Qed.

Theorem interp_L : forall {A} (t : lprog A) X (Q : A -> list (bptr * Z) -> Prop),
  lwf ok t X Q ->
  mspecL LBUDGET (QI (X ++ F) P) (interp t) (fun a s mo => exists X', Q a X' /\ QI (X' ++ F) P s mo).
Proof.
  intros A t. induction t as [a| |n k IH|p k IH|p n k IH]; intros X Q H; cbn [interp lwf] in *.
  - apply mspecL_ret. intros s mo HO. exists X. split; [exact H| exact HO].
  - destruct H.
  - destruct H as (Hn & Ho & HN & Hk).
    eapply mspecL_bind.
    { eapply mspecL_pre; [apply (raw_malloc_LQ (X ++ F) P n (proj1 Hn))|]. intros s mo HO. split; [exact HO| apply Hok; [exact (proj1 Hn)| exact Ho]]. }
    intros [q|]; [|rewrite HN; cbn [interp]; apply mspecL_munr].
    apply mspecL_pointwise. intros s1 mo1 [HO1 _].
    eapply mspecL_pre; [apply (IH (Some q) ((q, n) :: X) Q); apply Hk; apply fresh_app_l; exact (QI_fresh P _ _ _ _ _ HO1)|].
    intros s mo [-> ->]. exact HO1.
  - destruct H as (m & X' & HP & Hk).
    eapply mspecL_seq with (R := QI (X' ++ F) P).
    { eapply mspecL_pre; [apply (raw_free_LQ (X' ++ F) P p m)|]. intros s mo HO.
      eapply QI_perm; [|exact HO]. change ((p, m) :: X' ++ F) with (((p, m) :: X') ++ F). apply Permutation_app_tail. exact HP. }
    intros _. apply IH. exact Hk.
  - destruct H as (m & X' & HP & Hn & Hc & Ho & HN & Hk).
    assert (HPF : Permutation (X ++ F) ((p, m) :: X' ++ F)).
    { change ((p, m) :: X' ++ F) with (((p, m) :: X') ++ F). apply Permutation_app_tail. exact HP. }
    eapply mspecL_bind.
    { eapply mspecL_pre; [apply (raw_realloc_L P (X' ++ F) p m n (proj1 Hn))|]. intros s mo HO. split.
      - eapply QI_perm; [exact HPF| exact HO].
      - destruct (Hok X n (proj1 Hn) Ho) as [[R1 R2] HB]. unfold mal_okP, ROOMX.
        unfold LRX, n63X in *. rewrite <- !(zcount_perm _ _ _ HPF). unfold R63X in *.
        rewrite <- (zsum_map_perm _ _ _ HPF). auto. }
    intros [q|]; [|rewrite HN; cbn [interp]; apply mspecL_munr].
    apply mspecL_pointwise. intros s1 mo1 [HO1 Hfr].
    eapply mspecL_pre; [apply (IH (Some q) ((q, n) :: X') Q); apply Hk|].
    + intros Hin. apply Hfr. unfold slotsX in *.
      assert (Hin' : In (fst q) (map (fun xb : bptr * Z => fst (fst xb)) (X ++ F))) by (rewrite map_app; apply in_or_app; left; exact Hin).
      eapply Permutation_in; [apply Permutation_map; exact HPF| exact Hin'].
    + intros s mo [-> ->]. exact HO1.
Qed.

End Interp.
