(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma flat_map_app' : forall {A B} (f : A -> list B) l1 l2, flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. intros. apply flat_map_app. Qed.

Lemma flat_map_filter_perm : forall {A B} (f : A -> list B) (p : A -> bool) l,
  Permutation (flat_map f l) (flat_map f (filter p l) ++ flat_map f (filter (fun x => negb (p x)) l)).
Proof.
  intros A B f p l. induction l as [|x t IH]; [reflexivity|].
  cbn [flat_map filter]. destruct (p x); cbn [negb flat_map].
  - rewrite <- app_assoc. apply Permutation_app_head. exact IH.
  - rewrite app_assoc. eapply Permutation_trans; [| apply Permutation_app_tail; apply Permutation_app_comm ].
    rewrite <- app_assoc. apply Permutation_app_head. exact IH.
Qed.

Lemma flat_map_map' : forall {A B C} (f : B -> list C) (g : A -> B) l, flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. intros. induction l as [|x t IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma perm4 : forall {A} (a b c d : list A), Permutation (a ++ b ++ c ++ d) (b ++ d ++ a ++ c).
Proof.
  intros A a b c d. eapply Permutation_trans; [apply Permutation_app_swap_app|].
  apply Permutation_app_head. rewrite app_assoc. apply Permutation_app_comm.
Qed.

Lemma perm_surgery : forall {A} (C H MS Mo G Go : list A),
  Permutation (C ++ (H ++ MS ++ Mo) ++ G ++ Go) ((C ++ H ++ Mo ++ Go) ++ MS ++ G).
Proof.
  intros A C H MS Mo G Go. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
  apply perm4.
Qed.

Lemma flat_map_ext_in' : forall {A B} (f g : A -> list B) l, (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof.
  intros A B f g l H. induction l as [|x t IH]; [reflexivity|]. cbn. rewrite H by (left; reflexivity).
  rewrite IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma filter_none : forall {A} (eqb : A -> A -> bool) (l : list A) x,
  (forall a b, eqb a b = true <-> a = b) -> ~ In x l -> filter (fun y => eqb y x) l = [].
Proof.
  intros A eqb l x Heq Hn. induction l as [|y t IH]; [reflexivity|]. cbn [filter].
  destruct (eqb y x) eqn:E.
  - apply Heq in E. subst y. exfalso. apply Hn. left. reflexivity.
  - apply IH. intro Hc. apply Hn. right. exact Hc.
Qed.

Lemma filter_single : forall {A} (eqb : A -> A -> bool) (l : list A) x,
  (forall a b, eqb a b = true <-> a = b) -> NoDup l -> In x l ->
  filter (fun y => eqb y x) l = [x].
Proof.
  intros A eqb l x Heq ND Hin. induction l as [|y t IH]; [destruct Hin|].
  inversion ND as [|y' t' Hy Ht]; subst. cbn [filter].
  destruct (eqb y x) eqn:E.
  - apply Heq in E. subst y. rewrite (filter_none eqb t x Heq Hy). reflexivity.
  - destruct Hin as [Ey|Hin]; [subst y; exfalso; rewrite (proj2 (Heq x x) eq_refl) in E; discriminate|].
    apply IH; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aslot (a : sptr) (k : nat) : sptr := padd a (AREA_HDR + META_SIZE * Z.of_nat k).
Definition aslots (a : sptr) : list sptr := map (aslot a) (seq 0 (Z.to_nat METAS_PER_AREA)).
Definition all_slots (l : list sptr) : list sptr := flat_map aslots l.

Fixpoint ahdr (l : list sptr) : list mcell :=
  match l with
  | [] => []
  | a :: t => [MCell (LMem a) 8 VSec; MCell (LMem (padd a 8)) 8 (optr (hd_error t)); MCell (LMem (padd a 16)) 4 (VZ METAS_PER_AREA)]
              ++ ahdr t
  end.

Definition mcells (ms : list (sptr * mslot)) (q : sptr) : list mcell := meta_slot_cells q (mlookup ms q).

Lemma areas_cells_perm : forall s l,
  Permutation (areas_cells s l) (ahdr l ++ flat_map (mcells (st_metas s)) (all_slots l)).
Proof.
  intros s l. induction l as [|a t IH]; [reflexivity|].
  cbn [areas_cells ahdr all_slots flat_map]. unfold area_cells.
  rewrite flat_map_app'.
  assert (E : flat_map (fun k => meta_slot_cells (padd a (AREA_HDR + META_SIZE * Z.of_nat k))
                                      (mlookup (st_metas s) (padd a (AREA_HDR + META_SIZE * Z.of_nat k))))
                       (seq 0 (Z.to_nat METAS_PER_AREA))
              = flat_map (mcells (st_metas s)) (aslots a)).
  { unfold aslots, mcells, aslot. rewrite flat_map_map'. reflexivity. }
  rewrite E. rewrite <- !app_assoc. apply Permutation_app_head.
  eapply Permutation_trans; [apply Permutation_app_head; exact IH|].
  rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.

(* [comment removed for export] *)
Lemma aslot_inj : forall r1 o1 r2 o2 k1 k2,
  o1 mod PGSZ = 0 -> o2 mod PGSZ = 0 -> (k1 < 101)%nat -> (k2 < 101)%nat ->
  aslot (SP r1 o1) k1 = aslot (SP r2 o2) k2 -> r1 = r2 /\ o1 = o2 /\ k1 = k2.
Proof.
  intros r1 o1 r2 o2 k1 k2 H1 H2 K1 K2 E. unfold aslot in E.
  pose proof (f_equal prid E) as Er. pose proof (f_equal poff E) as Eo. cbn [prid poff padd] in Er, Eo.
  change AREA_HDR with 24 in Eo. change META_SIZE with 40 in Eo.
  unfold PGSZ in *. split; [exact Er|].
  assert (o1 = o2).
  { assert (A1 : o1 = 4096 * (o1 / 4096)) by (pose proof (Z.div_mod o1 4096 ltac:(lia)); lia).
    assert (A2 : o2 = 4096 * (o2 / 4096)) by (pose proof (Z.div_mod o2 4096 ltac:(lia)); lia).
    lia. }
  split; [exact H|]. subst. lia.
Qed.

Lemma NoDup_aslots : forall a, NoDup (aslots a).
Proof.
  intros [r o]. unfold aslots. apply Finite.Injective_map_NoDup; [|apply seq_NoDup].
  intros k1 k2 E. unfold aslot in E. pose proof (f_equal poff E) as Eo. cbn [poff padd] in Eo.
  change AREA_HDR with 24 in Eo. change META_SIZE with 40 in Eo. lia.
Qed.

Lemma In_aslots : forall a q, In q (aslots a) <-> exists k, (k < 101)%nat /\ q = aslot a k.
Proof.
  intros a q. unfold aslots. rewrite in_map_iff. split.
  - intros (k & E & Hk). apply in_seq in Hk. exists k. split; [cbn in Hk; lia | symmetry; exact E].
  - intros (k & Hk & E). exists k. split; [symmetry; exact E | apply in_seq; cbn; lia].
Qed.

Lemma NoDup_all_slots : forall l,
  NoDup l -> (forall a, In a l -> exists r o, a = SP r o /\ o mod PGSZ = 0) -> NoDup (all_slots l).
Proof.
  intros l ND Hal. induction l as [|a t IH]; [constructor|].
  inversion ND as [|a' t' Ha Ht]; subst. cbn [all_slots flat_map]. fold (all_slots t).
  apply NoDup_app; [apply NoDup_aslots | apply IH; [exact Ht | intros b Hb; apply Hal; right; exact Hb] |].
  intros q Hq1 Hq2. apply In_aslots in Hq1 as (k1 & K1 & E1).
  unfold all_slots in Hq2. apply in_flat_map in Hq2 as (b & Hb & Hq2). apply In_aslots in Hq2 as (k2 & K2 & E2).
  destruct (Hal a ltac:(left; reflexivity)) as (ra & oa & -> & Ha1).
  destruct (Hal b ltac:(right; exact Hb)) as (rb & ob & -> & Hb1).
  subst q. destruct (aslot_inj ra oa rb ob k1 k2 Ha1 Hb1 K1 K2 E2) as (-> & -> & _).
  apply Ha. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma key_once : forall s g, WF s -> In g (keys s) ->
  filter (fun q => sptr_eqb q g) (all_slots (st_areas s)) = [g].
Proof.
  intros s g HW Hg. apply filter_single; [apply sptr_eqb_eq | |].
  - pose proof (inv_areas HW) as (AND & AOK & _). apply NoDup_all_slots; [exact AND|].
    intros a Ha. destruct (AOK a Ha) as (r & o & rg & E & Ho & _). exists r, o. auto.
  - pose proof (inv_keys HW) as (_ & KP & _). destruct (KP g Hg) as (a & k & Ha & Hk & E).
    unfold all_slots. apply in_flat_map. exists a. split; [exact Ha|]. apply In_aslots.
    assert (Hh : handed s a <= METAS_PER_AREA) by (unfold handed; destruct (sptr_eqb _ _); pose proof (proj2 (proj2 (proj2 (proj2 (inv_keys HW))))); lia).
    exists (Z.to_nat k). split; [unfold METAS_PER_AREA in Hh; lia|]. unfold aslot. rewrite Z2Nat.id by lia. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition gcells (gm : sptr * ameta) : list mcell := group_cells (fst gm) (snd gm).

Lemma filter_key_none : forall {X} (l : list (sptr * X)) g,
  ~ In g (map fst l) -> filter (fun gm => sptr_eqb (fst gm) g) l = [].
Proof.
  intros X l g Hn. induction l as [|[q x] t IH]; [reflexivity|]. cbn [filter fst].
  destruct (sptr_eqb q g) eqn:E.
  - apply sptr_eqb_eq in E. subst q. exfalso. apply Hn. left. reflexivity.
  - apply IH. intro Hc. apply Hn. right. exact Hc.
Qed.

Lemma filter_key_single : forall {X} (l : list (sptr * X)) g x,
  NoDup (map fst l) -> In (g, x) l -> filter (fun gm => sptr_eqb (fst gm) g) l = [(g, x)].
Proof.
  intros X l g x ND Hin. induction l as [|[q y] t IH]; [destruct Hin|].
  cbn [map] in ND. inversion ND as [|q' t' Hq Ht]; subst. cbn [filter fst].
  destruct (sptr_eqb q g) eqn:E.
  - apply sptr_eqb_eq in E. subst q. rewrite (filter_key_none t g Hq).
    destruct Hin as [Eh|Hin]; [injection Eh as ->; reflexivity|].
    exfalso. apply Hq. apply in_map_iff. exists (g, x). auto.
  - destruct Hin as [Eh|Hin]; [injection Eh as -> _; rewrite sptr_eqb_refl in E; discriminate|].
    apply IH; assumption.
Qed.

Lemma used_once : forall s g am, WF s -> In (g, am) (used_metas s) ->
  filter (fun gm => sptr_eqb (fst gm) g) (used_metas s) = [(g, am)].
Proof.
  intros s g am HW Hin. apply filter_key_single; [|exact Hin].
  exact (NoDup_used_metas_keys s (proj1 (inv_keys HW))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition set_meta (s : astate) (g : sptr) (x : mslot) : astate := set_metas (mupdate (st_metas s) g x) s.

Lemma image_decomp : forall s g am, WF s -> MT s g = Some (MUsed am) ->
  Permutation (image s)
    ((ctx_cells s ++ ahdr (st_areas s)
       ++ flat_map (mcells (st_metas s)) (filter (fun q => negb (sptr_eqb q g)) (all_slots (st_areas s)))
       ++ flat_map gcells (filter (fun gm => negb (sptr_eqb (fst gm) g)) (used_metas s)))
     ++ meta_slot_cells g (Some (MUsed am)) ++ group_cells g am).
Proof.
  intros s g am HW Hg.
  assert (Hkey : In g (keys s)) by (unfold keys; eapply mlookup_In_keys; exact Hg).
  assert (Hused : In (g, am) (used_metas s)).
  { apply (used_metas_iff s g am (proj1 (inv_keys HW))). exact Hg. }
  unfold image.
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; apply areas_cells_perm|].
  eapply Permutation_trans.
  { apply Permutation_app_head. apply Permutation_app_head. apply (flat_map_filter_perm gcells (fun gm => sptr_eqb (fst gm) g)). }
  eapply Permutation_trans.
  { apply Permutation_app_head. apply Permutation_app_tail. apply Permutation_app_head.
    apply (flat_map_filter_perm (mcells (st_metas s)) (fun q => sptr_eqb q g)). }
  rewrite (key_once s g HW Hkey), (used_once s g am HW Hused).
  cbn [flat_map]. rewrite !app_nil_r. unfold mcells at 1, gcells at 1.
  change (mlookup (st_metas s) g) with (MT s g). rewrite Hg. cbn [fst snd].
  apply perm_surgery.
Qed.

Lemma mlookup_set_other : forall s g x q, q <> g -> mlookup (st_metas (set_meta s g x)) q = mlookup (st_metas s) q.
Proof. intros s g x q Hne. unfold set_meta. cbn [st_metas set_metas]. apply mlookup_mupdate_other. exact Hne. Qed.

Lemma used_metas_set_filter : forall s g am',
  filter (fun gm => negb (sptr_eqb (fst gm) g)) (used_metas (set_meta s g (MUsed am')))
  = filter (fun gm => negb (sptr_eqb (fst gm) g)) (used_metas s).
Proof.
  intros s g am'. unfold set_meta, used_metas. cbn [st_metas set_metas].
  induction (st_metas s) as [|[q x] t IH]; cbn [mupdate].
  - cbn [flat_map app filter fst]. rewrite sptr_eqb_refl. reflexivity.
  - destruct (sptr_eqb g q) eqn:E.
    + apply sptr_eqb_eq in E. subst q. cbn [flat_map app].
      destruct x as [pr nx| |am]; cbn [filter fst app]; try rewrite sptr_eqb_refl; cbn [negb]; reflexivity.
    + cbn [flat_map]. rewrite !filter_app. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma image_setm : forall s g am am', WF s -> MT s g = Some (MUsed am) ->
  exists U, Permutation (image s) (U ++ meta_slot_cells g (Some (MUsed am)) ++ group_cells g am) /\
            Permutation (image (set_meta s g (MUsed am'))) (U ++ meta_slot_cells g (Some (MUsed am')) ++ group_cells g am').
Proof.
  intros s g am am' HW Hg. eexists. split; [apply image_decomp; assumption|].
  set (s' := set_meta s g (MUsed am')).
  assert (Hg' : MT s' g = Some (MUsed am')).
  { unfold s', set_meta, MT. cbn [st_metas set_metas]. apply mlookup_mupdate_same. }
  unfold image.
  (* [comment removed for export] *)
  assert (Hkey : In g (keys s)) by (unfold keys; eapply mlookup_In_keys; exact Hg).
  assert (KO : filter (fun q => sptr_eqb q g) (all_slots (st_areas s')) = [g]) by (exact (key_once s g HW Hkey)).
  assert (NDK : NoDup (keys s')).
  { unfold s', set_meta, keys. cbn [st_metas set_metas]. rewrite map_fst_mupdate_In by exact Hkey. exact (proj1 (inv_keys HW)). }
  assert (UO : filter (fun gm => sptr_eqb (fst gm) g) (used_metas s') = [(g, am')]).
  { apply filter_key_single; [exact (NoDup_used_metas_keys s' NDK)|].
    apply (used_metas_iff s' g am' NDK). exact Hg'. }
  eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_app_tail; apply areas_cells_perm|].
  eapply Permutation_trans.
  { apply Permutation_app_head. apply Permutation_app_head. apply (flat_map_filter_perm gcells (fun gm => sptr_eqb (fst gm) g)). }
  eapply Permutation_trans.
  { apply Permutation_app_head. apply Permutation_app_tail. apply Permutation_app_head.
    apply (flat_map_filter_perm (mcells (st_metas s')) (fun q => sptr_eqb q g)). }
  rewrite KO, UO. cbn [flat_map]. rewrite !app_nil_r. unfold mcells at 1, gcells at 1.
  change (mlookup (st_metas s') g) with (MT s' g). rewrite Hg'. cbn [fst snd].
  replace (ctx_cells s') with (ctx_cells s) by reflexivity.
  replace (st_areas s') with (st_areas s) by reflexivity.
  replace (filter (fun gm : sptr * ameta => negb (sptr_eqb (fst gm) g)) (used_metas s'))
    with (filter (fun gm : sptr * ameta => negb (sptr_eqb (fst gm) g)) (used_metas s)) by (symmetry; exact (used_metas_set_filter s g am')).
  replace (flat_map (mcells (st_metas s')) (filter (fun q => negb (sptr_eqb q g)) (all_slots (st_areas s))))
    with (flat_map (mcells (st_metas s)) (filter (fun q => negb (sptr_eqb q g)) (all_slots (st_areas s)))).
  2:{ apply flat_map_ext_in'. intros q Hq. apply filter_In in Hq as [_ Hq]. unfold mcells.
      change (mlookup (st_metas s') q) with (mlookup (st_metas (set_meta s g (MUsed am'))) q).
      rewrite (mlookup_set_other s g (MUsed am') q); [reflexivity|]. intro E. subst q. rewrite sptr_eqb_refl in Hq. discriminate. }
  apply perm_surgery.
Qed.
