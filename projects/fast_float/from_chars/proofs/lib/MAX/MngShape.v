(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngLt MngGeoX MngNtfC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint ileaf {A : Type} (t : itree astate A) (Q : A -> Prop) : Prop :=
  match t with
  | IRet a => Q a
  | IFail _ => True
  | IAsk _ _ k => forall z, ileaf (k z) Q
  end.

Lemma ileaf_ibind : forall {A B} (t : itree astate A) (k : A -> itree astate B) (Q : B -> Prop),
  ileaf t (fun a => ileaf (k a) Q) -> ileaf (ibind t k) Q.
Proof.
  intros A B t k Q. induction t as [a | q sn c IH | f]; cbn; intros H; [exact H | intros z; apply IH, H | exact I].
Qed.

Lemma ileaf_bind : forall {A B} (m : M B) (k : B -> M A) s Q,
  ileaf (m s) (fun r => ileaf (k (fst r) (snd r)) Q) -> ileaf (bind m k s) Q.
Proof.
  intros A B m k s Q H. unfold bind. apply ileaf_ibind. revert H. generalize (m s). intros t H.
  induction t as [a | q sn c IH | f]; cbn in *; [destruct a; exact H | intros z; apply IH, H | exact I].
Qed.

Lemma ileaf_ret_eq : forall {A} (t : itree astate A) Q a, ileaf t Q -> t = IRet a -> Q a.
Proof. intros A t Q a H ->. exact H. Qed.

Ltac lstep := repeat lazymatch goal with |- ileaf (bind _ _ _) _ => apply ileaf_bind end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gshape (a b : ameta) : Prop :=
  am_mem a = am_mem b /\ am_maplen a = am_maplen b /\ am_last a = am_last b /\ am_sc a = am_sc b /\ am_slots a = am_slots b.

(* [comment removed for export] *)
Definition mshape (x y : mslot) : Prop :=
  match x, y with
  | MUsed a, MUsed b => gshape a b
  | MUsed _, _ => False
  | _, MUsed _ => False
  | _, _ => True
  end.

Definition SHP (s s' : astate) : Prop :=
  st_areas s' = st_areas s /\ st_regions s' = st_regions s /\
  Forall2 (fun e e' => fst e = fst e' /\ mshape (snd e) (snd e')) (st_metas s) (st_metas s') /\ st_usage s' = st_usage s /\
  st_init_done s' = st_init_done s.

Lemma gshape_refl : forall a, gshape a a.
Proof. intros a. repeat split. Qed.

Lemma gshape_trans : forall a b c, gshape a b -> gshape b c -> gshape a c.
Proof. intros a b c (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5). repeat split; congruence. Qed.

Lemma mshape_refl : forall x, mshape x x.
Proof. intros [pr nx| |a]; cbn; [exact I | exact I | apply gshape_refl]. Qed.

Lemma mshape_trans : forall x y z, mshape x y -> mshape y z -> mshape x z.
Proof.
  intros [pr nx| |a] [pr' nx'| |b] [pr'' nx''| |c]; cbn; try tauto. apply gshape_trans.
Qed.

Lemma Forall2_refl' : forall {A} (P : A -> A -> Prop) l, (forall x, P x x) -> Forall2 P l l.
Proof. intros A P l H. induction l as [|x t IH]; constructor; [apply H | exact IH]. Qed.

Lemma Forall2_trans' : forall {A} (P : A -> A -> Prop) l1 l2 l3, (forall x y z, P x y -> P y z -> P x z) ->
  Forall2 P l1 l2 -> Forall2 P l2 l3 -> Forall2 P l1 l3.
Proof.
  intros A P l1 l2 l3 HT H12. revert l3. induction H12 as [|x y t1 t2 Hxy H12 IH]; intros l3 H23; [exact H23|].
  inversion H23 as [|y' z t2' t3 Hyz H23']; subst. constructor; [exact (HT _ _ _ Hxy Hyz) | exact (IH _ H23')].
Qed.

Lemma SHP_refl : forall s, SHP s s.
Proof. intros s. split; [reflexivity|]. split; [reflexivity|]. split; [|split; reflexivity]. apply Forall2_refl'. intros e. split; [reflexivity | apply mshape_refl]. Qed.

Lemma SHP_trans : forall s1 s2 s3, SHP s1 s2 -> SHP s2 s3 -> SHP s1 s3.
Proof.
  intros s1 s2 s3 (A1 & B1 & C1 & D1 & E1) (A2 & B2 & C2 & D2 & E2). split; [congruence|]. split; [congruence|]. split; [|split; congruence].
  apply (Forall2_trans' _ _ _ _ (fun e1 e2 e3 H1 H2 => conj (eq_trans (proj1 H1) (proj1 H2)) (mshape_trans _ _ _ (proj2 H1) (proj2 H2))) C1 C2).
Qed.

(* [comment removed for export] *)
Lemma mupdate_shape : forall l p x y, mlookup l p = Some x -> mshape x y ->
  Forall2 (fun e e' => fst e = fst e' /\ mshape (snd e) (snd e')) l (mupdate l p y).
Proof.
  induction l as [|[q z] t IH]; intros p x y Hl Hs; cbn in Hl |- *; [discriminate|].
  destruct (sptr_eqb p q) eqn:E.
  - injection Hl as ->. constructor; [split; [reflexivity | exact Hs] | apply Forall2_refl'; intros e; split; [reflexivity | apply mshape_refl]].
  - constructor; [split; [reflexivity | apply mshape_refl] | exact (IH p x y Hl Hs)].
Qed.

Lemma SHP_set_metas : forall s p x y, mlookup (st_metas s) p = Some x -> mshape x y -> SHP s (set_metas (mupdate (st_metas s) p y) s).
Proof.
  intros s p x y Hl Hs. split; [reflexivity|]. split; [reflexivity|]. split; [|split; reflexivity]. cbn [st_metas set_metas]. exact (mupdate_shape _ p x y Hl Hs).
Qed.

Lemma SHP_ctx : forall s s', st_metas s' = st_metas s -> st_areas s' = st_areas s -> st_regions s' = st_regions s -> st_usage s' = st_usage s ->
  st_init_done s' = st_init_done s -> SHP s s'.
Proof.
  intros s s' E1 E2 E3 E4 E5. split; [exact E2|]. split; [exact E3|]. split; [|split; [exact E4 | exact E5]]. rewrite E1. apply Forall2_refl'. intros e. split; [reflexivity | apply mshape_refl].
Qed.

Lemma mshape_links : forall x pr nx, mshape x (with_links x pr nx).
Proof. intros [p0 n0| |a] pr nx; cbn; [exact I | exact I | repeat split]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cshape (c : mcell) : loc * nat := (mc_loc c, mc_w c).

Lemma cell_range_cshape : forall L c, cell_range L c = (loc_addr L (fst (cshape c)), Z.of_nat (snd (cshape c))).
Proof. intros L c. reflexivity. Qed.

Lemma ranges_of_shapes : forall L (l l' : list mcell), map cshape l' = map cshape l -> map (cell_range L) l' = map (cell_range L) l.
Proof.
  intros L l l' E.
  assert (F : forall k, map (cell_range L) k = map (fun p => (loc_addr L (fst p), Z.of_nat (snd p))) (map cshape k)) by (intros k; rewrite map_map; reflexivity).
  rewrite (F l'), (F l), E. reflexivity.
Qed.

Lemma stride_gshape : forall a b, gshape a b -> stride_of a = stride_of b.
Proof. intros a b (A1 & A2 & A3 & A4 & A5). unfold stride_of. rewrite A2, A3, A4. reflexivity. Qed.

Lemma slot_cells_shape : forall a b i, gshape a b -> map cshape (slot_cells b i) = map cshape (slot_cells a i).
Proof.
  intros a b i G. pose proof G as (A1 & A2 & A3 & A4 & A5).
  assert (ES : slot_start b i = slot_start a i) by (unfold slot_start; rewrite (stride_gshape a b G), A1; reflexivity).
  assert (EN : nth_slot b i = nth_slot a i) by (unfold nth_slot; rewrite A5; reflexivity).
  unfold slot_cells. rewrite ES, EN. rewrite !map_app. f_equal. f_equal.
  destruct (ss_fr (nth_slot a i)) as [fr|]; [|reflexivity]. destruct (fr_off fr =? 0); reflexivity.
Qed.

Lemma group_cells_shape : forall g a b, gshape a b -> map cshape (group_cells g b) = map cshape (group_cells g a).
Proof.
  intros g a b G. pose proof G as (A1 & A2 & A3 & A4 & A5). unfold group_cells. rewrite !map_app. rewrite A1, A2, A3.
  f_equal; [destruct (am_maplen b =? 0); reflexivity|]. revert G. generalize (zseq 0 (am_last b + 1)). intros l G. induction l as [|i t IH]; [reflexivity|].
  cbn [flat_map]. rewrite !map_app, IH. f_equal. exact (slot_cells_shape a b i G).
Qed.

Lemma mlookup_F2 : forall l l' q, Forall2 (fun e e' => fst e = fst e' /\ mshape (snd e) (snd e')) l l' ->
  match mlookup l q, mlookup l' q with
  | Some x, Some y => mshape x y
  | None, None => True
  | _, _ => False
  end.
Proof.
  intros l l' q H. induction H as [|[p x] [p' y] t t' (E1 & E2) H IH]; [exact I|]. cbn [fst snd] in E1, E2. subst p'. cbn.
  destruct (sptr_eqb q p); [exact E2 | exact IH].
Qed.

Lemma msc_shape : forall q x y, map cshape (meta_slot_cells q y) = map cshape (meta_slot_cells q x).
Proof. intros q x y. destruct x as [[pr nx| |a]|]; destruct y as [[pr' nx'| |b]|]; reflexivity. Qed.

Lemma area_cells_shape : forall s s' a n, map cshape (area_cells s' a n) = map cshape (area_cells s a n).
Proof.
  intros s s' a n. unfold area_cells. rewrite !map_app. f_equal. generalize (seq 0 (Z.to_nat METAS_PER_AREA)). intros l.
  induction l as [|k t IH]; [reflexivity|]. cbn [flat_map]. rewrite !map_app, IH. f_equal. apply msc_shape.
Qed.

Lemma areas_cells_shape : forall s s' l, map cshape (areas_cells s' l) = map cshape (areas_cells s l).
Proof.
  intros s s' l. induction l as [|a t IH]; [reflexivity|]. cbn [areas_cells]. rewrite !map_app, IH. f_equal. apply area_cells_shape.
Qed.

Lemma used_F2 : forall l l', Forall2 (fun e e' => fst e = fst e' /\ mshape (snd e) (snd e')) l l' ->
  map cshape (flat_map (fun gm : sptr * ameta => group_cells (fst gm) (snd gm))
       (flat_map (fun e : sptr * mslot => match e with (p, MUsed am) => [(p, am)] | _ => [] end) l')) =
  map cshape (flat_map (fun gm : sptr * ameta => group_cells (fst gm) (snd gm))
       (flat_map (fun e : sptr * mslot => match e with (p, MUsed am) => [(p, am)] | _ => [] end) l)).
Proof.
  intros l l' H. induction H as [|[p x] [p' y] t t' (E1 & E2) H IH]; [reflexivity|]. cbn [fst snd] in E1, E2. subst p'.
  cbn [flat_map]. rewrite !flat_map_app, !map_app, IH. f_equal.
  destruct x as [pr nx| |a]; destruct y as [pr' nx'| |b]; cbn in E2; try contradiction; cbn; try reflexivity.
  rewrite !app_nil_r. exact (group_cells_shape p a b E2).
Qed.

Theorem image_shape : forall s s', SHP s s' -> map cshape (image s') = map cshape (image s).
Proof.
  intros s s' (A & _ & C & _ & _). unfold image. rewrite !map_app.
  assert (E1 : map cshape (ctx_cells s') = map cshape (ctx_cells s)) by reflexivity.
  assert (E2 : map cshape (areas_cells s' (st_areas s')) = map cshape (areas_cells s (st_areas s))) by (rewrite A; apply areas_cells_shape).
  assert (E3 : map cshape (flat_map (fun gm : sptr * ameta => group_cells (fst gm) (snd gm)) (used_metas s')) =
               map cshape (flat_map (fun gm : sptr * ameta => group_cells (fst gm) (snd gm)) (used_metas s))) by (unfold used_metas; exact (used_F2 _ _ C)).
  rewrite E1, E2, E3. reflexivity.
Qed.

Corollary image_ranges : forall L s s', SHP s s' -> map (cell_range L) (image s') = map (cell_range L) (image s).
Proof. intros L s s' H. apply ranges_of_shapes. exact (image_shape s s' H). Qed.

(* [comment removed for export] *)
Corollary image_persist : forall L s s', SHP s s' -> forall c, In c (image s) -> exists c', In c' (image s') /\ cell_range L c' = cell_range L c.
Proof.
  intros L s s' H c Hc. pose proof (image_ranges L s s' H) as E.
  destruct (In_nth _ _ c Hc) as (k & Hk & Ek).
  assert (Hk' : (k < length (image s'))%nat) by (rewrite <- (length_map (cell_range L) (image s')), E, length_map; exact Hk).
  exists (nth k (image s') c). split; [apply nth_In; exact Hk'|].
  rewrite <- (map_nth (cell_range L) (image s') c k), E, map_nth, Ek. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma MT_shape : forall s s' q, SHP s s' ->
  match MT s q, MT s' q with Some x, Some y => mshape x y | None, None => True | _, _ => False end.
Proof. intros s s' q (_ & _ & C & _ & _). unfold MT. exact (mlookup_F2 _ _ q C). Qed.

Lemma XNU_shape : forall X s s', SHP s s' -> XNU X s -> XNU X s'.
Proof.
  intros X s s' H HX x Hx a E. pose proof (MT_shape s s' x H) as M. rewrite E in M.
  destruct (MT s x) as [[pr nx| |b]|] eqn:E0; try contradiction. exact (HX x Hx b E0).
Qed.

Lemma XNM_of_Xok : forall X s, Xok X s -> XNU X s -> XNM X s.
Proof.
  intros X s HOK HU x Hx. destruct (HOK x Hx) as (_ & Hm). destruct (MT s x) as [[[p|] [n|]| |a]|] eqn:E; try contradiction.
  - right. reflexivity.
  - left. reflexivity.
  - exfalso. exact (HU x Hx a E).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ileaf_mono : forall {A} (t : itree astate A) (Q Q' : A -> Prop), (forall a, Q a -> Q' a) -> ileaf t Q -> ileaf t Q'.
Proof. intros A t Q Q' HQ. induction t as [a | q sn k IH | f]; cbn; [apply HQ | intros H z; apply IH, H | auto]. Qed.

Lemma ileaf_bind_shp : forall {A B} (m : M B) (k : B -> M A) s,
  ileaf (m s) (fun r => SHP s (snd r)) -> (forall b s1, SHP s s1 -> ileaf (k b s1) (fun r => SHP s1 (snd r))) ->
  ileaf (bind m k s) (fun r => SHP s (snd r)).
Proof.
  intros A B m k s H1 H2. apply ileaf_bind. eapply ileaf_mono; [|exact H1]. intros [b s1] S1. cbn [fst snd] in *.
  apply (ileaf_mono _ _ _ (fun r H => SHP_trans _ _ _ S1 H)). exact (H2 b s1 S1).
Qed.

Lemma ileaf_bind_getm : forall {A} p (k : ameta -> M A) s,
  (forall am, mlookup (st_metas s) p = Some (MUsed am) -> ileaf (k am s) (fun r => SHP s (snd r))) ->
  ileaf (bind (getm p) k s) (fun r => SHP s (snd r)).
Proof.
  intros A p k s H. apply ileaf_bind. unfold getm. apply ileaf_bind. cbn [get fst snd ileaf].
  destruct (mlookup (st_metas s) p) as [[pr nx| |am]|] eqn:E; cbn; try exact I. exact (H am eq_refl).
Qed.

Lemma ileaf_bind_massert : forall {A} b site (k : unit -> M A) s Q, (b = true -> ileaf (k tt s) Q) -> ileaf (bind (massert b site) k s) Q.
Proof. intros A b site k s Q H. apply ileaf_bind. unfold massert. destruct b; [exact (H eq_refl) | exact I]. Qed.

Lemma ileaf_ret_shp : forall {A} (a : A) s, ileaf (ret a s) (fun r => SHP s (snd r)).
Proof. intros A a s. exact (SHP_refl s). Qed.

Lemma PRES_get_head : forall h s, ileaf (get_head h s) (fun r => SHP s (snd r)).
Proof. intros h s. unfold get_head. apply ileaf_bind. cbn. destruct h; exact (SHP_refl s). Qed.

Lemma PRES_set_head : forall h v s, ileaf (set_head h v s) (fun r => SHP s (snd r)).
Proof. intros h v s. unfold set_head. destruct h; cbn; apply SHP_ctx; reflexivity. Qed.

Lemma PRES_massert : forall b site s, ileaf (massert b site s) (fun r => SHP s (snd r)).
Proof. intros b site s. unfold massert. destruct b; [exact (SHP_refl s) | exact I]. Qed.

Lemma PRES_setm : forall p am am' s, mlookup (st_metas s) p = Some (MUsed am) -> gshape am am' -> ileaf (setm p am' s) (fun r => SHP s (snd r)).
Proof. intros p am am' s E G. exact (SHP_set_metas s p (MUsed am) (MUsed am') E G). Qed.

Lemma PRES_get_links : forall p s, ileaf (get_links p s) (fun r => SHP s (snd r)).
Proof. intros p s. unfold get_links. apply ileaf_bind. cbn. destruct (mlookup (st_metas s) p); [exact (SHP_refl s) | exact I]. Qed.

Lemma PRES_set_links : forall p pr nx s, ileaf (set_links p pr nx s) (fun r => SHP s (snd r)).
Proof.
  intros p pr nx s. unfold set_links. apply ileaf_bind. cbn [get fst snd ileaf].
  destruct (mlookup (st_metas s) p) as [x|] eqn:E; [|exact I]. exact (SHP_set_metas s p x _ E (mshape_links x pr nx)).
Qed.

Lemma PRES_set_next : forall p nx s, ileaf (set_next p nx s) (fun r => SHP s (snd r)).
Proof. intros p nx s. unfold set_next. apply ileaf_bind_shp; [apply PRES_get_links|]. intros b s1 _. apply PRES_set_links. Qed.

Lemma PRES_set_prev : forall p pr s, ileaf (set_prev p pr s) (fun r => SHP s (snd r)).
Proof. intros p pr s. unfold set_prev. apply ileaf_bind_shp; [apply PRES_get_links|]. intros b s1 _. apply PRES_set_links. Qed.

Lemma PRES_dequeue : forall h m s, ileaf (dequeue h m s) (fun r => SHP s (snd r)).
Proof.
  intros h m s. unfold dequeue. apply ileaf_bind_shp; [apply PRES_get_links|]. intros l s1 _.
  apply ileaf_bind_shp; [|intros b s2 _; apply PRES_set_links].
  destruct (osptr_eqb (snd l) (Some m)); [apply PRES_set_head|].
  destruct (fst l) as [pr|]; [|exact I]. destruct (snd l) as [nx|]; [|exact I].
  apply ileaf_bind_shp; [apply PRES_set_next|]. intros b2 s2 _. apply ileaf_bind_shp; [apply PRES_set_prev|]. intros b3 s3 _.
  apply ileaf_bind_shp; [apply PRES_get_head|]. intros hd s4 _. destruct (osptr_eqb hd (Some m)); [apply PRES_set_head | apply ileaf_ret_shp].
Qed.

Lemma PRES_decay : forall sc s, ileaf (decay_bounces sc s) (fun r => SHP s (snd r)).
Proof.
  intros sc s. unfold decay_bounces. destruct (bounce_idx sc) as [k|]; [|apply ileaf_ret_shp]. cbn.
  destruct (znth k (st_bounces s) =? 0); [apply SHP_refl | apply SHP_ctx; reflexivity].
Qed.

Lemma PRES_activate : forall m s, ileaf (activate_group m s) (fun r => SHP s (snd r)).
Proof.
  intros m s. unfold activate_group. apply ileaf_bind_getm. intros am E.
  apply ileaf_bind_massert. intros _.
  apply ileaf_bind_shp; [|intros b2 s2 _; apply ileaf_ret_shp].
  apply (PRES_setm m am _ s E). repeat split.
Qed.

Theorem try_avail_SHP : forall sc s, ileaf (try_avail sc s) (fun r => SHP s (snd r)).
Proof.
  intros sc s. unfold try_avail.
  apply ileaf_bind_shp; [apply PRES_get_head|]. intros hd s1 _.
  destruct hd as [m0|]; [|apply ileaf_ret_shp].
  apply ileaf_bind_getm. intros am0 E0. cbn beta zeta.
  destruct (negb (am_avail am0 =? 0)).
  - apply ileaf_bind_shp; [|intros b s2 _; apply ileaf_ret_shp]. apply (PRES_setm m0 am0 _ s1 E0). repeat split.
  - apply ileaf_bind_shp.
    + destruct (am_freed am0 =? 0).
      * apply ileaf_bind_shp; [apply PRES_dequeue|]. intros b s2 _. apply PRES_get_head.
      * apply ileaf_bind_shp; [apply PRES_set_head|]. intros b s2 _. apply ileaf_ret_shp.
    + intros om1 s2 _. destruct om1 as [m1|]; [|apply ileaf_ret_shp].
      apply ileaf_bind_getm. intros am1 E1.
      apply ileaf_bind_shp.
      * destruct (am_freed am1 =? ones (am_last am1)); [|apply ileaf_ret_shp].
        destruct (am_next am1) as [nx|]; [|exact I]. apply ileaf_bind_shp; [apply PRES_set_head|]. intros b s3 _. apply ileaf_ret_shp.
      * intros m2 s3 _. apply ileaf_bind_getm. intros am2 E2. cbn beta zeta.
        apply ileaf_bind_shp.
        -- destruct (Z.land (am_freed am2) (ones (am_aidx am2)) =? 0); [|apply ileaf_ret_shp].
           destruct (negb (osptr_eqb (am_next am2) (Some m2))).
           ++ destruct (am_next am2) as [nx|]; [|exact I]. apply ileaf_bind_shp; [apply PRES_set_head|]. intros b s4 _. apply ileaf_ret_shp.
           ++ cbn beta zeta. apply ileaf_bind_shp; [|intros b s4 _; apply ileaf_ret_shp]. apply (PRES_setm m2 am2 _ s3 E2). repeat split.
        -- intros m3 s4 _. apply ileaf_bind_shp; [apply PRES_activate|]. intros mask s5 _.
           apply ileaf_bind_massert. intros _.
           apply ileaf_bind_getm. intros am3 E3.
           apply ileaf_bind_shp; [apply PRES_decay|]. intros b s6 _. cbn beta zeta.
           apply ileaf_bind_getm. intros am3' E3'.
           apply ileaf_bind_shp; [|intros b' s7 _; apply ileaf_ret_shp]. apply (PRES_setm m3 am3' _ s6 E3'). repeat split.
Qed.

Corollary try_avail_shape : forall sc s first s', try_avail sc s = IRet (first, s') -> SHP s s'.
Proof. intros sc s first s' E. exact (ileaf_ret_eq _ _ _ (try_avail_SHP sc s) E). Qed.
