(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocLemmasBase MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import MngHeap MngRel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive subl {A : Type} : list A -> list A -> Prop :=
| sl_nil : subl [] []
| sl_skip x l' l : subl l' l -> subl l' (x :: l)
| sl_keep x l' l : subl l' l -> subl (x :: l') (x :: l).

Lemma subl_refl : forall {A} (l : list A), subl l l.
Proof. intros A l. induction l as [|x l IH]; [constructor | apply sl_keep; exact IH]. Qed.

Lemma subl_nil_l : forall {A} (l : list A), subl [] l.
Proof. intros A l. induction l as [|x l IH]; [constructor | apply sl_skip; exact IH]. Qed.

Lemma subl_incl : forall {A} (l' l : list A), subl l' l -> forall x, In x l' -> In x l.
Proof.
  intros A l' l H. induction H as [| x l' l H IH | x l' l H IH]; intros y Hy; [exact Hy | right; exact (IH y Hy) |].
  destruct Hy as [<-|Hy]; [left; reflexivity | right; exact (IH y Hy)].
Qed.

Lemma subl_app : forall {A} (a' a b' b : list A), subl a' a -> subl b' b -> subl (a' ++ b') (a ++ b).
Proof.
  intros A a' a b' b H1 H2. induction H1 as [| x l' l H IH | x l' l H IH]; cbn [app]; [exact H2 | apply sl_skip; exact IH | apply sl_keep; exact IH].
Qed.

Lemma subl_map : forall {A B} (f : A -> B) (l' l : list A), subl l' l -> subl (map f l') (map f l).
Proof.
  intros A B f l' l H. induction H as [| x l' l H IH | x l' l H IH]; cbn [map]; [constructor | apply sl_skip; exact IH | apply sl_keep; exact IH].
Qed.

Lemma subl_flat_map : forall {A B} (f' f : A -> list B) (l : list A), (forall x, In x l -> subl (f' x) (f x)) -> subl (flat_map f' l) (flat_map f l).
Proof.
  intros A B f' f l. induction l as [|x l IH]; intros H; cbn [flat_map]; [constructor|].
  apply subl_app; [apply H; left; reflexivity | apply IH; intros y Hy; apply H; right; exact Hy].
Qed.

Lemma pairwise_subl : forall {A} (R : A -> A -> Prop) (l' l : list A), subl l' l -> pairwise R l -> pairwise R l'.
Proof.
  intros A R l' l H. induction H as [| x l' l H IH | x l' l H IH]; intros HP; [exact I | exact (IH (proj2 HP)) |].
  destruct HP as (H1 & H2). split; [intros y Hy; apply H1; exact (subl_incl l' l H y Hy) | exact (IH H2)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma areas_cells_metas : forall s s' l, st_metas s' = st_metas s -> areas_cells s' l = areas_cells s l.
Proof.
  intros s s' l E. induction l as [|a l IH]; [reflexivity|]. cbn [areas_cells]. rewrite IH. f_equal.
  unfold area_cells. rewrite E. reflexivity.
Qed.

Lemma image_unm : forall s r, image (s_unm s r) = image s.
Proof.
  intros s r. unfold image. rewrite (areas_cells_metas s (s_unm s r) (st_areas (s_unm s r)) eq_refl). reflexivity.
Qed.

Lemma markers_unm : forall s r, markers (s_unm s r) = markers s.
Proof. intros s r. reflexivity. Qed.

Lemma used_metas_unm : forall s r, used_metas (s_unm s r) = used_metas s.
Proof. intros s r. reflexivity. Qed.

Lemma region_unm : forall s r k, region_of (s_unm s r) k =
  if (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool then Some (mkRegion RkMap (rg_len (nth r (st_regions s) (mkRegion RkMap 0 [] false))) [] false)
  else region_of s k.
Proof. intros s r k. unfold region_of, s_unm, set_regions. cbn [st_regions]. apply nth_error_lupd. Qed.

Lemma region_unm_live : forall s r k rg, region_of (s_unm s r) k = Some rg -> rg_live rg = true -> k <> r /\ region_of s k = Some rg.
Proof.
  intros s r k rg H Hl. rewrite region_unm in H. destruct (Nat.eqb_spec k r) as [->|Hne].
  - destruct (Nat.ltb r (length (st_regions s))) eqn:Ex; cbn in H; [injection H as <-; discriminate Hl|].
    exfalso. apply Nat.ltb_ge in Ex. unfold region_of in H. rewrite (proj2 (nth_error_None (st_regions s) r) Ex) in H. discriminate H.
  - cbn in H. exact (conj Hne H).
Qed.

Lemma footprint_unm_subl : forall s r, subl (footprint (s_unm s r)) (footprint s).
Proof.
  intros s r. unfold footprint. apply sl_keep. change (st_areas (s_unm s r)) with (st_areas s). apply subl_app; [apply subl_refl|].
  replace (length (st_regions (s_unm s r))) with (length (st_regions s)) by (unfold s_unm, set_regions; cbn [st_regions]; symmetry; apply length_lupd).
  apply subl_flat_map. intros k Hk. rewrite region_unm. destruct (Nat.eqb_spec k r) as [->|Hne]; cbn [andb].
  - destruct (Nat.ltb r (length (st_regions s))); cbn [rg_kind rg_live]; [apply subl_nil_l | apply subl_refl].
  - apply subl_refl.
Qed.

Lemma footprint_unm_In : forall s r rg, In rg (footprint (s_unm s r)) -> In rg (footprint s).
Proof. intros s r rg H. exact (subl_incl _ _ (footprint_unm_subl s r) rg H). Qed.

(* [comment removed for export] *)
Lemma flat_map_ext_In : forall {A B} (f g : A -> list B) (l : list A), (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof.
  intros A B f g l. induction l as [|x l IH]; intros H; [reflexivity|]. cbn [flat_map].
  rewrite (H x (or_introl eq_refl)), IH by (intros y Hy; exact (H y (or_intror Hy))). reflexivity.
Qed.

Lemma footprint_unm_split : forall s r rg, region_of s r = Some rg -> rg_kind rg = RkMap -> rg_live rg = true ->
  exists A B, footprint s = A ++ (LMem (SP r 0), rg_len rg) :: B /\ footprint (s_unm s r) = A ++ B.
Proof.
  intros s r rg Hr Hk Hl.
  assert (Hn : (r < length (st_regions s))%nat) by (apply nth_error_Some; unfold region_of in Hr; rewrite Hr; discriminate).
  set (n := length (st_regions s)) in *.
  set (f := fun k => match region_of s k with
                     | Some rg => match rg_kind rg with RkMap => if rg_live rg then [(LMem (SP k 0), rg_len rg)] else [] | _ => [] end
                     | None => [] end).
  set (f' := fun k => match region_of (s_unm s r) k with
                     | Some rg => match rg_kind rg with RkMap => if rg_live rg then [(LMem (SP k 0), rg_len rg)] else [] | _ => [] end
                     | None => [] end).
  assert (Eseq : seq 0 n = seq 0 r ++ r :: seq (S r) (n - S r)).
  { replace n with (r + (1 + (n - S r)))%nat at 1 by lia. rewrite seq_app. cbn [seq]. f_equal. }
  assert (Ef : forall k, k <> r -> f' k = f k).
  { intros k Hne. unfold f, f'. rewrite region_unm. destruct (Nat.eqb_spec k r) as [E|E]; [exfalso; exact (Hne E)|]. reflexivity. }
  assert (Efr : f' r = []).
  { unfold f'. rewrite region_unm. rewrite Nat.eqb_refl. replace (Nat.ltb r (length (st_regions s))) with true by (symmetry; apply Nat.ltb_lt; exact Hn). reflexivity. }
  assert (Efr0 : f r = [(LMem (SP r 0), rg_len rg)]) by (unfold f; rewrite Hr, Hk, Hl; reflexivity).
  exists ((LCtx 0, CTX_SIZE) :: map (fun a => (LMem a, PGSZ)) (st_areas s) ++ flat_map f (seq 0 r)), (flat_map f (seq (S r) (n - S r))).
  split.
  - unfold footprint. fold n. fold f. rewrite Eseq, flat_map_app. cbn [flat_map]. rewrite Efr0. cbn [app]. rewrite <- !app_assoc. reflexivity.
  - unfold footprint. change (st_areas (s_unm s r)) with (st_areas s).
    replace (length (st_regions (s_unm s r))) with n by (unfold n, s_unm, set_regions; cbn [st_regions]; symmetry; apply length_lupd).
    fold f'. rewrite Eseq, flat_map_app. cbn [flat_map]. rewrite Efr. cbn [app].
    rewrite (flat_map_ext_In f' f (seq 0 r)) by (intros k Hk'; apply in_seq in Hk'; apply Ef; lia).
    rewrite (flat_map_ext_In f' f (seq (S r) (n - S r))) by (intros k Hk'; apply in_seq in Hk'; apply Ef; lia).
    rewrite <- !app_assoc. reflexivity.
Qed.

Lemma layout_unm : forall L s r, layout_ok L s -> layout_ok L (s_unm s r).
Proof.
  intros L s r (H1 & H2 & H3 & H4). split; [exact H1|]. split.
  { intros k rg Hk Hl. destruct (region_unm_live s r k rg Hk Hl) as (_ & Hk'). exact (H2 k rg Hk' Hl). }
  split.
  { apply (pairwise_subl _ _ _ (subl_map (crange L) _ _ (footprint_unm_subl s r)) H3). }
  intros rg Hrg. exact (H4 rg (footprint_unm_In s r rg Hrg)).
Qed.

Lemma pairwise_app_cons' : forall {A} (R : A -> A -> Prop) l1 x l2, pairwise R (l1 ++ x :: l2) ->
  forall y, In y (l1 ++ l2) -> R x y \/ R y x.
Proof.
  intros A R l1. induction l1 as [|a t IH]; intros x l2 HP y Hy; cbn [app] in *.
  - destruct HP as [H1 _]. left. apply H1. exact Hy.
  - destruct HP as [H1 H2]. destruct Hy as [<-|Hy].
    + right. apply H1. apply in_app_iff. right. left. reflexivity.
    + exact (IH x l2 H2 y Hy).
Qed.

(* [comment removed for export] *)
Lemma footprint_of_kf : forall s s', st_regions s' = st_regions s -> st_areas s' = st_areas s -> footprint s' = footprint s.
Proof. intros s s' Er Ea. unfold footprint, region_of. rewrite Er, Ea. reflexivity. Qed.

(* [comment removed for export] *)
Lemma unm_disjoint : forall L s r rg rg', layout_ok L s -> region_of s r = Some rg -> rg_kind rg = RkMap -> rg_live rg = true ->
  In rg' (footprint (s_unm s r)) -> ranges_disjoint (crange L rg') (ly_reg L r, rg_len rg).
Proof.
  intros L s r rg rg' (_ & _ & HP & _) Hr Hk Hl Hin.
  destruct (footprint_unm_split s r rg Hr Hk Hl) as (A & B & E1 & E2). rewrite E1, map_app in HP. cbn [map] in HP.
  rewrite E2 in Hin. assert (Hy : In (crange L rg') (map (crange L) A ++ map (crange L) B)) by (rewrite <- map_app; apply in_map; exact Hin).
  destruct (pairwise_app_cons' _ _ _ _ HP _ Hy) as [D|D]; unfold ranges_disjoint, crange in *; cbn [fst snd loc_addr] in *; lia.
Qed.

Lemma kf_unm : forall s r len, MallocWfKf.kf_of (s_unm s r) = MallocWfKf.kstep (MallocWfKf.kf_of s) (KMunmap r len) 1.
Proof. intros s r len. reflexivity. Qed.
