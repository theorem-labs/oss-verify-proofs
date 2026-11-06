(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.

Module MallocLemmasRing.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocLemmasBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition links := option (option sptr * option sptr).
Definition lkmap := sptr -> links.

Definition lk_set (lk : lkmap) (p : sptr) (v : option sptr * option sptr) : lkmap :=
  fun q => if sptr_eqb q p then Some v else lk q.

Lemma lk_set_same lk p v : lk_set lk p v p = Some v.
Proof. unfold lk_set. rewrite sptr_eqb_refl. reflexivity. Qed.

Lemma lk_set_other lk p v q : q <> p -> lk_set lk p v q = lk q.
Proof. intros H. unfold lk_set. destruct (sptr_eqb q p) eqn:E; [apply sptr_eqb_eq in E; congruence | reflexivity]. Qed.

(* [comment removed for export] *)

Lemma chain_ext lk lk' prev l first :
  (forall x, In x l -> lk' x = lk x) -> chain lk prev l first -> chain lk' prev l first.
Proof.
  revert prev. induction l as [|x rest IH]; intros prev Hext H; cbn in *; [exact I|].
  destruct H as [Hx Hr]. split.
  - rewrite Hext by (left; reflexivity). exact Hx.
  - apply IH; [intros y Hy; apply Hext; right; exact Hy | exact Hr].
Qed.

Lemma cycle_ok_ext lk lk' ms :
  (forall x, In x ms -> lk' x = lk x) -> cycle_ok lk ms -> cycle_ok lk' ms.
Proof.
  intros Hext [Hnd H]. split; [exact Hnd|]. destruct ms as [|m0 rest]; [exact H|].
  apply chain_ext with lk; assumption.
Qed.

Lemma ring_ok_ext lk lk' hd ms :
  (forall x, In x ms -> lk' x = lk x) -> ring_ok lk hd ms -> ring_ok lk' hd ms.
Proof. intros Hext [Hc Hh]. split; [eapply cycle_ok_ext; eauto | exact Hh]. Qed.

Lemma chain_links lk prev l first x :
  chain lk prev l first -> In x l -> exists pr nx, lk x = Some (Some pr, Some nx).
Proof.
  revert prev. induction l as [|y rest IH]; intros prev H Hin; [destruct Hin|].
  cbn in H. destruct H as [Hy Hr]. destruct Hin as [<-|Hin].
  - eexists _, _. exact Hy.
  - eapply IH; eauto.
Qed.

Lemma cycle_links lk ms x :
  cycle_ok lk ms -> In x ms -> exists pr nx, lk x = Some (Some pr, Some nx).
Proof.
  intros [_ H] Hin. destruct ms as [|m0 rest]; [destruct Hin|]. eapply chain_links; eauto.
Qed.

Lemma ring_links lk hd ms x :
  ring_ok lk hd ms -> In x ms -> exists pr nx, lk x = Some (Some pr, Some nx).
Proof. intros [Hc _] Hin. eapply cycle_links; eauto. Qed.

Lemma ring_head lk hd ms : ring_ok lk hd ms -> hd = hd_error ms.
Proof. intros [_ H]. exact H. Qed.

Lemma ring_head_In lk h ms : ring_ok lk (Some h) ms -> In h ms /\ exists rest, ms = h :: rest.
Proof.
  intros [_ Hh]. destruct ms as [|m0 rest]; [discriminate|]. cbn in Hh.
  injection Hh as ->. split; [left; reflexivity | exists rest; reflexivity].
Qed.

Lemma ring_None lk ms : ring_ok lk None ms -> ms = [].
Proof. intros [_ Hh]. destruct ms; [reflexivity | discriminate]. Qed.

Lemma ring_nil lk hd : ring_ok lk hd [] -> hd = None.
Proof. intros [_ Hh]. exact Hh. Qed.

Lemma ring_ok_nil lk : ring_ok lk None [].
Proof. split; [split; [constructor | exact I] | reflexivity]. Qed.

Lemma last_indep {T} (l : list T) d d' : l <> [] -> last l d = last l d'.
Proof.
  induction l as [|x [|y t] IH]; intros H; [congruence | reflexivity |].
  cbn [last]. apply IH. discriminate.
Qed.

Lemma last_cons {T} (x : T) l d : last (x :: l) d = last l x.
Proof.
  destruct l as [|y t]; [reflexivity|].
  change (last (y :: t) d = last (y :: t) x). apply last_indep. discriminate.
Qed.

Lemma last_app_single {T} (l : list T) (a d : T) : last (l ++ [a]) d = a.
Proof. induction l as [|x [|y t] IH]; cbn in *; auto. Qed.

Lemma In_last {T} (l : list T) d : l <> [] -> In (last l d) l.
Proof.
  induction l as [|x [|y t] IH]; intros H; [congruence | left; reflexivity |].
  right. apply IH. discriminate.
Qed.

Lemma hd_app_indep {T} (l : list T) d d' r : l <> [] -> hd d (l ++ r) = hd d' l.
Proof. destruct l; [congruence | reflexivity]. Qed.

Lemma hd_app {T} (d : T) l r : hd d (l ++ r) = hd (hd d r) l.
Proof. destruct l; reflexivity. Qed.

Lemma chain_app lk prev l1 l2 first :
  chain lk prev (l1 ++ l2) first <-> chain lk prev l1 (hd first l2) /\ chain lk (last l1 prev) l2 first.
Proof.
  revert prev. induction l1 as [|x rest IH]; intros prev.
  - cbn. tauto.
  - cbn [app chain]. rewrite last_cons, hd_app, (IH x). tauto.
Qed.

(* [comment removed for export] *)
Lemma chain_next lk prev l first x pr nx :
  chain lk prev l first -> In x l -> lk x = Some (pr, nx) ->
  exists l1 l2, l = l1 ++ x :: l2 /\ nx = Some (hd first l2) /\ pr = Some (last l1 prev).
Proof.
  revert prev. induction l as [|y rest IH]; intros prev Hc Hin Hx; [destruct Hin|].
  cbn in Hc. destruct Hc as [Hy Hr]. destruct (sptr_eq_dec x y) as [<-|Hne].
  - exists [], rest. rewrite Hx in Hy. injection Hy as -> ->. repeat split; reflexivity.
  - destruct Hin as [->|Hin]; [congruence|].
    destruct (IH y Hr Hin Hx) as (l1 & l2 & -> & Hn & Hp).
    exists (y :: l1), l2. repeat split; try assumption.
    rewrite Hp. f_equal. symmetry. apply last_cons.
Qed.


Lemma cycle_rotate lk x l : cycle_ok lk (x :: l) -> cycle_ok lk (l ++ [x]).
Proof.
  intros [Hnd Hc]. split. apply NoDup_app_single; inversion Hnd; subst; assumption.
  destruct l as [|y l'].
  - cbn in *. exact Hc.
  - cbn [app]. rewrite last_cons, last_app_single.
    cbn [chain] in Hc. rewrite last_cons in Hc. destruct Hc as [Hx Hrest].
    change (chain lk x ((y :: l') ++ [x]) y). apply chain_app. split.
    + cbn [hd]. exact Hrest.
    + cbn [chain hd] in Hx |- *. split; [|exact I]. exact Hx.
Qed.

Lemma cycle_rotate_n lk l1 l2 : cycle_ok lk (l1 ++ l2) -> cycle_ok lk (l2 ++ l1).
Proof.
  revert l2. induction l1 as [|x rest IH]; intros l2 H.
  - rewrite app_nil_r. exact H.
  - cbn in H. apply cycle_rotate in H. rewrite <- app_assoc in H. apply IH in H.
    rewrite <- app_assoc in H. exact H.
Qed.

Lemma chain_snoc lk lk' p p' l f f' m :
  chain lk p l f -> NoDup l -> l <> [] -> ~ In m l ->
  (forall x pr nx, In x l -> lk x = Some (pr, nx) ->
     lk' x = Some ((if sptr_eqb x (hd m l) then Some p' else pr),
                   (if sptr_eqb x (last l m) then Some m else nx))) ->
  lk' m = Some (Some (last l m), Some f') ->
  chain lk' p' (l ++ [m]) f'.
Proof.
  revert p p'. induction l as [|x rest IH]; intros p p' Hc Hnd Hne Hm Hupd Hlm; [congruence|].
  cbn [chain] in Hc. destruct Hc as [Hx Hrest].
  inversion Hnd as [|x' rest' Hxn Hndr]; subst.
  cbn [app chain]. split.
  - rewrite (Hupd x _ _ (or_introl eq_refl) Hx). cbn [hd]. rewrite sptr_eqb_refl.
    destruct rest as [|y rest'].
    + cbn. rewrite sptr_eqb_refl. reflexivity.
    + rewrite last_cons.
      assert (E : sptr_eqb x (last (y :: rest') x) = false).
      { apply sptr_eqb_neq. intros Heq. apply Hxn. rewrite Heq at 1. apply In_last. discriminate. }
      rewrite E. reflexivity.
  - destruct rest as [|y rest'].
    + cbn. split; [|exact I]. rewrite Hlm. reflexivity.
    + apply (IH x x).
      * exact Hrest.
      * exact Hndr.
      * discriminate.
      * intros Hin. apply Hm. right. exact Hin.
      * intros z pr nx Hz Hlz. rewrite (Hupd z pr nx (or_intror Hz) Hlz).
        cbn [hd]. rewrite last_cons, (last_indep (y :: rest') x m) by discriminate.
        assert (E : sptr_eqb z x = false) by (apply sptr_eqb_neq; intros ->; exact (Hxn Hz)).
        rewrite E. destruct (sptr_eqb z y) eqn:Ezy; [|reflexivity].
        apply sptr_eqb_eq in Ezy. subst z. cbn [chain] in Hrest. destruct Hrest as [Hy _].
        rewrite Hy in Hlz. injection Hlz as <- <-. reflexivity.
      * rewrite Hlm. rewrite last_cons, (last_indep (y :: rest') x m) by discriminate. reflexivity.
Qed.

Lemma cycle_snoc lk lk' ms m :
  cycle_ok lk ms -> ms <> [] -> ~ In m ms ->
  (forall x pr nx, In x ms -> lk x = Some (pr, nx) ->
     lk' x = Some ((if sptr_eqb x (hd m ms) then Some m else pr),
                   (if sptr_eqb x (last ms m) then Some m else nx))) ->
  lk' m = Some (Some (last ms m), Some (hd m ms)) ->
  cycle_ok lk' (ms ++ [m]).
Proof.
  intros [Hnd Hc] Hne Hm Hupd Hlm. split; [apply NoDup_app_single; assumption|].
  destruct ms as [|m0 rest]; [congruence|]. cbn [app]. rewrite last_cons, last_app_single.
  change (chain lk' m ((m0 :: rest) ++ [m]) m0).
  rewrite (last_indep (m0 :: rest) m0 m) in Hc by discriminate.
  eapply chain_snoc; eauto.
Qed.

Lemma chain_retarget lk lk' p l x y :
  chain lk p l x -> NoDup l -> l <> [] -> (forall z, In z l -> z <> y) ->
  (forall z pr nx, In z l -> lk z = Some (pr, nx) ->
     lk' z = Some ((if sptr_eqb z y then Some (last l y) else pr),
                   (if sptr_eqb z (last l y) then Some y else nx))) ->
  chain lk' p l y.
Proof.
  revert p. induction l as [|z l IH]; intros p Hc Hnd Hne Hny Hupd; [congruence|].
  cbn [chain] in Hc |- *. destruct Hc as [Hz Hl]. inversion Hnd as [|z' l' Hzn Hndl]; subst.
  assert (Ezy : sptr_eqb z y = false) by (apply sptr_eqb_neq; apply Hny; left; reflexivity).
  split.
  - rewrite (Hupd z _ _ (or_introl eq_refl) Hz), Ezy. destruct l as [|w l''].
    + cbn. rewrite sptr_eqb_refl. reflexivity.
    + rewrite last_cons.
      assert (E : sptr_eqb z (last (w :: l'') z) = false).
      { apply sptr_eqb_neq. intros Heq. apply Hzn. rewrite Heq at 1. apply In_last. discriminate. }
      rewrite E. reflexivity.
  - destruct l as [|w l'']; [exact I|].
    apply IH; auto.
    + discriminate.
    + intros u Hu. apply Hny. right. exact Hu.
    + intros u pr nx Hu Hlu. rewrite last_cons, (last_indep (w :: l'') z y) in Hupd by discriminate.
      apply Hupd; [right; exact Hu | exact Hlu].
Qed.

Lemma cycle_remove_first lk lk' x ms :
  cycle_ok lk (x :: ms) -> ms <> [] ->
  (forall y pr nx, In y ms -> lk y = Some (pr, nx) ->
     lk' y = Some ((if sptr_eqb y (hd x ms) then Some (last ms x) else pr),
                   (if sptr_eqb y (last ms x) then Some (hd x ms) else nx))) ->
  cycle_ok lk' ms.
Proof.
  intros [Hnd Hc] Hne Hupd. inversion Hnd as [|x' ms' Hxn Hndm]; subst.
  split; [exact Hndm|]. destruct ms as [|y rest]; [congruence|].
  cbn [chain] in Hc. rewrite last_cons in Hc. destruct Hc as [Hx [Hy Hrest]].
  cbn [hd] in Hupd.
  rewrite (last_indep (y :: rest) x y) in Hupd by discriminate.
  inversion Hndm as [|y' rest' Hyn Hndr]; subst.
  cbn [chain]. split.
  - rewrite (Hupd y _ _ (or_introl eq_refl) Hy), sptr_eqb_refl.
    destruct rest as [|w rest''].
    + cbn. rewrite sptr_eqb_refl. reflexivity.
    + rewrite last_cons.
      assert (E : sptr_eqb y (last (w :: rest'') y) = false).
      { apply sptr_eqb_neq. intros Heq. apply Hyn. rewrite Heq at 1. apply In_last. discriminate. }
      rewrite E. reflexivity.
  - destruct rest as [|w rest'']; [exact I|].
    eapply chain_retarget.
    + exact Hrest.
    + exact Hndr.
    + discriminate.
    + intros z Hz ->. exact (Hyn Hz).
    + intros z pr nx Hz Hlz. rewrite (Hupd z _ _ (or_intror Hz) Hlz).
      rewrite last_cons. reflexivity.
Qed.

End MallocLemmasRing.


Module MallocWfInv.
(* [comment removed for export] *)

From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Export MallocModel MallocInv MallocLemmasBase.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
End MallocWfInv.


Module MallocWfFrame.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Ltac simp_st :=
  cbn [st_init_done st_mmap_counter st_free_meta_head st_avail_meta st_avail_meta_count
       st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_avail_meta_areas
       st_active st_usage st_unmap_seq st_bounces st_seq st_brk st_metas st_regions st_areas
       set_init_done set_mmap_counter set_free_meta_head set_avail_meta set_avail_meta_count
       set_avail_meta_area_count set_meta_alloc_shift set_area_head set_area_tail set_avail_meta_areas
       set_active set_usage set_unmap_seq set_bounces set_seq set_brk set_metas set_regions set_areas
       am_prev am_next am_mem am_avail am_freed am_last am_sc am_maplen am_aidx am_slots
       am_set_links am_set_prev am_set_next am_set_avail am_set_freed am_set_aidx am_set_slots] in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Scalars.
  Context (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).

  #[using="Type"] Lemma Inv_set_seq s v : Inv X R U s -> 0 <= v <= 255 -> Inv X R U (set_seq v s).
  Proof.
    intros H Hv. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
    pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st. tauto.
  Qed.

  #[using="Type"] Lemma Inv_set_mmap_counter s v : Inv X R U s -> 0 <= v < 2 ^ 32 -> Inv X R U (set_mmap_counter v s).
  Proof.
    intros H Hv. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
    pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st. tauto.
  Qed.

  #[using="Type"] Lemma Inv_set_init_done s : Inv X R U s -> Inv X R U (set_init_done true s).
  Proof.
    intros H. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
    pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st.
    repeat match goal with |- _ /\ _ => split end; try tauto. discriminate.
  Qed.

  #[using="Type"] Lemma Inv_set_unmap_seq s l :
    Inv X R U s -> length l = 32%nat -> (forall u, In u l -> 0 <= u <= 255) ->
    Inv X R U (set_unmap_seq l s).
  Proof.
    intros H Hl Hr. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
    pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st. tauto.
  Qed.

  #[using="Type"] Lemma Inv_set_bounces s l :
    Inv X R U s -> length l = 32%nat -> (forall u, In u l -> 0 <= u <= 255) ->
    Inv X R U (set_bounces l s).
  Proof.
    intros H Hl Hr. split; [| split; [exact (inv_keys H) | split; [exact (inv_areas H) | exact (inv_meta H)]]].
    pose proof (inv_ctx H) as C. unfold ctx_ok in *. simp_st. tauto.
  Qed.
End Scalars.

(* [comment removed for export] *)
Lemma zset_length32_range l k v :
  length l = 32%nat -> (forall u, In u l -> 0 <= u <= 255) -> 0 <= v <= 255 ->
  length (zset k v l) = 32%nat /\ (forall u, In u (zset k v l) -> 0 <= u <= 255).
Proof.
  intros Hl Hr Hv. split; [rewrite length_zset; exact Hl|].
  intros u Hu. unfold zset in Hu.
  revert Hu. generalize (Z.to_nat k) as n. intros n Hu.
  assert (G : forall l' n', (forall u, In u l' -> 0 <= u <= 255) -> In u (zupd l' n' v) -> 0 <= u <= 255).
  { clear - Hv. induction l' as [|h t IH]; intros [|n'] Hr' Hu; cbn in Hu; try contradiction.
    - destruct Hu as [<-|Hu]; [lia | apply Hr'; right; exact Hu].
    - destruct Hu as [<-|Hu]; [apply Hr'; left; reflexivity | apply (IH n'); [intros w Hw; apply Hr'; right; exact Hw | exact Hu]]. }
  eapply G; eauto.
Qed.

Lemma repeat0_32_range : length (repeat 0 32) = 32%nat /\ (forall u, In u (repeat 0 32) -> 0 <= u <= 255).
Proof. split; [reflexivity|]. intros u Hu. apply repeat_spec in Hu. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition upd_meta (g : sptr) (x : mslot) (s : astate) : astate :=
  set_metas (mupdate (st_metas s) g x) s.

Lemma MT_upd_same g x s : MT (upd_meta g x s) g = Some x.
Proof. unfold MT, upd_meta. simp_st. apply mlookup_mupdate_same. Qed.

Lemma MT_upd_other g x s p : p <> g -> MT (upd_meta g x s) p = MT s p.
Proof. intros. unfold MT, upd_meta. simp_st. apply mlookup_mupdate_other. assumption. Qed.

Lemma MT_upd g x s p : MT (upd_meta g x s) p = if sptr_eqb p g then Some x else MT s p.
Proof. unfold MT, upd_meta. simp_st. apply mlookup_mupdate. Qed.

Lemma keys_upd_In g x s : In g (keys s) -> keys (upd_meta g x s) = keys s.
Proof. intros. unfold keys, upd_meta. simp_st. apply map_fst_mupdate_In. assumption. Qed.

Lemma keys_upd_notIn g x s : ~ In g (keys s) -> keys (upd_meta g x s) = keys s ++ [g].
Proof. intros. unfold keys, upd_meta. simp_st. apply map_fst_mupdate_notIn. assumption. Qed.

Lemma MT_Some_In_keys s g x : MT s g = Some x -> In g (keys s).
Proof. unfold MT, keys. apply mlookup_In_keys. Qed.

Lemma MTX_upd X g x s p :
  MTX X (upd_meta g x s) p = if sptr_eqb p g then (if memb g X then None else Some x) else MTX X s p.
Proof.
  unfold MTX. rewrite MT_upd. destruct (sptr_eqb p g) eqn:E; [|reflexivity].
  apply sptr_eqb_eq in E. subst. reflexivity.
Qed.

Lemma usedX_upd X g x s p am :
  usedX X (upd_meta g x s) p am <->
  (p = g /\ memb g X = false /\ x = MUsed am) \/ (p <> g /\ usedX X s p am).
Proof.
  unfold usedX. rewrite MTX_upd. destruct (sptr_eqb p g) eqn:E.
  - apply sptr_eqb_eq in E. subst p. destruct (memb g X) eqn:M.
    + split; [discriminate | intros [[_ [H _]] | [H _]]; congruence].
    + split.
      * intros H. left. injection H as ->. auto.
      * intros [[_ [_ ->]] | [H _]]; [reflexivity | congruence].
  - apply sptr_eqb_neq in E. split.
    + intros H. right. auto.
    + intros [[H _] | [_ H]]; [congruence | exact H].
Qed.

Lemma usedX_MT X s g am : usedX X s g am -> MT s g = Some (MUsed am) /\ memb g X = false.
Proof. unfold usedX, MTX. destruct (memb g X); [discriminate | auto]. Qed.

Lemma usedX_intro X s g am : memb g X = false -> MT s g = Some (MUsed am) -> usedX X s g am.
Proof. intros M H. unfold usedX, MTX. rewrite M. exact H. Qed.

Lemma usedX_fun X s g a1 a2 : usedX X s g a1 -> usedX X s g a2 -> a1 = a2.
Proof. unfold usedX. intros H1 H2. rewrite H1 in H2. injection H2. auto. Qed.

(* [comment removed for export] *)
Definition geom_same (am0 am1 : ameta) : Prop :=
  am_mem am1 = am_mem am0 /\ am_last am1 = am_last am0 /\ am_sc am1 = am_sc am0 /\
  am_maplen am1 = am_maplen am0 /\
  (forall j fr, ss_fr (nth_slot am0 j) = Some fr -> fr_kind fr = FGroup -> ss_fr (nth_slot am1 j) = Some fr).

Lemma geom_same_stride am0 am1 : geom_same am0 am1 -> stride_of am1 = stride_of am0.
Proof. intros (_ & Hl & Hs & Hm & _). unfold stride_of. rewrite Hl, Hs, Hm. reflexivity. Qed.

Lemma geom_same_slot_start am0 am1 i : geom_same am0 am1 -> slot_start am1 i = slot_start am0 i.
Proof. intros G. unfold slot_start. rewrite (geom_same_stride _ _ G). destruct G as (-> & _). reflexivity. Qed.

Lemma geom_same_extent am0 am1 : geom_same am0 am1 -> group_extent am1 = group_extent am0.
Proof. intros G. unfold group_extent. rewrite (geom_same_stride _ _ G). destruct G as (_ & -> & _). reflexivity. Qed.

(* [comment removed for export] *)
Definition gframes_kept (X : list sptr) (s : astate) (am0 am1 : ameta) : Prop :=
  forall j fr, 0 <= j -> ss_fr (nth_slot am0 j) = Some fr -> fr_kind fr = FGroup ->
    ss_fr (nth_slot am1 j) = Some fr \/
    (forall c ac, usedX X s c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start am0 j).

Definition geom_same_upto (X : list sptr) (s : astate) (am0 am1 : ameta) : Prop :=
  am_mem am1 = am_mem am0 /\ am_last am1 = am_last am0 /\ am_sc am1 = am_sc am0 /\
  am_maplen am1 = am_maplen am0 /\ gframes_kept X s am0 am1.

Lemma geom_same_upto_of X s am0 am1 : geom_same am0 am1 -> geom_same_upto X s am0 am1.
Proof. intros (A & B & C & D & E). repeat split; auto. intros j fr _ H1 H2. left. apply E; assumption. Qed.

Lemma geom_same_upto_stride X s am0 am1 : geom_same_upto X s am0 am1 -> stride_of am1 = stride_of am0.
Proof. intros (_ & Hl & Hs & Hm & _). unfold stride_of. rewrite Hl, Hs, Hm. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section UsedUpdate.
  Variables (X : list sptr) (R R' : option (sptr * Z)) (U : Z -> Z) (s : astate) (g : sptr) (am0 am1 : ameta).
  Hypothesis HI : Inv X R U s.
  Hypothesis Hg : usedX X s g am0.
  Hypothesis G : geom_same_upto X s am0 am1.
  Hypothesis Lk : am_prev am1 = am_prev am0 /\ am_next am1 = am_next am0.
  Local Notation s' := (upd_meta g (MUsed am1) s).

  #[using="X am0 Hg"] Lemma uu_keys : keys s' = keys s.
  Proof. apply keys_upd_In. eapply MT_Some_In_keys. apply (proj1 (usedX_MT _ _ _ _ Hg)). Qed.

  #[using="s am0 Hg"] Lemma uu_notX : memb g X = false.
  Proof. exact (proj2 (usedX_MT _ _ _ _ Hg)). Qed.

  #[using="am0 Hg"] Lemma uu_usedX_g : usedX X s' g am1.
  Proof. apply usedX_upd. left. auto using uu_notX. Qed.

  #[using="Type"] Lemma uu_usedX_other p am : p <> g -> (usedX X s' p am <-> usedX X s p am).
  Proof. intros Hp. rewrite usedX_upd. split; [intros [[H _]|[_ H]]; [congruence|exact H] | intros H; right; auto]. Qed.

  #[using="Type"] Lemma uu_usedX_inv p am : usedX X s' p am -> (p = g /\ am = am1) \/ (p <> g /\ usedX X s p am).
  Proof.
    intros H. apply usedX_upd in H as [[-> [_ H]] | [Hp H]]; [left; injection H; auto | right; auto].
  Qed.

  #[using="X R U am0 HI Hg"] Lemma uu_ctx : ctx_ok s'.
  Proof.
    pose proof (inv_ctx HI) as C. unfold ctx_ok in *. unfold upd_meta. simp_st.
    destruct C as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12).
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj C11 _))))))))))).
    intros Hinit. exfalso. destruct (C12 Hinit) as (Hm & _).
    pose proof (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Hg))) as K.
    unfold keys in K. rewrite Hm in K. exact K.
  Qed.

  #[using="X R U am0 HI Hg"] Lemma uu_keys_ok : keys_ok s'.
  Proof.
    pose proof (inv_keys HI) as K. unfold keys_ok in *. rewrite uu_keys.
    unfold upd_meta. simp_st. exact K.
  Qed.

  #[using="X R U HI"] Lemma uu_areas : areas_ok s'.
  Proof. exact (inv_areas HI). Qed.

  #[using="R U am0 HI Hg"] Lemma uu_Xok : Xok X s'.
  Proof.
    intros x Hx. destruct (inv_X HI x Hx) as [K M]. split; [rewrite uu_keys; exact K|].
    rewrite MT_upd_other; [exact M|]. intros ->.
    pose proof uu_notX as N. unfold memb in N.
    assert (E : existsb (sptr_eqb g) X = true) by (apply existsb_exists; exists g; split; [exact Hx | apply sptr_eqb_refl]).
    congruence.
  Qed.

  (* [comment removed for export] *)
  #[using="am0 Hg G"] Lemma uu_used_fwd p a : usedX X s p a -> exists a', usedX X s' p a' /\
     am_mem a' = am_mem a /\ am_last a' = am_last a /\ am_sc a' = am_sc a /\ am_maplen a' = am_maplen a /\
     stride_of a' = stride_of a /\ gframes_kept X s a a'.
  Proof.
    intros Hp. destruct (sptr_eq_dec p g) as [->|Hne].
    - exists am1. pose proof (usedX_fun _ _ _ _ _ Hp Hg) as ->. split; [apply uu_usedX_g|].
      destruct G as (G1 & G2 & G3 & G4 & G5). repeat split; auto. eapply geom_same_upto_stride. exact G.
    - exists a. split; [apply uu_usedX_other; assumption|]. repeat split; auto. intros j fr _ H1 H2. left. exact H1.
  Qed.

  #[using="Hg G Lk"] Lemma uu_used_bwd p a' : usedX X s' p a' -> exists a, usedX X s p a /\
     am_mem a' = am_mem a /\ am_last a' = am_last a /\ am_sc a' = am_sc a /\ am_maplen a' = am_maplen a /\
     stride_of a' = stride_of a /\ am_prev a' = am_prev a /\ am_next a' = am_next a /\
     (p <> g -> a' = a) /\ (p = g -> a' = am1 /\ a = am0).
  Proof.
    intros Hp. apply uu_usedX_inv in Hp as [[-> ->] | [Hne Hp]].
    - exists am0. split; [exact Hg|]. destruct G as (G1 & G2 & G3 & G4 & G5). destruct Lk as [L1 L2].
      repeat split; auto; try congruence. eapply geom_same_upto_stride. exact G.
    - exists a'. repeat split; auto; congruence.
  Qed.

  #[using="am0 Hg G"] Lemma uu_nested p a a' :
    usedX X s p a ->
    am_maplen a' = am_maplen a -> am_sc a' = am_sc a -> am_mem a' = am_mem a -> am_last a' = am_last a ->
    nested_ok X s a -> nested_ok X s' a'.
  Proof.
    intros Up E1 E2 E3 E4 N Hm. rewrite E1 in Hm. destruct (N Hm) as [N63 (g' & b & i' & fr' & Hu & Hi & Hf & Hk & Hmem & Hsc & Hsc' & Hfit)].
    split; [congruence|].
    destruct (uu_used_fwd _ _ Hu) as (b' & Hu' & M1 & M2 & M3 & M4 & M5 & M6).
    assert (Hf' : ss_fr (nth_slot b' i') = Some fr').
    { destruct (M6 i' fr' ltac:(lia) Hf Hk) as [H|H]; [exact H|]. exfalso. exact (H p a Up Hm Hmem). }
    exists g', b', i', fr'. rewrite E2, E3, E4. split; [exact Hu'|]. split; [rewrite M2; exact Hi|].
    split; [exact Hf'|]. split; [exact Hk|]. split; [unfold slot_start in *; rewrite M1, M5; exact Hmem|].
    split; [rewrite M3; exact Hsc|]. split; [rewrite M3; exact Hsc'|]. exact Hfit.
  Qed.

  #[using="Type"] Lemma uu_mapped a a' :
    am_maplen a' = am_maplen a -> am_mem a' = am_mem a -> am_last a' = am_last a -> stride_of a' = stride_of a ->
    am_sc a' = am_sc a ->
    mapped_ok s a -> mapped_ok s' a'.
  Proof.
    intros E1 E2 E3 E4 E5 M Hm. rewrite E1 in Hm. destruct (M Hm) as (r & rg & H1 & H2 & H3 & H4 & H5 & H6 & H7).
    exists r, rg. rewrite E1, E2, E3, E4, E5. repeat split; auto.
  Qed.

  #[using="am0 Hg G"] Lemma uu_inside a a' b b' :
    am_mem a' = am_mem a -> group_extent a' = group_extent a ->
    am_mem b' = am_mem b -> am_last b' = am_last b -> stride_of b' = stride_of b ->
    gframes_kept X s b b' ->
    inside X s a b -> inside X s' a' b'.
  Proof.
    intros A1 A2 B1 B2 B3 B4 (j & fr & c & ac & Hj & Hfr & Hk & Hc & Hml & Hmem & Hlo & Hhi & Hfit).
    destruct (uu_used_fwd _ _ Hc) as (ac' & Hc' & C1 & C2 & C3 & C4 & C5 & C6).
    exists j, fr, c, ac'.
    split; [rewrite B2; exact Hj|].
    split; [destruct (B4 j fr ltac:(lia) Hfr Hk) as [H|H]; [exact H | exfalso; exact (H c ac Hc Hml Hmem)]|].
    split; [exact Hk|].
    split; [exact Hc'|].
    split; [rewrite C4; exact Hml|].
    split; [unfold slot_start in *; rewrite C1, B1, B3; exact Hmem|].
    split; [rewrite C1, A1; exact Hlo|].
    split; [rewrite A1, A2, C1; unfold group_extent in *; rewrite C5, C2; exact Hhi|].
    unfold group_extent in *. rewrite C5, C2. exact Hfit.
  Qed.

  #[using="R U am0 HI Hg G Lk"] Lemma uu_laminar : laminar X s'.
  Proof.
    intros p1 a1' p2 a2' H1 H2 Hne Hr.
    destruct (uu_used_bwd _ _ H1) as (a1 & U1 & M1 & L1 & S1 & P1 & T1 & _ & _ & _).
    destruct (uu_used_bwd _ _ H2) as (a2 & U2 & M2 & L2 & S2 & P2 & T2 & _ & _ & _).
    assert (X1 : group_extent a1' = group_extent a1) by (unfold group_extent; rewrite T1, L1; reflexivity).
    assert (X2 : group_extent a2' = group_extent a2) by (unfold group_extent; rewrite T2, L2; reflexivity).
    assert (F1 : gframes_kept X s a1 a1').
    { destruct (uu_used_fwd _ _ U1) as (x & Ux & _ & _ & _ & _ & _ & Fx). pose proof (usedX_fun _ _ _ _ _ Ux H1) as ->. exact Fx. }
    assert (F2 : gframes_kept X s a2 a2').
    { destruct (uu_used_fwd _ _ U2) as (x & Ux & _ & _ & _ & _ & _ & Fx). pose proof (usedX_fun _ _ _ _ _ Ux H2) as ->. exact Fx. }
    destruct (inv_laminar HI p1 a1 p2 a2 U1 U2 Hne ltac:(rewrite <- M1, <- M2; exact Hr)) as [D | [I | I]].
    - left. unfold spans_disjoint in *. rewrite M1, M2, X1, X2. exact D.
    - right. left. eapply uu_inside; eauto.
    - right. right. eapply uu_inside; eauto.
  Qed.

  #[using="R U am0 HI Hg G Lk"] Lemma uu_maps : maps_unique X s'.
  Proof.
    intros p1 a1' p2 a2' H1 H2 Hm1 Hm2 Hr.
    destruct (uu_used_bwd _ _ H1) as (a1 & U1 & M1 & _ & _ & P1 & _).
    destruct (uu_used_bwd _ _ H2) as (a2 & U2 & M2 & _ & _ & P2 & _).
    eapply (inv_maps HI p1 a1 p2 a2); eauto; try lia. congruence.
  Qed.

  #[using="am0 Hg G Lk"] Lemma uu_alinks sc q : alinks X s' sc q = alinks X s sc q.
  Proof.
    unfold alinks. rewrite MTX_upd. destruct (sptr_eqb q g) eqn:E; [|reflexivity].
    apply sptr_eqb_eq in E. subst q. rewrite uu_notX.
    pose proof Hg as Hg'. unfold usedX in Hg'. rewrite Hg'.
    destruct G as (_ & _ & -> & _). destruct Lk as [-> ->]. reflexivity.
  Qed.

  #[using="am0 Hg"] Lemma uu_flinks q : flinks X s' q = flinks X s q.
  Proof.
    unfold flinks. rewrite MTX_upd. destruct (sptr_eqb q g) eqn:E; [|reflexivity].
    apply sptr_eqb_eq in E. subst q. rewrite uu_notX.
    pose proof Hg as Hg'. unfold usedX in Hg'. rewrite Hg'. reflexivity.
  Qed.

  #[using="R am0 HI Hg G"] Lemma uu_usage : usage_ok X U s'.
  Proof.
    intros sc Hsc. pose proof (inv_usage HI sc Hsc) as E.
    unfold usage_of in *. unfold upd_meta at 1. simp_st. rewrite E. f_equal.
    unfold class_sum. rewrite uu_keys. apply (f_equal (fun l => fold_right _ 0 l)) || idtac.
    induction (keys s) as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. f_equal.
    unfold contrib. rewrite MTX_upd. destruct (sptr_eqb k g) eqn:Ek; [|reflexivity].
    apply sptr_eqb_eq in Ek. subst k. rewrite uu_notX. pose proof Hg as Hg'. unfold usedX in Hg'. rewrite Hg'.
    destruct G as (_ & -> & -> & _). reflexivity.
  Qed.

  #[using="Type"] Lemma uu_active_hd sc : active_hd s' sc = active_hd s sc.
  Proof. reflexivity. Qed.

  Section WithObligations.
    Hypothesis Hmasks : masks_ok am1.
    Hypothesis Hslots : forall i, 0 <= i <= am_last am1 -> slot_ok R' g am1 i.
    Hypothesis Hclass : class_ok R' g am1.
    Hypothesis HRother : forall p i, p <> g -> (R' = Some (p, i) <-> R = Some (p, i)).
    Hypothesis HRg : forall i, R' = Some (g, i) ->
      0 <= i <= am_last am1 /\ ss_fr (nth_slot am1 i) = None /\ allocated am1 i = true.
    Hypothesis Hfull : am_sc am0 < 48 -> (am_prev am0, am_next am0) = (None, None) ->
      am_avail am1 = 0 /\ am_freed am1 = 0.
    Hypothesis HR1 : am_sc am0 < 48 -> am_avail am1 <> 0 -> active_hd s (am_sc am0) = Some g.
    Hypothesis HR2 : am_sc am0 < 48 -> (am_prev am0, am_next am0) <> (None, None) ->
      active_hd s (am_sc am0) <> Some g -> (forall i, R' <> Some (g, i)) -> am_freed am1 <> 0.
    Hypothesis Hpart : am_aidx am1 < am_last am1 ->
      forall p a, usedX X s p a -> p <> g -> am_sc a = am_sc am0 -> ~ am_aidx a < am_last a.
    Hypothesis Hpcg : am_aidx am1 < am_last am1 -> am_aidx am0 < am_last am0.

    #[using="R U am0 HI Hg G Lk Hmasks Hslots Hclass HRother"] Lemma uu_groups p am : usedX X s' p am -> group_ok X R' s' p am.
    Proof.
      intros Hp. destruct (uu_used_bwd _ _ Hp) as (a & Ua & M1 & M2 & M3 & M4 & M5 & _ & _ & Ho & Hs).
      pose proof (inv_groups HI p a Ua) as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
      destruct (sptr_eq_dec p g) as [->|Hne].
      - destruct (Hs eq_refl) as [-> ->].
        split; [exact Hmasks|]. split; [rewrite M4; exact Gml|]. split; [exact Hslots|].
        split; [exact Hclass|]. split; [eapply uu_mapped; eauto|]. eapply uu_nested; eauto.
      - pose proof (Ho Hne) as ->.
        split; [exact Gm|]. split; [exact Gml|]. split.
        { intros i Hi. pose proof (Gsl i Hi) as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|].
          destruct (ss_fr (nth_slot a i)) as [fr|].
          - destruct S3 as (A1 & A2 & A3 & A4). split; [exact A1|].
            split; [intros HR'; apply A2; apply (HRother p i Hne); exact HR'|].
            split; [exact A3 | exact A4].
          - destruct S3 as [A1|A1]; [left; exact A1 | right]. apply (HRother p i Hne). exact A1. }
        split.
        { destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | C].
          - left. repeat split; auto. destruct C6 as [C6|C6]; [left | right; exact C6].
            apply (HRother p 0 Hne). exact C6.
          - right. exact C. }
        split; [eapply uu_mapped; eauto | eapply uu_nested; eauto].
    Qed.

    #[using="R U am0 HI Hg G Lk HRother Hfull HR1 HR2"] Lemma uu_rings : rings_ok X R' s'.
    Proof.
      destruct (inv_rings HI) as (F & A & D).
      split.
      { destruct F as (ms & Rg & Fall). exists ms. split.
        - eapply ring_ok_ext; [| exact Rg]. intros. apply uu_flinks.
        - intros q pr nx Hq. rewrite MTX_upd in Hq. destruct (sptr_eqb q g); [|eapply Fall; exact Hq].
          destruct (memb g X); discriminate. }
      split.
      { intros sc Hsc. destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
        split; [eapply ring_ok_ext; [intros; apply uu_alinks | exact Rg] |].
        rewrite uu_active_hd.
        split.
        { intros q a Hq Hsca. destruct (uu_used_bwd _ _ Hq) as (a0 & Ua & _ & _ & M3 & _ & _ & P1 & P2 & _ & _).
          rewrite P1, P2. apply (Mem q a0 Ua). congruence. }
        split.
        { intros q a Hq Hsca Hnin. destruct (uu_used_bwd _ _ Hq) as (a0 & Ua & _ & _ & M3 & _ & _ & P1 & P2 & Ho & Hs).
          destruct (sptr_eq_dec q g) as [->|Hne].
          - destruct (Hs eq_refl) as [-> ->]. apply Hfull; [lia|].
            destruct (Mem g am0 Hg ltac:(congruence)) as [M1 M2].
            destruct (am_prev am0), (am_next am0); try reflexivity; exfalso; apply Hnin, M2; discriminate.
          - pose proof (Ho Hne) as ->. apply (Full q a0 Ua); [congruence | exact Hnin]. }
        split.
        { intros q a Hq Hsca Hav. destruct (uu_used_bwd _ _ Hq) as (a0 & Ua & _ & _ & M3 & _ & _ & P1 & P2 & Ho & Hs).
          destruct (sptr_eq_dec q g) as [->|Hne].
          - destruct (Hs eq_refl) as [-> ->]. rewrite <- Hsca, M3. apply HR1; [lia|exact Hav].
          - pose proof (Ho Hne) as ->. eapply Q1; eauto; congruence. }
        { intros q a Hq Hsca Hin Hnh HnR. destruct (uu_used_bwd _ _ Hq) as (a0 & Ua & _ & _ & M3 & _ & _ & P1 & P2 & Ho & Hs).
          destruct (sptr_eq_dec q g) as [->|Hne].
          - destruct (Hs eq_refl) as [-> ->]. apply HR2; [lia| |rewrite <- M3, Hsca; exact Hnh|exact HnR].
            intros E. apply (Mem g am0 Hg ltac:(congruence)) in Hin. apply Hin. exact E.
          - pose proof (Ho Hne) as ->. eapply Q2; eauto; try congruence.
            intros i E. apply (HnR i). apply (HRother q i Hne). exact E. } }
      { intros q a Hq H63. destruct (uu_used_bwd _ _ Hq) as (a0 & Ua & _ & _ & M3 & _ & _ & P1 & P2 & _ & _).
        rewrite P1, P2. eapply D; eauto; congruence. }
    Qed.

    #[using="R U am0 HI Hg G Lk Hpart"] Lemma uu_partial : partial_unique X s'.
    Proof.
      pose proof (inv_partial HI) as P.
      intros p1 a1 p2 a2 H1 H2 Hsc Hp1 Hp2.
      destruct (uu_used_bwd _ _ H1) as (b1 & U1 & _ & L1 & S1 & _ & _ & _ & _ & Ho1 & Hs1).
      destruct (uu_used_bwd _ _ H2) as (b2 & U2 & _ & L2 & S2 & _ & _ & _ & _ & Ho2 & Hs2).
      destruct (sptr_eq_dec p1 g) as [->|N1]; destruct (sptr_eq_dec p2 g) as [->|N2]; try reflexivity.
      - destruct (Hs1 eq_refl) as [-> ->]. pose proof (Ho2 N2) as ->.
        exfalso. eapply (Hpart Hp1 p2 b2 U2 N2); [congruence | exact Hp2].
      - destruct (Hs2 eq_refl) as [-> ->]. pose proof (Ho1 N1) as ->.
        exfalso. eapply (Hpart Hp2 p1 b1 U1 N1); [congruence | exact Hp1].
      - pose proof (Ho1 N1) as ->. pose proof (Ho2 N2) as ->. eapply P; eauto.
    Qed.

    #[using="R U am0 HI Hg G Lk Hpcg"] Lemma uu_pcg : partial_ok X s'.
    Proof.
      pose proof (inv_pcg HI) as P. intros p a Hp Ha.
      destruct (uu_used_bwd _ _ Hp) as (b & Ub & _ & _ & _ & _ & _ & _ & _ & Ho & Hs).
      destruct (sptr_eq_dec p g) as [->|N].
      - destruct (Hs eq_refl) as [-> ->]. destruct G as (_ & Gl & Gs & Gm & _).
        rewrite Gl in Ha. rewrite Gm, Gs. exact (P g am0 Hg (Hpcg ltac:(rewrite Gl; exact Ha))).
      - pose proof (Ho N) as ->. exact (P p b Ub Ha).
    Qed.

    #[using="R U am0 HI Hg HRother HRg"] Lemma uu_reserved : reserved_ok X R' s'.
    Proof.
      intros p i HR'. destruct (sptr_eq_dec p g) as [->|Hne].
      - exists am1. split; [apply uu_usedX_g|]. apply HRg. exact HR'.
      - apply (HRother p i Hne) in HR'. destruct (inv_reserved HI p i HR') as (a & Ua & Hi & Hf & Ha).
        exists a. split; [apply uu_usedX_other; assumption|]. auto.
    Qed.

    #[using="R am0 HI Hg G Lk Hmasks Hslots Hclass HRother HRg Hfull HR1 HR2 Hpart Hpcg"] Lemma Inv_used_update : Inv X R' U s'.
    Proof.
      split; [apply uu_ctx|]. split; [apply uu_keys_ok|]. split; [apply uu_areas|].
      split; [apply uu_Xok|]. split; [apply uu_groups|]. split; [apply uu_laminar|].
      split; [apply uu_maps|]. split; [apply uu_rings|]. split; [apply uu_usage|].
      split; [apply uu_reserved|]. split; [apply uu_partial | apply uu_pcg].
    Qed.
  End WithObligations.
End UsedUpdate.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Transfer.
  Variables (X X' : list sptr) (R : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate).
  Hypothesis HI : Inv X R U s.
  Hypothesis EU : forall p am, usedX X' s' p am <-> usedX X s p am.
  Hypothesis ER : st_regions s' = st_regions s.

  #[using="EU"] Lemma tr_nested a : nested_ok X s a -> nested_ok X' s' a.
  Proof.
    intros N Hm. destruct (N Hm) as [N63 (g' & b & i' & fr' & Hu & Hrest)].
    split; [exact N63|]. exists g', b, i', fr'. split; [apply EU; exact Hu | exact Hrest].
  Qed.

  #[using="ER"] Lemma tr_mapped a : mapped_ok s a -> mapped_ok s' a.
  Proof.
    intros M Hm. destruct (M Hm) as (r & rg & H). exists r, rg. unfold region_of in *. rewrite ER. exact H.
  Qed.

  #[using="U' EU"] Lemma tr_inside a b : inside X s a b -> inside X' s' a b.
  Proof.
    intros (j & fr & c & ac & H1 & H2 & H3 & H4 & H5). exists j, fr, c, ac.
    repeat split; try tauto. apply EU. exact H4.
  Qed.

  #[using="X U s HI EU ER"] Lemma tr_groups : forall g am, usedX X' s' g am -> group_ok X' R s' g am.
  Proof.
    intros g am Hg. apply EU in Hg. pose proof (inv_groups HI g am Hg) as (G1 & G2 & G3 & G4 & G5 & G6).
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [apply tr_mapped; exact G5 | apply tr_nested; exact G6].
  Qed.

  #[using="X R U U' s HI EU"] Lemma tr_laminar : laminar X' s'.
  Proof.
    intros p1 a1 p2 a2 H1 H2 Hne Hr. apply EU in H1. apply EU in H2.
    destruct (inv_laminar HI p1 a1 p2 a2 H1 H2 Hne Hr) as [D|[I|I]];
      [left; exact D | right; left; apply tr_inside; exact I | right; right; apply tr_inside; exact I].
  Qed.

  #[using="X R U s HI EU"] Lemma tr_maps : maps_unique X' s'.
  Proof. intros p1 a1 p2 a2 H1 H2. apply EU in H1. apply EU in H2. eapply (inv_maps HI); eauto. Qed.

  #[using="X R U s HI EU"] Lemma tr_partial : partial_unique X' s'.
  Proof. intros p1 a1 p2 a2 H1 H2. apply EU in H1. apply EU in H2. eapply (inv_partial HI); eauto. Qed.

  #[using="X R U s HI EU"] Lemma tr_pcg : partial_ok X' s'.
  Proof. intros p a H1. apply EU in H1. eapply (inv_pcg HI); eauto. Qed.

  #[using="X U s HI EU"] Lemma tr_reserved : reserved_ok X' R s'.
  Proof.
    intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hu & H). exists am. split; [apply EU; exact Hu | exact H].
  Qed.

  #[using="X R U s HI EU"] Lemma tr_direct : direct_unlinked X' s'.
  Proof. intros g am Hg. apply EU in Hg. exact (proj2 (proj2 (inv_rings HI)) g am Hg). Qed.

  (* [comment removed for export] *)
  #[using="EU"] Lemma tr_alinks sc q : alinks X' s' sc q = alinks X s sc q.
  Proof.
    unfold alinks.
    destruct (MTX X' s' q) as [[pr nx| |am]|] eqn:E1; destruct (MTX X s q) as [[pr' nx'| |am']|] eqn:E2; try reflexivity.
    all: try (assert (Hu : usedX X' s' q am) by exact E1; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E2; try discriminate; injection E2 as ->; reflexivity).
    all: try (assert (Hu : usedX X s q am') by exact E2; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E1; discriminate).
  Qed.

  #[using="EU"] Lemma tr_active sc : st_active s' = st_active s -> active_ring_ok X R s sc -> active_ring_ok X' R s' sc.
  Proof.
    intros EA (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
    assert (EH : active_hd s' sc = active_hd s sc) by (unfold active_hd; rewrite EA; reflexivity).
    rewrite EH. split; [eapply ring_ok_ext; [intros; apply tr_alinks | exact Rg] |].
    split; [intros q a Hq; apply EU in Hq; apply Mem; exact Hq|].
    split; [intros q a Hq; apply EU in Hq; apply Full; exact Hq|].
    split; [intros q a Hq; apply EU in Hq; apply Q1; exact Hq|].
    intros q a Hq; apply EU in Hq; apply Q2; exact Hq.
  Qed.

  #[using="X U s HI EU ER"] Theorem Inv_transfer :
    ctx_ok s' -> keys_ok s' -> areas_ok s' -> Xok X' s' -> rings_ok X' R s' -> usage_ok X' U' s' ->
    Inv X' R U' s'.
  Proof.
    intros C K A XO RG US.
    split; [exact C|]. split; [exact K|]. split; [exact A|].
    split; [exact XO|]. split; [apply tr_groups|]. split; [apply tr_laminar|]. split; [apply tr_maps|].
    split; [exact RG|]. split; [exact US|]. split; [apply tr_reserved|]. split; [apply tr_partial | apply tr_pcg].
  Qed.
End Transfer.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nth_slot_upd_slot am i j x :
  0 <= i -> 0 <= j -> (Z.to_nat i < length (am_slots am))%nat ->
  nth_slot (upd_slot am i x) j = if j =? i then x else nth_slot am j.
Proof.
  intros Hi Hj Hlen. unfold nth_slot, upd_slot. cbn [am_slots am_set_slots]. rewrite nth_lupd.
  destruct (j =? i) eqn:E.
  - apply Z.eqb_eq in E. subst j. rewrite Nat.eqb_refl.
    replace (Nat.ltb (Z.to_nat i) (length (am_slots am))) with true; [reflexivity|].
    symmetry. apply Nat.ltb_lt. exact Hlen.
  - replace (Nat.eqb (Z.to_nat j) (Z.to_nat i)) with false; [reflexivity|].
    symmetry. apply Nat.eqb_neq. apply Z.eqb_neq in E. lia.
Qed.

Lemma flat_map_ext_In {A B} (f g : A -> list B) l :
  (forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l.
Proof.
  induction l as [|x t IH]; intros H; [reflexivity|]. cbn. rewrite H by (left; reflexivity).
  rewrite IH by (intros a Ha; apply H; right; exact Ha). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition slot_block0 (am : ameta) (i : Z) : list (sptr * Z) :=
  match ss_fr (nth_slot am i) with
  | Some fr => match fr_kind fr with
               | FUser => [(padd (slot_start am i) (UNIT * fr_off fr), fr_n fr)]
               | FGroup => []
               end
  | None => []
  end.
Definition blocks_of0 (am : ameta) : list (sptr * Z) := flat_map (slot_block0 am) (zseq 0 (am_last am + 1)).
Definition ucontrib0 (x : option mslot) : list (sptr * Z) :=
  match x with Some (MUsed am) => blocks_of0 am | _ => [] end.
Definition ublist0 (s : astate) : list (sptr * Z) := flat_map (fun g => ucontrib0 (MT s g)) (keys s).

Lemma user_blocks_ublist0 s : NoDup (keys s) -> user_blocks s = ublist0 s.
Proof.
  unfold user_blocks, ublist0, used_metas, keys, MT. generalize (st_metas s) as l. clear s.
  induction l as [|[p x] t IH]; intros ND; cbn; [reflexivity|].
  inversion ND as [|p' t' Hp Ht]; subst. rewrite sptr_eqb_refl.
  assert (E : flat_map (fun g => ucontrib0 (mlookup ((p, x) :: t) g)) (map fst t) = flat_map (fun g => ucontrib0 (mlookup t g)) (map fst t)).
  { apply flat_map_ext_In. intros g Hg. cbn. destruct (sptr_eqb g p) eqn:Eg; [|reflexivity].
    apply sptr_eqb_eq in Eg. subst g. exfalso. exact (Hp Hg). }
  cbn in E. rewrite E, <- (IH Ht). destruct x as [| |am]; cbn; reflexivity.
Qed.

(* [comment removed for export] *)
Notation ublk := ((sptr * Z) * (sptr * Z))%type (only parsing).

Definition slot_block (g : sptr) (am : ameta) (i : Z) : list ublk :=
  match ss_fr (nth_slot am i) with
  | Some fr => match fr_kind fr with
               | FUser => [((padd (slot_start am i) (UNIT * fr_off fr), fr_n fr), (g, i))]
               | FGroup => []
               end
  | None => []
  end.

Definition blocks_of (g : sptr) (am : ameta) : list ublk := flat_map (slot_block g am) (zseq 0 (am_last am + 1)).

Definition ucontrib (g : sptr) (x : option mslot) : list ublk :=
  match x with Some (MUsed am) => blocks_of g am | _ => [] end.

Definition ublist (s : astate) : list ublk := flat_map (fun g => ucontrib g (MT s g)) (keys s).

Lemma map_fst_blocks_of g am : map fst (blocks_of g am) = blocks_of0 am.
Proof.
  unfold blocks_of, blocks_of0. induction (zseq 0 (am_last am + 1)) as [|i z IH]; [reflexivity|].
  simpl. rewrite map_app, IH. f_equal.
  unfold slot_block, slot_block0. destruct (ss_fr (nth_slot am i)) as [fr|]; [destruct (fr_kind fr)|]; reflexivity.
Qed.

Lemma map_fst_ucontrib g x : map fst (ucontrib g x) = ucontrib0 x.
Proof. destruct x as [[| |am]|]; cbn [ucontrib ucontrib0 map]; try reflexivity. apply map_fst_blocks_of. Qed.

Lemma map_fst_ublist s : map fst (ublist s) = ublist0 s.
Proof.
  unfold ublist, ublist0. induction (keys s) as [|g k IH]; [reflexivity|]. simpl. rewrite map_app, IH, map_fst_ucontrib. reflexivity.
Qed.

Lemma user_blocks_ublist s : NoDup (keys s) -> user_blocks s = map fst (ublist s).
Proof. intros ND. rewrite map_fst_ublist. apply user_blocks_ublist0. exact ND. Qed.

Definition ub_same (s s' : astate) : Prop :=
  exists ext, keys s' = keys s ++ ext /\ (forall m, In m ext -> ucontrib m (MT s' m) = []) /\
    (forall g, In g (keys s) -> ucontrib g (MT s' g) = ucontrib g (MT s g)).

Lemma ub_same_refl s : ub_same s s.
Proof. exists []. rewrite app_nil_r. split; [reflexivity|]. split; [intros m []|]. intros; reflexivity. Qed.

Lemma ub_same_trans s1 s2 s3 : ub_same s1 s2 -> ub_same s2 s3 -> ub_same s1 s3.
Proof.
  intros (e1 & K1 & Z1 & S1) (e2 & K2 & Z2 & S2). exists (e1 ++ e2). rewrite K2, K1, <- app_assoc. split; [reflexivity|]. split.
  - intros m Hm. apply in_app_iff in Hm as [Hm|Hm]; [|apply Z2; exact Hm].
    rewrite S2; [apply Z1; exact Hm|]. rewrite K1. apply in_app_iff. right. exact Hm.
  - intros g Hg. rewrite S2; [apply S1; exact Hg|]. rewrite K1. apply in_app_iff. left. exact Hg.
Qed.

Lemma flat_map_nil_In {A B} (f : A -> list B) l : (forall a, In a l -> f a = []) -> flat_map f l = [].
Proof.
  induction l as [|x t IH]; intros H; [reflexivity|]. cbn. rewrite H by (left; reflexivity). cbn. apply IH. intros a Ha. apply H. right. exact Ha.
Qed.

Lemma ub_same_ublist s s' : ub_same s s' -> ublist s' = ublist s.
Proof.
  intros (ext & K & Zx & Sm). unfold ublist. rewrite K, flat_map_app.
  rewrite (flat_map_ext_In _ _ (keys s) Sm). rewrite (flat_map_nil_In _ ext Zx). apply app_nil_r.
Qed.

Lemma ub_same_user_blocks s s' : NoDup (keys s) -> NoDup (keys s') -> ub_same s s' -> user_blocks s' = user_blocks s.
Proof. intros N N' H. rewrite (user_blocks_ublist s N), (user_blocks_ublist s' N'). f_equal. apply ub_same_ublist. exact H. Qed.

Lemma ub_same_metas s s' : st_metas s' = st_metas s -> ub_same s s'.
Proof. intros E. exists []. unfold keys, MT. rewrite E, app_nil_r. split; [reflexivity|]. split; [intros m []|]. intros; reflexivity. Qed.

Lemma ub_same_upd_In s g x : In g (keys s) -> ucontrib g (Some x) = ucontrib g (MT s g) -> ub_same s (upd_meta g x s).
Proof.
  intros Hg Hx. exists []. rewrite app_nil_r. split; [apply keys_upd_In; exact Hg|]. split; [intros m []|].
  intros q Hq. rewrite MT_upd. destruct (sptr_eqb q g) eqn:E; [apply sptr_eqb_eq in E; subst q; exact Hx | reflexivity].
Qed.

Lemma ub_same_upd_notIn s g x : ~ In g (keys s) -> ucontrib g (Some x) = [] -> ub_same s (upd_meta g x s).
Proof.
  intros Hg Hx. exists [g]. split; [apply keys_upd_notIn; exact Hg|]. split.
  - intros m [<-|[]]. rewrite MT_upd_same. exact Hx.
  - intros q Hq. rewrite MT_upd_other; [reflexivity|]. intros ->. exact (Hg Hq).
Qed.

(* [comment removed for export] *)
Lemma blocks_of_ext g a b :
  am_mem b = am_mem a -> am_last b = am_last a -> am_sc b = am_sc a -> am_maplen b = am_maplen a -> am_slots b = am_slots a ->
  blocks_of g b = blocks_of g a.
Proof. intros E1 E2 E3 E4 E5. unfold blocks_of, slot_block, nth_slot, slot_start, stride_of. rewrite E1, E2, E3, E4, E5. reflexivity. Qed.

Lemma blocks_of_links g p n am : blocks_of g (am_set_links p n am) = blocks_of g am.
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.

Lemma blocks_of_masks g av fr ai am : blocks_of g (am_set_aidx ai (am_set_freed fr (am_set_avail av am))) = blocks_of g am.
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.

Lemma blocks_of_avail g av am : blocks_of g (am_set_avail av am) = blocks_of g am.
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.

Lemma blocks_of_freed g fr am : blocks_of g (am_set_freed fr am) = blocks_of g am.
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.

Lemma blocks_of_aidx g ai am : blocks_of g (am_set_aidx ai am) = blocks_of g am.
Proof. apply blocks_of_ext; destruct am; reflexivity. Qed.

Lemma ucontrib_with_links g x p n : ucontrib g (Some (with_links x p n)) = ucontrib g (Some x).
Proof. destruct x; cbn; [reflexivity | reflexivity | apply blocks_of_links]. Qed.

Lemma blocks_of_frameless g am : (forall j, ss_fr (nth_slot am j) = None) -> blocks_of g am = [].
Proof.
  intros H. unfold blocks_of. induction (zseq 0 (am_last am + 1)) as [|i t IH]; [reflexivity|]. cbn. unfold slot_block at 1. rewrite H. exact IH.
Qed.

(* [comment removed for export] *)
Definition slotst_block (g : sptr) (am : ameta) (i : Z) (x : slotst) : list ublk :=
  match ss_fr x with
  | Some fr => match fr_kind fr with
               | FUser => [((padd (slot_start am i) (UNIT * fr_off fr), fr_n fr), (g, i))]
               | FGroup => []
               end
  | None => []
  end.

Lemma slot_block_upd_slot g am i x j :
  0 <= i -> 0 <= j -> (Z.to_nat i < length (am_slots am))%nat ->
  slot_block g (upd_slot am i x) j = if j =? i then slotst_block g am i x else slot_block g am j.
Proof.
  intros Hi Hj Hlen. unfold slot_block, slotst_block. rewrite nth_slot_upd_slot by assumption.
  replace (slot_start (upd_slot am i x) j) with (slot_start am j) by (destruct am; reflexivity).
  destruct (j =? i) eqn:E; [apply Z.eqb_eq in E; subst j|]; reflexivity.
Qed.

Lemma zseq_NoDup lo n : NoDup (zseq lo n).
Proof.
  unfold zseq. apply NoDup_map_inv with (f := fun z => Z.to_nat (z - lo)).
  rewrite map_map. erewrite map_ext; [rewrite map_id; apply seq_NoDup|]. intros a. cbn. lia.
Qed.

Lemma blocks_of_upd_slot g am i x :
  0 <= i <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) ->
  exists l1 l2, blocks_of g am = l1 ++ slot_block g am i ++ l2 /\ blocks_of g (upd_slot am i x) = l1 ++ slotst_block g am i x ++ l2.
Proof.
  intros Hi Hlen. unfold blocks_of.
  replace (am_last (upd_slot am i x)) with (am_last am) by (destruct am; reflexivity).
  assert (Hin : In i (zseq 0 (am_last am + 1))) by (apply In_zseq; lia).
  destruct (in_split _ _ Hin) as (z1 & z2 & Ez).
  pose proof (zseq_NoDup 0 (am_last am + 1)) as ND. rewrite Ez in ND. pose proof (NoDup_remove_2 _ _ _ ND) as Hni.
  assert (EF : forall j, In j (z1 ++ z2) -> slot_block g (upd_slot am i x) j = slot_block g am j).
  { intros j Hj.
    assert (Hj0 : 0 <= j).
    { assert (In j (zseq 0 (am_last am + 1))) as H.
      { rewrite Ez. apply in_app_iff in Hj. apply in_app_iff. destruct Hj; [left | right; right]; assumption. }
      apply In_zseq in H. lia. }
    rewrite slot_block_upd_slot by (try lia; rewrite Hlen; lia). destruct (j =? i) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E. subst j. exfalso. exact (Hni Hj). }
  exists (flat_map (slot_block g am) z1), (flat_map (slot_block g am) z2).
  rewrite Ez, !flat_map_app. cbn [flat_map]. split; [reflexivity|].
  rewrite (flat_map_ext_In _ _ z1 (fun j Hj => EF j ltac:(apply in_app_iff; left; exact Hj))).
  rewrite (flat_map_ext_In _ _ z2 (fun j Hj => EF j ltac:(apply in_app_iff; right; exact Hj))).
  rewrite slot_block_upd_slot, Z.eqb_refl by (try lia; rewrite Hlen; lia). reflexivity.
Qed.

Lemma blocks_of_upd_slot_same g am i x :
  0 <= i <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) ->
  slotst_block g am i x = slot_block g am i -> blocks_of g (upd_slot am i x) = blocks_of g am.
Proof.
  intros Hi Hlen E. destruct (blocks_of_upd_slot g am i x Hi Hlen) as (l1 & l2 & E1 & E2). rewrite E2, E, <- E1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ublist_split s g :
  NoDup (keys s) -> In g (keys s) ->
  exists L1 L2, (forall x, ublist (upd_meta g x s) = L1 ++ ucontrib g (Some x) ++ L2) /\ ublist s = L1 ++ ucontrib g (MT s g) ++ L2.
Proof.
  intros ND Hg. destruct (in_split _ _ Hg) as (k1 & k2 & Ek).
  pose proof ND as ND'. rewrite Ek in ND'. pose proof (NoDup_remove_2 _ _ _ ND') as Hni.
  exists (flat_map (fun q => ucontrib q (MT s q)) k1), (flat_map (fun q => ucontrib q (MT s q)) k2). split.
  - intros x. unfold ublist. rewrite (keys_upd_In _ _ _ Hg), Ek, flat_map_app. cbn [flat_map]. rewrite MT_upd_same.
    rewrite (flat_map_ext_In (fun q => ucontrib q (MT (upd_meta g x s) q)) (fun q => ucontrib q (MT s q)) k1).
    2:{ intros q Hq. rewrite MT_upd_other; [reflexivity|]. intros ->. apply Hni. apply in_app_iff. left. exact Hq. }
    rewrite (flat_map_ext_In (fun q => ucontrib q (MT (upd_meta g x s) q)) (fun q => ucontrib q (MT s q)) k2).
    2:{ intros q Hq. rewrite MT_upd_other; [reflexivity|]. intros ->. apply Hni. apply in_app_iff. right. exact Hq. }
    reflexivity.
  - unfold ublist. rewrite Ek, flat_map_app. reflexivity.
Qed.

Lemma ublist_upd_slot s g am i x :
  NoDup (keys s) -> MT s g = Some (MUsed am) -> 0 <= i <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) ->
  exists l1 l2, ublist s = l1 ++ slot_block g am i ++ l2 /\
                ublist (upd_meta g (MUsed (upd_slot am i x)) s) = l1 ++ slotst_block g am i x ++ l2.
Proof.
  intros ND Mg Hi Hlen.
  destruct (ublist_split s g ND (MT_Some_In_keys _ _ _ Mg)) as (L1 & L2 & Hupd & Hs).
  destruct (blocks_of_upd_slot g am i x Hi Hlen) as (l1 & l2 & B1 & B2).
  exists (L1 ++ l1), (l2 ++ L2). rewrite Hs, Hupd, Mg. cbn [ucontrib]. rewrite B1, B2, <- !app_assoc. split; reflexivity.
Qed.
End MallocWfFrame.


Module MallocWfRingOps.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Ltac mbinds := repeat lazymatch goal with |- itok (bind _ _ _) _ => apply itok_bind end.

(* [comment removed for export] *)
Definition LK (s : astate) (q : sptr) : option (option sptr * option sptr) :=
  match MT s q with Some x => Some (links_of x) | None => None end.

Lemma links_with_links x pr nx : links_of (with_links x pr nx) = (pr, nx).
Proof. destruct x; reflexivity. Qed.

Lemma with_links_with_links x a b c d : with_links (with_links x a b) c d = with_links x c d.
Proof. destruct x; reflexivity. Qed.

(* [comment removed for export] *)
Definition set_head_st (h : headloc) (v : option sptr) (s : astate) : astate :=
  match h with
  | HActive sc => set_active (lupd (st_active s) (Z.to_nat sc) v) s
  | HFreeMeta => set_free_meta_head v s
  end.

Lemma itok_set_head' h v s (Q : unit * astate -> Prop) : Q (tt, set_head_st h v s) -> itok (set_head h v s) Q.
Proof. intros H. apply itok_set_head. destruct h; exact H. Qed.

Definition head_of (h : headloc) (s : astate) : option sptr :=
  match h with HActive sc => active_hd s sc | HFreeMeta => st_free_meta_head s end.

Lemma itok_get_head' h s (Q : option sptr * astate -> Prop) : Q (head_of h s, s) -> itok (get_head h s) Q.
Proof. intros H. apply itok_get_head. destruct h; exact H. Qed.

Definition head_idx_ok (h : headloc) (s : astate) : Prop :=
  match h with HActive sc => (Z.to_nat sc < length (st_active s))%nat | HFreeMeta => True end.

Lemma st_metas_set_head h v s : st_metas (set_head_st h v s) = st_metas s.
Proof. destruct h; reflexivity. Qed.

Lemma MT_set_head h v s q : MT (set_head_st h v s) q = MT s q.
Proof. unfold MT. rewrite st_metas_set_head. reflexivity. Qed.

Lemma head_of_set_head h v s : head_idx_ok h s -> head_of h (set_head_st h v s) = v.
Proof.
  destruct h as [sc|]; cbn; [|reflexivity]. intros Hi. unfold active_hd. cbn [st_active set_active].
  rewrite nth_lupd, Nat.eqb_refl. replace (Nat.ltb (Z.to_nat sc) (length (st_active s))) with true; [reflexivity|].
  symmetry. apply Nat.ltb_lt. exact Hi.
Qed.

Lemma nth_active_set_head h v s k :
  (forall sc, h = HActive sc -> k <> Z.to_nat sc) ->
  nth k (st_active (set_head_st h v s)) None = nth k (st_active s) None.
Proof.
  intros Hk. destruct h as [sc|]; cbn [st_active set_head_st set_active set_free_meta_head]; [|reflexivity].
  rewrite nth_lupd. replace (Nat.eqb k (Z.to_nat sc)) with false; [reflexivity|].
  symmetry. apply Nat.eqb_neq. apply Hk. reflexivity.
Qed.

Lemma fmh_set_head h v s : h <> HFreeMeta -> st_free_meta_head (set_head_st h v s) = st_free_meta_head s.
Proof. destruct h; [reflexivity | intros H; exfalso; apply H; reflexivity]. Qed.

Lemma length_active_set_head h v s : length (st_active (set_head_st h v s)) = length (st_active s).
Proof. destruct h; cbn; [apply length_lupd | reflexivity]. Qed.

Lemma head_idx_ok_set_head h h' v s : head_idx_ok h s -> head_idx_ok h (set_head_st h' v s).
Proof. unfold head_idx_ok. rewrite length_active_set_head. auto. Qed.

Lemma head_idx_ok_upd_meta h g x s : head_idx_ok h s -> head_idx_ok h (upd_meta g x s).
Proof. unfold head_idx_ok, upd_meta. cbn. auto. Qed.

Lemma head_of_upd_meta h g x s : head_of h (upd_meta g x s) = head_of h s.
Proof. destruct h; reflexivity. Qed.

(* [comment removed for export] *)
Lemma itok_set_links' p pr nx s x (Q : unit * astate -> Prop) :
  MT s p = Some x -> Q (tt, upd_meta p (with_links x pr nx) s) -> itok (set_links p pr nx s) Q.
Proof. intros. eapply itok_set_links; eauto. Qed.

Lemma itok_setm' p am s (Q : unit * astate -> Prop) : Q (tt, upd_meta p (MUsed am) s) -> itok (setm p am s) Q.
Proof. intros. apply itok_setm. assumption. Qed.

Lemma itok_setslot' p x s (Q : unit * astate -> Prop) : Q (tt, upd_meta p x s) -> itok (setslot p x s) Q.
Proof. intros. apply itok_setslot. assumption. Qed.

(* [comment removed for export] *)
Lemma itok_set_next p nx s x (Q : unit * astate -> Prop) :
  MT s p = Some x ->
  Q (tt, upd_meta p (with_links x (fst (links_of x)) nx) s) ->
  itok (set_next p nx s) Q.
Proof.
  intros Hm H. unfold set_next. apply itok_bind. eapply itok_get_links; [exact Hm|]. msimp.
  eapply itok_set_links; [exact Hm|]. exact H.
Qed.

Lemma itok_set_prev p pr s x (Q : unit * astate -> Prop) :
  MT s p = Some x ->
  Q (tt, upd_meta p (with_links x pr (snd (links_of x))) s) ->
  itok (set_prev p pr s) Q.
Proof.
  intros Hm H. unfold set_prev. apply itok_bind. eapply itok_get_links; [exact Hm|]. msimp.
  eapply itok_set_links; [exact Hm|]. exact H.
Qed.

(* [comment removed for export] *)
Definition same_but_metas_heads (s s' : astate) : Prop :=
  st_init_done s' = st_init_done s /\ st_mmap_counter s' = st_mmap_counter s /\
  st_avail_meta s' = st_avail_meta s /\ st_avail_meta_count s' = st_avail_meta_count s /\
  st_avail_meta_area_count s' = st_avail_meta_area_count s /\ st_meta_alloc_shift s' = st_meta_alloc_shift s /\
  st_area_head s' = st_area_head s /\ st_area_tail s' = st_area_tail s /\
  st_avail_meta_areas s' = st_avail_meta_areas s /\ st_usage s' = st_usage s /\
  st_unmap_seq s' = st_unmap_seq s /\ st_bounces s' = st_bounces s /\ st_seq s' = st_seq s /\
  st_brk s' = st_brk s /\ st_regions s' = st_regions s /\ st_areas s' = st_areas s /\
  keys s' = keys s.

Definition heads_same_except (h : headloc) (s s' : astate) : Prop :=
  (forall k, (forall sc, h = HActive sc -> k <> Z.to_nat sc) -> nth k (st_active s') None = nth k (st_active s) None) /\
  (h <> HFreeMeta -> st_free_meta_head s' = st_free_meta_head s) /\
  length (st_active s') = length (st_active s).

Lemma sbmh_refl s : same_but_metas_heads s s.
Proof. repeat split; reflexivity. Qed.

Lemma sbmh_trans s1 s2 s3 : same_but_metas_heads s1 s2 -> same_but_metas_heads s2 s3 -> same_but_metas_heads s1 s3.
Proof. unfold same_but_metas_heads. intros A B. decompose [and] A. decompose [and] B. repeat split; congruence. Qed.

Lemma sbmh_upd_meta g x s : In g (keys s) -> same_but_metas_heads s (upd_meta g x s).
Proof. intros Hg. repeat split; try reflexivity. apply keys_upd_In. exact Hg. Qed.

Lemma sbmh_set_head h v s : same_but_metas_heads s (set_head_st h v s).
Proof. destruct h; repeat split; reflexivity. Qed.

Lemma hse_refl h s : heads_same_except h s s.
Proof. repeat split; reflexivity. Qed.

Lemma hse_trans h s1 s2 s3 : heads_same_except h s1 s2 -> heads_same_except h s2 s3 -> heads_same_except h s1 s3.
Proof.
  intros (A1 & A2 & A3) (B1 & B2 & B3). split; [|split]; [intros k Hk; rewrite B1, A1; auto | intros H; rewrite B2, A2; auto | congruence].
Qed.

Lemma hse_upd_meta h g x s : heads_same_except h s (upd_meta g x s).
Proof. repeat split; reflexivity. Qed.

Lemma hse_set_head h v s : heads_same_except h s (set_head_st h v s).
Proof.
  split; [|split].
  - intros k Hk. apply nth_active_set_head. exact Hk.
  - apply fmh_set_head.
  - apply length_active_set_head.
Qed.

(* [comment removed for export] *)
Lemma In_keys_of_MT s q x : MT s q = Some x -> In q (keys s).
Proof. apply MT_Some_In_keys. Qed.

(* [comment removed for export] *)
Lemma dequeue_op h m s x rest (lk : sptr -> option (option sptr * option sptr)) (Q : unit * astate -> Prop) :
  MT s m = Some x ->
  cycle_ok lk (m :: rest) ->
  (forall q l, In q (m :: rest) -> lk q = Some l -> LK s q = Some l) ->
  head_idx_ok h s ->
  (forall s',
     same_but_metas_heads s s' ->
     heads_same_except h s s' ->
     head_of h s' = (match rest with
                     | [] => None
                     | y :: _ => if osptr_eqb (head_of h s) (Some m) then Some y else head_of h s
                     end) ->
     MT s' m = Some (with_links x None None) ->
     (forall q, ~ In q (m :: rest) -> MT s' q = MT s q) ->
     (forall y xy, In y rest -> MT s y = Some xy ->
        MT s' y = Some (with_links xy
                          (if sptr_eqb y (hd m rest) then Some (last rest m) else fst (links_of xy))
                          (if sptr_eqb y (last rest m) then Some (hd m rest) else snd (links_of xy)))) ->
     Q (tt, s')) ->
  itok (dequeue h m s) Q.
Proof.
  intros Hm Hcyc Hlk Hh HQ.
  destruct Hcyc as [Hnd Hch].
  assert (Lm : lk m = Some (Some (last rest m), Some (hd m rest))).
  { cbn [chain] in Hch. rewrite last_cons in Hch. destruct Hch as [Hx _]. exact Hx. }
  pose proof (Hlk m _ (or_introl eq_refl) Lm) as LKm. unfold LK in LKm. rewrite Hm in LKm.
  injection LKm as Lx.
  pose proof (In_keys_of_MT _ _ _ Hm) as Km.
  unfold dequeue. mbinds. eapply itok_get_links; [exact Hm|]. msimp. rewrite Lx. cbn [fst snd].
  inversion Hnd as [|m' rest0 Hmn Hndr]; subst.
  destruct rest as [|y rest'].
  - (* [comment removed for export] *)
    cbn [hd]. replace (osptr_eqb (Some m) (Some m)) with true by (cbn; rewrite sptr_eqb_refl; reflexivity).
    mbinds. apply itok_set_head'. msimp.
    eapply itok_set_links; [rewrite MT_set_head; exact Hm|].
    change (Q (tt, upd_meta m (with_links x None None) (set_head_st h None s))).
    apply HQ.
    + eapply sbmh_trans; [apply sbmh_set_head | apply sbmh_upd_meta]. unfold keys. rewrite st_metas_set_head. exact Km.
    + eapply hse_trans; [apply hse_set_head | apply hse_upd_meta].
    + rewrite head_of_upd_meta. apply head_of_set_head. exact Hh.
    + rewrite MT_upd_same. reflexivity.
    + intros q Hq. rewrite MT_upd_other, MT_set_head; [reflexivity|]. intros ->. apply Hq. left. reflexivity.
    + intros z xz Hz. destruct Hz.
  - (* [comment removed for export] *)
    cbn [hd].
    assert (Hym : y <> m) by (intros ->; apply Hmn; left; reflexivity).
    replace (osptr_eqb (Some y) (Some m)) with false
      by (symmetry; apply Bool.not_true_iff_false; rewrite osptr_eqb_eq; congruence).
    remember (last (y :: rest') m) as t eqn:Et.
    (* [comment removed for export] *)
    assert (Htin : In t (y :: rest')) by (rewrite Et; apply In_last; discriminate).
    assert (Htm : t <> m) by (intros E; apply Hmn; rewrite <- E; exact Htin).
    destruct Hch as [_ Hch].
    destruct (chain_links _ _ _ _ t Hch Htin) as (tpr & tnx & Lt).
    pose proof (Hlk t _ (or_intror Htin) Lt) as LKt. unfold LK in LKt.
    destruct (MT s t) as [xt|] eqn:Mt; [|discriminate]. injection LKt as Lxt.
    destruct (chain_links _ _ _ _ y Hch (or_introl eq_refl)) as (ypr & ynx & Ly).
    pose proof (Hlk y _ (or_intror (or_introl eq_refl)) Ly) as LKy. unfold LK in LKy.
    destruct (MT s y) as [xy|] eqn:My; [|discriminate]. injection LKy as Lxy.
    (* [comment removed for export] *)
    mbinds. eapply itok_set_next; [exact Mt|]. msimp. rewrite Lxt. cbn [fst].
    (* [comment removed for export] *)
    mbinds.
    apply (itok_set_prev _ _ _ (if sptr_eqb y t then with_links xt (Some tpr) (Some y) else xy)).
    { rewrite MT_upd. destruct (sptr_eqb y t); [reflexivity | exact My]. }
    msimp.
    (* [comment removed for export] *)
    mbinds. apply itok_get_head'. msimp. rewrite !head_of_upd_meta.
    match goal with |- itok ((if ?c then _ else _) ?st) _ => set (s2 := st) end.
    assert (K2 : same_but_metas_heads s s2 /\ heads_same_except h s s2 /\ head_of h s2 = head_of h s /\
                 head_idx_ok h s2 /\
                 MT s2 m = Some x /\
                 (forall q, ~ In q (m :: y :: rest') -> MT s2 q = MT s q) /\
                 (forall z xz, In z (y :: rest') -> MT s z = Some xz ->
                    MT s2 z = Some (with_links xz
                          (if sptr_eqb z y then Some t else fst (links_of xz))
                          (if sptr_eqb z t then Some y else snd (links_of xz))))).
    { subst s2. split.
      { eapply sbmh_trans; [apply sbmh_upd_meta; eapply In_keys_of_MT; exact Mt|].
        apply sbmh_upd_meta. rewrite keys_upd_In by (eapply In_keys_of_MT; exact Mt). eapply In_keys_of_MT; exact My. }
      split; [eapply hse_trans; apply hse_upd_meta|].
      split; [rewrite !head_of_upd_meta; reflexivity|].
      split; [apply head_idx_ok_upd_meta, head_idx_ok_upd_meta; exact Hh|].
      split.
      { rewrite MT_upd_other by (intros ->; exact (Hym eq_refl)).
        rewrite MT_upd_other by (intros ->; exact (Htm eq_refl)). exact Hm. }
      split.
      { intros q Hq. rewrite MT_upd_other by (intros ->; apply Hq; right; left; reflexivity).
        rewrite MT_upd_other by (intros ->; apply Hq; right; exact Htin). reflexivity. }
      intros z xz Hz Mz. rewrite MT_upd. destruct (sptr_eqb z y) eqn:Ezy.
      - apply sptr_eqb_eq in Ezy. subst z. rewrite My in Mz. injection Mz as <-.
        destruct (sptr_eqb y t) eqn:Eyt.
        + apply sptr_eqb_eq in Eyt. rewrite <- Eyt in *. rewrite Mt in My. injection My as <-.
          rewrite with_links_with_links, links_with_links. cbn [snd]. reflexivity.
        + rewrite Lxy. cbn [snd]. reflexivity.
      - rewrite MT_upd. destruct (sptr_eqb z t) eqn:Ezt.
        + apply sptr_eqb_eq in Ezt. subst z. rewrite Mt in Mz. injection Mz as <-. rewrite Lxt. reflexivity.
        + rewrite Mz. f_equal.
          destruct (chain_links _ _ _ _ z Hch Hz) as (zp & zn & Lz).
          pose proof (Hlk z _ (or_intror Hz) Lz) as LKz. unfold LK in LKz. rewrite Mz in LKz.
          injection LKz as Lxz.
          destruct xz as [p1 n1| |am]; cbn in Lxz |- *; [injection Lxz as -> ->; reflexivity | discriminate |].
          destruct am; cbn in Lxz |- *. injection Lxz as -> ->. reflexivity. }
    clearbody s2. destruct K2 as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
    (* [comment removed for export] *)
    assert (FIN : forall s3, same_but_metas_heads s s3 -> heads_same_except h s s3 ->
              head_of h s3 = (if osptr_eqb (head_of h s) (Some m) then Some y else head_of h s) ->
              (forall q, MT s3 q = MT s2 q) -> head_idx_ok h s3 ->
              itok (set_links m None None s3) Q).
    { intros s3 T1 T2 T3 T4 T5. eapply itok_set_links; [rewrite T4; exact S5|].
      change (Q (tt, upd_meta m (with_links x None None) s3)).
      apply HQ.
      - eapply sbmh_trans; [exact T1 | apply sbmh_upd_meta]. destruct T1 as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& ->). exact Km.
      - eapply hse_trans; [exact T2 | apply hse_upd_meta].
      - rewrite head_of_upd_meta. exact T3.
      - apply MT_upd_same.
      - intros q Hq. rewrite MT_upd_other by (intros ->; apply Hq; left; reflexivity). rewrite T4. apply S6. exact Hq.
      - intros z xz Hz Mz. rewrite MT_upd_other by (intros ->; apply Hmn; exact Hz). rewrite T4.
        cbn [hd]. apply S7; assumption. }
    destruct (osptr_eqb (head_of h s) (Some m)) eqn:Ehd.
    + mbinds. apply itok_set_head'. msimp. apply FIN.
      * eapply sbmh_trans; [exact S1 | apply sbmh_set_head].
      * eapply hse_trans; [exact S2 | apply hse_set_head].
      * apply head_of_set_head. exact S4.
      * intros q. apply MT_set_head.
      * apply head_idx_ok_set_head. exact S4.
    + mbinds. apply itok_ret. msimp. apply FIN; auto.
Qed.

(* [comment removed for export] *)
Lemma queue_op h m s x ms (lk : sptr -> option (option sptr * option sptr)) (Q : unit * astate -> Prop) :
  MT s m = Some x -> links_of x = (None, None) ->
  ring_ok lk (head_of h s) ms -> ~ In m ms ->
  (forall q l, In q ms -> lk q = Some l -> LK s q = Some l) ->
  head_idx_ok h s ->
  (forall s',
     same_but_metas_heads s s' ->
     heads_same_except h s s' ->
     head_of h s' = Some (hd m ms) ->
     MT s' m = Some (with_links x (Some (last ms m)) (Some (hd m ms))) ->
     (forall q, ~ In q (m :: ms) -> MT s' q = MT s q) ->
     (forall y xy, In y ms -> MT s y = Some xy ->
        MT s' y = Some (with_links xy
                          (if sptr_eqb y (hd m ms) then Some m else fst (links_of xy))
                          (if sptr_eqb y (last ms m) then Some m else snd (links_of xy)))) ->
     Q (tt, s')) ->
  itok (queue h m s) Q.
Proof.
  intros Hm Lx Hring Hnin Hlk Hh HQ.
  pose proof (In_keys_of_MT _ _ _ Hm) as Km.
  unfold queue. mbinds. eapply itok_get_links; [exact Hm|]. msimp. rewrite Lx. cbn [fst snd].
  mbinds. apply itok_massert; [reflexivity|]. msimp.
  mbinds. apply itok_get_head'. msimp.
  destruct Hring as [[Hnd Hch] Hhd].
  destruct ms as [|h0 rest].
  - (* [comment removed for export] *)
    cbn in Hhd. rewrite Hhd.
    mbinds. eapply itok_set_links'; [exact Hm|]. msimp.
    apply itok_set_head'.
    apply HQ.
    + eapply sbmh_trans; [apply sbmh_upd_meta; exact Km | apply sbmh_set_head].
    + eapply hse_trans; [apply hse_upd_meta | apply hse_set_head].
    + cbn [hd]. apply head_of_set_head. apply head_idx_ok_upd_meta. exact Hh.
    + rewrite MT_set_head, MT_upd_same. reflexivity.
    + intros q Hq. rewrite MT_set_head, MT_upd_other; [reflexivity|]. intros ->. apply Hq. left. reflexivity.
    + intros y xy Hy. destruct Hy.
  - cbn in Hhd. rewrite Hhd.
    assert (Hh0m : h0 <> m) by (intros ->; apply Hnin; left; reflexivity).
    remember (last (h0 :: rest) m) as t eqn:Et.
    assert (Et' : last (h0 :: rest) h0 = t) by (rewrite Et; apply last_indep; discriminate).
    rewrite Et' in Hch.
    assert (Htin : In t (h0 :: rest)) by (rewrite Et; apply In_last; discriminate).
    assert (Htm : t <> m) by (intros E; apply Hnin; rewrite <- E; exact Htin).
    (* [comment removed for export] *)
    pose proof Hch as Hch0. cbn [chain] in Hch0. destruct Hch0 as [Lh0 _].
    pose proof (Hlk h0 _ (or_introl eq_refl) Lh0) as LKh0. unfold LK in LKh0.
    destruct (MT s h0) as [xh|] eqn:Mh; [|discriminate]. injection LKh0 as Lxh.
    destruct (chain_links _ _ _ _ t Hch Htin) as (tpr & tnx & Lt).
    pose proof (Hlk t _ Htin Lt) as LKt. unfold LK in LKt.
    destruct (MT s t) as [xt|] eqn:Mt; [|discriminate]. injection LKt as Lxt.
    mbinds. eapply itok_get_links; [exact Mh|]. msimp. rewrite Lxh. cbn [fst].
    (* [comment removed for export] *)
    mbinds. eapply itok_set_links'; [exact Hm|]. msimp.
    (* [comment removed for export] *)
    mbinds. eapply (itok_set_next _ _ _ xt).
    { rewrite MT_upd_other by exact Htm. exact Mt. }
    msimp. rewrite Lxt. cbn [fst].
    (* [comment removed for export] *)
    apply (itok_set_prev _ _ _ (if sptr_eqb h0 t then with_links xt (Some tpr) (Some m) else xh)).
    { rewrite MT_upd. destruct (sptr_eqb h0 t); [reflexivity|]. rewrite MT_upd_other by exact Hh0m. exact Mh. }
    match goal with |- Q (tt, ?st) => set (s' := st) end.
    apply HQ; subst s'.
    + eapply sbmh_trans; [apply sbmh_upd_meta; exact Km|].
      eapply sbmh_trans; [apply sbmh_upd_meta | apply sbmh_upd_meta].
      * rewrite keys_upd_In by exact Km. eapply In_keys_of_MT; exact Mt.
      * rewrite keys_upd_In; [| rewrite keys_upd_In by exact Km; eapply In_keys_of_MT; exact Mt].
        rewrite keys_upd_In by exact Km. eapply In_keys_of_MT; exact Mh.
    + eapply hse_trans; [apply hse_upd_meta|]. eapply hse_trans; apply hse_upd_meta.
    + rewrite !head_of_upd_meta. cbn [hd]. exact Hhd.
    + cbn [hd]. rewrite MT_upd_other by (intros E; exact (Hh0m (eq_sym E))).
      rewrite MT_upd_other by (intros E; exact (Htm (eq_sym E))).
      rewrite MT_upd_same. reflexivity.
    + intros q Hq. rewrite MT_upd_other by (intros ->; apply Hq; right; left; reflexivity).
      rewrite MT_upd_other by (intros ->; apply Hq; right; exact Htin).
      rewrite MT_upd_other by (intros ->; apply Hq; left; reflexivity). reflexivity.
    + intros y xy Hy My. cbn [hd]. rewrite MT_upd. destruct (sptr_eqb y h0) eqn:Eyh.
      * apply sptr_eqb_eq in Eyh. subst y. rewrite Mh in My. injection My as <-.
        destruct (sptr_eqb h0 t) eqn:Eht.
        -- apply sptr_eqb_eq in Eht. rewrite <- Eht in Mt. rewrite Mh in Mt. injection Mt as <-.
           rewrite with_links_with_links, links_with_links. cbn [snd]. reflexivity.
        -- rewrite Lxh. cbn [snd]. reflexivity.
      * rewrite MT_upd. destruct (sptr_eqb y t) eqn:Eyt.
        -- apply sptr_eqb_eq in Eyt. subst y. rewrite Mt in My. injection My as <-. rewrite Lxt. reflexivity.
        -- rewrite MT_upd_other by (intros ->; apply Hnin; exact Hy). rewrite My. f_equal.
           destruct (chain_links _ _ _ _ y Hch Hy) as (yp & yn & Ly).
           pose proof (Hlk y _ Hy Ly) as LKy. unfold LK in LKy. rewrite My in LKy. injection LKy as Lxy.
           destruct xy as [p1 n1| |am]; cbn in Lxy |- *; [injection Lxy as -> ->; reflexivity | discriminate |].
           destruct am; cbn in Lxy |- *. injection Lxy as -> ->. reflexivity.
Qed.
End MallocWfRingOps.


Module MallocWfSurgery.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)

Definition strip (am : ameta) : ameta := am_set_links None None am.

Lemma strip_fields a b : strip a = strip b ->
  am_mem a = am_mem b /\ am_avail a = am_avail b /\ am_freed a = am_freed b /\ am_last a = am_last b /\
  am_sc a = am_sc b /\ am_maplen a = am_maplen b /\ am_aidx a = am_aidx b /\ am_slots a = am_slots b.
Proof. unfold strip, am_set_links. intros H. injection H. auto 10. Qed.

Lemma strip_stride a b : strip a = strip b -> stride_of a = stride_of b.
Proof. intros H. apply strip_fields in H. unfold stride_of. destruct H as (_&_&_&->&->&->&_). reflexivity. Qed.

Lemma strip_extent a b : strip a = strip b -> group_extent a = group_extent b.
Proof. intros H. unfold group_extent. rewrite (strip_stride _ _ H). apply strip_fields in H. destruct H as (_&_&_&->&_). reflexivity. Qed.

Lemma strip_slot_start a b i : strip a = strip b -> slot_start a i = slot_start b i.
Proof. intros H. unfold slot_start. rewrite (strip_stride _ _ H). apply strip_fields in H. destruct H as (->&_). reflexivity. Qed.

Lemma strip_nth_slot a b i : strip a = strip b -> nth_slot a i = nth_slot b i.
Proof. intros H. unfold nth_slot. apply strip_fields in H. destruct H as (_&_&_&_&_&_&_&->). reflexivity. Qed.

Lemma strip_allocated a b i : strip a = strip b -> allocated a i = allocated b i.
Proof. intros H. unfold allocated. apply strip_fields in H. destruct H as (_&->&->&_). reflexivity. Qed.

Lemma strip_hdr_byte3 a b i fr : strip a = strip b -> hdr_byte3 a i fr = hdr_byte3 b i fr.
Proof. intros H. unfold hdr_byte3, rsv_code. rewrite (strip_stride _ _ H). reflexivity. Qed.

Lemma strip_hdr_off16 a b i fr : strip a = strip b -> hdr_off16 a i fr = hdr_off16 b i fr.
Proof. intros H. unfold hdr_off16. rewrite (strip_stride _ _ H). reflexivity. Qed.

Lemma strip_set_links pr nx am : strip (am_set_links pr nx am) = strip am.
Proof. reflexivity. Qed.

Lemma strip_refl am : strip am = strip am.
Proof. reflexivity. Qed.

Lemma class_size_ge16 sc : 0 <= sc < 48 -> 16 <= class_size sc.
Proof.
  intros H. unfold class_size, znth.
  assert (G : forall n, (n < 48)%nat -> 16 <= UNIT * nth n size_classes 0).
  { intros n Hn. do 48 (destruct n as [|n]; [cbn; lia|]). lia. }
  apply G. lia.
Qed.

Lemma stride_pos X R s g am : group_ok X R s g am -> 16 <= stride_of am.
Proof.
  intros (Gm & Gml & _ & Gc & _). unfold stride_of. destruct Gm as (Hl & _).
  destruct ((am_last am =? 0) && negb (am_maplen am =? 0)) eqn:E.
  - apply andb_prop in E as [_ E2]. destruct (am_maplen am =? 0) eqn:E3; [discriminate|].
    apply Z.eqb_neq in E3. unfold UNIT. lia.
  - destruct Gc as [(H63 & Hl0 & Hmp & _) | (Hsc & _)].
    + rewrite Hl0 in E. cbn [Z.eqb andb] in E. destruct (am_maplen am =? 0) eqn:E3; [|discriminate].
      apply Z.eqb_eq in E3. lia.
    + apply class_size_ge16. exact Hsc.
Qed.

Lemma extent_pos X R s g am : group_ok X R s g am -> 0 < group_extent am.
Proof.
  intros G. pose proof (stride_pos _ _ _ _ _ G) as Hs. destruct G as ((Hl & _) & _).
  unfold group_extent, UNIT, IB. nia.
Qed.

Section Surgery.
  Variables (X X' : list sptr) (R R' : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate).
  Hypothesis HI : Inv X R U s.
  Hypothesis ER : forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> region_of s' k = Some rg.
  (* [comment removed for export] *)
  Hypothesis Cb : forall p am', usedX X' s' p am' -> exists am, usedX X s p am /\ strip am' = strip am.
  (* [comment removed for export] *)
  Hypothesis Cf : forall p am, usedX X s p am ->
    (exists am', usedX X' s' p am' /\ strip am' = strip am) \/
    (memb p X' = true /\ forall j, ss_fr (nth_slot am j) = None).
  (* [comment removed for export] *)
  Hypothesis HR' : reserved_ok X' R' s'.
  (* [comment removed for export] *)
  Hypothesis RR : forall p i am', usedX X' s' p am' ->
     (R = Some (p, i) <-> R' = Some (p, i)) \/
     (* [comment removed for export] *)
     (R' = Some (p, i) /\ R <> Some (p, i) /\ ss_fr (nth_slot am' i) = None) \/
     (* [comment removed for export] *)
     (R = Some (p, i) /\ R' <> Some (p, i) /\ (ss_fr (nth_slot am' i) = None -> allocated am' i = false)).

  #[using="Cf"] Lemma su_nested a a' : strip a' = strip a -> nested_ok X s a -> nested_ok X' s' a'.
  Proof.
    intros E N Hm. apply strip_fields in E as (Em & _ & _ & El & Es & Eml & _ & _).
    rewrite Eml in Hm. destruct (N Hm) as [N63 (g' & b & i' & fr' & Hu & Hi & Hf & Hk & Hmem & Hsc & Hsc' & Hfit)].
    split; [congruence|].
    destruct (Cf _ _ Hu) as [(b' & Hu' & Eb) | [_ Hgone]].
    - exists g', b', i', fr'. pose proof (strip_fields _ _ Eb) as (Bm&_&_&Bl&Bs&_&_&Bsl).
      split; [exact Hu'|]. split; [rewrite Bl; exact Hi|].
      split; [unfold nth_slot in *; rewrite Bsl; exact Hf|]. split; [exact Hk|].
      split; [rewrite Em, (strip_slot_start _ _ _ Eb); exact Hmem|].
      split; [rewrite Es, Bs; exact Hsc|]. split; [rewrite Bs; exact Hsc'|].
      rewrite Es, El. exact Hfit.
    - exfalso. rewrite (Hgone i') in Hf. discriminate.
  Qed.

  #[using="ER"] Lemma su_mapped a a' : strip a' = strip a -> mapped_ok s a -> mapped_ok s' a'.
  Proof.
    intros E M Hm. pose proof (strip_stride _ _ E) as Est. apply strip_fields in E as (Em & _ & _ & El & Es & Eml & _).
    rewrite Eml in Hm. destruct (M Hm) as (r & rg & H1 & H2 & H3 & H4 & H5 & H6). exists r, rg.
    rewrite Em, Eml, El, Est, Es. split; [exact H1|]. split; [apply ER; assumption|]. auto.
  Qed.

  #[using="ER Cf RR"] Lemma su_group p am am' :
    group_ok X R s p am -> usedX X' s' p am' -> strip am' = strip am -> group_ok X' R' s' p am'.
  Proof.
    intros G Hu E. pose proof G as (Gm & Gml & Gsl & Gcl & Gmp & Gns).
    pose proof (strip_fields _ _ E) as (Em & Eav & Efr & El & Es & Eml & Eai & Esl).
    pose proof (strip_stride _ _ E) as Est.
    split.
    { unfold masks_ok in *. rewrite El, Eai, Esl, Eav, Efr. exact Gm. }
    split; [rewrite Eml; exact Gml|].
    split.
    { intros i Hi. rewrite El in Hi. pose proof (Gsl i Hi) as (S1 & S2 & S3).
      unfold slot_ok. rewrite (strip_nth_slot _ _ i E), Eml.
      split; [exact S1|]. split; [exact S2|].
      pose proof (RR p i am' Hu) as RRi. rewrite (strip_nth_slot _ _ i E), (strip_allocated _ _ i E) in RRi.
      destruct (ss_fr (nth_slot am i)) as [fr|].
      - destruct S3 as (A1 & A2 & A3 & A4). rewrite (strip_allocated _ _ i E).
        split; [exact A1|]. split.
        { destruct RRi as [RRi | [(_ & _ & RRi) | (RRi & RRi' & _)]]; [ | discriminate | exact RRi'].
          intros H. apply A2. apply RRi. exact H. }
        split.
        { unfold frame_ok in *. rewrite Est, (strip_hdr_off16 _ _ i fr E). exact A3. }
        rewrite (strip_hdr_byte3 _ _ i fr E), (strip_hdr_off16 _ _ i fr E). exact A4.
      - rewrite (strip_allocated _ _ i E).
        destruct RRi as [RRi | [(RRi & _) | (_ & _ & RRi)]].
        + destruct S3 as [S3|S3]; [left; exact S3 | right; apply RRi; exact S3].
        + right. exact RRi.
        + left. apply RRi. reflexivity. }
    split.
    { unfold class_ok in *. rewrite Es, El, Eml, Eav, Efr, Est, (strip_allocated _ _ 0 E), (strip_nth_slot _ _ 0 E).
      destruct Gcl as [(C1 & C2 & C3 & C4 & C5 & C6) | C]; [left | right; exact C].
      repeat split; auto.
      destruct C6 as [C6 | C6]; [| right; exact C6].
      pose proof (RR p 0 am' Hu) as [RRi | [(RRi & _) | (_ & RRn & RRi)]].
      - left. apply RRi. exact C6.
      - left. exact RRi.
      - (* [comment removed for export] *)
        rewrite (strip_nth_slot _ _ 0 E), (strip_allocated _ _ 0 E) in RRi.
        destruct (ss_fr (nth_slot am 0)) as [fr|] eqn:Ef.
        + right. pose proof (Gsl 0 ltac:(lia)) as (_ & _ & S3). rewrite Ef in S3.
          exists fr. split; [reflexivity|].
          destruct S3 as (_ & HR2 & _). exfalso. exact (HR2 C6).
        + exfalso. specialize (RRi eq_refl). unfold allocated in RRi. rewrite C4, C5 in RRi. cbn in RRi.
          rewrite Z.lor_0_l, Z.bits_0 in RRi || (cbn in RRi). discriminate. }
    split; [eapply su_mapped; eauto | eapply su_nested; eauto].
  Qed.
End Surgery.

Section Surgery2.
  Variables (X X' : list sptr) (R R' : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate).
  Hypothesis HI : Inv X R U s.
  Hypothesis ER : forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> region_of s' k = Some rg.
  Hypothesis Cb : forall p am', usedX X' s' p am' -> exists am, usedX X s p am /\ strip am' = strip am.
  Hypothesis Cf : forall p am, usedX X s p am ->
    (exists am', usedX X' s' p am' /\ strip am' = strip am) \/
    (memb p X' = true /\ forall j, ss_fr (nth_slot am j) = None).
  Hypothesis HR' : reserved_ok X' R' s'.
  Hypothesis RR : forall p i am', usedX X' s' p am' ->
     (R = Some (p, i) <-> R' = Some (p, i)) \/
     (R' = Some (p, i) /\ R <> Some (p, i) /\ ss_fr (nth_slot am' i) = None) \/
     (R = Some (p, i) /\ R' <> Some (p, i) /\ (ss_fr (nth_slot am' i) = None -> allocated am' i = false)).

  #[using="X R U s HI ER Cb Cf RR"] Lemma su_groups : forall p am', usedX X' s' p am' -> group_ok X' R' s' p am'.
  Proof.
    intros p am' Hu. destruct (Cb _ _ Hu) as (am & Hu0 & E).
    eapply su_group; eauto. apply (inv_groups HI). exact Hu0.
  Qed.

  #[using="Cf"] Lemma su_inside a a' b b' :
    strip a' = strip a -> strip b' = strip b -> inside X s a b -> inside X' s' a' b' \/
    exists c ac, usedX X s c ac /\ memb c X' = true /\ (forall j, ss_fr (nth_slot ac j) = None) /\
      poff (am_mem ac) <= poff (am_mem a) /\ poff (am_mem a) + group_extent a <= poff (am_mem ac) + group_extent ac /\
      am_maplen ac = 0 /\ prid (am_mem ac) = prid (am_mem b).
  Proof.
    intros Ea Eb (j & fr & c & ac & Hj & Hfr & Hk & Hc & Hml & Hmem & Hlo & Hhi & Hfit).
    destruct (Cf _ _ Hc) as [(ac' & Hc' & Ec) | [Hg Hnone]].
    - left. pose proof (strip_fields _ _ Ec) as (Cm&_&_&_&_&Cml&_&_).
      pose proof (strip_fields _ _ Eb) as (Bm&_&_&Bl&_&_&_&Bsl).
      pose proof (strip_fields _ _ Ea) as (Am&_).
      exists j, fr, c, ac'. split; [rewrite Bl; exact Hj|]. split; [unfold nth_slot in *; rewrite Bsl; exact Hfr|].
      split; [exact Hk|]. split; [exact Hc'|]. split; [rewrite Cml; exact Hml|].
      split; [rewrite Cm, (strip_slot_start _ _ _ Eb); exact Hmem|].
      split; [rewrite Cm, Am; exact Hlo|].
      split; [rewrite Am, Cm, (strip_extent _ _ Ea), (strip_extent _ _ Ec); exact Hhi|].
      rewrite (strip_extent _ _ Ec). exact Hfit.
    - right. exists c, ac. repeat split; auto.
      rewrite Hmem. unfold slot_start. destruct (am_mem b); reflexivity.
  Qed.

  #[using="X R U s HI Cb Cf"] Lemma su_laminar : laminar X' s'.
  Proof.
    intros p1 a1' p2 a2' H1 H2 Hne Hr.
    destruct (Cb _ _ H1) as (a1 & U1 & E1). destruct (Cb _ _ H2) as (a2 & U2 & E2).
    pose proof (strip_fields _ _ E1) as (M1&_). pose proof (strip_fields _ _ E2) as (M2&_).
    assert (Hgone : forall a a' pa c ac, usedX X s pa a -> usedX X' s' pa a' -> strip a' = strip a ->
              usedX X s c ac -> memb c X' = true -> (forall j, ss_fr (nth_slot ac j) = None) ->
              poff (am_mem ac) <= poff (am_mem a) ->
              poff (am_mem a) + group_extent a <= poff (am_mem ac) + group_extent ac ->
              am_maplen ac = 0 -> prid (am_mem a) = prid (am_mem ac) -> False).
    { intros a a' pa c ac Ua Ua' Ea Uc Xc Fc Lo Hi Mc Pr.
      assert (Hpc : pa <> c).
      { intros ->. pose proof (usedX_MT _ _ _ _ Ua') as [_ M]. rewrite M in Xc. discriminate. }
      pose proof (extent_pos _ _ _ _ _ (inv_groups HI pa a Ua)) as Pa.
      destruct (inv_laminar HI pa a c ac Ua Uc Hpc Pr) as [D | [I | I]].
      - unfold spans_disjoint in D. lia.
      - destruct I as (j & fr & _ & _ & _ & Hfr & _). rewrite (Fc j) in Hfr. discriminate.
      - destruct I as (j & fr & c2 & ac2 & Hj & Hfr & Hk & Uc2 & Ml2 & Mem2 & Lo2 & Hi2 & _).
        (* [comment removed for export] *)
        pose proof (stride_pos _ _ _ _ _ (inv_groups HI pa a Ua)) as Sp.
        unfold slot_start in Mem2. rewrite Mem2 in Lo2. destruct (am_mem a) as [ra oa]. cbn [poff padd] in Lo2, Lo, Hi.
        assert (0 <= stride_of a * j) by (apply Z.mul_nonneg_nonneg; lia).
        unfold UNIT in Lo2. lia. }
    destruct (inv_laminar HI p1 a1 p2 a2 U1 U2 Hne ltac:(rewrite <- M1, <- M2; exact Hr)) as [D | [I | I]].
    - left. unfold spans_disjoint in *. rewrite M1, M2, (strip_extent _ _ E1), (strip_extent _ _ E2). exact D.
    - destruct (su_inside _ _ _ _ E1 E2 I) as [I' | (c & ac & Uc & Xc & Fc & Lo & Hi & Mc)]; [right; left; exact I'|].
      exfalso. destruct Mc as [Mc Pc]. eapply (Hgone a1 a1' p1 c ac); eauto.
      rewrite Pc, <- M1, <- M2. exact Hr.
    - destruct (su_inside _ _ _ _ E2 E1 I) as [I' | (c & ac & Uc & Xc & Fc & Lo & Hi & Mc)]; [right; right; exact I'|].
      exfalso. destruct Mc as [Mc Pc]. eapply (Hgone a2 a2' p2 c ac); eauto.
      rewrite Pc, <- M1, <- M2. symmetry. exact Hr.
  Qed.

  #[using="X R U s HI Cb"] Lemma su_maps : maps_unique X' s'.
  Proof.
    intros p1 a1' p2 a2' H1 H2 Hm1 Hm2 Hr.
    destruct (Cb _ _ H1) as (a1 & U1 & E1). destruct (Cb _ _ H2) as (a2 & U2 & E2).
    pose proof (strip_fields _ _ E1) as (M1&_&_&_&_&L1&_). pose proof (strip_fields _ _ E2) as (M2&_&_&_&_&L2&_).
    eapply (inv_maps HI p1 a1 p2 a2); eauto; try lia. congruence.
  Qed.

  #[using="X R U s HI Cb"] Lemma su_partial : partial_unique X' s'.
  Proof.
    intros p1 a1' p2 a2' H1 H2 Hsc Hp1 Hp2.
    destruct (Cb _ _ H1) as (a1 & U1 & E1). destruct (Cb _ _ H2) as (a2 & U2 & E2).
    pose proof (strip_fields _ _ E1) as (_&_&_&L1&S1&_&A1&_). pose proof (strip_fields _ _ E2) as (_&_&_&L2&S2&_&A2&_).
    eapply (inv_partial HI p1 a1 p2 a2); eauto; try lia; congruence.
  Qed.

  #[using="X R U s HI Cb"] Lemma su_pcg : partial_ok X' s'.
  Proof.
    intros p a' H Ha. destruct (Cb _ _ H) as (a & U1 & E1).
    pose proof (strip_fields _ _ E1) as (_&_&_&L1&S1&M1&A1&_).
    rewrite L1, A1 in Ha. rewrite M1, S1. exact (inv_pcg HI p a U1 Ha).
  Qed.

  #[using="X R U s HI ER Cb Cf HR' RR"] Theorem Inv_surgery :
    ctx_ok s' -> keys_ok s' -> areas_ok s' -> Xok X' s' -> rings_ok X' R' s' -> usage_ok X' U' s' ->
    Inv X' R' U' s'.
  Proof.
    intros C K A XO RG US.
    split; [exact C|]. split; [exact K|]. split; [exact A|].
    split; [exact XO|]. split; [apply su_groups|]. split; [apply su_laminar|]. split; [apply su_maps|].
    split; [exact RG|]. split; [exact US|]. split; [exact HR'|]. split; [apply su_partial | apply su_pcg].
  Qed.
End Surgery2.
End MallocWfSurgery.


Module MallocWfRings.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Lemma Inv_set_active X R U s l :
  Inv X R U s -> length l = 48%nat ->
  rings_ok X R (set_active l s) -> Inv X R U (set_active l s).
Proof.
  intros HI Hl RG.
  split.
  { pose proof (inv_ctx HI) as C. unfold ctx_ok in *. cbn -[Z.pow Z.le Z.lt]. cbn in C.
    destruct C as (C1 & Crest). split; [exact Hl | exact Crest]. }
  split; [exact (inv_keys HI)|]. split; [exact (inv_areas HI)|].
  pose proof (inv_meta HI) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
  split; [exact RG|]. split; [exact M6|]. split; [exact M7 | exact M8].
Qed.

Lemma active_hd_set_active_other s sc sc' v :
  0 <= sc -> 0 <= sc' -> sc' <> sc ->
  active_hd (set_active (lupd (st_active s) (Z.to_nat sc) v) s) sc' = active_hd s sc'.
Proof.
  intros H1 H2 H3. unfold active_hd. cbn [st_active set_active]. rewrite nth_lupd.
  replace (Nat.eqb (Z.to_nat sc') (Z.to_nat sc)) with false; [reflexivity|].
  symmetry. apply Nat.eqb_neq. lia.
Qed.

Lemma active_hd_set_active_same s sc v :
  (Z.to_nat sc < length (st_active s))%nat ->
  active_hd (set_active (lupd (st_active s) (Z.to_nat sc) v) s) sc = v.
Proof.
  intros H. unfold active_hd. cbn [st_active set_active]. rewrite nth_lupd, Nat.eqb_refl.
  replace (Nat.ltb (Z.to_nat sc) (length (st_active s))) with true; [reflexivity|].
  symmetry. apply Nat.ltb_lt. exact H.
Qed.

(* [comment removed for export] *)
Lemma ring_head_links X s sc m0 am0 ms :
  ring_ok (alinks X s sc) (Some m0) ms -> usedX X s m0 am0 ->
  exists rest, ms = m0 :: rest /\
    am_prev am0 = Some (last rest m0) /\ am_next am0 = Some (hd m0 rest).
Proof.
  intros Hr Hu. destruct (ring_head_In _ _ _ Hr) as [_ [rest ->]]. exists rest. split; [reflexivity|].
  destruct Hr as [[Hnd Hch] _]. cbn [chain] in Hch. rewrite last_cons in Hch. destruct Hch as [L _].
  unfold alinks in L. pose proof Hu as Hu'. unfold usedX in Hu'. rewrite Hu' in L.
  destruct (am_sc am0 =? sc); [|discriminate]. injection L as -> ->. auto.
Qed.

(* [comment removed for export] *)
Lemma Inv_rotate_head X R U s sc m0 am0 m1 :
  Inv X R U s -> 0 <= sc < 48 ->
  usedX X s m0 am0 -> am_sc am0 = sc -> active_hd s sc = Some m0 ->
  am_avail am0 = 0 -> am_freed am0 <> 0 -> am_next am0 = Some m1 ->
  Inv X R U (set_active (lupd (st_active s) (Z.to_nat sc) (Some m1)) s).
Proof.
  intros HI Hsc Hu Hsca Hhd Hav Hfr Hnx.
  pose proof (inv_ctx HI) as C. destruct C as (Clen & _).
  apply Inv_set_active; [exact HI | rewrite length_lupd; exact Clen |].
  destruct (inv_rings HI) as (F & A & D).
  split; [exact F|]. split; [|exact D].
  intros sc' Hsc'. destruct (Z.eq_dec sc' sc) as [->|Hne].
  - destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
    rewrite Hhd in Rg. destruct (ring_head_links _ _ _ _ _ _ Rg Hu) as (rest & -> & Hpr & Hnx').
    rewrite Hnx in Hnx'. injection Hnx' as Em1.
    exists (rest ++ [m0]).
    rewrite active_hd_set_active_same by (rewrite Clen; lia).
    split.
    { split; [apply cycle_rotate; exact (proj1 Rg)|].
      rewrite Em1. destruct rest; reflexivity. }
    split.
    { intros g am Hg Hs. rewrite <- (Mem g am Hg Hs), in_app_iff. cbn. tauto. }
    split.
    { intros g am Hg Hs Hnin. apply (Full g am Hg Hs). cbn. rewrite in_app_iff in Hnin. cbn in Hnin. tauto. }
    split.
    { intros g am Hg Hs Hav'. exfalso.
      pose proof (Q1 g am Hg Hs Hav') as E. rewrite Hhd in E. injection E as ->.
      pose proof (usedX_fun _ _ _ _ _ Hg Hu) as ->. exact (Hav' Hav). }
    { intros g am Hg Hs Hin Hnh HnR. destruct (sptr_eq_dec g m0) as [->|Hne].
      - pose proof (usedX_fun _ _ _ _ _ Hg Hu) as ->. exact Hfr.
      - apply (Q2 g am Hg Hs).
        + cbn. rewrite in_app_iff in Hin. cbn in Hin. tauto.
        + rewrite Hhd. congruence.
        + exact HnR. }
  - destruct (A sc' Hsc') as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
    rewrite active_hd_set_active_other by lia.
    exact (conj Rg (conj Mem (conj Full (conj Q1 Q2)))).
Qed.

(* [comment removed for export] *)
Lemma sbmh_ctx s s' :
  same_but_metas_heads s s' -> length (st_active s') = length (st_active s) ->
  (st_init_done s = false -> st_metas s' = []) ->
  ctx_ok s -> ctx_ok s'.
Proof.
  intros Sb Hl Hinit C. unfold same_but_metas_heads in Sb. unfold ctx_ok in *.
  destruct Sb as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
  rewrite Hl, E1, E2, E5, E6, E10, E11, E12, E13, E14, E16.
  destruct C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
  repeat (split; [assumption|]). intros Hi. destruct (C12 Hi) as (D1&D2&D3&D4). auto.
Qed.

Lemma sbmh_keys s s' : same_but_metas_heads s s' -> keys_ok s -> keys_ok s'.
Proof.
  intros Sb K. unfold same_but_metas_heads in Sb.
  destruct Sb as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
  unfold keys_ok, key_placed, handed in *. rewrite E17, E16, E3, E4. exact K.
Qed.

Lemma sbmh_areas s s' : same_but_metas_heads s s' -> areas_ok s -> areas_ok s'.
Proof.
  intros Sb A. unfold same_but_metas_heads in Sb.
  destruct Sb as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
  unfold areas_ok, area_ok, resv_total, resv_opened, resv_count, resv_covered, brk_regions, region_of in *.
  rewrite E16, E15, E7, E8, E6, E14, E5, E9. exact A.
Qed.

Lemma sbmh_usage_of s s' sc : same_but_metas_heads s s' -> usage_of s' sc = usage_of s sc.
Proof.
  intros Sb. unfold same_but_metas_heads in Sb.
  destruct Sb as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
  unfold usage_of. rewrite E10. reflexivity.
Qed.

(* [comment removed for export] *)
Definition relinked (s s' : astate) (S : list sptr) : Prop :=
  (forall q, ~ In q S -> MT s' q = MT s q) /\
  (forall q, In q S -> exists x pr nx, MT s q = Some x /\ MT s' q = Some (with_links x pr nx) /\ x <> MRaw).

Section Relinked.
  Variables (X : list sptr) (s s' : astate) (S : list sptr).
  Hypothesis RL : relinked s s' S.
  Hypothesis SX : forall q, In q S -> memb q X = false.

  #[using="RL"] Lemma rl_MT_cases q : MT s' q = MT s q \/ exists x pr nx, MT s q = Some x /\ MT s' q = Some (with_links x pr nx) /\ x <> MRaw /\ In q S.
  Proof.
    destruct RL as [R1 R2]. destruct (in_dec sptr_eq_dec q S) as [Hi|Hn].
    - right. destruct (R2 q Hi) as (x & pr & nx & A & B & C). exists x, pr, nx. auto.
    - left. apply R1. exact Hn.
  Qed.

  #[using="S RL"] Lemma rl_used_bwd q am' : usedX X s' q am' -> exists am, usedX X s q am /\ strip am' = strip am.
  Proof.
    intros Hu. pose proof (usedX_MT _ _ _ _ Hu) as [M NX].
    destruct (rl_MT_cases q) as [E | (x & pr & nx & A & B & C & D)].
    - exists am'. split; [apply usedX_intro; [exact NX | rewrite <- E; exact M] | reflexivity].
    - rewrite B in M. destruct x as [| |am]; cbn in M; try discriminate.
      injection M as <-. exists am. split; [apply usedX_intro; assumption | reflexivity].
  Qed.

  #[using="S RL"] Lemma rl_used_fwd q am : usedX X s q am -> exists am', usedX X s' q am' /\ strip am' = strip am.
  Proof.
    intros Hu. pose proof (usedX_MT _ _ _ _ Hu) as [M NX].
    destruct (rl_MT_cases q) as [E | (x & pr & nx & A & B & C & D)].
    - exists am. split; [apply usedX_intro; [exact NX | rewrite E; exact M] | reflexivity].
    - rewrite A in M. injection M as ->. exists (am_set_links pr nx am).
      split; [apply usedX_intro; [exact NX | exact B] | reflexivity].
  Qed.

  #[using="RL"] Lemma rl_used_same q am : ~ In q S -> (usedX X s' q am <-> usedX X s q am).
  Proof.
    intros Hn. destruct RL as [R1 _]. unfold usedX, MTX. rewrite (R1 q Hn). tauto.
  Qed.

  #[using="S RL SX"] Lemma rl_Xok : keys s' = keys s -> Xok X s -> Xok X s'.
  Proof.
    intros K XO x Hx. destruct (XO x Hx) as [Kx Mx]. split; [rewrite K; exact Kx|].
    destruct RL as [R1 _]. rewrite R1; [exact Mx|]. intros Hin. pose proof (SX x Hin) as E.
    unfold memb in E. assert (existsb (sptr_eqb x) X = true); [|congruence].
    apply existsb_exists. exists x. split; [exact Hx | apply sptr_eqb_refl].
  Qed.

  #[using="S RL"] Lemma rl_contrib sc q : contrib X s' sc q = contrib X s sc q.
  Proof.
    unfold contrib, MTX. destruct (memb q X); [reflexivity|].
    destruct (rl_MT_cases q) as [E | (x & pr & nx & A & B & C & D)]; [rewrite E; reflexivity|].
    rewrite A, B. destruct x; cbn; reflexivity.
  Qed.

  #[using="S RL"] Lemma rl_usage U : same_but_metas_heads s s' -> usage_ok X U s -> usage_ok X U s'.
  Proof.
    intros Sb Hu sc Hsc. rewrite (sbmh_usage_of _ _ sc Sb), (Hu sc Hsc). f_equal.
    unfold class_sum. destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). rewrite K.
    assert (E : forall l, fold_right (fun g acc => contrib X s' sc g + acc) 0 l =
                          fold_right (fun g acc => contrib X s sc g + acc) 0 l).
    { induction l as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH, rl_contrib. reflexivity. }
    symmetry. apply E.
  Qed.

  (* [comment removed for export] *)
  #[using="RL"] Lemma rl_flinks_same q : ~ In q S -> flinks X s' q = flinks X s q.
  Proof. intros Hn. destruct RL as [R1 _]. unfold flinks, MTX. rewrite (R1 q Hn). reflexivity. Qed.

  #[using="RL"] Lemma rl_alinks_same sc q : ~ In q S -> alinks X s' sc q = alinks X s sc q.
  Proof. intros Hn. destruct RL as [R1 _]. unfold alinks, MTX. rewrite (R1 q Hn). reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="RL"] Lemma rl_alinks_other sc sc' q :
    (forall p, In p S -> exists am, usedX X s p am /\ am_sc am = sc) -> sc' <> sc ->
    alinks X s' sc' q = alinks X s sc' q.
  Proof.
    intros HS Hne. destruct (in_dec sptr_eq_dec q S) as [Hi|Hn]; [|apply rl_alinks_same; exact Hn].
    destruct (HS q Hi) as (am & Hu & Hsc). destruct (rl_used_fwd _ _ Hu) as (am' & Hu' & E).
    unfold alinks. pose proof Hu as M. pose proof Hu' as M'. unfold usedX in M, M'. rewrite M, M'.
    apply strip_fields in E as (_&_&_&_&Es&_). rewrite Es, Hsc.
    replace (sc =? sc') with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  Qed.

  #[using="RL"] Lemma rl_flinks_used sc q :
    (forall p, In p S -> exists am, usedX X s p am /\ am_sc am = sc) ->
    flinks X s' q = flinks X s q.
  Proof.
    intros HS. destruct (in_dec sptr_eq_dec q S) as [Hi|Hn]; [|apply rl_flinks_same; exact Hn].
    destruct (HS q Hi) as (am & Hu & Hsc). destruct (rl_used_fwd _ _ Hu) as (am' & Hu' & E).
    unfold flinks. pose proof Hu as M. pose proof Hu' as M'. unfold usedX in M, M'. rewrite M, M'. reflexivity.
  Qed.
End Relinked.

Lemma ub_same_relinked s s' S : relinked s s' S -> keys s' = keys s -> ub_same s s'.
Proof.
  intros [R1 R2] K. exists []. rewrite app_nil_r. split; [exact K|]. split; [intros m []|].
  intros g Hg. destruct (in_dec sptr_eq_dec g S) as [Hi|Hn].
  - destruct (R2 g Hi) as (x & pr & nx & A & B & C). rewrite A, B. apply ucontrib_with_links.
  - rewrite (R1 g Hn). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma alinks_used X s sc q l : alinks X s sc q = Some l -> exists am, usedX X s q am /\ am_sc am = sc /\ l = (am_prev am, am_next am).
Proof.
  unfold alinks. destruct (MTX X s q) as [[| |am]|] eqn:E; try discriminate.
  destruct (am_sc am =? sc) eqn:Es; [|discriminate]. intros H. injection H as <-.
  exists am. split; [exact E|]. split; [apply Z.eqb_eq; exact Es | reflexivity].
Qed.

Lemma ring_members_used X s sc hd ms q :
  ring_ok (alinks X s sc) hd ms -> In q ms -> exists am, usedX X s q am /\ am_sc am = sc.
Proof.
  intros Hr Hin. destruct (ring_links _ _ _ _ Hr Hin) as (pr & nx & L).
  destruct (alinks_used _ _ _ _ _ L) as (am & Hu & Hs & _). exists am. auto.
Qed.

Lemma LK_of_alinks X s sc q l : alinks X s sc q = Some l -> LK s q = Some l.
Proof.
  intros H. destruct (alinks_used _ _ _ _ _ H) as (am & Hu & _ & ->).
  unfold LK. pose proof (usedX_MT _ _ _ _ Hu) as [M _]. rewrite M. reflexivity.
Qed.

Lemma LK_of_flinks X s q l : flinks X s q = Some l -> LK s q = Some l.
Proof.
  unfold flinks, LK, MTX. destruct (memb q X); [discriminate|].
  destruct (MT s q) as [[pr nx| |am]|]; try discriminate. intros H. injection H as <-. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Inv_dequeue_full_head X R U s sc m0 am0 (Q : unit * astate -> Prop) :
  Inv X R U s -> 0 <= sc < 48 -> usedX X s m0 am0 -> am_sc am0 = sc -> active_hd s sc = Some m0 ->
  am_avail am0 = 0 -> am_freed am0 = 0 ->
  (forall g am, usedX X s g am -> am_sc am = sc -> am_avail am = 0) ->
  (forall q i, R <> Some (q, i)) ->
  (forall s',
     Inv X R U s' ->
     same_but_metas_heads s s' -> heads_same_except (HActive sc) s s' ->
     (forall g am', usedX X s' g am' -> exists am, usedX X s g am /\ strip am' = strip am) ->
     (forall g am, usedX X s g am -> exists am', usedX X s' g am' /\ strip am' = strip am) ->
     MT s' m0 = Some (MUsed (am_set_links None None am0)) ->
     match active_hd s' sc with
     | None => True
     | Some m1 => m1 <> m0 /\ exists am1, usedX X s' m1 am1 /\ am_sc am1 = sc /\ am_freed am1 <> 0 /\
                  am_prev am1 <> None
     end ->
     ub_same s s' ->
     Q (tt, s')) ->
  itok (dequeue (HActive sc) m0 s) Q.
Proof.
  intros HI Hsc Hu Hsca Hhd Hav Hfr Hall HR0 HQ.
  destruct (inv_rings HI) as (F & A & D).
  destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2).
  rewrite Hhd in Rg. destruct (ring_head_In _ _ _ Rg) as [_ [rest Ems]]. subst ms.
  pose proof (usedX_MT _ _ _ _ Hu) as [Mm0 NX0].
  pose proof (inv_ctx HI) as C. destruct C as (Clen & Crest).
  eapply (dequeue_op (HActive sc) m0 s (MUsed am0) rest (alinks X s sc)).
  - exact Mm0.
  - exact (proj1 Rg).
  - intros q l _ Hl. eapply LK_of_alinks. exact Hl.
  - cbn. rewrite Clen. lia.
  - intros s' Sb Hse Hhd' Mm0' Mother Mrest.
    (* [comment removed for export] *)
    assert (RL : relinked s s' (m0 :: rest)).
    { split.
      - exact Mother.
      - intros q Hq. destruct Hq as [<- | Hq].
        + exists (MUsed am0), None, None. split; [exact Mm0|]. split; [exact Mm0'|]. discriminate.
        + destruct (ring_members_used _ _ _ _ _ q Rg (or_intror Hq)) as (am & Hqu & _).
          pose proof (usedX_MT _ _ _ _ Hqu) as [Mq _].
          eexists (MUsed am), _, _. split; [exact Mq|]. split; [apply (Mrest q (MUsed am) Hq Mq) | discriminate]. }
    assert (SX : forall q, In q (m0 :: rest) -> memb q X = false).
    { intros q Hq. destruct (ring_members_used _ _ _ _ _ q Rg Hq) as (am & Hqu & _). exact (proj2 (usedX_MT _ _ _ _ Hqu)). }
    assert (SC : forall q, In q (m0 :: rest) -> exists am, usedX X s q am /\ am_sc am = sc).
    { intros q Hq. eapply ring_members_used; eauto. }
    pose proof (rl_used_bwd X s s' _ RL) as Bwd. pose proof (rl_used_fwd X s s' _ RL) as Fwd.
    (* [comment removed for export] *)
    assert (Hhd_new : active_hd s' sc = match rest with [] => None | y :: _ => Some y end).
    { cbn [head_of] in Hhd'. rewrite Hhd' , Hhd. destruct rest; [reflexivity|]. cbn. rewrite sptr_eqb_refl. reflexivity. }
    assert (Rg' : ring_ok (alinks X s' sc) (active_hd s' sc) rest).
    { rewrite Hhd_new. split; [| destruct rest; reflexivity].
      destruct rest as [|y rest']; [split; [constructor | exact I] |].
      eapply (cycle_remove_first (alinks X s sc) (alinks X s' sc) m0 (y :: rest')).
      - exact (proj1 Rg).
      - discriminate.
      - intros z pr nx Hz Lz. destruct (alinks_used _ _ _ _ _ Lz) as (am & Hzu & Hzs & El).
        pose proof (usedX_MT _ _ _ _ Hzu) as [Mz NXz].
        pose proof (Mrest z (MUsed am) Hz Mz) as Mz'. cbn [with_links] in Mz'.
        unfold alinks, usedX, MTX in *. rewrite NXz in *. rewrite Mz'. cbn [am_sc am_prev am_next am_set_links].
        rewrite Hzs, Z.eqb_refl. injection El as -> ->. cbn [fst snd links_of]. reflexivity. }
    apply HQ; auto.
    all: try (eapply ub_same_relinked; [exact RL|]; destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K); exact K).
    + eapply (Inv_surgery X X R R U U s s' HI).
      * destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_& ER &_). intros k rg Hk _. unfold region_of in *. rewrite ER. exact Hk.
      * exact Bwd.
      * intros p am Hp. left. apply Fwd. exact Hp.
      * intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hgu & Hi & Hf & Ha).
        destruct (Fwd _ _ Hgu) as (am' & Hgu' & E). exists am'.
        pose proof (strip_fields _ _ E) as (_&_&_&El&_). rewrite (strip_nth_slot _ _ i E), (strip_allocated _ _ i E), El. auto.
      * intros p i am' _. left. tauto.
      * apply (sbmh_ctx s s' Sb).
        -- destruct Hse as (_&_&Hl). exact Hl.
        -- intros Hi. exfalso. destruct Crest as (_&_&_&_&_&_&_&_&_&_&Ci). destruct (Ci Hi) as (Hm & _).
           pose proof (MT_Some_In_keys _ _ _ Mm0) as K. unfold keys in K. rewrite Hm in K. exact K.
        -- exact (inv_ctx HI).
      * apply (sbmh_keys s s' Sb). exact (inv_keys HI).
      * apply (sbmh_areas s s' Sb). exact (inv_areas HI).
      * eapply rl_Xok; eauto. { destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). exact K. } exact (inv_X HI).
      * (* [comment removed for export] *)
        split.
        { destruct F as (fms & FR & Fall). exists fms. split.
          - destruct Hse as (_ & Hfm & _). rewrite (Hfm ltac:(discriminate)).
            eapply ring_ok_ext; [|exact FR]. intros q _. eapply rl_flinks_used; eauto.
          - intros g pr nx Hg. apply (Fall g pr nx). unfold MTX in *.
            destruct (memb g X); [discriminate|].
            destruct (rl_MT_cases s s' _ RL g) as [E | (x & p' & n' & A1 & B1 & C1 & D1)]; [rewrite <- E; exact Hg|].
            exfalso. destruct (SC g D1) as (am & Hgu & _). pose proof (usedX_MT _ _ _ _ Hgu) as [Mg _].
            rewrite Mg in A1. injection A1 as <-. rewrite B1 in Hg. cbn in Hg. discriminate. }
        split.
        { intros sc' Hsc'. destruct (Z.eq_dec sc' sc) as [->|Hne].
          - exists rest. split; [exact Rg'|].
            split.
            { intros g am' Hg Hs'. destruct (Bwd _ _ Hg) as (am & Hgu & E).
              pose proof (strip_fields _ _ E) as (_&_&_&_&Es&_).
              destruct (sptr_eq_dec g m0) as [->|Hne].
              - pose proof (usedX_MT _ _ _ _ Hg) as [Mg _]. rewrite Mm0' in Mg. injection Mg as <-. cbn.
                split; [intros Hin | intros H; exfalso; apply H; reflexivity].
                exfalso. destruct Rg as [[Hnd _] _]. inversion Hnd; subst. contradiction.
              - destruct (in_dec sptr_eq_dec g rest) as [Hin|Hnin].
                + split; [intros _ | intros _; exact Hin].
                  destruct (ring_links _ _ _ _ Rg' Hin) as (pr & nx & L).
                  unfold alinks in L. pose proof Hg as Hg2. unfold usedX in Hg2. rewrite Hg2 in L.
                  rewrite Hs', Z.eqb_refl in L. injection L as -> ->. discriminate.
                + rewrite (rl_used_same X s s' _ RL g am') in Hg by (intros [->|Hc]; [exact (Hne eq_refl)|exact (Hnin Hc)]).
                  rewrite <- (Mem g am' Hg ltac:(congruence)). cbn. split; [intros Hi; right; exact Hi|].
                  intros [->|Hi]; [exfalso; exact (Hne eq_refl)|exact Hi]. }
            split.
            { intros g am' Hg Hs' Hnin. destruct (Bwd _ _ Hg) as (am & Hgu & E).
              pose proof (strip_fields _ _ E) as (_&Eav&Efr&_&Es&_). rewrite Eav, Efr.
              destruct (sptr_eq_dec g m0) as [->|Hne].
              - pose proof (usedX_fun _ _ _ _ _ Hgu Hu) as ->. auto.
              - apply (Full g am Hgu ltac:(congruence)). cbn. intros [->|Hi]; [exact (Hne eq_refl)|exact (Hnin Hi)]. }
            split.
            { intros g am' Hg Hs' Hav'. exfalso. destruct (Bwd _ _ Hg) as (am & Hgu & E).
              pose proof (strip_fields _ _ E) as (_&Eav&_&_&Es&_). apply Hav'. rewrite Eav. apply (Hall g am Hgu). congruence. }
            { intros g am' Hg Hs' Hin Hnh HnR. destruct (Bwd _ _ Hg) as (am & Hgu & E).
              pose proof (strip_fields _ _ E) as (_&_&Efr&_&Es&_). rewrite Efr.
              apply (Q2 g am Hgu ltac:(congruence)); [right; exact Hin| |exact HnR].
              rewrite Hhd. intros E2. injection E2 as ->.
              destruct Rg as [[Hnd _] _]. inversion Hnd; subst. contradiction. }
          - destruct (A sc' Hsc') as (ms' & Rg2 & Mem2 & Full2 & Q12 & Q22). exists ms'.
            destruct Hse as (Hoth & _ & _).
            assert (EH : active_hd s' sc' = active_hd s sc').
            { unfold active_hd. apply Hoth. intros sc0 E0. injection E0 as <-. lia. }
            rewrite EH. split.
            { eapply ring_ok_ext; [|exact Rg2]. intros q _. eapply rl_alinks_other; eauto. }
            split; [|split; [|split]]; intros g am' Hg Hs'; destruct (Bwd _ _ Hg) as (am & Hgu & E);
              pose proof (strip_fields _ _ E) as (_&Eav&Efr&_&Es&_);
              assert (Hgn : ~ In g (m0 :: rest)) by (intros Hi; destruct (SC g Hi) as (a2 & Hu2 & Hs2); pose proof (usedX_fun _ _ _ _ _ Hu2 Hgu) as ->; congruence);
              rewrite (rl_used_same X s s' _ RL g am' Hgn) in Hg.
            + apply Mem2; [exact Hg | exact Hs'].
            + apply Full2; [exact Hg | exact Hs'].
            + apply Q12; [exact Hg | exact Hs'].
            + apply Q22; [exact Hg | exact Hs']. }
        { intros g am' Hg H63. destruct (Bwd _ _ Hg) as (am & Hgu & E).
          pose proof (strip_fields _ _ E) as (_&_&_&_&Es&_).
          assert (Hgn : ~ In g (m0 :: rest)).
          { intros Hi. destruct (SC g Hi) as (a2 & Hu2 & Hs2). pose proof (usedX_fun _ _ _ _ _ Hu2 Hgu) as ->. lia. }
          rewrite (rl_used_same X s s' _ RL g am' Hgn) in Hg. apply (D g am' Hg H63). }
      * eapply rl_usage; eauto. exact (inv_usage HI).
    + rewrite Hhd_new. destruct rest as [|y rest']; [exact I|].
      split.
      { intros ->. destruct Rg as [[Hnd _] _]. inversion Hnd; subst. apply H1. left. reflexivity. }
      destruct (ring_members_used _ _ _ _ _ y Rg (or_intror (or_introl eq_refl))) as (am & Hyu & Hys).
      destruct (Fwd _ _ Hyu) as (am' & Hyu' & E). exists am'.
      pose proof (strip_fields _ _ E) as (_&_&Efr&_&Es&_).
      split; [exact Hyu'|]. split; [congruence|]. split.
      { rewrite Efr. apply (Q2 y am Hyu Hys); [right; left; reflexivity| |intros i; apply HR0].
        rewrite Hhd. intros E2. injection E2 as ->. destruct Rg as [[Hnd _] _]. inversion Hnd; subst. apply H1. left. reflexivity. }
      destruct (ring_links _ _ _ _ Rg' (or_introl eq_refl)) as (pr & nx & L).
      unfold alinks in L. pose proof Hyu' as M. unfold usedX in M. rewrite M in L.
      rewrite Es, Hys, Z.eqb_refl in L. injection L as -> _. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Open Scope mm_scope.

Lemma memb_cons q m X : memb q (m :: X) = sptr_eqb q m || memb q X.
Proof. reflexivity. Qed.

Lemma memb_In q X : memb q X = true <-> In q X.
Proof.
  unfold memb. rewrite existsb_exists. split.
  - intros (x & Hx & E). apply sptr_eqb_eq in E. subst. exact Hx.
  - intros H. exists q. split; [exact H | apply sptr_eqb_refl].
Qed.

Lemma memb_false_notIn q X : memb q X = false <-> ~ In q X.
Proof.
  rewrite <- memb_In. destruct (memb q X); split; intros H; try discriminate; auto. exfalso. apply H. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma flinks_free X s q l : flinks X s q = Some l -> exists pr nx, memb q X = false /\ MT s q = Some (MFree pr nx) /\ l = (pr, nx).
Proof.
  unfold flinks, MTX. destruct (memb q X) eqn:M; [discriminate|].
  destruct (MT s q) as [[pr nx| |am]|] eqn:E; try discriminate. intros H. injection H as <-.
  exists pr, nx. auto.
Qed.

Lemma fring_members_free X s hd ms q :
  ring_ok (flinks X s) hd ms -> In q ms -> exists pr nx, memb q X = false /\ MT s q = Some (MFree pr nx).
Proof.
  intros Hr Hin. destruct (ring_links _ _ _ _ Hr Hin) as (pr & nx & L).
  destruct (flinks_free _ _ _ _ L) as (pr' & nx' & M & E & _). exists pr', nx'. auto.
Qed.

(* [comment removed for export] *)
Lemma dequeue_head_free_spec X R U s (Q : option sptr * astate -> Prop) :
  Inv X R U s ->
  (st_free_meta_head s = None ->
   (forall g pr nx, MTX X s g = Some (MFree pr nx) -> False) -> Q (None, s)) ->
  (forall m s',
     Inv (m :: X) R U s' -> memb m X = false -> MT s' m = Some (MFree None None) ->
     same_but_metas_heads s s' -> st_active s' = st_active s ->
     (forall g am, usedX (m :: X) s' g am <-> usedX X s g am) ->
     ub_same s s' ->
     Q (Some m, s')) ->
  itok (dequeue_head HFreeMeta s) Q.
Proof.
  intros HI HQnone HQsome.
  destruct (inv_rings HI) as (F & A & D). destruct F as (ms & FR & Fall).
  unfold dequeue_head. mbinds. apply itok_get_head'. msimp. cbn [head_of].
  destruct (st_free_meta_head s) as [m|] eqn:Efh.
  2:{ mbinds. apply itok_ret. apply HQnone; [reflexivity|].
      intros g pr nx Hg. pose proof (Fall g pr nx Hg) as Hin. apply ring_None in FR. subst ms. destruct Hin. }
  destruct (ring_head_In _ _ _ FR) as [_ [rest Ems]]. subst ms.
  destruct (fring_members_free _ _ _ _ m FR (or_introl eq_refl)) as (pr0 & nx0 & NXm & Mm).
  pose proof (inv_ctx HI) as (Clen & Crest).
  mbinds.
  eapply (dequeue_op HFreeMeta m s (MFree pr0 nx0) rest (flinks X s)).
  - exact Mm.
  - exact (proj1 FR).
  - intros q l _ Hl. eapply LK_of_flinks. exact Hl.
  - exact I.
  - intros s' Sb Hse Hhd' Mm' Mother Mrest. msimp. apply itok_ret.
    assert (RL : relinked s s' (m :: rest)).
    { split; [exact Mother|]. intros q [<-|Hq].
      - exists (MFree pr0 nx0), None, None. repeat split; auto. discriminate.
      - destruct (fring_members_free _ _ _ _ q FR (or_intror Hq)) as (pr & nx & _ & Mq).
        eexists (MFree pr nx), _, _. split; [exact Mq|]. split; [apply (Mrest q _ Hq Mq) | discriminate]. }
    assert (SX : forall q, In q (m :: rest) -> memb q X = false).
    { intros q Hq. destruct (fring_members_free _ _ _ _ q FR Hq) as (pr & nx & M & _). exact M. }
    (* [comment removed for export] *)
    assert (EU : forall g am, usedX (m :: X) s' g am <-> usedX X s g am).
    { intros g am. unfold usedX, MTX. rewrite memb_cons.
      destruct (sptr_eqb g m) eqn:Egm; cbn [orb].
      - apply sptr_eqb_eq in Egm. subst g. rewrite NXm, Mm. split; discriminate.
      - destruct (memb g X); [tauto|].
        destruct (rl_MT_cases s s' _ RL g) as [E | (x & p' & n' & A1 & B1 & C1 & D1)]; [rewrite E; tauto|].
        rewrite A1, B1. destruct (fring_members_free _ _ _ _ g FR D1) as (pr & nx & _ & Mg).
        rewrite Mg in A1. injection A1 as <-. cbn. split; discriminate. }
    destruct Hse as (Hact & _ & Hlen).
    assert (EA : st_active s' = st_active s).
    { apply nth_ext with (d := None) (d' := None); [exact Hlen|]. intros n _. apply Hact. intros sc E. discriminate. }
    apply HQsome; auto.
    2:{ eapply ub_same_relinked; [exact RL|]. destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). exact K. }
    eapply (Inv_surgery X (m :: X) R R U U s s' HI).
    + destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_& ER &_). intros k rg Hk _. unfold region_of in *. rewrite ER. exact Hk.
    + intros p am' Hp. exists am'. split; [apply EU; exact Hp | reflexivity].
    + intros p am Hp. left. exists am. split; [apply EU; exact Hp | reflexivity].
    + intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hgu & Hrest). exists am. split; [apply EU; exact Hgu | exact Hrest].
    + intros p i am' _. left. tauto.
    + apply (sbmh_ctx s s' Sb); [exact Hlen | | exact (inv_ctx HI)].
      intros Hi. exfalso. destruct Crest as (_&_&_&_&_&_&_&_&_&_&Ci). destruct (Ci Hi) as (Hm & _).
      pose proof (MT_Some_In_keys _ _ _ Mm) as K. unfold keys in K. rewrite Hm in K. exact K.
    + apply (sbmh_keys s s' Sb). exact (inv_keys HI).
    + apply (sbmh_areas s s' Sb). exact (inv_areas HI).
    + (* [comment removed for export] *)
      intros x Hx. destruct Hx as [<-|Hx].
      * split; [| rewrite Mm'; exact I].
        destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). rewrite K. eapply MT_Some_In_keys. exact Mm.
      * destruct (inv_X HI x Hx) as [Kx Mx].
        destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). rewrite K. split; [exact Kx|].
        destruct RL as [R1 _]. rewrite R1; [exact Mx|].
        intros Hin. pose proof (SX x Hin) as E. apply memb_false_notIn in E. exact (E Hx).
    + (* [comment removed for export] *)
      split.
      { exists rest.
        assert (Hfh : st_free_meta_head s' = match rest with [] => None | y :: _ => Some y end).
        { cbn [head_of] in Hhd'. rewrite Hhd', Efh. destruct rest; [reflexivity|]. cbn. rewrite sptr_eqb_refl. reflexivity. }
        split.
        - rewrite Hfh. split; [|destruct rest; reflexivity].
          destruct rest as [|y rest']; [split; [constructor | exact I]|].
          eapply (cycle_remove_first (flinks X s) (flinks (m :: X) s') m (y :: rest')).
          + exact (proj1 FR).
          + discriminate.
          + intros z pr nx Hz Lz. destruct (flinks_free _ _ _ _ Lz) as (pr' & nx' & NXz & Mz & El).
            injection El as <- <-.
            pose proof (Mrest z _ Hz Mz) as Mz'. cbn [with_links] in Mz'.
            unfold flinks, MTX. rewrite memb_cons, NXz.
            replace (sptr_eqb z m) with false.
            2:{ symmetry. apply sptr_eqb_neq. intros ->. destruct FR as [[Hnd _] _]. inversion Hnd; subst. contradiction. }
            cbn [orb]. rewrite Mz'. cbn [fst snd links_of]. reflexivity.
        - intros g pr nx Hg. unfold MTX in Hg. rewrite memb_cons in Hg.
          destruct (sptr_eqb g m) eqn:Egm; [discriminate|]. cbn [orb] in Hg.
          destruct (memb g X) eqn:NXg; [discriminate|].
          destruct (rl_MT_cases s s' _ RL g) as [E | (x & p' & n' & A1 & B1 & C1 & D1)].
          + rewrite E in Hg. assert (Hin : In g (m :: rest)) by (apply (Fall g pr nx); unfold MTX; rewrite NXg; exact Hg).
            destruct Hin as [->|Hin]; [rewrite sptr_eqb_refl in Egm; discriminate | exact Hin].
          + destruct D1 as [->|D1]; [rewrite sptr_eqb_refl in Egm; discriminate | exact D1]. }
      split.
      { intros sc Hsc. destruct (A sc Hsc) as (ms' & Rg2 & Mem2 & Full2 & Q12 & Q22). exists ms'.
        assert (EH : active_hd s' sc = active_hd s sc) by (unfold active_hd; rewrite EA; reflexivity).
        rewrite EH.
        assert (EL : forall q, alinks (m :: X) s' sc q = alinks X s sc q).
        { intros q. unfold alinks.
          destruct (MTX (m :: X) s' q) as [[| |am]|] eqn:E1.
          - destruct (MTX X s q) as [[| |am']|] eqn:E2; try reflexivity.
            assert (Hu : usedX X s q am') by exact E2. apply EU in Hu. unfold usedX in Hu. rewrite Hu in E1. discriminate.
          - destruct (MTX X s q) as [[| |am']|] eqn:E2; try reflexivity.
            assert (Hu : usedX X s q am') by exact E2. apply EU in Hu. unfold usedX in Hu. rewrite Hu in E1. discriminate.
          - assert (Hu : usedX (m :: X) s' q am) by exact E1. apply EU in Hu. unfold usedX in Hu. rewrite Hu. reflexivity.
          - destruct (MTX X s q) as [[| |am']|] eqn:E2; try reflexivity.
            assert (Hu : usedX X s q am') by exact E2. apply EU in Hu. unfold usedX in Hu. rewrite Hu in E1. discriminate. }
        split; [eapply ring_ok_ext; [intros q _; apply EL | exact Rg2]|].
        split; [intros g am Hg; apply EU in Hg; apply Mem2; exact Hg|].
        split; [intros g am Hg; apply EU in Hg; apply Full2; exact Hg|].
        split; [intros g am Hg; apply EU in Hg; apply Q12; exact Hg|].
        intros g am Hg; apply EU in Hg; apply Q22; exact Hg. }
      { intros g am Hg. apply EU in Hg. apply (D g am Hg). }
    + (* [comment removed for export] *)
      intros sc Hsc. rewrite (sbmh_usage_of _ _ sc Sb), (inv_usage HI sc Hsc). f_equal.
      unfold class_sum. destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). rewrite K.
      assert (E : forall l, fold_right (fun g acc => contrib (m :: X) s' sc g + acc) 0 l =
                            fold_right (fun g acc => contrib X s sc g + acc) 0 l).
      { induction l as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. f_equal.
        unfold contrib.
        destruct (MTX (m :: X) s' k) as [[| |am]|] eqn:E1; destruct (MTX X s k) as [[| |am']|] eqn:E2; try reflexivity.
        all: try (assert (Hu : usedX X s k am') by exact E2; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E1; discriminate).
        all: try (assert (Hu : usedX (m :: X) s' k am) by exact E1; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E2; try discriminate).
        injection E2 as ->. reflexivity. }
      symmetry. apply E.
Qed.

(* [comment removed for export] *)
Lemma Inv_upd_exempt X R U s g x :
  Inv X R U s -> In g X ->
  match x with MRaw => True | MFree None None => True
             | MUsed am => am_prev am = None /\ am_next am = None /\ (forall i, ss_fr (nth_slot am i) = None)
             | _ => False end ->
  Inv X R U (upd_meta g x s).
Proof.
  intros HI Hg Hx.
  pose proof (proj1 (inv_X HI g Hg)) as Kg.
  assert (Mg : memb g X = true) by (apply memb_In; exact Hg).
  assert (EMTX : forall q, MTX X (upd_meta g x s) q = MTX X s q).
  { intros q. unfold MTX. rewrite MT_upd. destruct (sptr_eqb q g) eqn:E; [|reflexivity].
    apply sptr_eqb_eq in E. subst q. rewrite Mg. reflexivity. }
  assert (EU : forall q am, usedX X (upd_meta g x s) q am <-> usedX X s q am).
  { intros q am. unfold usedX. rewrite EMTX. tauto. }
  assert (Sb : same_but_metas_heads s (upd_meta g x s)) by (apply sbmh_upd_meta; exact Kg).
  eapply (Inv_surgery X X R R U U s _ HI).
  - intros k rg Hk _. exact Hk.
  - intros p am' Hp. exists am'. split; [apply EU; exact Hp | reflexivity].
  - intros p am Hp. left. exists am. split; [apply EU; exact Hp | reflexivity].
  - intros q i HR. destruct (inv_reserved HI q i HR) as (am & Hu & Hrest). exists am. split; [apply EU; exact Hu | exact Hrest].
  - intros p i am' _. left. tauto.
  - apply (sbmh_ctx s _ Sb); [reflexivity | | exact (inv_ctx HI)].
    intros Hi. exfalso. pose proof (inv_ctx HI) as (_&_&_&_&_&_&_&_&_&_&_&Ci). destruct (Ci Hi) as (Hm & _).
    unfold keys in Kg. rewrite Hm in Kg. exact Kg.
  - apply (sbmh_keys s _ Sb). exact (inv_keys HI).
  - apply (sbmh_areas s _ Sb). exact (inv_areas HI).
  - intros y Hy. destruct (inv_X HI y Hy) as [Ky My]. split; [rewrite (keys_upd_In _ _ _ Kg); exact Ky|].
    rewrite MT_upd. destruct (sptr_eqb y g); [|exact My]. destruct x as [[p|] [n|]| |am]; try exact Hx; destruct Hx.
  - destruct (inv_rings HI) as (F & A & D). split; [|split].
    + destruct F as (ms & FR & Fall). exists ms. split.
      * eapply ring_ok_ext; [|exact FR]. intros q _. unfold flinks. rewrite EMTX. reflexivity.
      * intros q pr nx Hq. rewrite EMTX in Hq. eapply Fall. exact Hq.
    + intros sc Hsc. destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
      change (active_hd (upd_meta g x s) sc) with (active_hd s sc).
      split; [eapply ring_ok_ext; [|exact Rg]; intros q _; unfold alinks; rewrite EMTX; reflexivity|].
      split; [intros q am Hq; apply EU in Hq; apply Mem; exact Hq|].
      split; [intros q am Hq; apply EU in Hq; apply Full; exact Hq|].
      split; [intros q am Hq; apply EU in Hq; apply Q1; exact Hq|].
      intros q am Hq; apply EU in Hq; apply Q2; exact Hq.
    + intros q am Hq. apply EU in Hq. apply (D q am Hq).
  - intros sc Hsc. rewrite (sbmh_usage_of _ _ sc Sb), (inv_usage HI sc Hsc). f_equal.
    unfold class_sum. rewrite (keys_upd_In _ _ _ Kg).
    assert (E : forall l, fold_right (fun q acc => contrib X (upd_meta g x s) sc q + acc) 0 l =
                          fold_right (fun q acc => contrib X s sc q + acc) 0 l).
    { induction l as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. unfold contrib. rewrite EMTX. reflexivity. }
    symmetry. apply E.
Qed.

Lemma usedX_upd_exempt X s g x q am : In g X -> (usedX X (upd_meta g x s) q am <-> usedX X s q am).
Proof.
  intros Hg. unfold usedX, MTX. rewrite MT_upd. destruct (sptr_eqb q g) eqn:E; [|tauto].
  apply sptr_eqb_eq in E. subst q. rewrite (proj2 (memb_In g X) Hg). tauto.
Qed.

(* [comment removed for export] *)
Lemma ucontrib_exempt_nil X R U s g k : Inv X R U s -> In g X -> ucontrib k (MT s g) = [].
Proof.
  intros HI Hg. destruct (inv_X HI g Hg) as [_ Mx]. unfold ucontrib.
  destruct (MT s g) as [[pr nx| |am]|]; try reflexivity. destruct Mx as (A & B & H). apply blocks_of_frameless. exact H.
Qed.

Lemma free_meta_spec X R U s g (Q : unit * astate -> Prop) :
  Inv X R U s -> In g X ->
  (forall s', Inv (remove sptr_eq_dec g X) R U s' ->
     same_but_metas_heads s s' -> st_active s' = st_active s ->
     (forall q am, usedX (remove sptr_eq_dec g X) s' q am <-> usedX X s q am) ->
     ub_same s s' ->
     Q (tt, s')) ->
  itok (free_meta g s) Q.
Proof.
  intros HI Hg HQ.
  unfold free_meta. mbinds. apply itok_setslot'. msimp.
  set (s1 := upd_meta g (MFree None None) s).
  assert (HI1 : Inv X R U s1) by (apply Inv_upd_exempt; [exact HI | exact Hg | exact I]).
  pose proof (proj1 (inv_X HI g Hg)) as Kg.
  assert (Sb1 : same_but_metas_heads s s1) by (apply sbmh_upd_meta; exact Kg).
  assert (Mg1 : MT s1 g = Some (MFree None None)) by (subst s1; apply MT_upd_same).
  destruct (inv_rings HI1) as (F & A & D). destruct F as (ms & FR & Fall).
  pose proof (inv_ctx HI1) as (Clen & Crest).
  assert (Hgn : ~ In g ms).
  { intros Hin. destruct (fring_members_free _ _ _ _ g FR Hin) as (pr & nx & M & _).
    apply memb_false_notIn in M. exact (M Hg). }
  eapply (queue_op HFreeMeta g s1 (MFree None None) ms (flinks X s1)).
  - exact Mg1.
  - reflexivity.
  - exact FR.
  - exact Hgn.
  - intros q l _ Hl. eapply LK_of_flinks. exact Hl.
  - exact I.
  - intros s' Sb Hse Hhd' Mg' Mother Mms.
    set (X' := remove sptr_eq_dec g X) in *.
    assert (RL : relinked s1 s' (g :: ms)).
    { split; [exact Mother|]. intros q [<-|Hq].
      - eexists (MFree None None), _, _. split; [exact Mg1|]. split; [exact Mg'|]. discriminate.
      - destruct (fring_members_free _ _ _ _ q FR Hq) as (pr & nx & _ & Mq).
        eexists (MFree pr nx), _, _. split; [exact Mq|]. split; [apply (Mms q _ Hq Mq) | discriminate]. }
    assert (MX' : forall q, memb q X' = memb q X && negb (sptr_eqb q g)).
    { intros q. subst X'. destruct (memb q X) eqn:E1; destruct (sptr_eqb q g) eqn:E2; cbn.
      - apply memb_false_notIn. apply sptr_eqb_eq in E2. subst. apply remove_In.
      - apply memb_In. apply memb_In in E1. apply in_in_remove; [|exact E1]. apply sptr_eqb_neq in E2. exact E2.
      - apply memb_false_notIn. intros H. apply in_remove in H as [H _]. apply memb_false_notIn in E1. exact (E1 H).
      - apply memb_false_notIn. intros H. apply in_remove in H as [H _]. apply memb_false_notIn in E1. exact (E1 H). }
    assert (EU : forall q am, usedX X' s' q am <-> usedX X s1 q am).
    { intros q am. unfold usedX, MTX. rewrite MX'.
      destruct (sptr_eqb q g) eqn:Eqg; cbn [negb andb].
      - apply sptr_eqb_eq in Eqg. subst q. rewrite (proj2 (memb_In g X) Hg), Mg'. cbn. split; discriminate.
      - rewrite andb_true_r. destruct (memb q X); [tauto|].
        destruct (rl_MT_cases s1 s' _ RL q) as [E | (x & p' & n' & A1 & B1 & C1 & D1)]; [rewrite E; tauto|].
        rewrite A1, B1. destruct D1 as [->|D1]; [rewrite sptr_eqb_refl in Eqg; discriminate|].
        destruct (fring_members_free _ _ _ _ q FR D1) as (pr & nx & _ & Mq).
        rewrite Mq in A1. injection A1 as <-. cbn. split; discriminate. }
    destruct Hse as (Hact & _ & Hlen).
    assert (EA : st_active s' = st_active s1).
    { apply nth_ext with (d := None) (d' := None); [exact Hlen|]. intros n _. apply Hact. intros sc E. discriminate. }
    apply HQ.
    2:{ eapply sbmh_trans; [exact Sb1 | exact Sb]. }
    2:{ rewrite EA. reflexivity. }
    2:{ intros q am. rewrite EU. subst s1. apply usedX_upd_exempt. exact Hg. }
    2:{ eapply ub_same_trans.
        - subst s1. apply (ub_same_upd_In s g (MFree None None) Kg). rewrite (ucontrib_exempt_nil X R U s g g HI Hg). reflexivity.
        - eapply ub_same_relinked; [exact RL|]. destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). exact K. }
    eapply (Inv_surgery X X' R R U U s1 s' HI1).
    + destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_& ER &_). intros k rg Hk _. unfold region_of in *. rewrite ER. exact Hk.
    + intros p am' Hp. exists am'. split; [apply EU; exact Hp | reflexivity].
    + intros p am Hp. left. exists am. split; [apply EU; exact Hp | reflexivity].
    + intros q i HR. destruct (inv_reserved HI1 q i HR) as (am & Hu & Hrest). exists am. split; [apply EU; exact Hu | exact Hrest].
    + intros p i am' _. left. tauto.
    + apply (sbmh_ctx s1 s' Sb); [exact Hlen | | exact (inv_ctx HI1)].
      intros Hi. exfalso. destruct Crest as (_&_&_&_&_&_&_&_&_&_&Ci). destruct (Ci Hi) as (Hm & _).
      pose proof (MT_Some_In_keys _ _ _ Mg1) as K. unfold keys in K. rewrite Hm in K. exact K.
    + apply (sbmh_keys s1 s' Sb). exact (inv_keys HI1).
    + apply (sbmh_areas s1 s' Sb). exact (inv_areas HI1).
    + (* [comment removed for export] *)
      intros y Hy. subst X'. apply in_remove in Hy as [Hy Hyg].
      destruct (inv_X HI1 y Hy) as [Ky My].
      destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). rewrite K. split; [exact Ky|].
      destruct RL as [R1 _]. rewrite R1; [exact My|].
      intros [->|Hin]; [exact (Hyg eq_refl)|].
      destruct (fring_members_free _ _ _ _ y FR Hin) as (pr & nx & M & _). apply memb_false_notIn in M. exact (M Hy).
    + (* [comment removed for export] *)
      split.
      { exists (ms ++ [g]). cbn [head_of] in Hhd'. split.
        - split; [| rewrite Hhd'; destruct ms; reflexivity].
          destruct ms as [|h0 rest].
          { cbn. split; [constructor; [intros [] | constructor]|]. split; [|exact I].
            unfold flinks, MTX. rewrite MX', (proj2 (memb_In g X) Hg), sptr_eqb_refl. cbn [andb negb].
            rewrite Mg'. reflexivity. }
          eapply (cycle_snoc (flinks X s1) (flinks X' s') (h0 :: rest) g (proj1 FR)).
            * discriminate.
            * exact Hgn.
            * intros z pr nx Hz Lz. destruct (flinks_free _ _ _ _ Lz) as (pr' & nx' & NXz & Mz & El).
              injection El as <- <-.
              pose proof (Mms z _ Hz Mz) as Mz'. cbn [with_links] in Mz'.
              unfold flinks, MTX. rewrite MX', NXz.
              replace (sptr_eqb z g) with false by (symmetry; apply sptr_eqb_neq; intros ->; exact (Hgn Hz)).
              cbn [andb negb]. rewrite Mz'. cbn [fst snd links_of]. reflexivity.
            * unfold flinks, MTX. rewrite MX', (proj2 (memb_In g X) Hg), sptr_eqb_refl. cbn [andb negb].
              rewrite Mg'. reflexivity.
        - intros q pr nx Hq. unfold MTX in Hq. rewrite MX' in Hq.
          destruct (sptr_eqb q g) eqn:Eqg; [apply sptr_eqb_eq in Eqg; subst; apply in_app_iff; right; left; reflexivity|].
          rewrite andb_true_r in Hq. apply in_app_iff. left.
          destruct (memb q X) eqn:NXq; [discriminate|].
          destruct (rl_MT_cases s1 s' _ RL q) as [E | (x & p' & n' & A1 & B1 & C1 & D1)].
          + rewrite E in Hq. apply (Fall q pr nx). unfold MTX. rewrite NXq. exact Hq.
          + destruct D1 as [->|D1]; [rewrite sptr_eqb_refl in Eqg; discriminate | exact D1]. }
      split.
      { intros sc Hsc. destruct (A sc Hsc) as (ms' & Rg2 & Mem2 & Full2 & Q12 & Q22). exists ms'.
        assert (EH : active_hd s' sc = active_hd s1 sc) by (unfold active_hd; rewrite EA; reflexivity).
        rewrite EH.
        assert (EL : forall q, alinks X' s' sc q = alinks X s1 sc q).
        { intros q. unfold alinks.
          destruct (MTX X' s' q) as [[| |am]|] eqn:E1.
          - destruct (MTX X s1 q) as [[| |am']|] eqn:E2; try reflexivity.
            assert (Hu : usedX X s1 q am') by exact E2. apply EU in Hu. unfold usedX in Hu. rewrite Hu in E1. discriminate.
          - destruct (MTX X s1 q) as [[| |am']|] eqn:E2; try reflexivity.
            assert (Hu : usedX X s1 q am') by exact E2. apply EU in Hu. unfold usedX in Hu. rewrite Hu in E1. discriminate.
          - assert (Hu : usedX X' s' q am) by exact E1. apply EU in Hu. unfold usedX in Hu. rewrite Hu. reflexivity.
          - destruct (MTX X s1 q) as [[| |am']|] eqn:E2; try reflexivity.
            assert (Hu : usedX X s1 q am') by exact E2. apply EU in Hu. unfold usedX in Hu. rewrite Hu in E1. discriminate. }
        split; [eapply ring_ok_ext; [intros q _; apply EL | exact Rg2]|].
        split; [intros q am Hq; apply EU in Hq; apply Mem2; exact Hq|].
        split; [intros q am Hq; apply EU in Hq; apply Full2; exact Hq|].
        split; [intros q am Hq; apply EU in Hq; apply Q12; exact Hq|].
        intros q am Hq; apply EU in Hq; apply Q22; exact Hq. }
      { intros q am Hq. apply EU in Hq. apply (D q am Hq). }
    + (* [comment removed for export] *)
      intros sc Hsc. rewrite (sbmh_usage_of _ _ sc Sb), (inv_usage HI1 sc Hsc). f_equal.
      unfold class_sum. destruct Sb as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_& K). rewrite K.
      assert (E : forall l, fold_right (fun q acc => contrib X' s' sc q + acc) 0 l =
                            fold_right (fun q acc => contrib X s1 sc q + acc) 0 l).
      { induction l as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. f_equal.
        unfold contrib.
        destruct (MTX X' s' k) as [[| |am]|] eqn:E1; destruct (MTX X s1 k) as [[| |am']|] eqn:E2; try reflexivity.
        all: try (assert (Hu : usedX X s1 k am') by exact E2; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E1; discriminate).
        all: try (assert (Hu : usedX X' s' k am) by exact E1; apply EU in Hu; unfold usedX in Hu; rewrite Hu in E2; try discriminate).
        injection E2 as ->. reflexivity. }
      symmetry. apply E.
Qed.
End MallocWfRings.

Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRingOps OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfRings.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_of_app_old s l k : (k < length (st_regions s))%nat ->
  region_of (set_regions (st_regions s ++ l) s) k = region_of s k.
Proof. intros Hk. unfold region_of. cbn. rewrite nth_error_app1 by exact Hk. reflexivity. Qed.

Lemma region_of_app_new s x : region_of (set_regions (st_regions s ++ [x]) s) (length (st_regions s)) = Some x.
Proof. unfold region_of. cbn. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.


Lemma nth_error_Some_lt {A} (l : list A) k x : nth_error l k = Some x -> (k < length l)%nat.
Proof.
  revert k. induction l as [|h t IH]; intros [|k] H; cbn in H; try discriminate; cbn; [lia|].
  apply IH in H. lia.
Qed.

Lemma region_of_lt s k rg : region_of s k = Some rg -> (k < length (st_regions s))%nat.
Proof. unfold region_of. apply nth_error_Some_lt. Qed.

Lemma region_of_app s l k rg : region_of s k = Some rg -> region_of (set_regions (st_regions s ++ l) s) k = Some rg.
Proof. intros H. rewrite region_of_app_old; [exact H | eapply region_of_lt; exact H]. Qed.

Lemma region_of_upd s r f k :
  region_of (set_regions (lupd (st_regions s) r f) s) k =
  if (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool then Some f else region_of s k.
Proof. unfold region_of. cbn. apply nth_error_lupd. Qed.

(* [comment removed for export] *)
Lemma InvMeta_regions X R U s rs :
  (forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> region_of (set_regions rs s) k = Some rg) ->
  InvMeta X R U s -> InvMeta X R U (set_regions rs s).
Proof.
  intros Hreg (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
  assert (EU : forall g am, usedX X (set_regions rs s) g am <-> usedX X s g am) by (intros; unfold usedX, MTX, MT; cbn; tauto).
  split; [exact M1|]. split.
  { intros g am Hg. pose proof (M2 g am Hg) as (G1 & G2 & G3 & G4 & G5 & G6).
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [|exact G6].
    intros Hm. destruct (G5 Hm) as (r & rg & H1 & H2 & H3 & H4 & H5 & H6). exists r, rg.
    split; [exact H1|]. split; [apply Hreg; assumption|]. auto. }
  split; [exact M3|]. split; [exact M4|]. split; [exact M5|]. split; [exact M6|]. split; [exact M7 | exact M8].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma area_slots_disjoint s a1 a2 k1 k2 :
  areas_ok s -> In a1 (st_areas s) -> In a2 (st_areas s) -> a1 <> a2 ->
  0 <= k1 < METAS_PER_AREA -> 0 <= k2 < METAS_PER_AREA ->
  padd a1 (AREA_HDR + META_SIZE * k1) <> padd a2 (AREA_HDR + META_SIZE * k2).
Proof.
  intros A H1 H2 Hne Hk1 Hk2 E.
  destruct A as (_ & Aok & _).
  destruct (Aok a1 H1) as (r1 & o1 & rg1 & -> & Ho1 & _).
  destruct (Aok a2 H2) as (r2 & o2 & rg2 & -> & Ho2 & _).
  pose proof (f_equal prid E) as Er. pose proof (f_equal poff E) as Eo. cbn [prid poff padd] in Er, Eo. subst r2.
  assert (o1 <> o2) by (intros ->; apply Hne; reflexivity).
  pose proof (eq_refl : AREA_HDR = 24) as C1. pose proof (eq_refl : META_SIZE = 40) as C2.
  pose proof (eq_refl : METAS_PER_AREA = 101) as C3. pose proof (eq_refl : PGSZ = 4096) as C4.
  rewrite C4 in Ho1, Ho2.
  pose proof (Z_div_mod_eq_full o1 4096) as D1. pose proof (Z_div_mod_eq_full o2 4096) as D2.
  rewrite Ho1 in D1. rewrite Ho2 in D2.
  remember (o1 / 4096) as q1 eqn:Q1. remember (o2 / 4096) as q2 eqn:Q2. clear Q1 Q2. lia.
Qed.

Lemma area_slot_inj a k1 k2 :
  padd a (AREA_HDR + META_SIZE * k1) = padd a (AREA_HDR + META_SIZE * k2) -> k1 = k2.
Proof. destruct a. intros E. pose proof (f_equal poff E) as Eo. cbn [poff padd] in Eo. pose proof (eq_refl : META_SIZE = 40). lia. Qed.

(* [comment removed for export] *)
Lemma take_slot_Inv X R U s :
  Inv X R U s -> 0 < st_avail_meta_count s ->
  let m := st_avail_meta s in
  let s' := upd_meta m MRaw (set_avail_meta (padd m META_SIZE) (set_avail_meta_count (st_avail_meta_count s - 1) s)) in
  ~ In m (keys s) /\ memb m X = false /\ Inv (m :: X) R U s' /\
  (forall g am, usedX (m :: X) s' g am <-> usedX X s g am).
Proof.
  intros HI Hc m s'.
  pose proof (inv_keys HI) as (Knd & Kpl & Kemp & Kav & Krange).
  assert (Hne : st_areas s <> []) by (intros E; pose proof (Kemp E); lia).
  set (la := last (st_areas s) (SP 0%nat 0)) in *.
  assert (Hla : In la (st_areas s)) by (subst la; apply In_last; exact Hne).
  pose proof (Kav Hne) as Em. fold m in Em.
  assert (Hfresh : ~ In m (keys s)).
  { intros Hin. destruct (Kpl m Hin) as (a & k & Ha & Hk & Ep).
    unfold handed in Hk. fold la in Hk.
    destruct (sptr_eq_dec a la) as [->|Hna].
    - rewrite sptr_eqb_refl in Hk. rewrite Em in Ep. apply area_slot_inj in Ep. lia.
    - replace (sptr_eqb a la) with false in Hk by (symmetry; apply sptr_eqb_neq; exact Hna).
      rewrite Em in Ep.
      refine (area_slots_disjoint s la a (METAS_PER_AREA - st_avail_meta_count s) k (inv_areas HI) Hla Ha _ _ _ Ep).
      + intros E. apply Hna. symmetry. exact E.
      + pose proof (eq_refl : METAS_PER_AREA = 101). unfold METAS_PER_AREA in *. lia.
      + pose proof (eq_refl : METAS_PER_AREA = 101). unfold METAS_PER_AREA in *. lia. }
  assert (NXm : memb m X = false).
  { apply memb_false_notIn. intros Hx. apply Hfresh. exact (proj1 (inv_X HI m Hx)). }
  set (s1 := set_avail_meta (padd m META_SIZE) (set_avail_meta_count (st_avail_meta_count s - 1) s)).
  assert (K1 : keys s' = keys s ++ [m]).
  { subst s'. rewrite keys_upd_notIn; [reflexivity|]. exact Hfresh. }
  assert (EMT : forall q, q <> m -> MT s' q = MT s q).
  { intros q Hq. subst s'. rewrite MT_upd_other by exact Hq. reflexivity. }
  assert (Mm : MT s' m = Some MRaw) by (subst s'; apply MT_upd_same).
  assert (Mm0 : MT s m = None) by (unfold MT; apply mlookup_None_iff; exact Hfresh).
  assert (EU : forall g am, usedX (m :: X) s' g am <-> usedX X s g am).
  { intros g am. unfold usedX, MTX. rewrite memb_cons. destruct (sptr_eqb g m) eqn:E; cbn [orb].
    - apply sptr_eqb_eq in E. subst g. rewrite NXm, Mm0. split; discriminate.
    - rewrite EMT by (apply sptr_eqb_neq; exact E). tauto. }
  split; [exact Hfresh|]. split; [exact NXm|]. split; [|exact EU].
  assert (EMTX : forall q, MTX (m :: X) s' q = match MTX X s q with Some x => Some x | None => None end).
  { intros q. unfold MTX. rewrite memb_cons. destruct (sptr_eqb q m) eqn:E; cbn [orb].
    - apply sptr_eqb_eq in E. subst q. rewrite NXm, Mm0. reflexivity.
    - rewrite EMT by (apply sptr_eqb_neq; exact E). destruct (memb q X); [reflexivity|]. destruct (MT s q); reflexivity. }
  assert (EMTX' : forall q, MTX (m :: X) s' q = MTX X s q).
  { intros q. rewrite EMTX. destruct (MTX X s q); reflexivity. }
  eapply (Inv_surgery X (m :: X) R R U U s s' HI).
  - intros k rg Hk _. exact Hk.
  - intros p am' Hp. exists am'. split; [apply EU; exact Hp | reflexivity].
  - intros p am Hp. left. exists am. split; [apply EU; exact Hp | reflexivity].
  - intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hu & Hrest). exists am. split; [apply EU; exact Hu | exact Hrest].
  - intros p i am' _. left. tauto.
  - (* [comment removed for export] *)
    pose proof (inv_ctx HI) as C. unfold ctx_ok in *. subst s' s1. unfold upd_meta. cbn -[Z.pow Z.lt Z.le].
    destruct C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj C11 _))))))))))).
    intros Hi. exfalso. destruct (C12 Hi) as (_ & Ha & _). exact (Hne Ha).
  - (* [comment removed for export] *)
    unfold keys_ok. rewrite K1.
    assert (Ea : st_areas s' = st_areas s) by reflexivity. rewrite Ea.
    assert (Ev : st_avail_meta s' = padd m META_SIZE) by reflexivity.
    assert (Ec : st_avail_meta_count s' = st_avail_meta_count s - 1) by reflexivity.
    assert (Eh : forall a, handed s' a = if sptr_eqb a la then METAS_PER_AREA - (st_avail_meta_count s - 1) else METAS_PER_AREA).
    { intros a. unfold handed. rewrite Ea, Ec. fold la. reflexivity. }
    split.
    { apply NoDup_app_single; assumption. }
    split.
    { intros p Hp. apply in_app_iff in Hp as [Hp | [<- | []]].
      - destruct (Kpl p Hp) as (a & k & Ha & Hk & Ep). exists a, k. split; [exact Ha|]. split; [|exact Ep].
        rewrite Eh. unfold handed in Hk. fold la in Hk. destruct (sptr_eqb a la); lia.
      - exists la, (METAS_PER_AREA - st_avail_meta_count s). split; [exact Hla|]. split; [|exact Em].
        rewrite Eh, sptr_eqb_refl. lia. }
    split; [intros E; exfalso; exact (Hne E)|].
    split; [|rewrite Ec; lia].
    intros _. rewrite Ev, Ec, Em. fold la. destruct la; cbn [padd]. f_equal. pose proof (eq_refl : META_SIZE = 40). lia.
  - exact (inv_areas HI).
  - (* [comment removed for export] *)
    intros x [<-|Hx].
    + rewrite K1, Mm. split; [apply in_app_iff; right; left; reflexivity | exact I].
    + destruct (inv_X HI x Hx) as [Kx Mx]. rewrite K1. split; [apply in_app_iff; left; exact Kx|].
      rewrite EMT; [exact Mx|]. intros ->. exact (Hfresh Kx).
  - (* [comment removed for export] *)
    destruct (inv_rings HI) as (F & A & D). split; [|split].
    + destruct F as (ms & FR & Fall). exists ms. split.
      * eapply ring_ok_ext; [|exact FR]. intros q _. unfold flinks. rewrite EMTX'. reflexivity.
      * intros q pr nx Hq. rewrite EMTX' in Hq. eapply Fall. exact Hq.
    + intros sc Hsc. destruct (A sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
      change (active_hd s' sc) with (active_hd s sc).
      split; [eapply ring_ok_ext; [|exact Rg]; intros q _; unfold alinks; rewrite EMTX'; reflexivity|].
      split; [intros q am Hq; apply EU in Hq; apply Mem; exact Hq|].
      split; [intros q am Hq; apply EU in Hq; apply Full; exact Hq|].
      split; [intros q am Hq; apply EU in Hq; apply Q1; exact Hq|].
      intros q am Hq; apply EU in Hq; apply Q2; exact Hq.
    + intros q am Hq. apply EU in Hq. apply (D q am Hq).
  - (* [comment removed for export] *)
    intros sc Hsc. change (usage_of s' sc) with (usage_of s sc). rewrite (inv_usage HI sc Hsc). f_equal.
    unfold class_sum. rewrite K1, fold_right_app. cbn [fold_right].
    replace (contrib (m :: X) s' sc m) with 0.
    2:{ unfold contrib, MTX. rewrite memb_cons, sptr_eqb_refl. reflexivity. }
    rewrite Z.add_0_l || idtac.
    assert (E : forall l acc, fold_right (fun q a => contrib (m :: X) s' sc q + a) acc l =
                              fold_right (fun q a => contrib X s sc q + a) acc l).
    { induction l as [|k t IH]; intros acc; [reflexivity|]. cbn [fold_right]. rewrite IH. unfold contrib. rewrite EMTX'. reflexivity. }
    rewrite E. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Inv_nonmeta X R U s s' :
  Inv X R U s ->
  st_metas s' = st_metas s -> st_active s' = st_active s ->
  st_free_meta_head s' = st_free_meta_head s -> st_usage s' = st_usage s ->
  (forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> region_of s' k = Some rg) ->
  ctx_ok s' -> keys_ok s' -> areas_ok s' -> Inv X R U s'.
Proof.
  intros HI Em Ea Ef Eu Hreg C K A.
  assert (EMT : forall q, MT s' q = MT s q) by (intros; unfold MT; rewrite Em; reflexivity).
  assert (EU : forall g am, usedX X s' g am <-> usedX X s g am) by (intros; unfold usedX, MTX; rewrite EMT; tauto).
  eapply (Inv_surgery X X R R U U s s' HI).
  - exact Hreg.
  - intros p am' Hp. exists am'. split; [apply EU; exact Hp | reflexivity].
  - intros p am Hp. left. exists am. split; [apply EU; exact Hp | reflexivity].
  - intros g i HR. destruct (inv_reserved HI g i HR) as (am & Hu & Hrest). exists am. split; [apply EU; exact Hu | exact Hrest].
  - intros p i am' _. left. tauto.
  - exact C. - exact K. - exact A.
  - intros x Hx. destruct (inv_X HI x Hx) as [Kx Mx]. unfold keys. rewrite Em, EMT. split; [exact Kx | exact Mx].
  - destruct (inv_rings HI) as (F & AR & D). split; [|split].
    + destruct F as (ms & FR & Fall). exists ms. rewrite Ef. split.
      * eapply ring_ok_ext; [|exact FR]. intros q _. unfold flinks, MTX. rewrite EMT. reflexivity.
      * intros q pr nx Hq. unfold MTX in *. rewrite EMT in Hq. eapply Fall. exact Hq.
    + intros sc Hsc. destruct (AR sc Hsc) as (ms & Rg & Mem & Full & Q1 & Q2). exists ms.
      replace (active_hd s' sc) with (active_hd s sc) by (unfold active_hd; rewrite Ea; reflexivity).
      split; [eapply ring_ok_ext; [|exact Rg]; intros q _; unfold alinks, MTX; rewrite EMT; reflexivity|].
      split; [intros q am Hq; apply EU in Hq; apply Mem; exact Hq|].
      split; [intros q am Hq; apply EU in Hq; apply Full; exact Hq|].
      split; [intros q am Hq; apply EU in Hq; apply Q1; exact Hq|].
      intros q am Hq; apply EU in Hq; apply Q2; exact Hq.
    + intros q am Hq. apply EU in Hq. apply (D q am Hq).
  - intros sc Hsc. unfold usage_of. rewrite Eu. pose proof (inv_usage HI sc Hsc) as E. unfold usage_of in E. rewrite E.
    f_equal. unfold class_sum, keys. rewrite Em.
    assert (EE : forall l, fold_right (fun q a => contrib X s' sc q + a) 0 l = fold_right (fun q a => contrib X s sc q + a) 0 l).
    { induction l as [|k t IH]; [reflexivity|]. cbn [fold_right]. rewrite IH. unfold contrib, MTX. rewrite EMT. reflexivity. }
    symmetry. apply EE.
Qed.

(* [comment removed for export] *)
Lemma Inv_brk_dead X R U s :
  Inv X R U s -> st_brk s <> BrkDead -> st_init_done s = true -> Inv X R U (set_brk BrkDead s).
Proof.
  intros HI Hb Hinit. eapply Inv_nonmeta; try exact HI; try reflexivity.
  - intros k rg Hk _. exact Hk.
  - pose proof (inv_ctx HI) as C. unfold ctx_ok in *.
    destruct C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj C11 _))))))))))).
    cbn [st_init_done set_brk]. intros Hi. rewrite Hinit in Hi. discriminate.
  - exact (inv_keys HI).
  - pose proof (inv_areas HI) as A. unfold areas_ok in *.
    destruct A as (A1&A2&A3&A4&A5&A6&A7&A8).
    refine (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj _ A8))))))).
    cbn [st_brk set_brk]. change (brk_regions (set_brk BrkDead s)) with (brk_regions s).
    change (region_of (set_brk BrkDead s)) with (region_of s).
    destruct (st_brk s) as [| |r p] eqn:Eb.
    + intros r Hr. rewrite A7 in Hr. destruct Hr.
    + exfalso. apply Hb. reflexivity.
    + intros r' Hr'. destruct A7 as (Hbr & rg & Hrg & Hl & Hlen & Hp). rewrite Hbr in Hr' |- *.
      destruct Hr' as [<-|[]]. split; [reflexivity|]. exists rg. split; [exact Hrg|]. split; [exact Hl|].
      rewrite Hlen. pose proof (eq_refl : PGSZ = 4096). split; [|nia].
      rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)

Lemma brk_regions_app s x :
  brk_regions (set_regions (st_regions s ++ [x]) s) =
  brk_regions s ++ match rg_kind x with RkBrk => [length (st_regions s)] | _ => [] end.
Proof.
  unfold brk_regions. cbn [st_regions set_regions]. rewrite length_app. cbn [length].
  rewrite Nat.add_1_r, seq_S, flat_map_app. cbn [flat_map]. rewrite region_of_app_new, app_nil_r. f_equal.
  apply flat_map_ext_In. intros k Hk. apply in_seq in Hk. rewrite region_of_app_old by lia. reflexivity.
Qed.

Lemma brk_regions_upd s r x rg :
  region_of s r = Some rg -> rg_kind x = rg_kind rg ->
  brk_regions (set_regions (lupd (st_regions s) r x) s) = brk_regions s.
Proof.
  intros Hr Hk. unfold brk_regions. cbn [st_regions set_regions]. rewrite length_lupd.
  apply flat_map_ext_In. intros k Hk'. rewrite region_of_upd.
  destruct (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [E1 _]. apply Nat.eqb_eq in E1. subst k. rewrite Hr, Hk. reflexivity.
Qed.

Lemma resv_total_app s x :
  resv_total (set_regions (st_regions s ++ [x]) s) =
  resv_total s + match rg_kind x with RkMetaRes => rg_len x | _ => 0 end.
Proof.
  unfold resv_total. cbn [st_regions set_regions]. rewrite fold_right_app. cbn [fold_right].
  assert (G : forall l acc, fold_right (fun rg a => match rg_kind rg with RkMetaRes => rg_len rg + a | _ => a end) acc l =
                           fold_right (fun rg a => match rg_kind rg with RkMetaRes => rg_len rg + a | _ => a end) 0 l + acc).
  { induction l as [|h t IH]; intros acc; cbn; [lia|]. rewrite IH. destruct (rg_kind h); lia. }
  rewrite G. destruct (rg_kind x); lia.
Qed.

Lemma resv_opened_app s x :
  resv_opened (set_regions (st_regions s ++ [x]) s) =
  resv_opened s + match rg_kind x with RkMetaRes => Z.of_nat (length (rg_rw x)) | _ => 0 end.
Proof.
  unfold resv_opened. cbn [st_regions set_regions]. rewrite fold_right_app. cbn [fold_right].
  assert (G : forall l acc, fold_right (fun rg a => match rg_kind rg with RkMetaRes => Z.of_nat (length (rg_rw rg)) + a | _ => a end) acc l =
                           fold_right (fun rg a => match rg_kind rg with RkMetaRes => Z.of_nat (length (rg_rw rg)) + a | _ => a end) 0 l + acc).
  { induction l as [|h t IH]; intros acc; cbn [fold_right]; [lia|]. rewrite IH. destruct (rg_kind h); lia. }
  rewrite G. destruct (rg_kind x); lia.
Qed.

Lemma resv_count_app s x :
  resv_count (set_regions (st_regions s ++ [x]) s) = resv_count s + match rg_kind x with RkMetaRes => 1 | _ => 0 end.
Proof.
  unfold resv_count. cbn [st_regions set_regions]. rewrite fold_right_app. cbn [fold_right].
  assert (G : forall l acc, fold_right (fun rg a => match rg_kind rg with RkMetaRes => 1 + a | _ => a end) acc l =
                           fold_right (fun rg a => match rg_kind rg with RkMetaRes => 1 + a | _ => a end) 0 l + acc).
  { induction l as [|h t IH]; intros acc; cbn [fold_right]; [lia|]. rewrite IH. destruct (rg_kind h); lia. }
  rewrite G. destruct (rg_kind x); lia.
Qed.

Lemma resv_oc_upd s r x rg :
  region_of s r = Some rg ->
  match rg_kind rg with RkMetaRes => rg_kind x = RkMetaRes | _ => rg_kind x <> RkMetaRes end ->
  resv_count (set_regions (lupd (st_regions s) r x) s) = resv_count s /\ resv_opened (set_regions (lupd (st_regions s) r x) s) =
    resv_opened s + match rg_kind rg with RkMetaRes => Z.of_nat (length (rg_rw x)) - Z.of_nat (length (rg_rw rg)) | _ => 0 end.
Proof.
  unfold resv_count, resv_opened, region_of. cbn [st_regions set_regions].
  revert r. induction (st_regions s) as [|h t IH]; intros [|r] Hr Hk; cbn [fold_right lupd nth_error] in Hr |- *; try discriminate.
  - injection Hr as ->. destruct (rg_kind rg) eqn:E.
    + destruct (rg_kind x); [split; lia | congruence | split; lia].
    + rewrite Hk. split; lia.
    + destruct (rg_kind x); [split; lia | congruence | split; lia].
  - destruct (IH r Hr Hk) as [A B]. rewrite A, B. destruct (rg_kind h); split; lia.
Qed.

Lemma resv_total_upd s r x rg :
  region_of s r = Some rg ->
  match rg_kind rg with RkMetaRes => rg_kind x = RkMetaRes /\ rg_len x = rg_len rg | _ => rg_kind x <> RkMetaRes end ->
  resv_total (set_regions (lupd (st_regions s) r x) s) = resv_total s.
Proof.
  unfold resv_total, region_of. cbn [st_regions set_regions].
  revert r. induction (st_regions s) as [|h t IH]; intros [|r] Hr Hk; cbn in Hr |- *; try discriminate.
  - injection Hr as ->. destruct (rg_kind rg) eqn:E.
    + destruct (rg_kind x); [reflexivity| congruence | reflexivity].
    + destruct Hk as [-> ->]. reflexivity.
    + destruct (rg_kind x); [reflexivity | congruence | reflexivity].
  - rewrite (IH r Hr Hk). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Inv_new_resv X R U s :
  Inv X R U s -> st_avail_meta_area_count s = 0 -> st_init_done s = true ->
  let n := Z.shiftl 2 (st_meta_alloc_shift s) in
  let r := length (st_regions s) in
  Inv X R U (set_meta_alloc_shift (st_meta_alloc_shift s + 1)
              (set_avail_meta_area_count (n - 1)
                (set_avail_meta_areas (SP r PGSZ)
                  (set_regions (st_regions s ++ [mkRegion RkMetaRes (n * PGSZ) [] true]) s)))).
Proof.
  intros HI Hc0 Hinit n r.
  pose proof (inv_ctx HI) as C. pose proof C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
  assert (Hn : n = 2 * 2 ^ st_meta_alloc_shift s) by (subst n; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  assert (Hpow : 1 <= 2 ^ st_meta_alloc_shift s).
  { pose proof (Z.pow_pos_nonneg 2 (st_meta_alloc_shift s)). lia. }
  assert (Hn2 : 2 <= n) by lia.
  pose proof (eq_refl : PGSZ = 4096) as HP.
  set (x := mkRegion RkMetaRes (n * PGSZ) [] true).
  set (s' := set_meta_alloc_shift _ _).
  assert (ERG : forall k, region_of s' k = region_of (set_regions (st_regions s ++ [x]) s) k) by reflexivity.
  eapply Inv_nonmeta; try exact HI; try reflexivity.
  - intros k rg Hk _. rewrite ERG. apply region_of_app. exact Hk.
  - unfold ctx_ok. subst s'. simp_st.
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj _ (conj _ _))))))))))); [lia | lia |].
    intros Hi. rewrite Hinit in Hi. discriminate.
  - exact (inv_keys HI).
  - pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9&A10). unfold areas_ok.
    refine (conj A1 (conj _ (conj A3 (conj A4 (conj _ (conj _ (conj _ (conj _ _)))))))).
    + intros a Ha. destruct (A2 a Ha) as (ra & oa & rga & Ea & Ho & Hlo & Hrg & Hl & Hhi & Hk).
      exists ra, oa, rga. repeat (split; [assumption|]). split; [| split; [exact Hl | split; [exact Hhi | exact Hk]]].
      rewrite ERG. apply region_of_app. exact Hrg.
    + intros k rg Hk Hkind. rewrite ERG in Hk.
      unfold region_of in Hk. cbn [st_regions set_regions] in Hk. rewrite nth_error_app in Hk.
      destruct (Nat.ltb k (length (st_regions s))) eqn:El.
      * eapply A5; [exact Hk | exact Hkind].
      * destruct (k - length (st_regions s))%nat as [|k'] eqn:Ek; cbn in Hk; [|destruct k'; discriminate].
        injection Hk as <-. unfold x. cbn [rg_live rg_len]. split; [reflexivity|]. split; [|nia]. rewrite HP. apply Z_mod_mult.
    + destruct A6 as (A6a & A6b & A6c & A6d). split; [|split; [|split]].
      * change (resv_total (set_regions (st_regions s ++ [x]) s) = 2 * PGSZ * (2 ^ (st_meta_alloc_shift s + 1) - 1)).
        rewrite resv_total_app. unfold x. cbn [rg_kind rg_len]. rewrite A6a, Z.pow_add_r, Hn by lia. change (2 ^ 1) with 2. lia.
      * change (PGSZ * (resv_opened (set_regions (st_regions s ++ [x]) s) + (n - 1) + resv_count (set_regions (st_regions s ++ [x]) s)) =
                resv_total (set_regions (st_regions s ++ [x]) s)).
        rewrite resv_total_app, resv_opened_app, resv_count_app. unfold x. cbn [rg_kind rg_len rg_rw length Z.of_nat].
        rewrite Hc0 in A6b. rewrite HP in *. lia.
      * change (resv_count (set_regions (st_regions s ++ [x]) s) = st_meta_alloc_shift s + 1).
        rewrite resv_count_app. unfold x. cbn [rg_kind]. rewrite A6c. reflexivity.
      * intros r' rg' o Hr' Hk' Ho1 Ho2. rewrite ERG in Hr'. unfold region_of in Hr'. cbn [st_regions set_regions] in Hr'.
        rewrite nth_error_app in Hr'. destruct (Nat.ltb r' (length (st_regions s))) eqn:El.
        -- destruct (A6d r' rg' o Hr' Hk' Ho1 Ho2) as [Hin|(Hc & _)]; [left; exact Hin | rewrite Hc0 in Hc; lia].
        -- destruct (r' - length (st_regions s))%nat as [|k'] eqn:Ek; cbn in Hr'; [|destruct k'; discriminate].
           injection Hr' as <-. right. change (st_avail_meta_area_count s') with (n - 1). change (st_avail_meta_areas s') with (SP r PGSZ).
           cbn [prid poff]. split; [lia|]. split; [|lia]. subst r. apply Nat.ltb_ge in El. lia.
    + change (st_brk s') with (st_brk s).
      assert (EB : brk_regions s' = brk_regions s).
      { change (brk_regions (set_regions (st_regions s ++ [x]) s) = brk_regions s).
        rewrite brk_regions_app. unfold x. cbn [rg_kind]. apply app_nil_r. }
      rewrite EB.
      destruct (st_brk s) as [| |rb pb].
      * exact A7.
      * intros rr Hrr. destruct (A7 rr Hrr) as (Hbr & rg & Hrg & Hrest). split; [exact Hbr|]. exists rg.
        split; [rewrite ERG; apply region_of_app; exact Hrg | exact Hrest].
      * destruct A7 as (Hbr & rg & Hrg & Hrest). split; [exact Hbr|]. exists rg.
        split; [rewrite ERG; apply region_of_app; exact Hrg | exact Hrest].
    + change (st_avail_meta_area_count s') with (n - 1). change (st_avail_meta_areas s') with (SP r PGSZ).
      intros _. exists r, PGSZ, x.
      split; [reflexivity|]. split.
      { rewrite ERG. subst r. apply region_of_app_new. }
      unfold x. cbn [rg_kind rg_live rg_len rg_rw]. split; [reflexivity|]. split; [reflexivity|].
      split; [rewrite HP; reflexivity|]. split; [lia|]. split; [nia|]. intros y [].
    + split.
      * intros k rg Hk. rewrite ERG in Hk. unfold region_of in Hk. cbn [st_regions set_regions] in Hk. rewrite nth_error_app in Hk.
        destruct (Nat.ltb k (length (st_regions s))); [eapply A9; exact Hk|].
        destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk; [injection Hk as <-; cbn; split; [nia | intros _; nia] | destruct k'; discriminate].
      * intros _. change (st_avail_meta_areas s') with (SP r PGSZ). cbn [prid]. exists x. rewrite ERG. subst r. apply region_of_app_new.
Qed.

(* [comment removed for export] *)
Definition open_st (p : sptr) (s : astate) : astate :=
  set_avail_meta (padd p AREA_HDR)
    (set_avail_meta_count METAS_PER_AREA
      (set_areas (st_areas s ++ [p])
        (set_area_head (match st_area_head s with None => Some p | h => h end)
          (set_area_tail (Some p)
            (set_avail_meta_areas (padd p 4096)
              (set_avail_meta_area_count (st_avail_meta_area_count s - 1) s)))))).

Lemma st_areas_open p s : st_areas (open_st p s) = st_areas s ++ [p]. Proof. reflexivity. Qed.
Lemma st_area_head_open p s : st_area_head (open_st p s) = match st_area_head s with None => Some p | h => h end. Proof. reflexivity. Qed.
Lemma st_area_tail_open p s : st_area_tail (open_st p s) = Some p. Proof. reflexivity. Qed.
Lemma st_regions_open p s : st_regions (open_st p s) = st_regions s. Proof. reflexivity. Qed.
Lemma st_brk_open p s : st_brk (open_st p s) = st_brk s. Proof. reflexivity. Qed.
Lemma st_shift_open p s : st_meta_alloc_shift (open_st p s) = st_meta_alloc_shift s. Proof. reflexivity. Qed.
Lemma st_area_count_open p s : st_avail_meta_area_count (open_st p s) = st_avail_meta_area_count s - 1. Proof. reflexivity. Qed.
Lemma st_areas_ptr_open p s : st_avail_meta_areas (open_st p s) = padd p 4096. Proof. reflexivity. Qed.
Lemma region_of_open p s k : region_of (open_st p s) k = region_of s k. Proof. reflexivity. Qed.
Lemma brk_regions_open p s : brk_regions (open_st p s) = brk_regions s. Proof. reflexivity. Qed.
Lemma resv_total_open p s : resv_total (open_st p s) = resv_total s. Proof. reflexivity. Qed.
Lemma resv_opened_open p s : resv_opened (open_st p s) = resv_opened s. Proof. reflexivity. Qed.
Lemma resv_count_open p s : resv_count (open_st p s) = resv_count s. Proof. reflexivity. Qed.
Lemma st_metas_open p s : st_metas (open_st p s) = st_metas s. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma keys_ok_open s p :
  keys_ok s -> st_avail_meta_count s = 0 -> ~ In p (st_areas s) ->
  keys_ok (open_st p s).
Proof.
  intros (Knd & Kpl & Kemp & Kav & Krange) Hc0 Hfresh.
  unfold keys_ok, key_placed, handed. unfold open_st. simp_st.
  change (keys (set_avail_meta _ _)) with (keys s).
  rewrite last_app_single.
  split; [exact Knd|]. split.
  { intros q Hq. destruct (Kpl q Hq) as (a & k & Ha & Hk & E). exists a, k.
    split; [apply in_app_iff; left; exact Ha|]. split; [|exact E].
    unfold handed in Hk. replace (sptr_eqb a p) with false by (symmetry; apply sptr_eqb_neq; intros ->; exact (Hfresh Ha)).
    destruct (sptr_eqb a (last (st_areas s) (SP 0%nat 0))); lia. }
  split; [intros E; destruct (st_areas s); discriminate|].
  split; [| pose proof (eq_refl : METAS_PER_AREA = 101); lia].
  intros _. rewrite Z.sub_diag, Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.

Lemma ctx_ok_open s p :
  ctx_ok s -> st_init_done s = true -> 1 <= st_avail_meta_area_count s -> ctx_ok (open_st p s).
Proof.
  intros C Hi Hc. unfold ctx_ok in *. unfold open_st. simp_st.
  destruct C as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
  refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj _ _))))))))))); [lia|].
  intros H. rewrite Hi in H. discriminate.
Qed.

Lemma brk_regions_In s r : In r (brk_regions s) -> exists rg, region_of s r = Some rg /\ rg_kind rg = RkBrk.
Proof.
  unfold brk_regions. intros H. apply in_flat_map in H as (k & Hk & Hin).
  destruct (region_of s k) as [rg|] eqn:E; [|destruct Hin].
  destruct (rg_kind rg) eqn:Ek; try (destruct Hin; fail); destruct Hin as [<-|[]].
  exists rg. auto.
Qed.

(* [comment removed for export] *)
Lemma Inv_open_resv X R U s r o rg :
  Inv X R U s -> 0 < st_avail_meta_area_count s -> st_avail_meta_count s = 0 -> st_init_done s = true ->
  st_avail_meta_areas s = SP r o -> region_of s r = Some rg ->
  Inv X R U (open_st (SP r o) (set_regions (lupd (st_regions s) r (mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [o]) (rg_live rg))) s)).
Proof.
  intros HI Hc Hm0 Hinit Ep Hrg.
  pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9&A10).
  destruct (A8 Hc) as (r' & o' & rg' & Ep' & Hrg' & Hk & Hl & Ho & Hlo & Hlen & Hrw).
  rewrite Ep in Ep'. injection Ep' as <- <-. rewrite Hrg in Hrg'. injection Hrg' as <-.
  set (x := mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [o]) (rg_live rg)).
  set (s1 := set_regions (lupd (st_regions s) r x) s).
  pose proof (region_of_lt _ _ _ Hrg) as Hrlt.
  assert (ERG : forall k, region_of (open_st (SP r o) s1) k = region_of s1 k) by reflexivity.
  assert (R1 : region_of s1 r = Some x).
  { subst s1. rewrite region_of_upd, Nat.eqb_refl. replace (Nat.ltb r (length (st_regions s))) with true; [reflexivity|].
    symmetry. apply Nat.ltb_lt. exact Hrlt. }
  assert (R2 : forall k, k <> r -> region_of s1 k = region_of s k).
  { intros k Hk'. subst s1. rewrite region_of_upd. replace (Nat.eqb k r) with false; [reflexivity|].
    symmetry. apply Nat.eqb_neq. exact Hk'. }
  assert (Hfresh : ~ In (SP r o) (st_areas s)).
  { intros Hin. destruct (A2 _ Hin) as (r2 & o2 & rg2 & E2 & _ & _ & Hrg2 & _ & _ & Hkind2).
    injection E2 as <- <-. rewrite Hrg in Hrg2. injection Hrg2 as <-. rewrite Hk in Hkind2.
    pose proof (Hrw o Hkind2). lia. }
  pose proof (eq_refl : PGSZ = 4096) as HP.
  eapply Inv_nonmeta; try exact HI; try reflexivity.
  - intros k rgk Hk' Hkind. rewrite ERG. destruct (Nat.eq_dec k r) as [->|Hne].
    + rewrite Hrg in Hk'. injection Hk' as ->. rewrite Hk in Hkind. discriminate.
    + rewrite R2 by exact Hne. exact Hk'.
  - apply ctx_ok_open; [exact (inv_ctx HI) | exact Hinit | change (st_avail_meta_area_count s1) with (st_avail_meta_area_count s); lia].
  - apply keys_ok_open; [exact (inv_keys HI) | exact Hm0 | exact Hfresh].
  - unfold areas_ok.
    rewrite !st_areas_open, st_area_head_open, st_area_tail_open, st_brk_open, st_shift_open,
            st_area_count_open, st_areas_ptr_open, brk_regions_open, resv_total_open, resv_opened_open, resv_count_open.
    change (st_areas s1) with (st_areas s). change (st_area_head s1) with (st_area_head s).
    change (st_meta_alloc_shift s1) with (st_meta_alloc_shift s). change (st_brk s1) with (st_brk s).
    change (st_avail_meta_area_count s1) with (st_avail_meta_area_count s).
    split.
    { apply NoDup_app_single; [exact A1 | exact Hfresh]. }
    split.
    { intros a Ha. apply in_app_iff in Ha as [Ha | [<- | []]].
      - destruct (A2 a Ha) as (ra & oa & rga & Ea & Hoa & Hloa & Hrga & Hla & Hhia & Hka).
        exists ra, oa. destruct (Nat.eq_dec ra r) as [->|Hne].
        + exists x. rewrite Hrg in Hrga. injection Hrga as ->. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
          split; [rewrite ERG; exact R1|]. unfold x. cbn [rg_live rg_len rg_kind rg_rw].
          split; [exact Hla|]. split; [exact Hhia|]. rewrite Hk in Hka |- *. apply in_app_iff. left. exact Hka.
        + exists rga. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
          split; [rewrite ERG, R2 by exact Hne; exact Hrga|]. split; [exact Hla|]. split; [exact Hhia | exact Hka].
      - exists r, o, x. split; [reflexivity|]. split; [exact Ho|]. split; [exact Hlo|]. split; [rewrite ERG; exact R1|].
        unfold x. cbn [rg_live rg_len rg_kind rg_rw]. split; [exact Hl|]. split; [nia|].
        rewrite Hk. apply in_app_iff. right. left. reflexivity. }
    split.
    { rewrite A3. destruct (st_areas s); reflexivity. }
    split.
    { destruct (st_areas s ++ [SP r o]) as [|a0 l0] eqn:E.
      - exfalso. destruct (st_areas s); discriminate.
      - rewrite <- E, last_app_single. reflexivity. }
    split.
    { intros k rgk Hk'. rewrite ERG in Hk'. destruct (Nat.eq_dec k r) as [->|Hne].
      - rewrite R1 in Hk'. injection Hk' as <-. unfold x. cbn [rg_kind rg_live rg_len]. intros _. eapply A5; eauto.
      - rewrite R2 in Hk' by exact Hne. eapply A5; eauto. }
    split.
    { subst s1. rewrite (resv_total_upd s r x rg Hrg) by (unfold x; cbn [rg_kind rg_len]; rewrite Hk; split; reflexivity).
      destruct (resv_oc_upd s r x rg Hrg ltac:(unfold x; cbn [rg_kind]; rewrite Hk; reflexivity)) as (EC & EO).
      rewrite EC, EO, Hk. unfold x. cbn [rg_rw]. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add.
      destruct A6 as (A6a & A6b & A6c & A6d). split; [exact A6a|]. split; [change (Z.of_nat 1) with 1; rewrite HP in *; lia|].
      split; [exact A6c|].
      intros rq rgq oq Hrq Hkq Hoq1 Hoq2. rewrite ERG in Hrq.
      rewrite st_area_count_open, st_areas_ptr_open.
      change (st_avail_meta_area_count (set_regions (lupd (st_regions s) r x) s)) with (st_avail_meta_area_count s). cbn [padd prid poff].
      destruct (Nat.eq_dec rq r) as [->|Hneq].
      - rewrite R1 in Hrq. injection Hrq as <-. unfold x in *. cbn [rg_kind rg_len rg_rw] in *.
        destruct (A6d r rg oq Hrg Hkq Hoq1 Hoq2) as [Hin|(_ & _ & Hpo)].
        + left. apply in_app_iff. left. exact Hin.
        + rewrite Ep in Hpo. cbn [poff] in Hpo. destruct (Z.eq_dec oq o) as [->|Hne'].
          * left. apply in_app_iff. right. left. reflexivity.
          * right. rewrite HP in *. assert (Q1 := Z.div_mod oq 4096 ltac:(lia)). assert (Q2 := Z.div_mod o 4096 ltac:(lia)).
            assert (Hq : oq / 4096 <> o / 4096) by (intros E; apply Hne'; lia).
            assert (Hge : o + 4096 <= oq).
            { clear - Q1 Q2 Hq Hpo Hoq1 Ho. rewrite Hoq1 in Q1. rewrite Ho in Q2.
              set (qa := oq / 4096) in *. set (qb := o / 4096) in *. clearbody qa qb. lia. }
            change (st_avail_meta_area_count (set_regions (lupd (st_regions s) r (mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [o]) (rg_live rg))) s))
              with (st_avail_meta_area_count s).
            split; [clear - Hge Hlen Hoq2; lia|]. split; [reflexivity|]. lia.
      - rewrite R2 in Hrq by exact Hneq. destruct (A6d rq rgq oq Hrq Hkq Hoq1 Hoq2) as [Hin|(_ & Hpr & _)].
        + left. exact Hin.
        + exfalso. apply Hneq. rewrite Ep in Hpr. cbn [prid] in Hpr. symmetry. exact Hpr. }
    split.
    { assert (EB : brk_regions s1 = brk_regions s).
      { subst s1. eapply brk_regions_upd; [exact Hrg | reflexivity]. }
      rewrite EB. destruct (st_brk s) as [| |rb pb].
      - exact A7.
      - intros rr Hrr. destruct (A7 rr Hrr) as (Hbr & rgb & Hrgb & Hrest). split; [exact Hbr|]. exists rgb. split; [|exact Hrest].
        rewrite ERG, R2; [exact Hrgb|]. intros ->.
        destruct (brk_regions_In s r Hrr) as (rg2 & Hrg2 & Hk2). rewrite Hrg in Hrg2. injection Hrg2 as <-. rewrite Hk in Hk2. discriminate.
      - destruct A7 as (Hbr & rgb & Hrgb & Hrest). split; [exact Hbr|]. exists rgb. split; [|exact Hrest].
        rewrite ERG, R2; [exact Hrgb|]. intros ->.
        destruct (brk_regions_In s r ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2).
        rewrite Hrg in Hrg2. injection Hrg2 as <-. rewrite Hk in Hk2. discriminate. }
    split.
    { intros Hc'. exists r, (o + 4096), x. split; [reflexivity|]. split; [rewrite ERG; exact R1|].
      unfold x. cbn [rg_kind rg_live rg_len rg_rw]. split; [exact Hk|]. split; [exact Hl|].
      split; [rewrite HP in Ho |- *; replace (o + 4096) with (o + 1 * 4096) by lia; rewrite Z_mod_plus_full; exact Ho|].
      split; [lia|]. split; [nia|].
      intros y Hy. apply in_app_iff in Hy as [Hy | [<- | []]]; [pose proof (Hrw y Hy); lia | lia]. }
    split.
    { intros k rgk Hk'. rewrite ERG in Hk'. destruct (Nat.eq_dec k r) as [->|Hne].
      - rewrite R1 in Hk'. injection Hk' as <-. unfold x. cbn [rg_len rg_live]. exact (A9 _ _ Hrg).
      - rewrite R2 in Hk' by exact Hne. eapply A9. exact Hk'. }
    { intros _. exists x. cbn [prid padd]. rewrite ?ERG. exact R1. }
Qed.

(* [comment removed for export] *)
Lemma Inv_open_brk_first X R U s :
  Inv X R U s -> st_brk s = BrkNever -> st_avail_meta_area_count s = 0 -> st_avail_meta_count s = 0 ->
  st_init_done s = true ->
  let r := length (st_regions s) in
  let s1 := set_brk (BrkCur r 2) (set_avail_meta_areas (SP r PGSZ) (set_avail_meta_area_count 1
              (set_regions (st_regions s ++ [mkRegion RkBrk (2 * PGSZ) [] true]) s))) in
  Inv X R U (open_st (SP r PGSZ) s1).
Proof.
  intros HI Hb Hc0 Hm0 Hinit r s1.
  pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9&A10).
  set (x := mkRegion RkBrk (2 * PGSZ) [] true) in *.
  assert (ERG : forall k, region_of (open_st (SP r PGSZ) s1) k = region_of (set_regions (st_regions s ++ [x]) s) k) by reflexivity.
  assert (R1 : region_of (set_regions (st_regions s ++ [x]) s) r = Some x) by (subst r; apply region_of_app_new).
  pose proof (eq_refl : PGSZ = 4096) as HP.
  rewrite Hb in A7.
  assert (Hfresh : ~ In (SP r PGSZ) (st_areas s)).
  { intros Hin. destruct (A2 _ Hin) as (r2 & o2 & rg2 & E2 & _ & _ & Hrg2 & _). injection E2 as <- <-.
    pose proof (region_of_lt _ _ _ Hrg2). lia. }
  eapply Inv_nonmeta; try exact HI; try reflexivity.
  - intros k rgk Hk' _. rewrite ERG. apply region_of_app. exact Hk'.
  - apply ctx_ok_open; [| exact Hinit | change (st_avail_meta_area_count s1) with 1; lia].
    pose proof (inv_ctx HI) as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12). unfold ctx_ok. subst s1. simp_st.
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj _ _))))))))))); [lia|].
    intros Hi. rewrite Hinit in Hi. discriminate.
  - apply keys_ok_open; [| exact Hm0 | exact Hfresh].
    pose proof (inv_keys HI) as K. unfold keys_ok, key_placed, handed in *. subst s1. simp_st. exact K.
  - unfold areas_ok.
    rewrite !st_areas_open, st_area_head_open, st_area_tail_open, st_brk_open, st_shift_open,
            st_area_count_open, st_areas_ptr_open, brk_regions_open, resv_total_open, resv_opened_open, resv_count_open.
    change (st_areas s1) with (st_areas s). change (st_area_head s1) with (st_area_head s).
    change (st_meta_alloc_shift s1) with (st_meta_alloc_shift s). change (st_brk s1) with (BrkCur r 2).
    change (st_avail_meta_area_count s1) with 1.
    split.
    { apply NoDup_app_single; [exact A1 | exact Hfresh]. }
    split.
    { intros a Ha. apply in_app_iff in Ha as [Ha | [<- | []]].
      - destruct (A2 a Ha) as (ra & oa & rga & Ea & Hoa & Hloa & Hrga & Hla & Hhia & Hka).
        exists ra, oa, rga. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
        split; [rewrite ERG; apply region_of_app; exact Hrga|]. split; [exact Hla|]. split; [exact Hhia | exact Hka].
      - exists r, PGSZ, x. split; [reflexivity|]. split; [rewrite HP; reflexivity|]. split; [lia|]. split; [rewrite ERG; exact R1|].
        unfold x. cbn [rg_live rg_len rg_kind rg_rw]. split; [reflexivity|]. split; [lia | exact I]. }
    split.
    { rewrite A3. destruct (st_areas s); reflexivity. }
    split.
    { destruct (st_areas s ++ [SP r PGSZ]) as [|a0 l0] eqn:E.
      - exfalso. destruct (st_areas s); discriminate.
      - rewrite <- E, last_app_single. reflexivity. }
    split.
    { intros k rgk Hk'. rewrite ERG in Hk'. unfold region_of in Hk'. cbn [st_regions set_regions] in Hk'.
      rewrite nth_error_app in Hk'. destruct (Nat.ltb k (length (st_regions s))) eqn:El.
      - eapply A5. exact Hk'.
      - destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk'; [|destruct k'; discriminate].
        injection Hk' as <-. unfold x. cbn [rg_kind]. discriminate. }
    split.
    { change (resv_total s1) with (resv_total (set_regions (st_regions s ++ [x]) s)).
      change (resv_opened s1) with (resv_opened (set_regions (st_regions s ++ [x]) s)).
      change (resv_count s1) with (resv_count (set_regions (st_regions s ++ [x]) s)).
      rewrite resv_total_app, resv_opened_app, resv_count_app. unfold x. cbn [rg_kind]. rewrite !Z.add_0_r.
      destruct A6 as (A6a & A6b & A6c & A6d). rewrite Hc0 in A6b. split; [exact A6a|]. split; [lia|]. split; [exact A6c|].
      intros rq rgq oq Hrq Hkq Hoq1 Hoq2. left. rewrite ERG in Hrq. unfold region_of in Hrq. cbn [st_regions set_regions] in Hrq.
      rewrite nth_error_app in Hrq. destruct (Nat.ltb rq (length (st_regions s))) eqn:El.
      * destruct (A6d rq rgq oq Hrq Hkq Hoq1 Hoq2) as [Hin|(Hc & _)]; [exact Hin | rewrite Hc0 in Hc; lia].
      * destruct (rq - length (st_regions s))%nat as [|k'] eqn:Ek; cbn in Hrq; [|destruct k'; discriminate].
        injection Hrq as <-. cbn [rg_kind] in Hkq. discriminate. }
    split.
    { change (brk_regions s1) with (brk_regions (set_regions (st_regions s ++ [x]) s)).
      rewrite brk_regions_app, A7. unfold x. cbn [rg_kind app]. split; [reflexivity|].
      exists x. split; [rewrite ERG; exact R1|]. unfold x. cbn [rg_live rg_len]. split; [reflexivity|]. split; [lia | lia]. }
    split.
    { intros Hc'. lia. }
    split.
    { intros k rgk Hk'. rewrite ERG in Hk'. unfold region_of in Hk'. cbn [st_regions set_regions] in Hk'. rewrite nth_error_app in Hk'.
      destruct (Nat.ltb k (length (st_regions s))); [eapply A9; exact Hk'|].
      destruct (k - length (st_regions s))%nat as [|k']; cbn in Hk'; [injection Hk' as <-; cbn; split; [lia | intros _; lia] | destruct k'; discriminate]. }
    { intros _. exists x. cbn [prid padd]. rewrite ?ERG. exact R1. }
Qed.

(* [comment removed for export] *)
Lemma Inv_open_brk_grow X R U s r p rg :
  Inv X R U s -> st_brk s = BrkCur r p -> st_avail_meta_area_count s = 0 -> st_avail_meta_count s = 0 ->
  st_init_done s = true -> region_of s r = Some rg ->
  let x := mkRegion RkBrk (rg_len rg + PGSZ) [] true in
  let s1 := set_brk (BrkCur r (p + 1)) (set_avail_meta_areas (SP r (PGSZ * p)) (set_avail_meta_area_count 1
              (set_regions (lupd (st_regions s) r x) s))) in
  Inv X R U (open_st (SP r (PGSZ * p)) s1).
Proof.
  intros HI Hb Hc0 Hm0 Hinit Hrg x s1.
  pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9&A10).
  rewrite Hb in A7. destruct A7 as (Hbr & rg0 & Hrg0 & Hl0 & Hlen0 & Hp2).
  rewrite Hrg in Hrg0. injection Hrg0 as <-.
  pose proof (region_of_lt _ _ _ Hrg) as Hrlt.
  assert (ERG : forall k, region_of (open_st (SP r (PGSZ * p)) s1) k = region_of (set_regions (lupd (st_regions s) r x) s) k) by reflexivity.
  assert (R1 : region_of (set_regions (lupd (st_regions s) r x) s) r = Some x).
  { rewrite region_of_upd, Nat.eqb_refl. replace (Nat.ltb r (length (st_regions s))) with true; [reflexivity|].
    symmetry. apply Nat.ltb_lt. exact Hrlt. }
  assert (R2 : forall k, k <> r -> region_of (set_regions (lupd (st_regions s) r x) s) k = region_of s k).
  { intros k Hk'. rewrite region_of_upd. replace (Nat.eqb k r) with false; [reflexivity|]. symmetry. apply Nat.eqb_neq. exact Hk'. }
  pose proof (eq_refl : PGSZ = 4096) as HP.
  assert (Hkind : rg_kind rg = RkBrk).
  { destruct (brk_regions_In s r ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2). rewrite Hrg in Hrg2. injection Hrg2 as <-. exact Hk2. }
  assert (Hfresh : ~ In (SP r (PGSZ * p)) (st_areas s)).
  { intros Hin. destruct (A2 _ Hin) as (r2 & o2 & rg2 & E2 & _ & _ & Hrg2 & _ & Hhi2 & _).
    pose proof (f_equal prid E2) as Er2. pose proof (f_equal poff E2) as Eo2. cbn [prid poff] in Er2, Eo2. subst r2 o2.
    rewrite Hrg in Hrg2. injection Hrg2 as <-. rewrite Hlen0 in Hhi2. nia. }
  eapply Inv_nonmeta; try exact HI; try reflexivity.
  - intros k rgk Hk' Hkk. rewrite ERG. destruct (Nat.eq_dec k r) as [->|Hne].
    + rewrite Hrg in Hk'. injection Hk' as ->. rewrite Hkind in Hkk. discriminate.
    + rewrite R2 by exact Hne. exact Hk'.
  - apply ctx_ok_open; [| exact Hinit | change (st_avail_meta_area_count s1) with 1; lia].
    pose proof (inv_ctx HI) as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12). unfold ctx_ok. subst s1. simp_st.
    refine (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 (conj C8 (conj C9 (conj C10 (conj _ _))))))))))); [lia|].
    intros Hi. rewrite Hinit in Hi. discriminate.
  - apply keys_ok_open; [| exact Hm0 | exact Hfresh].
    pose proof (inv_keys HI) as K. unfold keys_ok, key_placed, handed in *. subst s1. simp_st. exact K.
  - unfold areas_ok.
    rewrite !st_areas_open, st_area_head_open, st_area_tail_open, st_brk_open, st_shift_open,
            st_area_count_open, st_areas_ptr_open, brk_regions_open, resv_total_open, resv_opened_open, resv_count_open.
    change (st_areas s1) with (st_areas s). change (st_area_head s1) with (st_area_head s).
    change (st_meta_alloc_shift s1) with (st_meta_alloc_shift s). change (st_brk s1) with (BrkCur r (p + 1)).
    change (st_avail_meta_area_count s1) with 1.
    split.
    { apply NoDup_app_single; [exact A1 | exact Hfresh]. }
    split.
    { intros a Ha. apply in_app_iff in Ha as [Ha | [<- | []]].
      - destruct (A2 a Ha) as (ra & oa & rga & Ea & Hoa & Hloa & Hrga & Hla & Hhia & Hka).
        exists ra, oa. destruct (Nat.eq_dec ra r) as [->|Hne].
        + exists x. rewrite Hrg in Hrga. injection Hrga as ->. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
          split; [rewrite ERG; exact R1|]. unfold x. cbn [rg_live rg_len rg_kind rg_rw].
          split; [reflexivity|]. split; [lia | exact I].
        + exists rga. split; [exact Ea|]. split; [exact Hoa|]. split; [exact Hloa|].
          split; [rewrite ERG, R2 by exact Hne; exact Hrga|]. split; [exact Hla|]. split; [exact Hhia | exact Hka].
      - exists r, (PGSZ * p), x. split; [reflexivity|]. split; [rewrite HP, Z.mul_comm; apply Z_mod_mult|]. split; [nia|].
        split; [rewrite ERG; exact R1|].
        unfold x. cbn [rg_live rg_len rg_kind rg_rw]. split; [reflexivity|]. split; [lia | exact I]. }
    split.
    { rewrite A3. destruct (st_areas s); reflexivity. }
    split.
    { destruct (st_areas s ++ [SP r (PGSZ * p)]) as [|a0 l0] eqn:E.
      - exfalso. destruct (st_areas s); discriminate.
      - rewrite <- E, last_app_single. reflexivity. }
    split.
    { intros k rgk Hk'. rewrite ERG in Hk'. destruct (Nat.eq_dec k r) as [->|Hne].
      - rewrite R1 in Hk'. injection Hk' as <-. unfold x. cbn [rg_kind]. discriminate.
      - rewrite R2 in Hk' by exact Hne. eapply A5. exact Hk'. }
    split.
    { change (resv_total s1) with (resv_total (set_regions (lupd (st_regions s) r x) s)).
      change (resv_opened s1) with (resv_opened (set_regions (lupd (st_regions s) r x) s)).
      change (resv_count s1) with (resv_count (set_regions (lupd (st_regions s) r x) s)).
      rewrite (resv_total_upd s r x rg Hrg) by (rewrite Hkind; unfold x; cbn [rg_kind]; discriminate).
      destruct (resv_oc_upd s r x rg Hrg ltac:(rewrite Hkind; unfold x; cbn [rg_kind]; discriminate)) as (EC & EO).
      rewrite EC, EO, Hkind. rewrite Z.add_0_r.
      destruct A6 as (A6a & A6b & A6c & A6d). rewrite Hc0 in A6b. split; [exact A6a|]. split; [lia|]. split; [exact A6c|].
      intros rq rgq oq Hrq Hkq Hoq1 Hoq2. left. rewrite ERG in Hrq. destruct (Nat.eq_dec rq r) as [->|Hne].
      * rewrite R1 in Hrq. injection Hrq as <-. unfold x in Hkq. cbn [rg_kind] in Hkq. discriminate.
      * rewrite R2 in Hrq by exact Hne.
        destruct (A6d rq rgq oq Hrq Hkq Hoq1 Hoq2) as [Hin|(Hc & _)]; [exact Hin | rewrite Hc0 in Hc; lia]. }
    split.
    { change (brk_regions s1) with (brk_regions (set_regions (lupd (st_regions s) r x) s)).
      rewrite (brk_regions_upd s r x rg Hrg) by (rewrite Hkind; reflexivity). split; [exact Hbr|].
      exists x. split; [rewrite ERG; exact R1|]. unfold x. cbn [rg_live rg_len]. split; [reflexivity|]. split; [lia | lia]. }
    split.
    { intros Hc'. lia. }
    split.
    { intros k rgk Hk'. rewrite ERG in Hk'. destruct (Nat.eq_dec k r) as [->|Hne].
      - rewrite R1 in Hk'. injection Hk' as <-. unfold x. cbn [rg_len rg_live]. pose proof (A9 _ _ Hrg) as [? ?]. unfold PGSZ in *. split; [lia | intros _; lia].
      - rewrite R2 in Hk' by exact Hne. eapply A9. exact Hk'. }
    { intros _. exists x. cbn [prid padd]. rewrite ?ERG. exact R1. }
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition am_frame (s s' : astate) : Prop :=
  st_active s' = st_active s /\ st_usage s' = st_usage s /\
  (forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> region_of s' k = Some rg) /\
  (length (st_regions s) <= length (st_regions s'))%nat /\
  st_mmap_counter s' = st_mmap_counter s.

Lemma am_frame_refl s : am_frame s s.
Proof. repeat split; auto. Qed.

Lemma am_frame_trans s1 s2 s3 : am_frame s1 s2 -> am_frame s2 s3 -> am_frame s1 s3.
Proof.
  intros (A1&A2&A5&A6&A7) (B1&B2&B5&B6&B7). repeat split; try congruence.
  - intros k rg Hk Hkd. apply B5; [apply A5; assumption | exact Hkd].
  - lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_of_set_brk b s k : region_of (set_brk b s) k = region_of s k. Proof. reflexivity. Qed.
Lemma region_of_set_ama p s k : region_of (set_avail_meta_areas p s) k = region_of s k. Proof. reflexivity. Qed.
Lemma region_of_set_amac c s k : region_of (set_avail_meta_area_count c s) k = region_of s k. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma open_area_resv_spec X R U s (Q : bool * astate -> Prop) :
  Inv X R U s -> 0 < st_avail_meta_area_count s -> st_avail_meta_count s = 0 -> st_init_done s = true ->
  (forall (ok : bool) s', Inv X R U s' -> am_frame s s' -> st_metas s' = st_metas s -> st_init_done s' = true ->
     (ok = true -> 0 < st_avail_meta_count s') -> Q (ok, s')) ->
  itok (open_area true s) Q.
Proof.
  intros HI Hc Hm0 Hinit HQ.
  pose proof (inv_areas HI) as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10).
  destruct (E8 Hc) as (r & o & rg & Ep & Hrg & Hk & Hl & Ho & Hlo & Hlen & Hrw).
  pose proof (eq_refl : PGSZ = 4096) as HP.
  unfold open_area. mbinds. apply itok_get. msimp. mbinds. apply itok_ask.
  { cbn. split; [exact Hc|]. split; [reflexivity|]. exists rg. rewrite Ep. cbn.
    repeat (split; [assumption|]). split; [lia|]. intros Hin. pose proof (Hrw o Hin). lia. }
  intros z _. msimp. destruct (z =? 0) eqn:Ez; cbn [negb].
  - apply itok_ret. apply HQ; auto; [apply am_frame_refl | intros; discriminate].
  - mbinds. unfold upd_region. apply itok_modify. msimp. mbinds. apply itok_modify. msimp. apply itok_ret.
    rewrite Ep. cbn [prid poff]. unfold region_of in Hrg. rewrite !(nth_error_nth _ _ _ Hrg).
    match goal with |- Q (true, ?st) =>
      change st with (open_st (SP r o) (set_regions (lupd (st_regions s) r (mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [o]) (rg_live rg))) s)) end.
    apply HQ.
    + apply Inv_open_resv; auto.
    + repeat split; try reflexivity; try tauto.
      * intros k rgk Hk' Hkk. rewrite region_of_open, region_of_upd.
        destruct (Nat.eqb k r && Nat.ltb r (length (st_regions s)))%bool eqn:E; [|exact Hk'].
        apply andb_prop in E as [E _]. apply Nat.eqb_eq in E. subst k. unfold region_of in Hk'. rewrite Hrg in Hk'. injection Hk' as ->.
        rewrite Hk in Hkk. discriminate.
      * rewrite st_regions_open. cbn. rewrite length_lupd. lia.
    + reflexivity.
    + exact Hinit.
    + intros _. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma resv_then_open_spec X R U s (Q : bool * astate -> Prop) :
  Inv X R U s -> st_avail_meta_count s = 0 -> st_init_done s = true ->
  (forall (ok : bool) s', Inv X R U s' -> am_frame s s' -> st_metas s' = st_metas s -> st_init_done s' = true ->
     (ok = true -> 0 < st_avail_meta_count s') -> Q (ok, s')) ->
  itok ((rs <- area_from_mmap ;; if rs then open_area true else ret false) s) Q.
Proof.
  intros HI Hm0 Hinit HQ.
  pose proof (inv_ctx HI) as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
  unfold area_from_mmap. mbinds. apply itok_get. msimp.
  destruct (st_avail_meta_area_count s =? 0) eqn:Ec.
  - apply Z.eqb_eq in Ec. mbinds. apply itok_ask.
    { cbn. pose proof (inv_areas HI) as (_&_&_&_&_&A6&_). split; [reflexivity|]. split; [exact Ec|]. split; [exact C10|].
      destruct A6 as (A6a & A6b & A6c & A6d). split; [exact A6a|]. rewrite Ec, Z.add_0_r in A6b. split; [symmetry; exact A6b|].
      split; [exact A6c|].
      intros rq rgq oq Hrq Hkq Hoq1 Hoq2. destruct (A6d rq rgq oq Hrq Hkq Hoq1 Hoq2) as [Hin|(Hc & _)]; [exact Hin | rewrite Ec in Hc; lia]. }
    intros z _. msimp. destruct (z =? 0) eqn:Ez; cbn [negb].
    + mbinds. apply itok_ret. msimp. apply itok_ret. apply HQ; auto; [apply am_frame_refl | intros; discriminate].
    + unfold new_region. mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. mbinds. apply itok_ret. msimp.
      mbinds. apply itok_modify. msimp. mbinds. apply itok_ret. msimp.
      match goal with |- itok (open_area true ?st) _ => set (s2 := st) end.
      assert (HI2 : Inv X R U s2) by exact (Inv_new_resv X R U s HI Ec Hinit).
      assert (Fr2 : am_frame s s2).
      { subst s2. repeat split; try reflexivity; try tauto.
        - intros k rg Hk _. cbn [set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas]. apply region_of_app. exact Hk.
        - cbn. rewrite length_app. cbn. lia. }
      assert (Hc2 : 0 < st_avail_meta_area_count s2).
      { subst s2. cbn -[Z.lt Z.sub Z.shiftl]. rewrite Z.shiftl_mul_pow2 by lia.
        pose proof (Z.pow_pos_nonneg 2 (st_meta_alloc_shift s)). lia. }
      eapply open_area_resv_spec; [exact HI2 | exact Hc2 | subst s2; exact Hm0 | subst s2; exact Hinit |].
      intros ok s' HI' Fr' Em' Hi' Hok.
      apply HQ; [exact HI' | eapply am_frame_trans; [exact Fr2 | exact Fr'] | rewrite Em'; subst s2; reflexivity | exact Hi' | exact Hok].
  - apply Z.eqb_neq in Ec. mbinds. apply itok_ret. msimp.
    eapply open_area_resv_spec; [exact HI | lia | exact Hm0 | exact Hinit | exact HQ].
Qed.

(* [comment removed for export] *)
Lemma new_area_spec X R U s (Q : bool * astate -> Prop) :
  Inv X R U s -> st_avail_meta_count s = 0 -> st_init_done s = true ->
  (forall (ok : bool) s', Inv X R U s' -> am_frame s s' -> st_metas s' = st_metas s -> st_init_done s' = true ->
     (ok = true -> 0 < st_avail_meta_count s') -> Q (ok, s')) ->
  itok ((nu <- area_from_brk ;; rs <- area_from_mmap ;; if rs then open_area nu else ret false) s) Q.
Proof.
  intros HI Hm0 Hinit HQ.
  pose proof (inv_areas HI) as (A1&A2&A3&A4&A5&A6&A7&A8&A9&A10).
  pose proof (inv_ctx HI) as (C1&C2&C3&C4&C5&C6&C7&C8&C9&C10&C11&C12).
  pose proof (eq_refl : PGSZ = 4096) as HP.
  unfold area_from_brk. mbinds. apply itok_get. msimp.
  destruct ((st_avail_meta_area_count s =? 0) && match st_brk s with BrkDead => false | _ => true end) eqn:Econd.
  2:{ (* [comment removed for export] *)
      mbinds. apply itok_ret. msimp. eapply resv_then_open_spec; eauto. }
  apply andb_prop in Econd as [Ec Eb]. apply Z.eqb_eq in Ec.
  destruct (st_brk s) as [| |rb pb] eqn:Ebrk; [ | discriminate | ].
  - (* [comment removed for export] *)
    mbinds. apply itok_ask. { cbn. rewrite Ebrk. auto. }
    intros z1 _. msimp. mbinds. apply itok_ask.
    { cbn. left. rewrite Ebrk. auto. }
    intros z2 _. msimp. destruct (z2 =? 0) eqn:Ez2; cbn [negb].
    + (* [comment removed for export] *)
      mbinds. apply itok_modify. msimp. mbinds. apply itok_ret. msimp.
      assert (HI1 : Inv X R U (set_brk BrkDead s)) by (apply Inv_brk_dead; [exact HI | rewrite Ebrk; discriminate | exact Hinit]).
      eapply resv_then_open_spec; [exact HI1 | exact Hm0 | exact Hinit |].
      intros ok s' HI' Fr' Em' Hi' Hok.
      apply HQ; [exact HI' | | rewrite Em'; reflexivity | exact Hi' | exact Hok].
      eapply am_frame_trans; [| exact Fr']. repeat split; try reflexivity; try tauto; try (intros k rg Hk _; exact Hk).
    + (* [comment removed for export] *)
      unfold new_region. mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. mbinds. apply itok_ret. msimp.
      mbinds. apply itok_modify. msimp. mbinds. apply itok_ask.
      { cbn. eexists (length (st_regions s)), _. split; [reflexivity|]. split; [rewrite length_app; cbn; lia|].
        split; [apply region_of_app_new|]. cbn. split; [reflexivity|]. split; [reflexivity|].
        apply Forall_forall. intros a Ha. destruct (A2 a Ha) as (r0 & o0 & rg0 & -> & _ & _ & Hrg0 & _). cbn.
        pose proof (region_of_lt _ _ _ Hrg0). lia. }
      intros z3 _. msimp. mbinds. apply itok_ret. msimp.
      (* [comment removed for export] *)
      unfold area_from_mmap. mbinds. apply itok_get. msimp. cbn [Z.eqb st_avail_meta_area_count set_brk set_avail_meta_areas set_avail_meta_area_count set_regions].
      mbinds. apply itok_ret. msimp.
      unfold open_area. mbinds. apply itok_get. msimp. mbinds. apply itok_ret. msimp. cbn [negb].
      mbinds. apply itok_ret. msimp. mbinds. apply itok_modify. msimp. apply itok_ret.
      match goal with |- Q (true, ?st) =>
        change st with (open_st (SP (length (st_regions s)) PGSZ)
          (set_brk (BrkCur (length (st_regions s)) 2) (set_avail_meta_areas (SP (length (st_regions s)) PGSZ)
            (set_avail_meta_area_count 1 (set_regions (st_regions s ++ [mkRegion RkBrk (2 * PGSZ) [] true]) s))))) end.
      apply HQ.
      * apply Inv_open_brk_first; auto.
      * repeat split; try reflexivity; try tauto.
        -- intros k rg Hk _. rewrite region_of_open, region_of_set_brk, region_of_set_ama, region_of_set_amac.
           apply region_of_app. exact Hk.
        -- rewrite st_regions_open. cbn. rewrite length_app. cbn. lia.
      * reflexivity.
      * exact Hinit.
      * intros _. cbn. reflexivity.
  - (* [comment removed for export] *)
    destruct A7 as (Hbr & rg & Hrg & Hl & Hlen & Hp2).
    mbinds. apply itok_ask.
    { cbn. right. split; [reflexivity|]. exists rb, pb, rg. rewrite Ebrk.
      destruct (brk_regions_In s rb ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2).
      rewrite Hrg in Hrg2. injection Hrg2 as <-. auto 6. }
    intros z2 _. msimp. destruct (z2 =? 0) eqn:Ez2; cbn [negb].
    + mbinds. apply itok_modify. msimp. mbinds. apply itok_ret. msimp.
      assert (HI1 : Inv X R U (set_brk BrkDead s)) by (apply Inv_brk_dead; [exact HI | rewrite Ebrk; discriminate | exact Hinit]).
      eapply resv_then_open_spec; [exact HI1 | exact Hm0 | exact Hinit |].
      intros ok s' HI' Fr' Em' Hi' Hok.
      apply HQ; [exact HI' | | rewrite Em'; reflexivity | exact Hi' | exact Hok].
      eapply am_frame_trans; [| exact Fr']. repeat split; try reflexivity; try tauto; try (intros k rg' Hk _; exact Hk).
    + unfold upd_region. mbinds. apply itok_modify. msimp. mbinds. apply itok_modify. msimp. mbinds. apply itok_ret. msimp.
      unfold region_of in Hrg. rewrite !(nth_error_nth _ _ _ Hrg).
      unfold area_from_mmap. mbinds. apply itok_get. msimp. cbn [Z.eqb st_avail_meta_area_count set_brk set_avail_meta_areas set_avail_meta_area_count set_regions].
      mbinds. apply itok_ret. msimp.
      unfold open_area. mbinds. apply itok_get. msimp. mbinds. apply itok_ret. msimp. cbn [negb].
      mbinds. apply itok_ret. msimp. mbinds. apply itok_modify. msimp. apply itok_ret.
      match goal with |- Q (true, ?st) =>
        change st with (open_st (SP rb (PGSZ * pb))
          (set_brk (BrkCur rb (pb + 1)) (set_avail_meta_areas (SP rb (PGSZ * pb))
            (set_avail_meta_area_count 1 (set_regions (lupd (st_regions s) rb (mkRegion RkBrk (rg_len rg + PGSZ) [] true)) s))))) end.
      apply HQ.
      * apply (Inv_open_brk_grow X R U s rb pb rg); auto.
      * repeat split; try reflexivity; try tauto.
        -- intros k rgk Hk Hkk. rewrite region_of_open, region_of_set_brk, region_of_set_ama, region_of_set_amac.
           rewrite region_of_upd. destruct (Nat.eqb k rb && Nat.ltb rb (length (st_regions s)))%bool eqn:E; [|exact Hk].
           apply andb_prop in E as [E _]. apply Nat.eqb_eq in E. subst k.
           exfalso. destruct (brk_regions_In s rb ltac:(rewrite Hbr; left; reflexivity)) as (rg2 & Hrg2 & Hk2).
           rewrite Hk in Hrg2. injection Hrg2 as ->. rewrite Hk2 in Hkk. discriminate.
        -- rewrite st_regions_open. cbn. rewrite length_lupd. lia.
      * reflexivity.
      * exact Hinit.
      * intros _. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma alloc_meta_spec X R U s (Q : option sptr * astate -> Prop) :
  Inv X R U s ->
  (forall s', Inv X R U s' -> am_frame s s' ->
     (forall g am, usedX X s' g am <-> usedX X s g am) -> ub_same s s' -> Q (None, s')) ->
  (forall m s', Inv (m :: X) R U s' -> memb m X = false -> In m (keys s') ->
     (MT s' m = Some MRaw \/ MT s' m = Some (MFree None None)) ->
     am_frame s s' ->
     (forall g am, usedX (m :: X) s' g am <-> usedX X s g am) -> ub_same s s' -> Q (Some m, s')) ->
  itok (alloc_meta s) Q.
Proof.
  intros HI HQn HQs.
  unfold alloc_meta. mbinds. apply itok_modify. msimp.
  set (s0 := set_init_done true s).
  assert (HI0 : Inv X R U s0) by (apply Inv_set_init_done; exact HI).
  assert (Fr0 : am_frame s s0) by (repeat split; try reflexivity; intros k rg Hk _; exact Hk).
  assert (Hinit0 : st_init_done s0 = true) by reflexivity.
  mbinds. eapply dequeue_head_free_spec; [exact HI0 | |].
  - (* [comment removed for export] *)
    intros Hfh Hnofree. msimp. mbinds. apply itok_get. msimp.
    (* [comment removed for export] *)
    assert (TAKE : forall s1, Inv X R U s1 -> am_frame s s1 -> st_metas s1 = st_metas s -> 0 < st_avail_meta_count s1 ->
              itok ((s2 <- get ;;
                     put (set_avail_meta (padd (st_avail_meta s2) META_SIZE) (set_avail_meta_count (st_avail_meta_count s2 - 1) s2)) ;;
                     setslot (st_avail_meta s2) MRaw ;; ret (Some (st_avail_meta s2))) s1) Q).
    { intros s1 HI1 Fr1 Em1 Hc1.
      mbinds. apply itok_get. msimp. mbinds. apply itok_put. msimp. mbinds. apply itok_setslot'. msimp. apply itok_ret.
      destruct (take_slot_Inv X R U s1 HI1 Hc1) as (Hfresh & NX & HI2 & EU2).
      apply HQs.
      + exact HI2.
      + exact NX.
      + rewrite keys_upd_notIn by exact Hfresh. apply in_app_iff. right. left. reflexivity.
      + left. apply MT_upd_same.
      + eapply am_frame_trans; [exact Fr1|]. repeat split; try reflexivity. intros k rg Hk _. exact Hk.
      + intros g am. rewrite EU2. unfold usedX, MTX, MT. rewrite Em1. reflexivity.
      + eapply ub_same_trans; [| apply ub_same_upd_notIn; [exact Hfresh | reflexivity]]. apply ub_same_metas. exact Em1. }
    destruct (0 <? st_avail_meta_count s0) eqn:Ec.
    + apply Z.ltb_lt in Ec. mbinds. apply itok_ret. msimp. cbn [negb].
      apply TAKE; [exact HI0 | exact Fr0 | reflexivity | exact Ec].
    + apply Z.ltb_ge in Ec. pose proof (inv_keys HI0) as (_ & _ & _ & _ & Krange).
      assert (Hm0 : st_avail_meta_count s0 = 0) by lia.
      apply itok_bind.
      eapply new_area_spec; [exact HI0 | exact Hm0 | exact Hinit0 |].
      intros ok s1 HI1 Fr1 Em1 Hi1 Hok. msimp. destruct ok; cbn [negb].
      * apply TAKE; [exact HI1 | eapply am_frame_trans; [exact Fr0 | exact Fr1] | rewrite Em1; reflexivity | apply Hok; reflexivity].
      * apply itok_ret. apply HQn; [exact HI1 | eapply am_frame_trans; [exact Fr0 | exact Fr1] | |].
        -- intros g am. unfold usedX, MTX, MT. rewrite Em1. reflexivity.
        -- apply ub_same_metas. rewrite Em1. reflexivity.
  - (* [comment removed for export] *)
    intros m s' HI' NX Mm Sb Ea EU UB. msimp. apply itok_ret. apply HQs.
    + exact HI'.
    + exact NX.
    + eapply MT_Some_In_keys. exact Mm.
    + right. exact Mm.
    + eapply am_frame_trans; [exact Fr0|].
      destruct Sb as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11&E12&E13&E14&E15&E16&E17).
      repeat split; try assumption.
      * intros k rg Hk _. unfold region_of in *. rewrite E15. exact Hk.
      * rewrite E15. lia.
    + intros g am. rewrite EU. reflexivity.
    + eapply ub_same_trans; [apply ub_same_metas; reflexivity | exact UB].
Qed.
