(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1 AsanWf2 AsanWf3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section WF.
Variable E : aenv.
Variable P : list Z.
Variable D : list batch.
Local Notation SB := (ae_space_beg E).
Local Notation AWF := (AWf E P D).

Lemma cache_pop_spec_ne : forall s0 c,
  1 <= c <= kLargestClassID -> AWF s0 -> get_cache s0 c <> [] ->
  hoare (fun s => s = s0) (cache_pop E c)
    (fun s' r => AWF s' /\ pframe s0 s'
                 /\ (forall c' a, carved E s0 c' a -> carved E s' c' a)
                 /\ (forall c', c' <> c -> get_cache s' c' = get_cache s0 c')
                 /\ match r with
                    | None => True
                    | Some a => as_cache_inited s' = true /\ avail E D s' c a
                                /\ exists x, a = chunk_of_compact SB c x /\ (16 * x) mod class_size c = 0
                    end).
Proof.
  intros s0 c Hc WF NE0. unfold cache_pop. apply hoare_get_bind. intros s ->.
  eapply hoare_bind with (Q := fun s1 ok => s1 = s0 /\ ok = true).
  { destruct (get_cache s0 c) as [|y l] eqn:HC0; [exfalso; exact (NE0 eq_refl)|].
    apply hoare_ret. intros s1 ->. split; reflexivity. }
  intros ok. apply hoare_pre. intros s1 [-> ->]. cbn [negb].
  assert (HI1 : as_cache_inited s0 = true).
  { destruct (as_cache_inited s0) eqn:HI; [reflexivity|]. exfalso.
    destruct WF as (_ & _ & (_ & C2 & _) & _). destruct (C2 HI) as [CE _].
    apply NE0. unfold get_cache. rewrite CE, lookup_empty. reflexivity. }
  apply hoare_get_bind. intros s2 ->.
  destruct (get_cache s0 c) as [|y l'] eqn:HC1; [exfalso; exact (NE0 eq_refl)|].
  set (l := y :: l') in *.
  apply hoare_upd_bind. apply hoare_ret. intros s' (s2 & -> & ->).
  set (x := List.last l 0). set (s' := upd_cache_allocated _ (upd_cache_stale _ (set_cache c (removelast l) s0))).
  assert (LNE : l <> []) by (subst l; discriminate).
  pose proof (app_removelast_last 0 LNE) as SPLIT. fold x in SPLIT. rewrite <- removelast_eq in SPLIT.
  assert (INx : In x l) by (rewrite SPLIT; apply in_app_iff; right; left; reflexivity).
  assert (INrl : forall z, In z (removelast l) -> In z l) by (intros z Hz; rewrite SPLIT; apply in_app_iff; left; exact Hz).
  assert (GCe : get_cache s' c = removelast l) by (subst s'; rewrite get_cache_upd_cache_allocated, get_cache_upd_cache_stale, get_set_cache_eq; reflexivity).
  assert (GCo : forall c', c' <> c -> get_cache s' c' = get_cache s0 c').
  { intros c' NE; subst s'. rewrite get_cache_upd_cache_allocated, get_cache_upd_cache_stale, get_set_cache_ne by auto. reflexivity. }
  assert (RG : as_regions s' = as_regions s0) by (subst s'; reflexivity).
  assert (GR : forall c', get_region s' c' = get_region s0 c') by (intros; unfold get_region; rewrite RG; reflexivity).
  assert (PF : pframe s0 s') by (subst s'; unfold pframe; repeat split; reflexivity).
  assert (CARV : forall c' a, carved E s0 c' a <-> carved E s' c' a) by (intros; unfold carved, region_of; rewrite GR; tauto).
  pose proof WF as X. destruct X as (WE1 & WR1 & (C1 & C2 & C3) & _).
  destruct (C3 c Hc) as (X1 & X2 & X3).
  rewrite HC1 in X1, X2, X3.
  assert (NDl : List.NoDup l) by exact X2.
  assert (NIx : ~ In x (removelast l)).
  { rewrite SPLIT in NDl. pose proof (NoDup_remove_2 _ [] _ NDl) as R. rewrite app_nil_r in R. exact R. }
  assert (WF' : AWF s').
  { eapply AWf_frame_prim; [exact PF| intros c' a H; apply CARV; exact H| | | | | exact WF].
    - intros c' a _ _ H. left. unfold in_free, region_of in *. rewrite GR in H. exact H.
    - intros c' a _ _ H. left. unfold in_cache in *. destruct (Z.eq_dec c' c) as [->|NE].
      + rewrite GCe in H. rewrite HC1. apply INrl. exact H.
      + rewrite GCo in H by auto. exact H.
    - eapply wf_regions_same; [exact RG| exact WR1].
    - unfold wf_cache. replace (as_cache_inited s') with true by (subst s'; cbn; symmetry; exact HI1).
      split; [| split; [discriminate|]].
      + subst s'. cbn. intros c0 l0 Hl. destruct (Z.eq_dec c0 c) as [->|NE]; [lia|]. rewrite lookup_insert_ne in Hl by auto. eapply C1; exact Hl.
      + intros c0 Hc0. unfold region_of. rewrite GR. destruct (Z.eq_dec c0 c) as [->|NE].
        * rewrite GCe. split.
          { unfold zlen in *. rewrite SPLIT in X1. rewrite length_app in X1. replace (length [x]) with 1%nat in X1 by reflexivity. clear -X1. lia. }
          split; [rewrite SPLIT in NDl; exact (NoDup_app_remove_r _ _ NDl)|].
          intros z Hz. destruct (X3 z (INrl z Hz)) as (Y1 & Y2 & Y3). split; [apply CARV; exact Y1|]. split; [exact Y2| exact Y3].
        * rewrite GCo by auto. destruct (C3 c0 Hc0) as (Z1 & Z2 & Z3). split; [exact Z1|]. split; [exact Z2|].
          intros z Hz. destruct (Z3 z Hz) as (Y1 & Y2 & Y3). split; [apply CARV; exact Y1|]. split; [exact Y2| exact Y3]. }
  split; [exact WF'|]. split; [exact PF|].
  split; [intros c' a H; apply CARV; exact H|].
  split; [intros c' NE; rewrite GCo by auto; reflexivity|].
  split; [subst s'; cbn; exact HI1|].
  destruct (X3 x INx) as (Cx & Mx & Fx).
  split.
  - split; [apply CARV; exact Cx|]. split.
    + unfold in_free, region_of. rewrite compact_chunk_id, GR. exact Fx.
    + split; [unfold in_cache; rewrite compact_chunk_id, GCe; exact NIx|].
      eapply (untracked_pframe D); [exact PF|].
      pose proof (cache_entry_untracked E P D s0 c x WF Hc ltac:(rewrite HC1; exact INx)) as [_ U]. exact U.
  - exists x. split; [reflexivity| exact Mx].
Qed.

End WF.
End RC__1.
