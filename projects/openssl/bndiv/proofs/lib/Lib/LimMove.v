(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import BudgetPremise.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import LimBase LimMm LimMmap LimMremap LimCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

(* [comment removed for export] *)
Definition vm_fit (h : VmMaps) : Prop :=
  forall (a sz : word), In (a, sz) (vm_maps h) -> (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z.

Lemma filter_length_le {A} (f : A -> bool) (l : list A) : (length (List.filter f l) <= length l)%nat.
Proof. induction l as [|x l IH]; cbn [List.filter length]; [lia | destruct (f x); cbn [length]; lia]. Qed.

Lemma maps_subtract_within_none : forall X lo hi,
  (forall (b s : word), In (b, s) X -> (lo <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= hi)%Z) ->
  maps_subtract X lo hi = [].
Proof.
  induction X as [|[b s] X IH]; intros lo hi H; [reflexivity|].
  cbn [maps_subtract]. destruct (H b s (or_introl eq_refl)) as [H1 H2].
  unfold iv_subtract. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _) H1). rewrite (proj2 (Z.ltb_ge _ _) H2). cbn [app].
  apply IH. intros b' s' Hin. apply H. right. exact Hin.
Qed.

Theorem move_charge_le : forall m old old_n dst new_n,
  vm_fit (m_vmmaps m) ->
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned new_n mod page_size = 0)%Z ->
  (0 < bv_unsigned new_n)%Z ->
  (bv_unsigned dst + bv_unsigned new_n < two_pow_64)%Z ->
  region_free (map_remove (vm_maps (m_vmmaps m)) old) dst new_n = true ->
  (vm_backing_used (mremap_model_next m old old_n dst new_n) <= mremap_move_charge m old old_n new_n)%Z.
Proof.
  intros m old old_n dst new_n Hfit Halign Hnalign Hpos Hend Hmaps.
  assert (P1 : forall L P m', m_vmmaps (with_vm_backing L P m') = m_vmmaps m') by reflexivity.
  assert (P2 : forall L P m', m_vm_lazy (with_vm_backing L P m') = L) by reflexivity.
  assert (P3 : forall L P m', m_vm_materialized (with_vm_backing L P m') = P) by reflexivity.
  assert (P4 : forall h m', m_vmmaps (with_vmmaps h m') = h) by reflexivity.
  assert (P5 : forall h m', m_vm_lazy (with_vmmaps h m') = m_vm_lazy m') by reflexivity.
  assert (P6 : forall h m', m_vm_materialized (with_vmmaps h m') = m_vm_materialized m') by reflexivity.
  unfold vm_backing_used, mremap_move_charge, mremap_model_next, vm_resize_backing, mremap_maps_next.
  cbv zeta.
  rewrite !P1, !P2, !P3, !P4, !P5, !P6.
  unfold vm_backed_maps. cbn [vm_maps vm_noaccess vm_limit].
  set (KL := maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) in *.
  set (KP := List.filter (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) (m_vm_materialized m)) in *.
  set (R0 := map_remove (vm_maps (m_vmmaps m)) old) in *.
  set (NA := vm_noaccess (m_vmmaps m)) in *.
  set (dlo := bv_unsigned dst) in *. set (dhi := (dlo + bv_unsigned new_n)%Z) in *.
  pose proof (mremap_word_range dst) as Hdr. fold dlo in Hdr.
  (* [comment removed for export] *)
  assert (HfitR : forall (a sz : word), In (a, sz) R0 -> (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z).
  { intros a sz Hin. apply Hfit. unfold R0, map_remove in Hin. apply List.filter_In in Hin as [Hin _]. exact Hin. }
  (* [comment removed for export] *)
  assert (HX : forall (b s : word), In (b, s) (maps_subtract_all R0 NA) ->
            (bv_unsigned b + bv_unsigned s <= two_pow_64
             /\ (bv_unsigned b + bv_unsigned s <= dlo \/ dhi <= bv_unsigned b))%Z).
  { intros b s Hin.
    destruct (maps_subtract_all_within NA R0 b s HfitR Hin) as [a [sz [Hin0 Hw]]].
    pose proof (HfitR a sz Hin0) as Hf.
    pose proof (region_free_In R0 dst new_n a sz Hmaps Hin0) as Hov.
    unfold iv_overlap in Hov. apply andb_false_iff in Hov. fold dlo in Hov.
    pose proof (mremap_word_range s).
    split; [lia|].
    destruct Hov as [Hov | Hov]; apply Z.ltb_ge in Hov; unfold dhi; lia. }
  (* [comment removed for export] *)
  assert (HPG : forall MV : list word,
            (length (MV ++ List.filter (page_outside_range dlo dhi) KP) <= length MV + length KP)%nat).
  { intros MV. rewrite length_app. pose proof (filter_length_le (page_outside_range dlo dhi) KP). lia. }
  (* [comment removed for export] *)
  change ((dst, new_n) :: R0) with ([(dst, new_n)] ++ R0).
  rewrite maps_subtract_all_app.
  (* [comment removed for export] *)
  assert (HD : forall (b s : word), In (b, s) (maps_subtract_all [(dst, new_n)] NA) ->
            (dlo <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= dhi)%Z).
  { intros b s Hin.
    destruct (maps_subtract_all_within NA [(dst, new_n)] b s) as [a [sz [Hin0 Hw]]]; [| exact Hin |].
    - intros a sz [Heq|[]]. inversion Heq; subst a sz. fold dlo. lia.
    - destruct Hin0 as [Heq|[]]. inversion Heq; subst a sz. fold dlo in Hw. unfold dhi. lia. }
  destruct (mremap_source_lazy_b m old old_n) eqn:Hsrc.
  - (* [comment removed for export] *)
    rewrite (lazy_interior_aligned dst new_n Halign Hnalign Hpos).
    rewrite maps_subtract_all_app, live_bytes_app.
    cbn [app]. cbn [maps_subtract_all]. fold dlo. fold dhi.
    rewrite (maps_subtract_within_none (maps_subtract_all [(dst, new_n)] NA) dlo dhi HD).
    rewrite maps_subtract_all_nil. cbn [live_bytes].
    rewrite (live_bytes_subtract_free (maps_subtract KL dlo dhi) (maps_subtract_all R0 NA) dlo dhi ltac:(unfold dhi; lia)
               (fun b s Hin => proj2 (HX b s Hin))).
    rewrite (live_bytes_cuts_forget dlo dhi KL (maps_subtract_all R0 NA) ltac:(lia) ltac:(unfold dhi; lia) Hend HX).
    pose proof (HPG (List.map (move_page_base old dst)
       (List.filter (fun p => page_in_half_open (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n) p
                              && (bv_unsigned p - bv_unsigned old <? bv_unsigned new_n)%Z) (m_vm_materialized m)))) as Hpg.
    rewrite length_map in Hpg. unfold page_size. lia.
  - (* [comment removed for export] *)
    rewrite maps_subtract_all_app, live_bytes_app.
    rewrite (live_bytes_cuts_forget dlo dhi KL (maps_subtract_all R0 NA) ltac:(lia) ltac:(unfold dhi; lia) Hend HX).
    pose proof (live_bytes_maps_subtract_all_le (maps_subtract KL dlo dhi) (maps_subtract_all [(dst, new_n)] NA)) as H1.
    pose proof (live_bytes_maps_subtract_all_le NA [(dst, new_n)]) as H2. cbn [live_bytes] in H2.
    pose proof (HPG []) as Hpg. cbn [app length] in Hpg. cbn [app length].
    unfold page_size. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mremap_at_down : forall L i m old old_size new_size flags,
  vm_fit (m_vmmaps m) ->
  (L <= mlim m)%Z ->
  mremap_budget_refused_b old old_size new_size flags (setL L m) = false ->
  lim_at L i m (mremap_spec old old_size new_size flags) (mremap_spec old old_size new_size flags).
Proof.
  intros L i m old old_size new_size flags Hfit HL R2.
  unfold mremap_spec, mremap_budget_refused_b in *. cbv zeta in *.
  revert R2.
  set (old_nZ := page_round_up_Z (bv_unsigned old_size)). set (new_nZ := page_round_up_Z (bv_unsigned new_size)).
  set (old_n := Z_to_bv 64 old_nZ). set (new_n := Z_to_bv 64 new_nZ).
  destruct (negb (bv_unsigned flags =? MREMAP_MAYMOVE)%Z); [intros _; at_auto|].
  destruct (negb (bv_unsigned old mod page_size =? 0)%Z); [intros _; at_auto|].
  destruct (page_align_is0_b new_size) eqn:Hnew; [intros _; at_auto|].
  destruct (page_align_is0_b old_size) eqn:Hold; [intros _; at_auto|].
  intros R2. apply at_get_model. cbv beta zeta.
  change (mremap_source_b (m_vmmaps (setL L m)) old old_n old_nZ) with (mremap_source_b (m_vmmaps m) old old_n old_nZ).
  change (mremap_backing_uniform_b (setL L m) old old_n) with (mremap_backing_uniform_b m old old_n).
  revert R2.
  change (mremap_source_b (m_vmmaps (setL L m)) old old_n old_nZ) with (mremap_source_b (m_vmmaps m) old old_n old_nZ).
  change (mremap_backing_uniform_b (setL L m) old old_n) with (mremap_backing_uniform_b m old old_n).
  destruct (negb (mremap_source_b (m_vmmaps m) old old_n old_nZ && mremap_backing_uniform_b m old old_n)); [intros _; at_auto|].
  destruct (old_nZ =? new_nZ)%Z eqn:Eeq; [intros _; at_auto|].
  intros R2. apply at_alt; [at_auto|].
  destruct (new_nZ <? old_nZ)%Z eqn:Elt.
  - (* [comment removed for export] *)
    apply at_bind; [apply at_modify; reflexivity | intros [] ? ? _; at_auto].
  - (* [comment removed for export] *)
    apply Z.ltb_ge in Elt. apply Z.eqb_neq in Eeq.
    assert (Hle : (new_nZ <=? old_nZ)%Z = false) by (apply Z.leb_gt; lia).
    rewrite Hle in R2. apply negb_false_iff in R2. apply andb_true_iff in R2 as [Rf Rm].
    pose proof (page_align_is0_b_false_word new_size Hnew) as Hnw. fold new_nZ in Hnw. fold new_n in Hnw.
    pose proof (page_round_up_Z_mod (bv_unsigned new_size)) as Hnmod. fold new_nZ in Hnmod.
    pose proof (page_round_up_Z_nonneg (bv_unsigned old_size) (proj1 (mremap_word_range old_size))) as Honn. fold old_nZ in Honn.
    pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
    unfold mremap_move_budget_b in Rm. apply Z.leb_le in Rm.
    change (mremap_move_charge (setL L m) old old_n new_n) with (mremap_move_charge m old old_n new_n) in Rm.
    change (vm_limit (m_vmmaps (setL L m))) with L in Rm.
    rewrite mremap_final_budget_b_setL in Rf.
    assert (Rfm : mremap_final_budget_b m old old_n old new_n = true).
    { unfold mremap_final_budget_b, vm_backing_within_limit. apply Z.leb_le. apply Z.leb_le in Rf.
      change (vm_limit (m_vmmaps (mremap_model_next m old old_n old new_n))) with (mlim m). lia. }
    assert (MOVE : lim_at L i m
              (dst <- choose (fun dst => mremap_fresh_b m old_nZ new_nZ old old_n dst new_n = true) ;;
               modify (fun _ => mremap_model_next m old old_n dst new_n) ;;
               pure (mremap_move_effect old old_n dst old_nZ new_nZ))
              (dst <- choose (fun dst => mremap_fresh_b (setL L m) old_nZ new_nZ old old_n dst new_n = true) ;;
               modify (fun _ => mremap_model_next (setL L m) old old_n dst new_n) ;;
               pure (mremap_move_effect old old_n dst old_nZ new_nZ))).
    { apply at_bind.
      - apply at_choose. intros dst Hd. unfold mremap_fresh_b in *. cbv zeta in *.
        apply andb_true_iff in Hd as [Hd _]. apply andb_true_iff. split; [exact Hd|].
        rewrite mremap_final_budget_b_setL. apply Z.leb_le.
        apply andb_true_iff in Hd as [Hd Hrf]. apply andb_true_iff in Hd as [Hd Htp].
        apply andb_true_iff in Hd as [Hd _]. apply andb_true_iff in Hd as [_ Hal].
        apply Z.eqb_eq in Hal. apply Z.leb_le in Htp.
        change (m_vmmaps (setL L m)) with (setvl L (m_vmmaps m)) in Hrf, Htp.
        change (alloc_top (setvl L (m_vmmaps m))) with (alloc_top (m_vmmaps m)) in Htp.
        cbn [setvl vm_reserved vm_maps] in Hrf.
        pose proof (mremap_word_range dst) as Hdr.
        assert (Hc : (vm_backing_used (mremap_model_next m old old_n dst new_n) <= mremap_move_charge m old old_n new_n)%Z).
        { apply move_charge_le.
          - exact Hfit.
          - exact Hal.
          - rewrite Hnw. exact Hnmod.
          - rewrite Hnw. lia.
          - rewrite Hnw. lia.
          - apply region_free_map_remove. exact (region_free_app_r _ _ _ _ Hrf). }
        lia.
      - intros dst m1 ev Hc. apply choose_inv in Hc as (_ & -> & ->).
        apply at_bind; [apply at_modify; reflexivity | intros [] ? ? _; at_auto]. }
    assert (IG : mremap_inplace_grow_b (setL L m) old old_n new_n old_nZ new_nZ = mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ).
    { unfold mremap_inplace_grow_b. cbv zeta.
      change (m_vmmaps (setL L m)) with (setvl L (m_vmmaps m)).
      change (alloc_top (setvl L (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
      change (vm_reserved (setvl L (m_vmmaps m))) with (vm_reserved (m_vmmaps m)).
      change (vm_maps (setvl L (m_vmmaps m))) with (vm_maps (m_vmmaps m)).
      rewrite Rfm. rewrite mremap_final_budget_b_setL. rewrite Rf. reflexivity. }
    rewrite IG.
    destruct (mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ).
    + apply at_alt; [| exact MOVE].
      apply at_bind; [apply at_modify; reflexivity | intros [] ? ? _; at_auto].
    + exact MOVE.
Qed.
