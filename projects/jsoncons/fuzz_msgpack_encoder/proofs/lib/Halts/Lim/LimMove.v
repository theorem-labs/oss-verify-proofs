(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by gabelogan195, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimMove.v at commit f92feaf8b7, whole, with the module path OSSVerify.Proofs.openssl.bndiv.lib.Lib changed to OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.Lim and nothing else. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the move proofs follow mremap's source cut (maps_subtract, region_free_maps_subtract), its TASK_SIZE gate and its in-place grow when there is room (mremap_inplace_room_b), with a comment on each, and the comment on the grow branch of mremap_at_down is left out. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import BudgetPremise.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.Lim Require Import LimBase LimMm LimMmap LimMremap LimCut.
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

(* LPS 08b1429: a range free of every mapping is free of the mremap source cut, whose pieces lie
   inside those mappings ([maps_subtract_In], [iv_subtract_within]). *)
Lemma region_free_maps_subtract : forall (l : list (word * word)) (lo hi : Z) (a n : word),
  (forall (b s : word), In (b, s) l -> (bv_unsigned b + bv_unsigned s <= two_pow_64)%Z) ->
  region_free l a n = true -> region_free (maps_subtract l lo hi) a n = true.
Proof.
  intros l lo hi a n Hfit Hf. apply State.region_free_intro. intros b s Hin.
  destruct (maps_subtract_In l lo hi b s Hin) as (b0 & s0 & Hin0 & Hiv).
  destruct (iv_subtract_within b0 s0 lo hi b s (Hfit b0 s0 Hin0) Hiv) as [W1 W2].
  pose proof (State.region_free_In l a n b0 s0 Hf Hin0) as H0.
  unfold iv_overlap in *. apply andb_false_iff in H0. apply andb_false_iff.
  destruct H0 as [H0|H0]; apply Z.ltb_ge in H0; [left | right]; apply Z.ltb_ge; lia.
Qed.

Theorem move_charge_le : forall m old old_n dst new_n,
  vm_fit (m_vmmaps m) ->
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned new_n mod page_size = 0)%Z ->
  (0 < bv_unsigned new_n)%Z ->
  (bv_unsigned dst + bv_unsigned new_n < two_pow_64)%Z ->
  (* LPS 08b1429: [mremap_maps_next] cuts the source RANGE ([maps_subtract]) where it used
     [map_remove] on the base address, so the free-destination premise reads the same list. *)
  region_free (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) dst new_n = true ->
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
  set (R0 := maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) in *.
  set (NA := vm_noaccess (m_vmmaps m)) in *.
  set (dlo := bv_unsigned dst) in *. set (dhi := (dlo + bv_unsigned new_n)%Z) in *.
  pose proof (mremap_word_range dst) as Hdr. fold dlo in Hdr.
  (* [comment removed for export] *)
  assert (HfitR : forall (a sz : word), In (a, sz) R0 -> (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z).
  { intros a sz Hin. unfold R0 in Hin.
    destruct (maps_subtract_In (vm_maps (m_vmmaps m)) _ _ a sz Hin) as (a0 & sz0 & Hin0 & Hiv).
    pose proof (Hfit a0 sz0 Hin0) as Hf0.
    destruct (iv_subtract_within a0 sz0 _ _ a sz Hf0 Hiv). lia. }
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
  (* LPS 08b1429's gate: a page-aligned new length over TASK_SIZE is EINVAL. *)
  destruct (TASK_SIZE <? new_nZ)%Z; [intros _; at_auto|].
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
  -
    apply Z.ltb_ge in Elt. apply Z.eqb_neq in Eeq.
    assert (Hle : (new_nZ <=? old_nZ)%Z = false) by (apply Z.leb_gt; lia).
    rewrite Hle in R2.
    pose proof (page_align_is0_b_false_word new_size Hnew) as Hnw. fold new_nZ in Hnw. fold new_n in Hnw.
    pose proof (page_round_up_Z_mod (bv_unsigned new_size)) as Hnmod. fold new_nZ in Hnmod.
    pose proof (page_round_up_Z_nonneg (bv_unsigned old_size) (proj1 (mremap_word_range old_size))) as Honn. fold old_nZ in Honn.
    pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
    (* LPS 08b1429: the grow path is the in-place one when there is room, the move otherwise;
       [setL] changes only [vm_limit], which the room test does not read. *)
    assert (IR : mremap_inplace_room_b (setL L m) old old_n new_n old_nZ new_nZ
                 = mremap_inplace_room_b m old old_n new_n old_nZ new_nZ).
    { unfold mremap_inplace_room_b. cbv zeta.
      change (m_vmmaps (setL L m)) with (setvl L (m_vmmaps m)).
      change (alloc_top (setvl L (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
      change (vm_reserved (setvl L (m_vmmaps m))) with (vm_reserved (m_vmmaps m)).
      change (vm_maps (setvl L (m_vmmaps m))) with (vm_maps (m_vmmaps m)).
      reflexivity. }
    rewrite IR in R2. rewrite IR. revert R2.
    destruct (mremap_inplace_room_b m old old_n new_n old_nZ new_nZ) eqn:Eroom; intros R2.
    +
      apply negb_false_iff in R2.
      apply at_bind.
      * apply at_choose. intros [] _. exact R2.
      * intros [] m1 ev Hc. apply choose_inv in Hc as (_ & -> & ->).
        apply at_bind; [apply at_modify; reflexivity | intros [] ? ? _; at_auto].
    +
      apply negb_false_iff in R2.
      unfold mremap_move_budget_b in R2. apply Z.leb_le in R2.
      change (mremap_move_charge (setL L m) old old_n new_n) with (mremap_move_charge m old old_n new_n) in R2.
      change (vm_limit (m_vmmaps (setL L m))) with L in R2.
      apply at_bind.
      * apply at_choose. intros dst Hd. unfold mremap_dst_ok in *. destruct Hd as [Hp Hf].
        split; [exact Hp|]. unfold mremap_fresh_b in *. cbv zeta in *.
        apply andb_true_iff in Hf as [Hf _]. apply andb_true_iff. split; [exact Hf|].
        rewrite mremap_final_budget_b_setL. apply Z.leb_le.
        apply andb_true_iff in Hf as [Hf Hrf]. apply andb_true_iff in Hf as [Hf Htp].
        apply andb_true_iff in Hf as [Hf _]. apply andb_true_iff in Hf as [_ Hal].
        apply Z.eqb_eq in Hal. apply Z.leb_le in Htp.
        pose proof (mremap_word_range dst) as Hdr.
        assert (Hc : (vm_backing_used (mremap_model_next m old old_n dst new_n) <= mremap_move_charge m old old_n new_n)%Z).
        { apply move_charge_le.
          - exact Hfit.
          - exact Hal.
          - rewrite Hnw. exact Hnmod.
          - rewrite Hnw. lia.
          - rewrite Hnw. lia.
          - apply region_free_maps_subtract; [exact Hfit | exact (region_free_app_r _ _ _ _ Hrf)]. }
        lia.
      * intros dst m1 ev Hc. apply choose_inv in Hc as (_ & -> & ->).
        apply at_bind; [apply at_modify; reflexivity | intros [] ? ? _; at_auto].
Qed.
