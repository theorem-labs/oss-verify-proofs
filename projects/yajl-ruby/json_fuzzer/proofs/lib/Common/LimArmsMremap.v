(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require VmMapsDisjoint BudgetPremise.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import
  LimBase LimMonad LimFitBase LimFitVm LimFit LimInv LimInterval LimArmsVm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma filter_length_le {A} : forall (f : A -> bool) l, (length (List.filter f l) <= length l)%nat.
Proof.
  intros f l. induction l as [| x r IH]; cbn; [lia |]. destruct (f x); cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_clear_id : forall (b t : word) lo hi,
  clear_of lo hi (b, t) -> lo <= hi -> iv_subtract b t lo hi = [(b, t)].
Proof.
  intros b t lo hi (Hnz & Hfit & Hmiss) Hlh. cbn [fst snd] in *.
  pose proof (word_range b) as Rb. pose proof (word_range t) as Rt.
  destruct Hmiss as [Hmiss | Hmiss]; iv_cases; iv_close.
Qed.

Lemma maps_subtract_clear_id : forall Y lo hi,
  Forall (clear_of lo hi) Y -> lo <= hi -> maps_subtract Y lo hi = Y.
Proof.
  induction Y as [| [b t] r IH]; intros lo hi H Hlh; cbn [maps_subtract]; [reflexivity |].
  inversion H as [| e l He Hr]; subst.
  rewrite (iv_subtract_clear_id b t lo hi He Hlh). cbn [app]. f_equal. apply IH; assumption.
Qed.

(* [comment removed for export] *)
Definition inside_of (lo hi : Z) (e : word * word) : Prop :=
  lo <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= hi.

Lemma inside_of_iv_subtract : forall (b t : word) lo hi x y,
  hi <= two_pow_64 -> inside_of lo hi (b, t) -> Forall (inside_of lo hi) (iv_subtract b t x y).
Proof.
  intros b t lo hi x y Hhi [H1 H2]. cbn [fst snd] in *.
  pose proof (word_range b) as Rb. pose proof (word_range t) as Rt.
  unfold iv_subtract. cbv zeta. apply Forall_app. split.
  - destruct (bv_unsigned b <? x) eqn:E; [| constructor]. apply Z.ltb_lt in E.
    constructor; [| constructor]. unfold inside_of. cbn [fst snd].
    rewrite unsigned_Z_to_bv_small by (unfold two_pow_64 in *; lia). lia.
  - destruct (y <? bv_unsigned b + bv_unsigned t) eqn:E; [| constructor]. apply Z.ltb_lt in E.
    constructor; [| constructor]. unfold inside_of. cbn [fst snd].
    rewrite (unsigned_Z_to_bv_small (Z.max (bv_unsigned b) y)) by (unfold two_pow_64 in *; lia).
    rewrite unsigned_Z_to_bv_small by (unfold two_pow_64 in *; lia). lia.
Qed.

Lemma inside_of_maps_subtract : forall Y lo hi x y,
  hi <= two_pow_64 -> Forall (inside_of lo hi) Y -> Forall (inside_of lo hi) (maps_subtract Y x y).
Proof.
  induction Y as [| [b t] r IH]; intros lo hi x y Hhi H; cbn [maps_subtract]; [constructor |].
  inversion H as [| e l He Hr]; subst. apply Forall_app. split.
  - apply inside_of_iv_subtract; assumption.
  - apply IH; assumption.
Qed.

Lemma inside_of_maps_subtract_all : forall cuts Y lo hi,
  hi <= two_pow_64 -> Forall (inside_of lo hi) Y -> Forall (inside_of lo hi) (maps_subtract_all Y cuts).
Proof.
  induction cuts as [| [a n] r IH]; intros Y lo hi Hhi H; cbn [maps_subtract_all]; [exact H |].
  apply IH; [exact Hhi |]. apply inside_of_maps_subtract; assumption.
Qed.

(* [comment removed for export] *)
Lemma clear_of_fresh : forall m old dst new_n,
  linv m ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst new_n = true ->
  Forall (clear_of (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n))
         (map_remove (vm_maps (m_vmmaps m)) old).
Proof.
  intros m old dst new_n HI Hfree.
  pose proof (proj1 HI) as HF. pose proof (linv_nonzero m HI) as HNZ.
  unfold fits in HF. apply Forall_forall. intros [a sz] Hin.
  unfold map_remove in Hin. apply filter_In in Hin as [Hin _].
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hfit.
  pose proof (proj1 (Forall_forall _ _) HNZ _ Hin) as Hnz.
  pose proof (region_free_In _ dst new_n a sz Hfree (in_or_app _ _ _ (or_intror Hin))) as Hov.
  unfold entry_fits in Hfit. cbn [fst snd] in *.
  pose proof (word_range sz) as Rs.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov.
  unfold clear_of. cbn [fst snd].
  split; [lia |]. split; [exact Hfit |].
  destruct Hov as [Hov | Hov]; apply Z.ltb_ge in Hov; [left | right]; lia.
Qed.

(* [comment removed for export] *)
Theorem move_charge_bound : forall m old old_n dst new_n,
  linv m ->
  bv_unsigned dst mod page_size = 0 ->
  bv_unsigned new_n mod page_size = 0 ->
  0 < bv_unsigned new_n ->
  bv_unsigned dst + bv_unsigned new_n < two_pow_64 ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst new_n = true ->
  vm_backing_used (mremap_model_next m old old_n dst new_n) <= mremap_move_charge m old old_n new_n.
Proof.
  intros m old old_n dst new_n HI Halign Hnalign Hpos Hend Hfree.
  pose proof (clear_of_fresh m old dst new_n HI Hfree) as HC0.
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
  set (dlo := bv_unsigned dst) in *. set (dhi := bv_unsigned dst + bv_unsigned new_n) in *.
  set (KL := maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) in *.
  set (KP := List.filter (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n))
               (m_vm_materialized m)) in *.
  set (R0 := map_remove (vm_maps (m_vmmaps m)) old) in *.
  set (NA := vm_noaccess (m_vmmaps m)) in *.
  pose proof (word_range dst) as Rd. pose proof (word_range new_n) as Rn.
  assert (Hlh : dlo <= dhi) by (unfold dlo, dhi; lia).
  assert (Hlo : 0 <= dlo) by (unfold dlo; lia).
  (* [comment removed for export] *)
  pose proof (clear_of_maps_subtract_all NA R0 dlo dhi HC0) as HCY.
  (* [comment removed for export] *)
  assert (HIN : Forall (inside_of dlo dhi) (maps_subtract_all [(dst, new_n)] NA)).
  { apply inside_of_maps_subtract_all; [unfold dhi; lia |].
    constructor; [| constructor]. unfold inside_of, dlo, dhi. cbn [fst snd]. lia. }
  change ((dst, new_n) :: R0) with ([(dst, new_n)] ++ R0).
  rewrite (Mremap.maps_subtract_all_app NA [(dst, new_n)] R0).
  rewrite length_app.
  pose proof (filter_length_le (page_outside_range dlo dhi) KP) as HKP.
  change (dlo + bv_unsigned new_n) with dhi.
  destruct (mremap_source_lazy_b m old old_n) eqn:Hsrc.
  - (* [comment removed for export] *)
    rewrite (Mremap.lazy_interior_aligned dst new_n Halign Hnalign Hpos).
    rewrite length_map.
    rewrite Mremap.maps_subtract_all_app, Mremap.live_bytes_app.
    cbn [app]. cbn [maps_subtract_all]. fold dlo. change (dlo + bv_unsigned new_n) with dhi.
    rewrite (maps_subtract_inside _ dlo dhi HIN). rewrite Mremap.maps_subtract_all_nil. cbn [live_bytes].
    rewrite (maps_subtract_clear_id _ dlo dhi HCY Hlh).
    rewrite (maps_subtract_all_cut_clear KL _ dlo dhi Hlo Hlh Hend HCY).
    unfold page_size. lia.
  - (* [comment removed for export] *)
    rewrite Mremap.maps_subtract_all_app, Mremap.live_bytes_app.
    rewrite (maps_subtract_all_cut_clear KL _ dlo dhi Hlo Hlh Hend HCY).
    pose proof (Mremap.live_bytes_maps_subtract_all_le (maps_subtract KL dlo dhi) (maps_subtract_all [(dst, new_n)] NA)) as B1.
    pose proof (Mremap.live_bytes_maps_subtract_all_le NA [(dst, new_n)]) as B2.
    cbn [live_bytes] in B2. cbn [length] in *. unfold page_size. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Mremap.
Variable L : Z.

Lemma mremap_model_next_sl : forall m old old_n dst new_n,
  mremap_model_next (sl L m) old old_n dst new_n = sl L (mremap_model_next m old old_n dst new_n).
Proof. reflexivity. Qed.

Lemma mremap_model_next_mlim : forall m old old_n dst new_n,
  mlim (mremap_model_next m old old_n dst new_n) = mlim m.
Proof. reflexivity. Qed.

Lemma final_budget_sl : forall m old old_n dst new_n,
  mremap_final_budget_b (sl L m) old old_n dst new_n
  = (vm_backing_used (mremap_model_next m old old_n dst new_n) <=? L).
Proof. reflexivity. Qed.

Lemma final_budget_big : forall m old old_n dst new_n,
  mremap_final_budget_b m old old_n dst new_n
  = (vm_backing_used (mremap_model_next m old old_n dst new_n) <=? mlim m).
Proof. reflexivity. Qed.

Lemma move_budget_sl : forall m old old_n new_n,
  mremap_move_budget_b (sl L m) old old_n new_n = (mremap_move_charge m old old_n new_n <=? L).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mark_grow : forall old old_size new_size flags m,
  mremap_budget_refused_b old old_size new_size flags (sl L m) = false ->
  negb (bv_unsigned flags =? MREMAP_MAYMOVE) = false ->
  negb (bv_unsigned old mod page_size =? 0) = false ->
  page_align_is0_b new_size = false ->
  page_align_is0_b old_size = false ->
  negb (mremap_source_b (m_vmmaps m) old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
          (page_round_up_Z (bv_unsigned old_size))
        && mremap_backing_uniform_b m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))) = false ->
  page_round_up_Z (bv_unsigned old_size) < page_round_up_Z (bv_unsigned new_size) ->
  vm_backing_used (mremap_model_next m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size))) old
                     (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))) <= L
  /\ mremap_move_charge m old (Z_to_bv 64 (page_round_up_Z (bv_unsigned old_size)))
       (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) <= L.
Proof.
  intros old old_size new_size flags m HM E0 E1 E2 E3 E4 Hgrow.
  unfold mremap_budget_refused_b in HM. cbv zeta in HM.
  rewrite E0, E1, E2, E3 in HM.
  change (m_vmmaps (sl L m)) with (vml L (m_vmmaps m)) in HM.
  change (mremap_source_b (vml L (m_vmmaps m))) with (mremap_source_b (m_vmmaps m)) in HM.
  change (mremap_backing_uniform_b (sl L m)) with (mremap_backing_uniform_b m) in HM.
  rewrite E4 in HM.
  rewrite (proj2 (Z.leb_gt _ _) Hgrow) in HM.
  apply negb_false_iff in HM. apply andb_true_iff in HM as [H1 H2].
  rewrite final_budget_sl in H1. rewrite move_budget_sl in H2.
  apply Z.leb_le in H1, H2. split; assumption.
Qed.

Lemma inplace_sl : forall m old old_n new_n old_nZ new_nZ,
  L <= mlim m ->
  vm_backing_used (mremap_model_next m old old_n old new_n) <= L ->
  mremap_inplace_grow_b (sl L m) old old_n new_n old_nZ new_nZ
  = mremap_inplace_grow_b m old old_n new_n old_nZ new_nZ.
Proof.
  intros m old old_n new_n old_nZ new_nZ HL Hip.
  unfold mremap_inplace_grow_b. cbv zeta.
  change (m_vmmaps (sl L m)) with (vml L (m_vmmaps m)).
  change (alloc_top (vml L (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
  cbn [vml vm_reserved vm_maps].
  rewrite final_budget_sl, final_budget_big.
  rewrite (proj2 (Z.leb_le _ _) Hip).
  replace (vm_backing_used (mremap_model_next m old old_n old new_n) <=? mlim m) with true
    by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma fresh_sl : forall m old old_n new_size dst old_nZ,
  linv m -> L <= mlim m ->
  page_align_is0_b new_size = false ->
  0 < page_round_up_Z (bv_unsigned new_size) ->
  mremap_move_charge m old old_n (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) <= L ->
  mremap_fresh_b (sl L m) old_nZ (page_round_up_Z (bv_unsigned new_size)) old old_n dst
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
  = mremap_fresh_b m old_nZ (page_round_up_Z (bv_unsigned new_size)) old old_n dst
      (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))).
Proof.
  intros m old old_n new_size dst old_nZ HI HL Hal0 Hpos0 Hmv.
  pose proof (BudgetPremise.page_align_is0_b_false_word new_size Hal0) as Hnw.
  pose proof (BudgetPremise.page_round_up_Z_mod (bv_unsigned new_size)) as Hnmod.
  unfold mremap_fresh_b. cbv zeta.
  change (m_vmmaps (sl L m)) with (vml L (m_vmmaps m)).
  change (alloc_top (vml L (m_vmmaps m))) with (alloc_top (m_vmmaps m)).
  cbn [vml vm_reserved vm_maps].
  destruct (negb (bv_eqb dst old) && (bv_unsigned dst mod page_size =? 0) && (0 <? bv_unsigned dst)
            && (bv_unsigned dst + page_round_up_Z (bv_unsigned new_size) <=? alloc_top (m_vmmaps m))
            && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst
                 (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))))%bool eqn:SH;
    [| reflexivity].
  cbn [andb].
  apply andb_true_iff in SH as [SH Hfree]. apply andb_true_iff in SH as [SH Htop].
  apply andb_true_iff in SH as [SH _]. apply andb_true_iff in SH as [_ Hal].
  apply Z.eqb_eq in Hal. apply Z.leb_le in Htop.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hat.
  pose proof (move_charge_bound m old old_n dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) HI Hal
                ltac:(rewrite Hnw; exact Hnmod) ltac:(rewrite Hnw; exact Hpos0)
                ltac:(rewrite Hnw; lia) Hfree) as HB.
  rewrite final_budget_sl, final_budget_big.
  replace (vm_backing_used (mremap_model_next m old old_n dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))) <=? L) with true
    by (symmetry; apply Z.leb_le; lia).
  replace (vm_backing_used (mremap_model_next m old old_n dst (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))) <=? mlim m) with true
    by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma fr_mremap : forall old old_size new_size flags i m,
  linv m -> L <= mlim m -> mremap_budget_refused_b old old_size new_size flags (sl L m) = false ->
  FR L i m (mremap_spec old old_size new_size flags) (mremap_spec old old_size new_size flags).
Proof.
  intros old old_size new_size flags i m HI HL HM. unfold mremap_spec.
  frE.
  (* [comment removed for export] *)
  apply Z.eqb_neq in Heqb4. apply Z.ltb_ge in Heqb5.
  assert (Hgrow : page_round_up_Z (bv_unsigned old_size) < page_round_up_Z (bv_unsigned new_size)) by lia.
  destruct (mark_grow old old_size new_size flags m HM Heqb Heqb0 Heqb1 Heqb2 Heqb3 Hgrow) as [Hip Hmv].
  assert (Hpos0 : 0 < page_round_up_Z (bv_unsigned new_size)).
  { pose proof (BudgetPremise.page_round_up_Z_nonneg (bv_unsigned old_size) (proj1 (word_range old_size))). lia. }
  rewrite (inplace_sl m old _ _ _ _ HL Hip).
  frE.
  all: try (rewrite (fresh_sl m old _ new_size _ _ HI HL Heqb1 Hpos0 Hmv); reflexivity).
  all: try (fr_inv; reflexivity).
Qed.

End Mremap.
