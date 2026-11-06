(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BudgetMonoCut.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma cut_app : forall C1 C2 X,
  maps_subtract_all X (C1 ++ C2) = maps_subtract_all (maps_subtract_all X C1) C2.
Proof.
  induction C1 as [|[a n] r IH]; intros C2 X; [reflexivity |].
  cbn [app maps_subtract_all]. apply IH.
Qed.

Lemma cut_cons : forall a n C X,
  maps_subtract_all X ((a, n) :: C)
  = maps_subtract_all (maps_subtract X (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) C.
Proof. reflexivity. Qed.


Lemma maps_subtract_single : forall b s lo hi,
  maps_subtract [(b, s)] lo hi = iv_subtract b s lo hi.
Proof. intros. cbn [maps_subtract]. apply app_nil_r. Qed.

Lemma live_bytes_single : forall (b s : word), live_bytes [(b, s)] = bv_unsigned s.
Proof. intros. cbn [live_bytes]. lia. Qed.

(* [comment removed for export] *)
Lemma live_cut_zero : forall C (b s : word),
  bv_unsigned s = 0%Z -> live_bytes (maps_subtract_all [(b, s)] C) = 0%Z.
Proof.
  intros C b s Hs.
  pose proof (live_bytes_maps_subtract_all_le C [(b, s)]) as H1.
  pose proof (live_bytes_nonneg (maps_subtract_all [(b, s)] C)).
  rewrite live_bytes_single in H1. lia.
Qed.

Lemma live_cut_iv_zero : forall C (b s : word) lo hi,
  bv_unsigned s = 0%Z -> (lo <= hi)%Z ->
  live_bytes (maps_subtract_all (iv_subtract b s lo hi) C) = 0%Z.
Proof.
  intros C b s lo hi Hs Hlh.
  pose proof (live_bytes_maps_subtract_all_le C (iv_subtract b s lo hi)) as H1.
  pose proof (live_bytes_nonneg (maps_subtract_all (iv_subtract b s lo hi) C)).
  pose proof (live_bytes_iv_subtract_le b s lo hi Hlh). lia.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_hi_irrel_left : forall (b s : word) a h1 h2,
  (bv_unsigned b + bv_unsigned s <= h1)%Z -> (bv_unsigned b + bv_unsigned s <= h2)%Z ->
  iv_subtract b s a h1 = iv_subtract b s a h2.
Proof.
  intros b s a h1 h2 H1 H2. unfold iv_subtract. cbv zeta.
  rewrite (proj2 (Z.ltb_ge h1 _) H1), (proj2 (Z.ltb_ge h2 _) H2). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_lo_max_right : forall (b s : word) a hi h,
  (hi <= bv_unsigned b)%Z ->
  iv_subtract b s (Z.max a hi) h = iv_subtract b s a h.
Proof.
  intros b s a hi h Hb. unfold iv_subtract. cbv zeta.
  destruct (Z.max_spec a hi) as [[Hm Hmx] | [Hm Hmx]]; rewrite Hmx; [| reflexivity].
  (* [comment removed for export] *)
  rewrite (proj2 (Z.ltb_ge (bv_unsigned b) hi) Hb).
  rewrite (proj2 (Z.ltb_ge (bv_unsigned b) a) ltac:(lia)). reflexivity.
Qed.

Section Heart.

Variables lo hi : Z.
Hypothesis Hlo : (0 <= lo)%Z.
Hypothesis Hlh : (lo <= hi)%Z.
Hypothesis Hhi : (hi < two_pow_64)%Z.

(* [comment removed for export] *)
Definition misses (X : list (word * word)) : Prop :=
  forall (b s : word), In (b, s) X ->
    (bv_unsigned b + bv_unsigned s <= two_pow_64)%Z
    /\ (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z.

Lemma misses_cut : forall C X, misses X -> misses (maps_subtract_all X C).
Proof.
  intros C X HX b s Hin.
  destruct (maps_subtract_all_within C X b s (fun a sz H => proj1 (HX a sz H)) Hin)
    as [a [sz [Hin' Hw]]].
  destruct (HX a sz Hin') as [Hf Hd]. split; lia.
Qed.

Lemma misses_cons : forall b s X, misses ((b, s) :: X) -> misses [(b, s)] /\ misses X.
Proof.
  intros b s X H. split.
  - intros b' s' [E | []]. apply H. left. exact E.
  - intros b' s' Hin. apply H. right. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma heart_entry : forall (b s a n : word) C,
  (bv_unsigned b + bv_unsigned s <= two_pow_64)%Z ->
  (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z ->
  live_bytes (maps_subtract_all [(b, s)] (iv_subtract a n lo hi ++ C))
  = live_bytes (maps_subtract_all (iv_subtract b s (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) C).
Proof.
  intros b s a n C Hfit Hdisj.
  pose proof (mremap_word_range a) as Ra. pose proof (mremap_word_range n) as Rn.
  pose proof (mremap_word_range b) as Rb. pose proof (mremap_word_range s) as Rs.
  destruct (Z.eq_dec (bv_unsigned s) 0) as [Hs0 | Hs0].
  { rewrite live_cut_zero by exact Hs0. rewrite live_cut_iv_zero by (try exact Hs0; lia).
    reflexivity. }
  assert (Hspos : (0 < bv_unsigned s)%Z) by lia.
  unfold iv_subtract at 1. cbv zeta.
  destruct (bv_unsigned a <? lo)%Z eqn:E1;
    [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1];
  destruct (hi <? bv_unsigned a + bv_unsigned n)%Z eqn:E2;
    [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2 | apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
  cbn [app].
  (* [comment removed for export] *)
  all: try (rewrite cut_cons;
            rewrite (mremap_u64 (Z.min (bv_unsigned n) (lo - bv_unsigned a))) by
              (pose proof (Z.min_spec (bv_unsigned n) (lo - bv_unsigned a)); lia)).
  all: try (rewrite ?cut_cons;
            rewrite (mremap_u64 (Z.max (bv_unsigned a) hi)) by
              (pose proof (Z.max_spec (bv_unsigned a) hi); lia);
            rewrite (mremap_u64 (bv_unsigned a + bv_unsigned n - Z.max (bv_unsigned a) hi)) by
              (pose proof (Z.max_spec (bv_unsigned a) hi); lia);
            replace (Z.max (bv_unsigned a) hi
                     + (bv_unsigned a + bv_unsigned n - Z.max (bv_unsigned a) hi))%Z
              with (bv_unsigned a + bv_unsigned n)%Z by lia).
  - (* [comment removed for export] *)
    destruct Hdisj as [Hd | Hd].
    + (* [comment removed for export] *)
      rewrite live_bytes_subtract_free.
      * rewrite maps_subtract_single.
        rewrite (iv_subtract_hi_irrel_left b s (bv_unsigned a)
                   (bv_unsigned a + Z.min (bv_unsigned n) (lo - bv_unsigned a))
                   (bv_unsigned a + bv_unsigned n)); [reflexivity | |];
          pose proof (Z.min_spec (bv_unsigned n) (lo - bv_unsigned a)); lia.
      * pose proof (Z.max_spec (bv_unsigned a) hi). lia.
      * intros b' s' Hin. rewrite maps_subtract_single in Hin.
        pose proof (iv_subtract_within b s _ _ b' s' Hfit Hin).
        pose proof (Z.max_spec (bv_unsigned a) hi). lia.
    + (* [comment removed for export] *)
      rewrite (maps_subtract_single b s), iv_subtract_disjoint;
        [| lia | pose proof (Z.min_spec (bv_unsigned n) (lo - bv_unsigned a)); lia
         | pose proof (Z.min_spec (bv_unsigned n) (lo - bv_unsigned a)); lia].
      rewrite maps_subtract_single, (iv_subtract_lo_max_right b s (bv_unsigned a) hi)
        by exact Hd.
      reflexivity.
  - (* [comment removed for export] *)
    destruct Hdisj as [Hd | Hd].
    + rewrite maps_subtract_single.
      destruct (Z.min_spec (bv_unsigned n) (lo - bv_unsigned a)) as [[Hm Hmx] | [Hm Hmx]];
        rewrite Hmx; [reflexivity |].
      rewrite (iv_subtract_hi_irrel_left b s (bv_unsigned a)
                 (bv_unsigned a + (lo - bv_unsigned a)) (bv_unsigned a + bv_unsigned n))
        by lia.
      reflexivity.
    + rewrite maps_subtract_single, iv_subtract_disjoint;
        [| lia | pose proof (Z.min_spec (bv_unsigned n) (lo - bv_unsigned a)); lia
         | pose proof (Z.min_spec (bv_unsigned n) (lo - bv_unsigned a)); lia].
      rewrite (iv_subtract_disjoint b s (bv_unsigned a)) by lia.
      reflexivity.
  - (* [comment removed for export] *)
    destruct Hdisj as [Hd | Hd].
    + rewrite live_bytes_subtract_free.
      * rewrite (iv_subtract_disjoint b s (bv_unsigned a)) by lia. reflexivity.
      * pose proof (Z.max_spec (bv_unsigned a) hi). lia.
      * intros b' s' [E | []]. inversion E; subst b' s'.
        pose proof (Z.max_spec (bv_unsigned a) hi). lia.
    + rewrite maps_subtract_single, (iv_subtract_lo_max_right b s (bv_unsigned a) hi)
        by exact Hd.
      reflexivity.
  - (* [comment removed for export] *)
    rewrite (iv_subtract_disjoint b s (bv_unsigned a)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma heart_step : forall X (a n : word) D,
  misses X ->
  live_bytes (maps_subtract_all X (iv_subtract a n lo hi ++ D))
  = live_bytes (maps_subtract_all (maps_subtract X (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) D).
Proof.
  induction X as [|[b s] X IH]; intros a n D HX.
  - rewrite !maps_subtract_all_nil. reflexivity.
  - destruct (misses_cons b s X HX) as [He HX'].
    destruct (He b s (or_introl eq_refl)) as [Hfit Hd].
    change ((b, s) :: X) with ([(b, s)] ++ X).
    rewrite maps_subtract_all_app, live_bytes_app, maps_subtract_app,
      maps_subtract_all_app, live_bytes_app.
    rewrite (heart_entry b s a n D Hfit Hd), (IH a n D HX'), maps_subtract_single.
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma heart_gen : forall C X D,
  misses X ->
  live_bytes (maps_subtract_all X (maps_subtract C lo hi ++ D))
  = live_bytes (maps_subtract_all X (C ++ D)).
Proof.
  induction C as [|[a n] C IH]; intros X D HX; [reflexivity |].
  cbn [maps_subtract]. rewrite <- app_assoc, cut_app.
  rewrite (IH _ D (misses_cut _ X HX)), <- cut_app.
  rewrite (heart_step X a n (C ++ D) HX). reflexivity.
Qed.

(* [comment removed for export] *)
Theorem live_cut_hole : forall C X,
  misses X ->
  live_bytes (maps_subtract_all X (maps_subtract C lo hi))
  = live_bytes (maps_subtract_all X C).
Proof.
  intros C X HX. pose proof (heart_gen C X [] HX) as H. rewrite !app_nil_r in H. exact H.
Qed.

End Heart.
End BudgetMonoCut.
Require LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BudgetMonoMremap.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoTac BudgetMonoCut OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma filter_length_le' : forall {A} (f : A -> bool) (l : list A),
  (length (List.filter f l) <= length l)%nat.
Proof.
  intros A f l. induction l as [|x l IH]; cbn [List.filter length]; [lia |].
  destruct (f x); cbn [length]; lia.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_inside : forall X lo hi,
  (forall (b s : word), In (b, s) X -> lo <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= hi)%Z ->
  maps_subtract X lo hi = [].
Proof.
  induction X as [|[b s] X IH]; intros lo hi H; [reflexivity |].
  cbn [maps_subtract]. destruct (H b s (or_introl eq_refl)) as [H1 H2].
  unfold iv_subtract. cbv zeta.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned b) lo) H1),
          (proj2 (Z.ltb_ge hi _) H2). cbn [app].
  apply IH. intros b' s' Hin. apply H. right. exact Hin.
Qed.

Theorem mremap_charge_le : forall m old old_n dst new_n,
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned new_n mod page_size = 0)%Z ->
  (0 < bv_unsigned new_n)%Z ->
  (bv_unsigned dst + bv_unsigned new_n < two_pow_64)%Z ->
  (forall (a sz : word), In (a, sz) (map_remove (vm_maps (m_vmmaps m)) old) ->
     (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z) ->
  region_free (map_remove (vm_maps (m_vmmaps m)) old) dst new_n = true ->
  (vm_backing_used (mremap_model_next m old old_n dst new_n)
   <= mremap_move_charge m old old_n new_n)%Z.
Proof.
  intros m old old_n dst new_n Halign Hnalign Hpos Hend Hfit Hmaps.
  assert (P1 : forall L P m', m_vmmaps (with_vm_backing L P m') = m_vmmaps m')
    by reflexivity.
  assert (P2 : forall L P m', m_vm_lazy (with_vm_backing L P m') = L)
    by reflexivity.
  assert (P3 : forall L P m', m_vm_materialized (with_vm_backing L P m') = P)
    by reflexivity.
  assert (P4 : forall h m', m_vmmaps (with_vmmaps h m') = h) by reflexivity.
  assert (P5 : forall h m', m_vm_lazy (with_vmmaps h m') = m_vm_lazy m')
    by reflexivity.
  assert (P6 : forall h m', m_vm_materialized (with_vmmaps h m')
                            = m_vm_materialized m') by reflexivity.
  unfold vm_backing_used, mremap_move_charge, mremap_model_next,
    vm_resize_backing, mremap_maps_next.
  cbv zeta.
  rewrite !P1, !P2, !P3, !P4, !P5, !P6.
  unfold vm_backed_maps. cbn [vm_maps vm_noaccess vm_limit].
  set (KL := maps_subtract (m_vm_lazy m) (bv_unsigned old)
               (bv_unsigned old + bv_unsigned old_n)) in *.
  set (KP := List.filter (page_outside_range (bv_unsigned old)
                            (bv_unsigned old + bv_unsigned old_n))
               (m_vm_materialized m)) in *.
  set (R0 := map_remove (vm_maps (m_vmmaps m)) old) in *.
  set (NA := vm_noaccess (m_vmmaps m)) in *.
  set (dhi := (bv_unsigned dst + bv_unsigned new_n)%Z) in *.
  set (dlo := bv_unsigned dst) in *.
  pose proof (mremap_word_range dst) as Rd.
  pose proof (filter_length_le' (page_outside_range dlo dhi) KP) as HKP.
  rewrite length_app.
  change ((dst, new_n) :: R0) with ([(dst, new_n)] ++ R0).
  rewrite maps_subtract_all_app.
  set (A := maps_subtract_all [(dst, new_n)] NA).
  set (B := maps_subtract_all R0 NA).
  (* [comment removed for export] *)
  assert (HA : forall (b s : word), In (b, s) A ->
            (dlo <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= dhi)%Z).
  { intros b s Hin.
    destruct (maps_subtract_all_within NA [(dst, new_n)] b s
                (fun a sz Hin' => match Hin' with
                                  | or_introl E => ltac:(inversion E; subst; unfold dhi in *; lia)
                                  | or_intror F => match F with end end) Hin)
      as [a [sz [[E | []] Hw]]].
    inversion E; subst a sz. unfold dlo, dhi. lia. }
  (* [comment removed for export] *)
  assert (HB : misses dlo dhi B).
  { intros b s Hin.
    destruct (maps_subtract_all_within NA R0 b s Hfit Hin) as [a [sz [Hin0 Hw]]].
    pose proof (Hfit a sz Hin0).
    pose proof (region_free_In R0 dst new_n a sz Hmaps Hin0) as Hov.
    unfold iv_overlap in Hov. apply andb_false_iff in Hov.
    split; [lia |].
    destruct Hov as [Hov | Hov]; apply Z.ltb_ge in Hov; unfold dlo, dhi; lia. }
  assert (Hps : (0 < page_size)%Z) by (unfold page_size; lia).
  destruct (mremap_source_lazy_b m old old_n) eqn:Hsrc.
  - (* [comment removed for export] *)
    rewrite (lazy_interior_aligned dst new_n Halign Hnalign Hpos).
    rewrite length_map.
    rewrite maps_subtract_all_app, live_bytes_app.
    cbn [app]. rewrite !cut_cons.
    fold dlo. replace (dlo + bv_unsigned new_n)%Z with dhi by reflexivity.
    rewrite (maps_subtract_inside A dlo dhi HA), maps_subtract_all_nil.
    rewrite (live_bytes_subtract_free _ B dlo dhi ltac:(lia)
               (fun b s Hin => proj2 (HB b s Hin))).
    pose proof (live_cut_hole dlo dhi ltac:(lia) ltac:(lia) ltac:(unfold dhi; lia) KL B HB) as HH.
    cbn [live_bytes].
    nia.
  - (* [comment removed for export] *)
    rewrite maps_subtract_all_app, live_bytes_app.
    pose proof (live_cut_hole dlo dhi ltac:(lia) ltac:(lia) ltac:(unfold dhi; lia) KL B HB) as HH.
    pose proof (live_bytes_maps_subtract_all_le (maps_subtract KL dlo dhi) A) as H1.
    pose proof (live_bytes_maps_subtract_all_le NA [(dst, new_n)]) as H2.
    fold A in H2. rewrite live_bytes_single in H2.
    cbn [length]. nia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition maps_fit (m : Model) : Prop :=
  forall (a sz : word), In (a, sz) (vm_maps (m_vmmaps m)) ->
    (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z.

Lemma mremap_model_next_relim : forall L m old old_n dst new_n,
  mremap_model_next (relim L m) old old_n dst new_n
  = relim L (mremap_model_next m old old_n dst new_n).
Proof. reflexivity. Qed.

Lemma mremap_final_budget_b_relim : forall L m old old_n dst new_n,
  mremap_final_budget_b (relim L m) old old_n dst new_n
  = (vm_backing_used (mremap_model_next m old old_n dst new_n) <=? L)%Z.
Proof. reflexivity. Qed.

Lemma mremap_final_budget_b_mono : forall L m old old_n dst new_n,
  (L <= mlim m)%Z ->
  mremap_final_budget_b (relim L m) old old_n dst new_n = true ->
  mremap_final_budget_b m old old_n dst new_n = true.
Proof.
  intros L m old old_n dst new_n HL H.
  unfold mremap_final_budget_b in *. rewrite mremap_model_next_relim in H.
  exact (vm_backing_within_limit_mono L (mremap_model_next m old old_n dst new_n) HL H).
Qed.

Lemma mremap_move_budget_b_relim : forall L m old old_n new_n,
  mremap_move_budget_b (relim L m) old old_n new_n
  = (mremap_move_charge m old old_n new_n <=? L)%Z.
Proof. reflexivity. Qed.

Lemma page_round_up_Z_ge' : forall z, (0 <= z)%Z -> (z <= page_round_up_Z z)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4095) 4096 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (z + 4095) 4096 ltac:(lia)) as Hm.
  lia.
Qed.

Lemma page_round_up_Z_mod' : forall z, (page_round_up_Z z mod page_size = 0)%Z.
Proof. intro z. unfold page_round_up_Z. apply Z_mod_mult. Qed.

Lemma page_round_up_Z_nonneg' : forall z, (0 <= z)%Z -> (0 <= page_round_up_Z z)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  pose proof (Z.div_pos (z + 4096 - 1) 4096 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma page_align_is0_b_false_word' : forall len,
  page_align_is0_b len = false ->
  bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len)))
  = page_round_up_Z (bv_unsigned len).
Proof.
  intros len H. unfold page_align_is0_b in H.
  apply orb_false_iff in H as [_ H]. apply Z.leb_gt in H.
  pose proof (bv_unsigned_in_range 64 len) as Hr.
  change (bv_modulus 64) with two_pow_64 in Hr.
  apply mremap_u64. split; [apply page_round_up_Z_nonneg'; lia | exact H].
Qed.

Lemma region_free_app_r' : forall l1 l2 lo n,
  region_free (l1 ++ l2) lo n = true -> region_free l2 lo n = true.
Proof.
  intros l1 l2 lo n H. apply region_free_intro. intros a sz Hin.
  exact (region_free_In _ _ _ _ _ H (in_or_app _ _ _ (or_intror Hin))).
Qed.

Lemma region_free_map_remove' : forall maps old lo n,
  region_free maps lo n = true -> region_free (map_remove maps old) lo n = true.
Proof.
  intros maps old lo n H. apply region_free_intro. intros a sz Hin.
  unfold map_remove in Hin. apply List.filter_In in Hin as [Hin _].
  exact (region_free_In _ _ _ _ _ H Hin).
Qed.

Lemma map_remove_In : forall maps old (a sz : word),
  In (a, sz) (map_remove maps old) -> In (a, sz) maps.
Proof. intros maps old a sz Hin. unfold map_remove in Hin. apply List.filter_In in Hin. tauto. Qed.

(* [comment removed for export] *)
Lemma mremap_fresh_b_relim : forall L m old_nZ new_size old old_n dst,
  (L <= mlim m)%Z ->
  maps_fit m ->
  page_align_is0_b new_size = false ->
  mremap_move_budget_b (relim L m) old old_n
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))) = true ->
  mremap_fresh_b (relim L m) old_nZ (page_round_up_Z (bv_unsigned new_size)) old old_n dst
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size)))
  = mremap_fresh_b m old_nZ (page_round_up_Z (bv_unsigned new_size)) old old_n dst
    (Z_to_bv 64 (page_round_up_Z (bv_unsigned new_size))).
Proof.
  intros L m old_nZ new_size old old_n dst HL Hfit Hnew Hmove.
  pose proof (page_align_is0_b_false_word' new_size Hnew) as Hnw.
  pose proof (page_round_up_Z_mod' (bv_unsigned new_size)) as Hnmod.
  assert (Hnpos : (0 < page_round_up_Z (bv_unsigned new_size))%Z).
  { unfold page_align_is0_b in Hnew. apply orb_false_iff in Hnew as [Hz _].
    pose proof (w_is0_false_pos new_size Hz).
    pose proof (page_round_up_Z_ge' (bv_unsigned new_size)). lia. }
  set (nZ := page_round_up_Z (bv_unsigned new_size)) in *.
  set (n := Z_to_bv 64 nZ) in *.
  unfold mremap_fresh_b. cbv zeta.
  rewrite !m_vmmaps_relim, !alloc_top_vmrelim. bm_vm_proj.
  destruct (negb (bv_eqb dst old) && (bv_unsigned dst mod page_size =? 0)%Z
            && (0 <? bv_unsigned dst)%Z && (bv_unsigned dst + nZ <=? alloc_top (m_vmmaps m))%Z
            && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) dst n) eqn:Hc;
    [| reflexivity].
  cbn [andb].
  repeat (apply andb_true_iff in Hc as [Hc ?]).
  match goal with
  | Ha : (bv_unsigned dst mod page_size =? 0)%Z = true,
    Ht : (bv_unsigned dst + nZ <=? alloc_top _)%Z = true,
    Hr : region_free _ dst n = true |- _ =>
      apply Z.eqb_eq in Ha; apply Z.leb_le in Ht;
      pose proof (alloc_top_lt (m_vmmaps m));
      pose proof (mremap_charge_le m old old_n dst n Ha ltac:(rewrite Hnw; exact Hnmod)
                    ltac:(rewrite Hnw; exact Hnpos) ltac:(rewrite Hnw; lia)
                    (fun a sz Hin => Hfit a sz (map_remove_In _ old a sz Hin))
                    (region_free_map_remove' _ old _ _ (region_free_app_r' _ _ _ _ Hr))) as Hle
  end.
  rewrite mremap_move_budget_b_relim in Hmove. apply Z.leb_le in Hmove.
  assert (Hg1 : mremap_final_budget_b (relim L m) old old_n dst n = true).
  { rewrite mremap_final_budget_b_relim. apply Z.leb_le. lia. }
  rewrite Hg1, (mremap_final_budget_b_mono L m old old_n dst n HL Hg1). reflexivity.
Qed.

Lemma mremap_source_b_vmrelim : forall L h old old_n old_nZ,
  mremap_source_b (vmrelim L h) old old_n old_nZ = mremap_source_b h old old_n old_nZ.
Proof. reflexivity. Qed.

Lemma mremap_backing_uniform_b_relim : forall L m old old_n,
  mremap_backing_uniform_b (relim L m) old old_n = mremap_backing_uniform_b m old old_n.
Proof. reflexivity. Qed.

Lemma relim_arm_mremap : forall i eff m L,
  (L <= mlim m)%Z ->
  maps_fit m ->
  mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (relim L m) = false ->
  ca_check arm_mremap i eff (relim L m) = cr_map (relim L) (ca_check arm_mremap i eff m).
Proof.
  intros i eff m L HL Hfit Hmk. rewrite !ca_check_arm_mremap. unfold check_mremap.
  unfold mremap_budget_refused_b in Hmk.
  set (old := in_arg i 0) in *. set (old_size := in_arg i 1) in *.
  set (new_size := in_arg i 2) in *. set (flags := in_arg i 3) in *.
  cbv zeta in *.
  rewrite !m_vmmaps_relim, !mremap_source_b_vmrelim, !mremap_backing_uniform_b_relim in *.
  destruct (negb (bv_unsigned flags =? MREMAP_MAYMOVE)%Z); [reflexivity |].
  destruct (negb (bv_unsigned old mod page_size =? 0)%Z); [bm_go_relim |].
  destruct (page_align_is0_b new_size) eqn:Hnew; [bm_go_relim |].
  destruct (page_align_is0_b old_size); [reflexivity |].
  set (old_nZ := page_round_up_Z (bv_unsigned old_size)) in *.
  set (new_nZ := page_round_up_Z (bv_unsigned new_size)) in *.
  set (old_n := Z_to_bv 64 old_nZ) in *.
  set (new_n := Z_to_bv 64 new_nZ) in *.
  destruct (negb (mremap_source_b (m_vmmaps m) old old_n old_nZ
                  && mremap_backing_uniform_b m old old_n)); [reflexivity |].
  destruct (old_nZ =? new_nZ)%Z eqn:Heq; [bm_go_relim |].
  destruct eff as [r l1 zs us cs l5].
  destruct l1 as [|x1 l1]; [| reflexivity].
  destruct l5 as [|x5 l5]; [| reflexivity].
  destruct (errno_ret_in mremap_errnos r); [bm_go_relim |].
  destruct (bv_eqb r old).
  - destruct (new_nZ <? old_nZ)%Z eqn:Hlt; [bm_go_relim |].
    (* [comment removed for export] *)
    apply Z.ltb_ge in Hlt. apply Z.eqb_neq in Heq.
    rewrite (proj2 (Z.leb_gt new_nZ old_nZ) ltac:(lia)) in Hmk.
    apply negb_false_iff, andb_true_iff in Hmk as [Hin Hmv].
    unfold mremap_inplace_grow_b. cbv zeta.
    rewrite !m_vmmaps_relim, !alloc_top_vmrelim. bm_vm_proj.
    rewrite Hin, (mremap_final_budget_b_mono L m old old_n old new_n HL Hin).
    bm_go_relim.
  - destruct (old_nZ <? new_nZ)%Z eqn:Hlt; cbn [andb]; [| reflexivity].
    apply Z.ltb_lt in Hlt.
    rewrite (proj2 (Z.leb_gt new_nZ old_nZ) Hlt) in Hmk.
    apply negb_false_iff, andb_true_iff in Hmk as [Hin Hmv].
    pose proof (mremap_fresh_b_relim L m old_nZ new_size old old_n r HL Hfit Hnew Hmv) as Hf.
    change (page_round_up_Z (bv_unsigned new_size)) with new_nZ in Hf.
    change (Z_to_bv 64 new_nZ) with new_n in Hf.
    rewrite Hf.
    bm_go_relim.
Qed.
End BudgetMonoMremap.
Module BudgetMonoCheck.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoArmsA OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoArmsB OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoArmsC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm BudgetMonoMremap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition arm_ok (c : CheckedArm) : Prop :=
  forall i eff m L,
    (L <= mlim m)%Z -> maps_fit m ->
    ca_no c = bv_unsigned (in_sysno i) ->
    alloc_budget_refused_b i (relim L m) = false ->
    ca_check c i eff (relim L m) = cr_map (relim L) (ca_check c i eff m).

(* [comment removed for export] *)
Lemma revs_frame : forall (f : Model -> check_result),
  (forall S m, f (revs S m) = cr_map (revs S) (f m)) ->
  forall m m' evs, f m = CheckOk m' evs -> m_vm m' = m_vm m.
Proof.
  intros f Hf m m' evs H.
  pose proof (Hf (m_vm m) m) as E. rewrite revs_self, H in E. cbn [cr_map] in E.
  injection E as E. rewrite E at 1. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma revs_relim : forall (f : Model -> check_result),
  (forall S m, f (revs S m) = cr_map (revs S) (f m)) ->
  forall L m, f (relim L m) = cr_map (relim L) (f m).
Proof.
  intros f Hf L m. rewrite relim_as_revs, Hf.
  destruct (f m) as [m' evs| |] eqn:E; cbn [cr_map]; [| reflexivity | reflexivity].
  pose proof (revs_frame f Hf m m' evs E) as Hv. f_equal.
  destruct m' as [fd' vm' io' fs' pr' li' ti']. cbn [m_vm] in Hv. subst vm'.
  reflexivity.
Qed.

Lemma arm_ok_of_revs : forall c,
  (forall i eff m S, ca_check c i eff (revs S m) = cr_map (revs S) (ca_check c i eff m)) ->
  arm_ok c.
Proof.
  intros c H i eff m L _ _ _ _.
  exact (revs_relim (fun m => ca_check c i eff m) (fun S m => H i eff m S) L m).
Qed.

Lemma arm_ok_of_relim : forall c,
  (forall i eff m L, ca_check c i eff (relim L m) = cr_map (relim L) (ca_check c i eff m)) ->
  arm_ok c.
Proof. intros c H i eff m L _ _ _ _. apply H. Qed.

Lemma lookup_ca_In' : forall t n c,
  lookup_ca t n = Some c -> In c t /\ ca_no c = n.
Proof.
  induction t as [|x t IH]; intros n c H; [discriminate H |].
  cbn [lookup_ca] in H. destruct (Z.eqb (ca_no x) n) eqn:E.
  - injection H as <-. split; [left; reflexivity | apply Z.eqb_eq; exact E].
  - destruct (IH n c H) as [Hin Hno]. split; [right; exact Hin | exact Hno].
Qed.

Lemma checked_table_ok : Forall arm_ok checked_table.
Proof.
  unfold checked_table.
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_getcwd |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_eventfd2 |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_epoll_create1 |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_epoll_ctl |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_epoll_pwait |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_dup |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_dup3 |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_fcntl |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_ioctl |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_flock |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_unlinkat |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_ftruncate |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_faccessat |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_openat |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_close |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_pipe2 |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_getdents64 |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_lseek |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_read |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_write |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_readv |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_writev |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_pread64 |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_pwrite64 |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_pselect6 |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_ppoll |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_readlinkat |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_newfstatat |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_fstat |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_fsync |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_fdatasync |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_timerfd_create |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_exit |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_exit_group |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_set_tid_address |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_futex |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_nanosleep |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_clock_gettime |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_sched_setscheduler |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_sched_getaffinity |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_sched_yield |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_tkill |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_tgkill |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_sigaltstack |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_rt_sigaction |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_rt_sigprocmask |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_setgid |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_setuid |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_setresuid |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_setresgid |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_setsid |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_getgroups |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_setgroups |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_uname |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_prctl |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_gettimeofday |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_getpid |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_getuid |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_geteuid |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_getgid |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_getegid |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_gettid |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_socket |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_socketpair |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_bind |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_listen |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_accept |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_connect |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_getsockname |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_getpeername |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_sendto |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_recvfrom |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_setsockopt |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_getsockopt |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_shutdown |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_sendmsg |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_recvmsg |].
  apply Forall_cons.
  { intros i eff m L HL Hfit Hno Hmk.
    assert (Hn : bv_unsigned (in_sysno i) = 214%Z) by (rewrite <- Hno; reflexivity).
    unfold alloc_budget_refused_b in Hmk. cbv zeta in Hmk. rewrite Hn in Hmk. cbn [Z.eqb] in Hmk.
    exact (relim_arm_brk i eff m L HL Hmk). }
  apply Forall_cons; [apply arm_ok_of_relim; exact relim_arm_munmap |].
  apply Forall_cons.
  { intros i eff m L HL Hfit Hno Hmk.
    assert (Hn : bv_unsigned (in_sysno i) = 216%Z) by (rewrite <- Hno; reflexivity).
    unfold alloc_budget_refused_b in Hmk. cbv zeta in Hmk. rewrite Hn in Hmk. cbn [Z.eqb] in Hmk.
    exact (relim_arm_mremap i eff m L HL Hfit Hmk). }
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_clone |].
  apply Forall_cons.
  { intros i eff m L HL Hfit Hno Hmk.
    assert (Hn : bv_unsigned (in_sysno i) = 222%Z) by (rewrite <- Hno; reflexivity).
    unfold alloc_budget_refused_b in Hmk. cbv zeta in Hmk. rewrite Hn in Hmk. cbn [Z.eqb] in Hmk.
    exact (relim_arm_mmap i eff m L HL Hmk). }
  apply Forall_cons.
  { intros i eff m L HL Hfit Hno Hmk.
    assert (Hn : bv_unsigned (in_sysno i) = 226%Z) by (rewrite <- Hno; reflexivity).
    unfold alloc_budget_refused_b in Hmk. cbv zeta in Hmk. rewrite Hn in Hmk. cbn [Z.eqb] in Hmk.
    exact (relim_arm_mprotect i eff m L HL Hmk). }
  apply Forall_cons; [apply arm_ok_of_relim; exact relim_arm_madvise |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_accept4 |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_wait4 |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_prlimit64 |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_getrandom |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_clone3 |].
  apply Forall_cons; [apply arm_ok_of_revs; exact revs_arm_faccessat2 |].
  apply Forall_nil.
Qed.

(* [comment removed for export] *)
Theorem check_syscall_relim : forall i eff m L,
  (L <= mlim m)%Z -> maps_fit m ->
  alloc_budget_refused_b i (relim L m) = false ->
  check_syscall i eff (relim L m) = cr_map (relim L) (check_syscall i eff m).
Proof.
  intros i eff m L HL Hfit Hmk. unfold check_syscall.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [| reflexivity].
  destruct (lookup_ca_In' _ _ _ Elk) as [Hin Hno].
  pose proof checked_table_ok as Hall. rewrite Forall_forall in Hall.
  exact (Hall c Hin i eff m L HL Hfit Hno Hmk).
Qed.
End BudgetMonoCheck.
Require LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BudgetMonoFrameMm.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoDefs BudgetMonoMremap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition fit_list (l : list (word * word)) : Prop :=
  forall (a sz : word), In (a, sz) l -> (bv_unsigned a + bv_unsigned sz <= two_pow_64)%Z.

(* [comment removed for export] *)
Definition vm_pres (m m' : Model) : Prop :=
  mlim m' = mlim m /\ (maps_fit m -> maps_fit m').

Lemma vm_pres_refl : forall m, vm_pres m m.
Proof. intros m. split; [reflexivity | tauto]. Qed.

Lemma vm_pres_vmmaps : forall m m', m_vmmaps m' = m_vmmaps m -> vm_pres m m'.
Proof.
  intros m m' E. split; [unfold mlim; rewrite E; reflexivity |].
  unfold maps_fit. rewrite E. tauto.
Qed.

Lemma vm_pres_intro : forall m m' h',
  m_vmmaps m' = h' ->
  vm_limit h' = vm_limit (m_vmmaps m) ->
  (fit_list (vm_maps (m_vmmaps m)) -> fit_list (vm_maps h')) ->
  vm_pres m m'.
Proof.
  intros m m' h' E Hl Hf. split; [unfold mlim; rewrite E; exact Hl |].
  unfold maps_fit. rewrite E. exact Hf.
Qed.

Lemma fit_cons : forall (a n : word) l,
  (bv_unsigned a + bv_unsigned n <= two_pow_64)%Z -> fit_list l -> fit_list ((a, n) :: l).
Proof.
  intros a n l H Hl b s [E | Hin]; [inversion E; subst; exact H | exact (Hl b s Hin)].
Qed.

Lemma fit_filter : forall f l, fit_list l -> fit_list (List.filter f l).
Proof. intros f l Hl a sz Hin. apply List.filter_In in Hin as [Hin _]. exact (Hl a sz Hin). Qed.

Lemma fit_subtract : forall l lo hi, fit_list l -> fit_list (maps_subtract l lo hi).
Proof.
  intros l lo hi Hl b s Hin.
  destruct (maps_subtract_In l lo hi b s Hin) as [a [sz [Hin0 Hiv]]].
  pose proof (Hl a sz Hin0) as Hf.
  pose proof (iv_subtract_within a sz lo hi b s Hf Hiv). lia.
Qed.

Lemma vm_pres_ret_only : forall eff r m evs0 m' evs,
  check_ret_only eff r m evs0 = CheckOk m' evs -> vm_pres m m'.
Proof. intros. apply check_ret_only_model in H. subst. apply vm_pres_refl. Qed.

Ltac dife H := match type of H with
               | context [ if ?b then _ else _ ] => destruct b
               end.

(* [comment removed for export] *)

Lemma pres_brk : forall req eff m m' evs,
  check_brk req eff m = CheckOk m' evs -> vm_pres m m'.
Proof.
  intros req [ret ws zs us cs ci] m m' evs H.
  unfold check_brk in H.
  destruct ws as [|? ?]; [|discriminate].
  destruct cs as [|? ?]; [|discriminate].
  destruct ci as [|? ?]; [|discriminate].
  destruct (brk_r_ok m req ret
            && listNN_eqb zs (brk_zeros req ret (vm_brk (m_vmmaps m)))
            && listNN_eqb us (brk_unmaps ret (vm_brk (m_vmmaps m)))) eqn:E;
    [|discriminate].
  injection H as <- <-.
  apply (vm_pres_intro _ _ (brk_model_next (m_vmmaps m) req ret)); [apply vmm_brk_next | reflexivity |].
  intros Hf. set (h := m_vmmaps m) in *.
  unfold brk_model_next, brk_maps_next. cbn [vm_maps].
  destruct (Z.ltb 0 (bv_unsigned (vm_brk h))
            && Z.ltb (bv_unsigned ret) (bv_unsigned (vm_brk h))) eqn:Eshrink.
  - apply fit_subtract. exact Hf.
  - unfold brk_grants. destruct (brk_is_grow req ret (vm_brk h)) eqn:Egrow; cbn [app]; [| exact Hf].
    apply fit_cons; [| exact Hf].
    unfold brk_is_grow in Egrow.
    apply andb_true_iff in Egrow as [_ Hlt]. apply Z.ltb_lt in Hlt.
    pose proof (word_range ret) as Hr. pose proof (word_range (vm_brk h)) as Hb.
    assert (Hsz : bv_unsigned (ret - vm_brk h)%bv = (bv_unsigned ret - bv_unsigned (vm_brk h))%Z).
    { rewrite bv_sub_unsigned. apply bv_wrap_small.
      change (bv_modulus 64) with (2 ^ 64)%Z. lia. }
    rewrite Hsz. unfold two_pow_64. lia.
Qed.

(* [comment removed for export] *)

Lemma pres_munmap : forall addr len eff m m' evs,
  check_munmap addr len eff m = CheckOk m' evs -> vm_pres m m'.
Proof.
  intros addr len [ret ws zs us cs ci] m m' evs H.
  unfold check_munmap in H. cbv zeta in H.
  dif H; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
  dif H; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
  dif H.
  - destruct ws, zs, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-.
    eapply vm_pres_intro; [apply vmm_mmap_destroyed | reflexivity |].
    cbn [vm_maps]. intros Hf. unfold map_remove. apply fit_filter. exact Hf.
  - dif H; [exact (vm_pres_ret_only _ _ _ _ _ _ H) | discriminate].
Qed.

Lemma pres_mprotect : forall addr len prot eff m m' evs,
  check_mprotect addr len prot eff m = CheckOk m' evs -> vm_pres m m'.
Proof.
  intros addr len prot [ret ws zs us cs ci] m m' evs H.
  unfold check_mprotect in H. cbv zeta in H.
  dif H; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
  dif H; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
  dif H; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
  dif H; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
  dif H; [discriminate|].
  dif H.
  - destruct ws, us, cs, ci; try discriminate.
    dif H.
    + destruct zs; [|discriminate]. injection H as <- <-. apply vm_pres_refl.
    + dif H; [|discriminate]. injection H as <- <-.
      eapply vm_pres_intro; [apply vmm_mprotect_next | reflexivity |].
      cbn [vm_maps]. tauto.
  - dif H; [|discriminate].
    destruct ws, zs, us, cs, ci; try discriminate.
    dif H; [|discriminate]. injection H as <- <-. apply vm_pres_refl.
Qed.

Lemma pres_madvise : forall addr len advice eff m m' evs,
  check_madvise addr len advice eff m = CheckOk m' evs -> vm_pres m m'.
Proof.
  intros addr len advice eff m m' evs H. apply vm_pres_vmmaps.
  exact (check_madvise_frame addr len advice eff m m' evs H).
Qed.

(* [comment removed for export] *)

Lemma pres_mmap : forall addr len prot flags fd off eff m m' evs,
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs -> vm_pres m m'.
Proof.
  intros addr len prot flags fd off [ret ws zs us cs ci] m m' evs H.
  unfold check_mmap in H. cbv zeta in H.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range len) as Hlenr.
  pose proof (word_range addr) as Haddrr.
  destruct (negb (mmap_off_aligned_b off)) eqn:Eoff.
  { destruct (mmap_pglen_ok_b len); [|discriminate].
    exact (vm_pres_ret_only _ _ _ _ _ _ H). }
  destruct (negb (mmap_anon_b flags)) eqn:Eanon; [discriminate|].
  destruct (w_is0 len) eqn:Elen.
  { destruct (mmap_plain_anon_b flags); [|discriminate].
    exact (vm_pres_ret_only _ _ _ _ _ _ H). }
  pose proof (w_is0_false len Elen) as Hlen0.
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z)
    by (apply page_round_up_pos; lia).
  destruct (mmap_modeled_b prot flags off) eqn:Emod.
  { destruct ws, us, cs, ci; try discriminate.
    dife H.
    { destruct zs; [|discriminate]. injection H as <- <-. apply vm_pres_refl. }
    difn H E; [|discriminate]. injection H as <- <-.
    eapply vm_pres_intro; [rewrite vmm_mmap_backing, vmm_vmmaps; reflexivity | reflexivity |].
    cbn [vm_maps]. intros Hf.
    apply andb_true_iff in E as [E Hzs].
    apply andb_true_iff in E as [E Hbud].
    apply andb_true_iff in E as [E Hfree].
    apply andb_true_iff in E as [E Hceil].
    apply Z.leb_le in Hceil.
    apply fit_cons; [rewrite u64 by lia; unfold two_pow_64; lia | exact Hf]. }
  destruct (mmap_noaccess_b prot flags off) eqn:Enoa.
  { destruct ws, zs, cs, ci; try discriminate.
    dife H.
    { destruct us; [|discriminate]. injection H as <- <-. apply vm_pres_refl. }
    difn H E; [|discriminate]. injection H as <- <-.
    eapply vm_pres_intro; [rewrite vmm_mmap_backing, vmm_vmmaps; reflexivity | reflexivity |].
    cbn [vm_maps]. intros Hf.
    apply andb_true_iff in E as [E Hus].
    apply andb_true_iff in E as [E Hfree].
    apply andb_true_iff in E as [E Hceil].
    apply Z.leb_le in Hceil.
    apply fit_cons; [rewrite u64 by lia; unfold two_pow_64; lia | exact Hf]. }
  destruct (mmap_fixed_noaccess_b prot flags off) eqn:Efix.
  { difn H Enomem; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    difn H Elive.
    - destruct ws, zs, cs, ci; try discriminate.
      dife H.
      + destruct us.
        * injection H as <- <-. apply vm_pres_refl.
        * difn H Edes; [|discriminate]. injection H as <- <-.
          eapply vm_pres_intro; [apply vmm_mmap_destroyed | reflexivity |].
          cbn [vm_maps]. apply fit_subtract.
      + difn H Eok; [|discriminate]. injection H as <- <-.
        eapply vm_pres_intro; [rewrite vmm_mmap_replacement, vmm_vmmaps; reflexivity | reflexivity |].
        cbn [vm_maps]. tauto.
    - difn H Efree.
      + destruct ws, zs, cs, ci; try discriminate.
        dife H.
        * destruct us; [|discriminate]. injection H as <- <-. apply vm_pres_refl.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          eapply vm_pres_intro; [rewrite vmm_mmap_backing, vmm_vmmaps; reflexivity | reflexivity |].
          cbn [vm_maps]. intros Hf.
          apply fit_cons; [rewrite u64 by lia; unfold two_pow_64; lia | exact Hf].
      + difn H Espan; [|discriminate].
        destruct ws, zs, cs, ci; try discriminate.
        dife H.
        * destruct us.
          -- injection H as <- <-. apply vm_pres_refl.
          -- difn H Edes; [|discriminate]. injection H as <- <-.
             eapply vm_pres_intro; [apply vmm_mmap_destroyed | reflexivity |].
             cbn [vm_maps]. apply fit_subtract.
        * difn H Eok; [|discriminate]. injection H as <- <-.
          eapply vm_pres_intro; [rewrite vmm_mmap_replacement, vmm_vmmaps; reflexivity | reflexivity |].
          cbn [vm_maps mmap_fixed_noaccess_span_next]. intros Hf.
          apply fit_cons; [rewrite u64 by lia; unfold two_pow_64; lia | apply fit_subtract; exact Hf]. }
  destruct (mmap_fixed_rw_b prot flags off) eqn:Efixrw.
  2: {
    destruct (mmap_noreplace_noaccess_b prot flags off) eqn:Enrn.
    { difn H Enomem; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
      difn H Eceil; [discriminate|].
      difn H Ealign; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
      difn H Epos; [discriminate|].
      apply negb_false_iff, Z.leb_le in Eceil.
      difn H Efree.
      - destruct ws, zs, cs, ci; try discriminate.
        dife H.
        + destruct us; [|discriminate]. injection H as <- <-. apply vm_pres_refl.
        + difn H Eok; [|discriminate]. injection H as <- <-.
          eapply vm_pres_intro; [rewrite vmm_mmap_backing, vmm_vmmaps; reflexivity | reflexivity |].
          cbn [vm_maps]. intros Hf.
          apply fit_cons; [rewrite u64 by lia; unfold two_pow_64; lia | exact Hf].
      - destruct ws, zs, us, cs, ci; try discriminate.
        difn H Eerr; [|discriminate]. injection H as <- <-. apply vm_pres_refl. }
    destruct (mmap_noreplace_rw_b prot flags off) eqn:Enrr; [|discriminate].
    difn H Enomem; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
    difn H Eceil; [discriminate|].
    difn H Ealign; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
    difn H Epos; [discriminate|].
    apply negb_false_iff, Z.leb_le in Eceil.
    difn H Efree.
    - destruct ws, us, cs, ci; try discriminate.
      dife H.
      + destruct zs; [|discriminate]. injection H as <- <-. apply vm_pres_refl.
      + difn H Eok; [|discriminate]. injection H as <- <-.
        eapply vm_pres_intro; [rewrite vmm_mmap_backing, vmm_vmmaps; reflexivity | reflexivity |].
        cbn [vm_maps]. intros Hf.
        apply fit_cons; [rewrite u64 by lia; unfold two_pow_64; lia | exact Hf].
    - destruct ws, zs, us, cs, ci; try discriminate.
      difn H Eerr; [|discriminate]. injection H as <- <-. apply vm_pres_refl. }
  difn H Enomem; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
  difn H Eceil; [discriminate|].
  difn H Ealign; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
  difn H Epos; [discriminate|].
  apply negb_false_iff, Z.leb_le in Eceil.
  difn H Elive.
  - destruct ws, cs, ci; try discriminate.
    dife H.
    + destruct zs; [|discriminate]. destruct us.
      * injection H as <- <-. apply vm_pres_refl.
      * difn H Edes; [|discriminate]. injection H as <- <-.
        eapply vm_pres_intro; [apply vmm_mmap_destroyed | reflexivity |].
        cbn [vm_maps]. apply fit_subtract.
    + destruct us; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      eapply vm_pres_intro; [rewrite vmm_mmap_replacement, vmm_vmmaps; reflexivity | reflexivity |].
      rewrite vmm_fixed_rw_next. tauto.
  - difn H Efree.
    + destruct ws, us, cs, ci; try discriminate.
      dife H.
      * destruct zs; [|discriminate]. injection H as <- <-. apply vm_pres_refl.
      * difn H Eok; [|discriminate]. injection H as <- <-.
        eapply vm_pres_intro; [rewrite vmm_mmap_backing, vmm_vmmaps; reflexivity | reflexivity |].
        cbn [vm_maps]. intros Hf.
        apply fit_cons; [rewrite u64 by lia; unfold two_pow_64; lia | exact Hf].
    + difn H Espan; [|discriminate].
      destruct ws, cs, ci; try discriminate.
      dife H.
      * destruct zs; [|discriminate]. destruct us.
        -- injection H as <- <-. apply vm_pres_refl.
        -- difn H Edes; [|discriminate]. injection H as <- <-.
           eapply vm_pres_intro; [apply vmm_mmap_destroyed | reflexivity |].
           cbn [vm_maps]. apply fit_subtract.
      * destruct us; [|discriminate].
        difn H Eok; [|discriminate]. injection H as <- <-.
        eapply vm_pres_intro; [rewrite vmm_mmap_replacement, vmm_vmmaps; reflexivity | reflexivity |].
        cbn [vm_maps mmap_fixed_rw_span_next]. intros Hf.
        apply fit_cons; [rewrite u64 by lia; unfold two_pow_64; lia | apply fit_subtract; exact Hf].
Qed.

(* [comment removed for export] *)

Lemma pres_mremap : forall old old_size new_size flags eff m m' evs,
  check_mremap old old_size new_size flags eff m = CheckOk m' evs -> vm_pres m m'.
Proof.
  intros old old_size new_size flags [ret ws zs us cs ci] m m' evs H.
  unfold check_mremap in H. cbv zeta in H.
  pose proof (alloc_top_lt (m_vmmaps m)) as Hac. unfold two_pow_64 in Hac.
  pose proof (word_range old) as Hor.
  pose proof (word_range old_size) as Hos.
  pose proof (word_range new_size) as Hns.
  difn H Eflag; [discriminate|].
  difn H Ealign; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
  difn H Enew; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
  difn H Eold; [discriminate|].
  difn H Esrc; [discriminate|].
  difn H Eeq; [exact (vm_pres_ret_only _ _ _ _ _ _ H)|].
  destruct ws; [|discriminate]. destruct ci; [|discriminate].
  unfold page_align_is0_b in Enew. apply orb_false_iff in Enew as [Enew0 EnewB].
  apply Z.leb_gt in EnewB.
  pose proof (w_is0_false new_size Enew0) as Hnew0.
  assert (HnewZ : (0 < page_round_up_Z (bv_unsigned new_size))%Z)
    by (apply page_round_up_pos; lia).
  apply negb_false_iff in Esrc.
  apply andb_true_iff in Esrc as [Esrc _].
  unfold mremap_source_b in Esrc.
  apply andb_true_iff in Esrc as [Esrc _].
  apply andb_true_iff in Esrc as [Esrc Hhas].
  apply andb_true_iff in Esrc as [Hoceil _].
  apply Z.leb_le in Hoceil.
  assert (HoldZ : (0 <= page_round_up_Z (bv_unsigned old_size))%Z)
    by (apply page_round_up_Z_nonneg; lia).
  destruct (errno_ret_in mremap_errnos ret).
  { destruct zs, us, cs; try discriminate. injection H as <- <-. apply vm_pres_refl. }
  destruct (bv_eqb ret old).
  - difn H Eshrink.
    + difn H Eok; [|discriminate]. injection H as <- <-.
      apply Z.ltb_lt in Eshrink.
      eapply vm_pres_intro; [apply vmm_mremap_next | reflexivity |].
      unfold mremap_maps_next. cbn [vm_maps]. intros Hf.
      apply fit_cons; [rewrite u64 by lia; unfold two_pow_64; lia |].
      unfold map_remove. apply fit_filter. exact Hf.
    + difn H Egrow; [|discriminate].
      difn H Eok; [|discriminate]. injection H as <- <-.
      eapply vm_pres_intro; [apply vmm_mremap_next | reflexivity |].
      unfold mremap_maps_next. cbn [vm_maps]. intros Hf.
      unfold mremap_inplace_grow_b in Egrow. cbv zeta in Egrow.
      apply andb_true_iff in Egrow as [Egrow _].
      apply andb_true_iff in Egrow as [Hgceil Hgfree].
      apply Z.leb_le in Hgceil.
      apply fit_cons; [rewrite u64 by lia; unfold two_pow_64; lia |].
      unfold map_remove. apply fit_filter. exact Hf.
  - difn H Emove; [|discriminate]. injection H as <- <-.
    eapply vm_pres_intro; [apply vmm_mremap_next | reflexivity |].
    unfold mremap_maps_next. cbn [vm_maps]. intros Hf.
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [Emove _].
    apply andb_true_iff in Emove as [_ Hfresh].
    unfold mremap_fresh_b in Hfresh. cbv zeta in Hfresh.
    apply andb_true_iff in Hfresh as [Hfresh _].
    apply andb_true_iff in Hfresh as [Hfresh Hffree].
    apply andb_true_iff in Hfresh as [Hfresh Hfceil].
    apply Z.leb_le in Hfceil.
    apply fit_cons; [rewrite u64 by lia; unfold two_pow_64; lia |].
    unfold map_remove. apply fit_filter. exact Hf.
Qed.
End BudgetMonoFrameMm.
Module BudgetMonoFrame.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoArmsA OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoArmsB OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoArmsC BudgetMonoMremap BudgetMonoCheck BudgetMonoFrameMm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition arm_pres (c : CheckedArm) : Prop :=
  forall i eff m m' evs, ca_check c i eff m = CheckOk m' evs -> vm_pres m m'.

Lemma arm_pres_of_revs : forall c,
  (forall i eff m S, ca_check c i eff (revs S m) = cr_map (revs S) (ca_check c i eff m)) ->
  arm_pres c.
Proof.
  intros c H i eff m m' evs E. apply vm_pres_vmmaps.
  pose proof (revs_frame (fun m => ca_check c i eff m) (fun S m => H i eff m S) m m' evs E) as Hv.
  unfold m_vmmaps. rewrite Hv. reflexivity.
Qed.

Lemma checked_table_pres : Forall arm_pres checked_table.
Proof.
  unfold checked_table.
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_getcwd |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_eventfd2 |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_epoll_create1 |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_epoll_ctl |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_epoll_pwait |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_dup |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_dup3 |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_fcntl |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_ioctl |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_flock |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_unlinkat |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_ftruncate |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_faccessat |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_openat |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_close |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_pipe2 |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_getdents64 |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_lseek |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_read |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_write |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_readv |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_writev |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_pread64 |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_pwrite64 |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_pselect6 |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_ppoll |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_readlinkat |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_newfstatat |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_fstat |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_fsync |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_fdatasync |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_timerfd_create |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_exit |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_exit_group |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_set_tid_address |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_futex |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_nanosleep |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_clock_gettime |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_sched_setscheduler |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_sched_getaffinity |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_sched_yield |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_tkill |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_tgkill |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_sigaltstack |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_rt_sigaction |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_rt_sigprocmask |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_setgid |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_setuid |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_setresuid |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_setresgid |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_setsid |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_getgroups |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_setgroups |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_uname |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_prctl |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_gettimeofday |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_getpid |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_getuid |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_geteuid |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_getgid |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_getegid |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_gettid |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_socket |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_socketpair |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_bind |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_listen |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_accept |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_connect |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_getsockname |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_getpeername |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_sendto |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_recvfrom |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_setsockopt |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_getsockopt |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_shutdown |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_sendmsg |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_recvmsg |].
  apply Forall_cons; [intros i eff m m' evs E; rewrite ca_check_arm_brk in E; eapply pres_brk; exact E |].
  apply Forall_cons; [intros i eff m m' evs E; rewrite ca_check_arm_munmap in E; eapply pres_munmap; exact E |].
  apply Forall_cons; [intros i eff m m' evs E; rewrite ca_check_arm_mremap in E; eapply pres_mremap; exact E |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_clone |].
  apply Forall_cons; [intros i eff m m' evs E; rewrite ca_check_arm_mmap in E; eapply pres_mmap; exact E |].
  apply Forall_cons; [intros i eff m m' evs E; rewrite ca_check_arm_mprotect in E; eapply pres_mprotect; exact E |].
  apply Forall_cons; [intros i eff m m' evs E; rewrite ca_check_arm_madvise in E; eapply pres_madvise; exact E |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_accept4 |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_wait4 |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_prlimit64 |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_getrandom |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_clone3 |].
  apply Forall_cons; [apply arm_pres_of_revs; exact revs_arm_faccessat2 |].
  apply Forall_nil.
Qed.

Theorem check_syscall_pres : forall i eff m m' evs,
  check_syscall i eff m = CheckOk m' evs -> vm_pres m m'.
Proof.
  intros i eff m m' evs H. unfold check_syscall in H.
  destruct (lookup_ca checked_table (bv_unsigned (in_sysno i))) as [c|] eqn:Elk;
    [| discriminate H].
  destruct (lookup_ca_In' _ _ _ Elk) as [Hin _].
  pose proof checked_table_pres as Hall. rewrite Forall_forall in Hall.
  exact (Hall c Hin i eff m m' evs H).
Qed.
End BudgetMonoFrame.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BudgetMonoStep.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoDefs BudgetMonoMremap BudgetMonoCheck BudgetMonoFrameMm BudgetMonoFrame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)

Lemma materialize_accesses_mono : forall lz mat used L L' acc p,
  materialize_accesses lz mat used L acc = Some p -> (L <= L')%Z ->
  materialize_accesses lz mat used L' acc = Some p.
Proof.
  intros lz mat used L L' acc p H HL. unfold materialize_accesses in *. cbv zeta in *.
  destruct (newly_materialized_pages lz mat acc) as [|x r]; [exact H |].
  destruct (used + Z.of_nat (length (x :: r)) * page_size <=? L)%Z eqn:E; [| discriminate H].
  apply Z.leb_le in E.
  assert (E' : (used + Z.of_nat (length (x :: r)) * page_size <=? L')%Z = true)
    by (apply Z.leb_le; lia).
  rewrite E'. exact H.
Qed.

Lemma mat_relim : forall L m acc,
  materialize_model_accesses (relim L m) acc =
  match materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) L acc with
  | Some pages => Some (relim L (with_vm_backing (m_vm_lazy m) pages m))
  | None => None
  end.
Proof. reflexivity. Qed.

Lemma mat_plain : forall m acc,
  materialize_model_accesses m acc =
  match materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) (mlim m) acc with
  | Some pages => Some (with_vm_backing (m_vm_lazy m) pages m)
  | None => None
  end.
Proof. reflexivity. Qed.

Lemma mat_relim_some : forall L m acc x,
  (L <= mlim m)%Z ->
  materialize_model_accesses (relim L m) acc = Some x ->
  exists y, materialize_model_accesses m acc = Some y /\ x = relim L y.
Proof.
  intros L m acc x HL H. rewrite mat_relim in H. rewrite mat_plain.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) L acc)
    as [p|] eqn:E; [| discriminate H].
  injection H as <-. rewrite (materialize_accesses_mono _ _ _ _ _ _ _ E HL).
  eexists. split; reflexivity.
Qed.

Lemma mat_some_relim : forall L m acc y,
  (L <= mlim m)%Z ->
  materialize_model_accesses m acc = Some y ->
  materialize_model_accesses (relim L m) acc = None
  \/ materialize_model_accesses (relim L m) acc = Some (relim L y).
Proof.
  intros L m acc y HL H. rewrite mat_relim. rewrite mat_plain in H.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) L acc)
    as [p|] eqn:E; [| left; reflexivity].
  right. rewrite (materialize_accesses_mono _ _ _ _ _ _ _ E HL) in H.
  injection H as <-. reflexivity.
Qed.

Lemma mat_none_relim : forall L m acc,
  (L <= mlim m)%Z ->
  materialize_model_accesses m acc = None ->
  materialize_model_accesses (relim L m) acc = None.
Proof.
  intros L m acc HL H. rewrite mat_relim. rewrite mat_plain in H.
  destruct (materialize_accesses (m_vm_lazy m) (m_vm_materialized m) (vm_backing_used m) L acc)
    as [p|] eqn:E; [| reflexivity].
  rewrite (materialize_accesses_mono _ _ _ _ _ _ _ E HL) in H. discriminate H.
Qed.

Lemma mat_pres : forall m acc y,
  materialize_model_accesses m acc = Some y -> vm_pres m y.
Proof.
  intros m acc y H. apply vm_pres_vmmaps.
  exact (proj1 (proj2 (materialize_model_accesses_frame m acc y H))).
Qed.

Lemma vm_pres_trans : forall m1 m2 m3, vm_pres m1 m2 -> vm_pres m2 m3 -> vm_pres m1 m3.
Proof.
  intros m1 m2 m3 [H1 H1'] [H2 H2']. split; [congruence | tauto].
Qed.

(* [comment removed for export] *)

Lemma cr_map_ok_inv : forall f r m1 evs,
  cr_map f r = CheckOk m1 evs -> exists m2, r = CheckOk m2 evs /\ m1 = f m2.
Proof.
  intros f [m2 evs2| |] m1 evs H; cbn [cr_map] in H; try discriminate H.
  injection H as <- <-. eexists. split; reflexivity.
Qed.

Lemma cr_map_unmodeled_inv : forall f r, cr_map f r = CheckUnmodeled -> r = CheckUnmodeled.
Proof. intros f [m2 evs2| |] H; cbn [cr_map] in H; try discriminate H. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma spec_relim_down : forall i m L eff m1 evs,
  (L <= mlim m)%Z -> maps_fit m ->
  alloc_budget_refused_b i (relim L m) = false ->
  syscall_spec i (relim L m) (Ok eff m1 evs) ->
  exists m2, syscall_spec i m (Ok eff m2 evs) /\ m1 = relim L m2.
Proof.
  intros i m L eff m1 evs HL Hfit Hmk H.
  apply check_syscall_ok_iff in H. rewrite (check_syscall_relim i eff m L HL Hfit Hmk) in H.
  destruct (cr_map_ok_inv _ _ _ _ H) as [m2 [E ->]].
  exists m2. split; [apply check_syscall_ok_iff; exact E | reflexivity].
Qed.

Lemma spec_relim_up : forall i m L eff m2 evs,
  (L <= mlim m)%Z -> maps_fit m ->
  alloc_budget_refused_b i (relim L m) = false ->
  syscall_spec i m (Ok eff m2 evs) ->
  syscall_spec i (relim L m) (Ok eff (relim L m2) evs).
Proof.
  intros i m L eff m2 evs HL Hfit Hmk H.
  apply check_syscall_ok_iff in H. apply check_syscall_ok_iff.
  rewrite (check_syscall_relim i eff m L HL Hfit Hmk), H. reflexivity.
Qed.

Lemma spec_unmodeled_relim : forall i m L,
  (L <= mlim m)%Z -> maps_fit m ->
  alloc_budget_refused_b i (relim L m) = false ->
  (syscall_spec i (relim L m) Unmodeled <-> syscall_spec i m Unmodeled).
Proof.
  intros i m L HL Hfit Hmk.
  set (e0 := mkEffectU (Z_to_bv 64 0) [] [] [] [] []).
  rewrite <- (check_syscall_err_iff i e0 (relim L m)), <- (check_syscall_err_iff i e0 m).
  rewrite (check_syscall_relim i e0 m L HL Hfit Hmk). split.
  - apply cr_map_unmodeled_inv.
  - intros ->. reflexivity.
Qed.

Lemma spec_pres : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) -> vm_pres m m'.
Proof.
  intros i m eff m' evs H. apply check_syscall_ok_iff in H. exact (check_syscall_pres _ _ _ _ _ H).
Qed.

(* [comment removed for export] *)

Ltac sstep_cases H :=
  destruct H as [ms0 model0 ms' model' Hh Hs Ha | ms0 model0 Hh Hs Ha | ms0 model0 Hh Hs Ha
                | ms0 model0 x8 eff model' model'' evs Hh Hs Hsp Hh' Hm
                | ms0 model0 x8 eff model' evs Hh Hs Hsp Hh' Hm
                | ms0 model0 x8 eff model' evs code Hh Hs Hsp Hh' Hk
                | ms0 model0 x8 eff model' evs sig Hh Hs Hsp Hk
                | ms0 model0 x8 Hh Hs Hsp].

Theorem sstep_pres : forall c e c',
  sstep segs c e (SNext c') -> vm_pres (cfg_model c) (cfg_model c').
Proof.
  intros c e c' H. remember (SNext c') as st eqn:Est.
  sstep_cases H; try discriminate Est; injection Est as <-; cbn [cfg_model].
  - apply vm_pres_vmmaps.
    exact (proj1 (proj2 (mi_account_step_model_frame segs ms0 model0 ms' model' Ha))).
  - eapply vm_pres_trans; [eapply spec_pres; eassumption | eapply mat_pres; eassumption].
  - eapply spec_pres; eassumption.
  - eapply spec_pres; eassumption.
Qed.

(* [comment removed for export] *)

Lemma budget_refused_syscall_mark : forall ms model x8,
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  ~ budget_refused_at segs (mkCfg ms model) ->
  alloc_budget_refused_b (sys_input segs ms x8) model = false.
Proof.
  intros ms model x8 Hh Hx H. destruct (alloc_budget_refused_b (sys_input segs ms x8) model) eqn:E;
    [| reflexivity].
  exfalso. apply H. split; [exact Hh |]. right. exists x8. split; [exact Hx | left; exact E].
Qed.

Lemma budget_refused_syscall_mat : forall ms model x8 eff m1 evs,
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  ~ budget_refused_at segs (mkCfg ms model) ->
  syscall_spec (sys_input segs ms x8) model (Ok eff m1 evs) ->
  m_halted m1 = None ->
  materialize_model_accesses m1 (syscall_effect_accesses eff) <> None.
Proof.
  intros ms model x8 eff m1 evs Hh Hx H Hs Hh1 Hm. apply H. split; [exact Hh |].
  right. exists x8. split; [exact Hx |]. right. exists eff, m1, evs. tauto.
Qed.

Lemma budget_refused_instr_mat : forall ms model report,
  m_halted model = None -> ms_svc_pending ms = None ->
  ~ budget_refused_at segs (mkCfg ms model) ->
  step_accesses segs ms = MachineOk report ->
  materialize_model_accesses model (@accessed_ranges _ report) <> None.
Proof.
  intros ms model report Hh Hx H Hs Hm. apply H. split; [exact Hh |].
  left. split; [exact Hx |]. exists report. split; assumption.
Qed.

Theorem sstep_relim_down : forall L c e st1,
  (L <= mlim (cfg_model c))%Z -> maps_fit (cfg_model c) ->
  ~ budget_refused_at segs (relimc L c) ->
  sstep segs (relimc L c) e st1 ->
  exists st2, sstep segs c e st2 /\ st1 = relims L st2.
Proof.
  intros L [ms model] e st1 HL Hfit Hnb H. cbn [cfg_model] in HL, Hfit.
  unfold relimc in H, Hnb. cbn [cfg_ms cfg_model] in H, Hnb.
  remember (mkCfg ms (relim L model)) as c0 eqn:Ec.
  sstep_cases H; injection Ec as -> ->.
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Es; try discriminate Ha.
    destruct (materialize_model_accesses (relim L model) (@accessed_ranges _ report))
      as [x|] eqn:Em; [| discriminate Ha].
    injection Ha as <- <-.
    destruct (mat_relim_some L model _ x HL Em) as [y [Ey ->]].
    exists (SNext (mkCfg (@access_value _ report) y)). split; [| reflexivity].
    apply sstep_instr; [exact Hh | exact Hs |].
    unfold mi_account_step. rewrite Es, Ey. reflexivity.
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Es; try discriminate Ha.
    + destruct (materialize_model_accesses (relim L model) (@accessed_ranges _ report))
        eqn:Em; [discriminate Ha |].
      exfalso. exact (budget_refused_instr_mat ms (relim L model) report Hh Hs Hnb Es Em).
    + exists SError. split; [| reflexivity].
      apply sstep_instr_fault; [exact Hh | exact Hs |].
      unfold mi_account_step. rewrite Es. reflexivity.
  - (* [comment removed for export] *)
    exists SError. split; [| reflexivity].
    apply sstep_instr_unmodeled; [exact Hh | exact Hs |].
    unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report| |] eqn:Es; try discriminate Ha.
    + destruct (materialize_model_accesses (relim L model) (@accessed_ranges _ report));
        discriminate Ha.
    + reflexivity.
  - (* [comment removed for export] *)
    pose proof (budget_refused_syscall_mark ms _ x8 Hh Hs Hnb) as Hmk.
    destruct (spec_relim_down _ model L eff model' evs HL Hfit Hmk Hsp) as [m2 [Hs2 ->]].
    destruct (spec_pres _ _ _ _ _ Hs2) as [Hl2 Hf2].
    destruct (mat_relim_some L m2 _ model'' ltac:(rewrite Hl2; exact HL) Hm) as [y [Ey ->]].
    exists (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) y)). split; [| reflexivity].
    eapply sstep_syscall; [exact Hh | exact Hs | exact Hs2 | exact Hh' | exact Ey].
  - (* [comment removed for export] *)
    exfalso. exact (budget_refused_syscall_mat ms _ x8 eff model' evs Hh Hs Hnb Hsp Hh' Hm).
  - (* [comment removed for export] *)
    pose proof (budget_refused_syscall_mark ms _ x8 Hh Hs Hnb) as Hmk.
    destruct (spec_relim_down _ model L eff model' evs HL Hfit Hmk Hsp) as [m2 [Hs2 ->]].
    exists (SNext (mkCfg ms m2)). split; [| reflexivity].
    change (m_fs (relim L m2)) with (m_fs m2).
    eapply sstep_exit; [exact Hh | exact Hs | exact Hs2 | exact Hh' | exact Hk].
  - (* [comment removed for export] *)
    pose proof (budget_refused_syscall_mark ms _ x8 Hh Hs Hnb) as Hmk.
    destruct (spec_relim_down _ model L eff model' evs HL Hfit Hmk Hsp) as [m2 [Hs2 ->]].
    exists (SNext (mkCfg ms m2)). split; [| reflexivity].
    change (m_fs (relim L m2)) with (m_fs m2).
    eapply sstep_killed; [exact Hh | exact Hs | exact Hs2 | exact Hk].
  - (* [comment removed for export] *)
    pose proof (budget_refused_syscall_mark ms _ x8 Hh Hs Hnb) as Hmk.
    exists SError. split; [| reflexivity].
    eapply sstep_syscall_unmodeled; [exact Hh | exact Hs |].
    apply (proj1 (spec_unmodeled_relim _ model L HL Hfit Hmk)). exact Hsp.
Qed.

Theorem sstep_relim_up : forall L c e st2,
  (L <= mlim (cfg_model c))%Z -> maps_fit (cfg_model c) ->
  ~ budget_refused_at segs (relimc L c) ->
  sstep segs c e st2 ->
  sstep segs (relimc L c) e (relims L st2).
Proof.
  intros L [ms model] e st2 HL Hfit Hnb H. cbn [cfg_model] in HL, Hfit.
  unfold relimc in Hnb |- *. cbn [cfg_ms cfg_model] in Hnb |- *.
  remember (mkCfg ms model) as c0 eqn:Ec.
  sstep_cases H; injection Ec as -> ->; cbn [relims relimc cfg_ms cfg_model].
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Es; try discriminate Ha.
    destruct (materialize_model_accesses model (@accessed_ranges _ report))
      as [y|] eqn:Em; [| discriminate Ha].
    injection Ha as <- <-.
    destruct (mat_some_relim L model _ y HL Em) as [En | Es'].
    + exfalso. exact (budget_refused_instr_mat ms (relim L model) report Hh Hs Hnb Es En).
    + apply sstep_instr; [exact Hh | exact Hs |].
      unfold mi_account_step. rewrite Es, Es'. reflexivity.
  - (* [comment removed for export] *)
    unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Es; try discriminate Ha.
    + destruct (materialize_model_accesses model (@accessed_ranges _ report)) eqn:Em;
        [discriminate Ha |].
      exfalso. exact (budget_refused_instr_mat ms (relim L model) report Hh Hs Hnb Es
                        (mat_none_relim L model _ HL Em)).
    + apply sstep_instr_fault; [exact Hh | exact Hs |].
      unfold mi_account_step. rewrite Es. reflexivity.
  - (* [comment removed for export] *)
    apply sstep_instr_unmodeled; [exact Hh | exact Hs |].
    unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report| |] eqn:Es; try discriminate Ha.
    + destruct (materialize_model_accesses model (@accessed_ranges _ report));
        discriminate Ha.
    + reflexivity.
  - (* [comment removed for export] *)
    pose proof (budget_refused_syscall_mark ms (relim L model) x8 Hh Hs Hnb) as Hmk.
    pose proof (spec_relim_up _ model L eff model' evs HL Hfit Hmk Hsp) as Hs1.
    destruct (spec_pres _ _ _ _ _ Hsp) as [Hl2 Hf2].
    destruct (mat_some_relim L model' _ model'' ltac:(rewrite Hl2; exact HL) Hm) as [En | Es'].
    + exfalso. exact (budget_refused_syscall_mat ms (relim L model) x8 eff (relim L model') evs Hh Hs Hnb Hs1 Hh' En).
    + eapply sstep_syscall; [exact Hh | exact Hs | exact Hs1 | exact Hh' | exact Es'].
  - (* [comment removed for export] *)
    pose proof (budget_refused_syscall_mark ms (relim L model) x8 Hh Hs Hnb) as Hmk.
    pose proof (spec_relim_up _ model L eff model' evs HL Hfit Hmk Hsp) as Hs1.
    destruct (spec_pres _ _ _ _ _ Hsp) as [Hl2 Hf2].
    exfalso. exact (budget_refused_syscall_mat ms (relim L model) x8 eff (relim L model') evs Hh Hs Hnb Hs1 Hh'
                      (mat_none_relim L model' _ ltac:(rewrite Hl2; exact HL) Hm)).
  - (* [comment removed for export] *)
    pose proof (budget_refused_syscall_mark ms (relim L model) x8 Hh Hs Hnb) as Hmk.
    pose proof (spec_relim_up _ model L eff model' evs HL Hfit Hmk Hsp) as Hs1.
    change (m_fs model') with (m_fs (relim L model')).
    eapply sstep_exit; [exact Hh | exact Hs | exact Hs1 | exact Hh' | exact Hk].
  - (* [comment removed for export] *)
    pose proof (budget_refused_syscall_mark ms (relim L model) x8 Hh Hs Hnb) as Hmk.
    pose proof (spec_relim_up _ model L eff model' evs HL Hfit Hmk Hsp) as Hs1.
    change (m_fs model') with (m_fs (relim L model')).
    eapply sstep_killed; [exact Hh | exact Hs | exact Hs1 | exact Hk].
  - (* [comment removed for export] *)
    pose proof (budget_refused_syscall_mark ms (relim L model) x8 Hh Hs Hnb) as Hmk.
    eapply sstep_syscall_unmodeled; [exact Hh | exact Hs |].
    apply (proj2 (spec_unmodeled_relim _ model L HL Hfit Hmk)). exact Hsp.
Qed.

Lemma refusal_b_relim : forall i m L r, refusal_b i (relim L m) r = refusal_b i m r.
Proof. reflexivity. Qed.

Lemma spurious_relim : forall sc i m L eff,
  (L <= mlim m)%Z -> maps_fit m ->
  alloc_budget_refused_b i (relim L m) = false ->
  (spurious_refusal_cfg sc i (relim L m) eff <-> spurious_refusal_cfg sc i m eff).
Proof.
  intros sc i m L eff HL Hfit Hmk.
  split; intros (Hoff & Hr & (eff' & m' & evs' & Hs & Hnr)).
  - rewrite refusal_b_relim in Hr. rewrite refusal_b_relim in Hnr.
    destruct (spec_relim_down i m L eff' m' evs' HL Hfit Hmk Hs) as [m2 [Hs2 _]].
    split; [exact Hoff |]. split; [exact Hr |].
    exists eff', m2, evs'. split; [exact Hs2 | exact Hnr].
  - split; [exact Hoff |]. split; [rewrite refusal_b_relim; exact Hr |].
    exists eff', (relim L m'), evs'.
    split; [exact (spec_relim_up i m L eff' m' evs' HL Hfit Hmk Hs) | rewrite refusal_b_relim; exact Hnr].
Qed.

Theorem sstep_cfg_pres : forall sc c e c',
  sstep_cfg segs sc c e (SNext c') -> vm_pres (cfg_model c) (cfg_model c').
Proof.
  intros sc c e c' H. exact (sstep_pres c e c' (sstep_cfg_sub segs sc c e (SNext c') H)).
Qed.

Ltac sstep_cfg_cases H :=
  destruct H as [ms0 model0 ms' model' Hh Hs Ha | ms0 model0 Hh Hs Ha | ms0 model0 Hh Hs Ha
                | ms0 model0 x8 eff model' model'' evs Hh Hs Hsp Hns Hh' Hm
                | ms0 model0 x8 eff model' evs Hh Hs Hsp Hns Hh' Hm
                | ms0 model0 x8 eff model' evs code Hh Hs Hsp Hh' Hk
                | ms0 model0 x8 eff model' evs sig Hh Hs Hsp Hk
                | ms0 model0 x8 Hh Hs Hsp].

Theorem sstep_cfg_relim_down : forall sc L c e st1,
  (L <= mlim (cfg_model c))%Z -> maps_fit (cfg_model c) ->
  ~ budget_refused_at segs (relimc L c) ->
  sstep_cfg segs sc (relimc L c) e st1 ->
  exists st2, sstep_cfg segs sc c e st2 /\ st1 = relims L st2.
Proof.
  intros sc L [ms model] e st1 HL Hfit Hnb H. cbn [cfg_model] in HL, Hfit.
  unfold relimc in H, Hnb. cbn [cfg_ms cfg_model] in H, Hnb.
  remember (mkCfg ms (relim L model)) as c0 eqn:Ec.
  sstep_cfg_cases H; injection Ec as -> ->.
  - unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Es; try discriminate Ha.
    destruct (materialize_model_accesses (relim L model) (@accessed_ranges _ report))
      as [x|] eqn:Em; [| discriminate Ha].
    injection Ha as <- <-.
    destruct (mat_relim_some L model _ x HL Em) as [y [Ey ->]].
    exists (SNext (mkCfg (@access_value _ report) y)). split; [| reflexivity].
    apply sstep_cfg_instr; [exact Hh | exact Hs |].
    unfold mi_account_step. rewrite Es, Ey. reflexivity.
  - unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Es; try discriminate Ha.
    + destruct (materialize_model_accesses (relim L model) (@accessed_ranges _ report))
        eqn:Em; [discriminate Ha |].
      exfalso. exact (budget_refused_instr_mat ms (relim L model) report Hh Hs Hnb Es Em).
    + exists SError. split; [| reflexivity].
      apply sstep_cfg_instr_fault; [exact Hh | exact Hs |].
      unfold mi_account_step. rewrite Es. reflexivity.
  - exists SError. split; [| reflexivity].
    apply sstep_cfg_instr_unmodeled; [exact Hh | exact Hs |].
    unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report| |] eqn:Es; try discriminate Ha.
    + destruct (materialize_model_accesses (relim L model) (@accessed_ranges _ report));
        discriminate Ha.
    + reflexivity.
  - pose proof (budget_refused_syscall_mark ms _ x8 Hh Hs Hnb) as Hmk.
    destruct (spec_relim_down _ model L eff model' evs HL Hfit Hmk Hsp) as [m2 [Hs2 ->]].
    destruct (spec_pres _ _ _ _ _ Hs2) as [Hl2 Hf2].
    destruct (mat_relim_some L m2 _ model'' ltac:(rewrite Hl2; exact HL) Hm) as [y [Ey ->]].
    exists (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) y)). split; [| reflexivity].
    eapply sstep_cfg_syscall; [exact Hh | exact Hs | exact Hs2 | | exact Hh' | exact Ey].
    intros Hsp'. apply Hns. exact (proj2 (spurious_relim sc _ model L eff HL Hfit Hmk) Hsp').
  - exfalso. exact (budget_refused_syscall_mat ms _ x8 eff model' evs Hh Hs Hnb Hsp Hh' Hm).
  - pose proof (budget_refused_syscall_mark ms _ x8 Hh Hs Hnb) as Hmk.
    destruct (spec_relim_down _ model L eff model' evs HL Hfit Hmk Hsp) as [m2 [Hs2 ->]].
    exists (SNext (mkCfg ms m2)). split; [| reflexivity].
    change (m_fs (relim L m2)) with (m_fs m2).
    eapply sstep_cfg_exit; [exact Hh | exact Hs | exact Hs2 | exact Hh' | exact Hk].
  - pose proof (budget_refused_syscall_mark ms _ x8 Hh Hs Hnb) as Hmk.
    destruct (spec_relim_down _ model L eff model' evs HL Hfit Hmk Hsp) as [m2 [Hs2 ->]].
    exists (SNext (mkCfg ms m2)). split; [| reflexivity].
    change (m_fs (relim L m2)) with (m_fs m2).
    eapply sstep_cfg_killed; [exact Hh | exact Hs | exact Hs2 | exact Hk].
  - pose proof (budget_refused_syscall_mark ms _ x8 Hh Hs Hnb) as Hmk.
    exists SError. split; [| reflexivity].
    eapply sstep_cfg_syscall_unmodeled; [exact Hh | exact Hs |].
    apply (proj1 (spec_unmodeled_relim _ model L HL Hfit Hmk)). exact Hsp.
Qed.

Theorem sstep_cfg_relim_up : forall sc L c e st2,
  (L <= mlim (cfg_model c))%Z -> maps_fit (cfg_model c) ->
  ~ budget_refused_at segs (relimc L c) ->
  sstep_cfg segs sc c e st2 ->
  sstep_cfg segs sc (relimc L c) e (relims L st2).
Proof.
  intros sc L [ms model] e st2 HL Hfit Hnb H. cbn [cfg_model] in HL, Hfit.
  unfold relimc in Hnb |- *. cbn [cfg_ms cfg_model] in Hnb |- *.
  remember (mkCfg ms model) as c0 eqn:Ec.
  sstep_cfg_cases H; injection Ec as -> ->; cbn [relims relimc cfg_ms cfg_model].
  - unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Es; try discriminate Ha.
    destruct (materialize_model_accesses model (@accessed_ranges _ report))
      as [y|] eqn:Em; [| discriminate Ha].
    injection Ha as <- <-.
    destruct (mat_some_relim L model _ y HL Em) as [En | Es'].
    + exfalso. exact (budget_refused_instr_mat ms (relim L model) report Hh Hs Hnb Es En).
    + apply sstep_cfg_instr; [exact Hh | exact Hs |].
      unfold mi_account_step. rewrite Es, Es'. reflexivity.
  - unfold mi_account_step in Ha.
    destruct (step_accesses segs ms) as [report| |] eqn:Es; try discriminate Ha.
    + destruct (materialize_model_accesses model (@accessed_ranges _ report)) eqn:Em;
        [discriminate Ha |].
      exfalso. exact (budget_refused_instr_mat ms (relim L model) report Hh Hs Hnb Es
                        (mat_none_relim L model _ HL Em)).
    + apply sstep_cfg_instr_fault; [exact Hh | exact Hs |].
      unfold mi_account_step. rewrite Es. reflexivity.
  - apply sstep_cfg_instr_unmodeled; [exact Hh | exact Hs |].
    unfold mi_account_step in *.
    destruct (step_accesses segs ms) as [report| |] eqn:Es; try discriminate Ha.
    + destruct (materialize_model_accesses model (@accessed_ranges _ report));
        discriminate Ha.
    + reflexivity.
  - pose proof (budget_refused_syscall_mark ms (relim L model) x8 Hh Hs Hnb) as Hmk.
    pose proof (spec_relim_up _ model L eff model' evs HL Hfit Hmk Hsp) as Hs1.
    destruct (spec_pres _ _ _ _ _ Hsp) as [Hl2 Hf2].
    destruct (mat_some_relim L model' _ model'' ltac:(rewrite Hl2; exact HL) Hm) as [En | Es'].
    + exfalso. exact (budget_refused_syscall_mat ms (relim L model) x8 eff (relim L model') evs Hh Hs Hnb Hs1 Hh' En).
    + eapply sstep_cfg_syscall; [exact Hh | exact Hs | exact Hs1 | | exact Hh' | exact Es'].
      intros Hsp'. apply Hns. exact (proj1 (spurious_relim sc _ model L eff HL Hfit Hmk) Hsp').
  - pose proof (budget_refused_syscall_mark ms (relim L model) x8 Hh Hs Hnb) as Hmk.
    pose proof (spec_relim_up _ model L eff model' evs HL Hfit Hmk Hsp) as Hs1.
    destruct (spec_pres _ _ _ _ _ Hsp) as [Hl2 Hf2].
    exfalso. exact (budget_refused_syscall_mat ms (relim L model) x8 eff (relim L model') evs Hh Hs Hnb Hs1 Hh'
                      (mat_none_relim L model' _ ltac:(rewrite Hl2; exact HL) Hm)).
  - pose proof (budget_refused_syscall_mark ms (relim L model) x8 Hh Hs Hnb) as Hmk.
    pose proof (spec_relim_up _ model L eff model' evs HL Hfit Hmk Hsp) as Hs1.
    change (m_fs model') with (m_fs (relim L model')).
    eapply sstep_cfg_exit; [exact Hh | exact Hs | exact Hs1 | exact Hh' | exact Hk].
  - pose proof (budget_refused_syscall_mark ms (relim L model) x8 Hh Hs Hnb) as Hmk.
    pose proof (spec_relim_up _ model L eff model' evs HL Hfit Hmk Hsp) as Hs1.
    change (m_fs model') with (m_fs (relim L model')).
    eapply sstep_cfg_killed; [exact Hh | exact Hs | exact Hs1 | exact Hk].
  - pose proof (budget_refused_syscall_mark ms (relim L model) x8 Hh Hs Hnb) as Hmk.
    eapply sstep_cfg_syscall_unmodeled; [exact Hh | exact Hs |].
    apply (proj2 (spec_unmodeled_relim _ model L HL Hfit Hmk)). exact Hsp.
Qed.

End WithSegs.
End BudgetMonoStep.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BudgetMonoRun.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BudgetMonoMm.BudgetMonoDefs BudgetMonoMremap BudgetMonoFrameMm BudgetMonoStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section Bridge.
Variable segs : list Segment.
Variable L : Z.

Definition good (c : config) : Prop :=
  (L <= mlim (cfg_model c))%Z /\ maps_fit (cfg_model c)
  /\ ~ reaches_budget_refused_cfg segs CfgStep.kit_cfg (relimc L c).

Lemma good_not_refused : forall c, good c -> ~ budget_refused_at segs (relimc L c).
Proof.
  intros c (_ & _ & H) Hb. apply H. exists [], (relimc L c). split; [apply star_cfg_refl | exact Hb].
Qed.

Lemma good_up : forall c e st, good c -> sstep_cfg segs CfgStep.kit_cfg c e st -> sstep_cfg segs CfgStep.kit_cfg (relimc L c) e (relims L st).
Proof.
  intros c e st Hg H. destruct Hg as (HL & Hf & Hn) eqn:Eg.
  exact (sstep_cfg_relim_up segs CfgStep.kit_cfg L c e st HL Hf (good_not_refused c Hg) H).
Qed.

Lemma good_down : forall c e st1, good c -> sstep_cfg segs CfgStep.kit_cfg (relimc L c) e st1 ->
  exists st2, sstep_cfg segs CfgStep.kit_cfg c e st2 /\ st1 = relims L st2.
Proof.
  intros c e st1 Hg H. destruct Hg as (HL & Hf & Hn) eqn:Eg.
  exact (sstep_cfg_relim_down segs CfgStep.kit_cfg L c e st1 HL Hf (good_not_refused c Hg) H).
Qed.

Lemma good_step : forall c e c', good c -> sstep_cfg segs CfgStep.kit_cfg c e (SNext c') -> good c'.
Proof.
  intros c e c' Hg H.
  pose proof (good_up c e (SNext c') Hg H) as Hup. cbn [relims] in Hup.
  destruct (sstep_cfg_pres segs CfgStep.kit_cfg c e c' H) as [Hl Hf'].
  destruct Hg as (HL & Hf & Hn).
  split; [rewrite Hl; exact HL |]. split; [exact (Hf' Hf) |].
  intros (tr & c2 & Hst & Hb). apply Hn. exists (e ++ tr), c2.
  split; [eapply star_cfg_step; [exact Hup | exact Hst] | exact Hb].
Qed.

Lemma relims_not_error : forall st, st <> SError -> relims L st <> SError.
Proof. intros [c|] H; cbn [relims]; [discriminate | exact H]. Qed.

Lemma relims_next_inv : forall st c1, SNext c1 = relims L st ->
  exists c2, st = SNext c2 /\ c1 = relimc L c2.
Proof.
  intros [c2|] c1 H; cbn [relims] in H; [| discriminate H].
  injection H as ->. eexists. split; reflexivity.
Qed.

(* [comment removed for export] *)

Lemma node_ok_relim : forall c (I : Type) (evs : I -> list event) (nx : I -> config),
  good c -> node_ok segs c I evs nx ->
  node_ok segs (relimc L c) I evs (fun i => relimc L (nx i)).
Proof.
  intros c I evs nx Hg [Hcomp Hsound]. split.
  - intros i. exact (good_up c (evs i) (SNext (nx i)) Hg (Hcomp i)).
  - intros e st H. destruct (good_down c e st Hg H) as [st2 [H2 ->]].
    destruct (Hsound e st2 H2) as [i [-> ->]]. exists i. split; reflexivity.
Qed.

Definition lift (R : config -> Prop) (d : config) : Prop :=
  exists c, R c /\ good c /\ d = relimc L c.

Lemma trap_relim : forall R, trap segs R -> trap segs (lift R).
Proof.
  intros R HR d (c & Hc & Hg & ->). destruct (HR c Hc) as [[e [st Hst]] Hall]. split.
  - exists e, (relims L st). exact (good_up c e st Hg Hst).
  - intros e' st' H. destruct (good_down c e' st' Hg H) as [st2 [H2 ->]].
    destruct (Hall e' st2 H2) as (-> & c1 & -> & Hc1). split; [reflexivity |].
    exists (relimc L c1). split; [reflexivity |].
    exists c1. split; [exact Hc1 |]. split; [exact (good_step c [] c1 Hg H2) | reflexivity].
Qed.

Lemma prog_relim : forall (P Q : config -> Prop) b c,
  prog segs P Q b c -> good c -> prog segs (lift P) (lift Q) b (relimc L c).
Proof.
  intros P Q b c H. induction H as [c Hq | c Hex Hall Hnx IH | c Hp | c H IH]; intros Hg.
  - apply pg_done. exists c. auto.
  - apply pg_step.
    + destruct Hex as [e [st Hst]]. exists e, (relims L st). exact (good_up c e st Hg Hst).
    + intros e st H. destruct (good_down c e st Hg H) as [st2 [H2 ->]].
      destruct (Hall e st2 H2) as [-> Hne]. split; [reflexivity | exact (relims_not_error st2 Hne)].
    + intros e c1 H. destruct (good_down c e (SNext c1) Hg H) as [st2 [H2 E]].
      destruct (relims_next_inv st2 c1 E) as [c2 [-> ->]].
      exact (IH e c2 H2 (good_step c e c2 Hg H2)).
  - apply pg_head. exists c. auto.
  - apply pg_lift. exact (IH Hg).
Qed.

Lemma star_relim : forall c tr c', star_cfg segs CfgStep.kit_cfg c tr c' -> good c ->
  star_cfg segs CfgStep.kit_cfg (relimc L c) tr (relimc L c') /\ good c'.
Proof.
  intros c tr c' H. induction H as [c | c1 evs c2 tr c3 Hs Hstar IH]; intros Hg.
  - split; [apply star_cfg_refl | exact Hg].
  - pose proof (good_step c1 evs c2 Hg Hs) as Hg2.
    destruct (IH Hg2) as [Hst Hg3]. split; [| exact Hg3].
    eapply star_cfg_step; [| exact Hst]. exact (good_up c1 evs (SNext c2) Hg Hs).
Qed.

Lemma reaches_relim : forall (Q : config -> Prop) c,
  reaches segs Q c -> good c -> reaches segs (lift Q) (relimc L c).
Proof.
  intros Q c (c' & Hst & Hq) Hg. destruct (star_relim c [] c' Hst Hg) as [Hst' Hg'].
  exists (relimc L c'). split; [exact Hst' |]. exists c'. auto.
Qed.

(* [comment removed for export] *)
Theorem rrealizes_relim_good : forall c T,
  rrealizes segs c T -> good c -> rrealizes segs (relimc L c) T.
Proof.
  intros c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | R c HR Hc
                               | P Q c T Hprog HP Hreach HQ IH | c T T' H IH Heq];
    intros Hg.
  - eapply (rrz_node segs (relimc L c) I evs (fun i => relimc L (nx i)) T i0).
    + exact (node_ok_relim c I evs nx Hg Hnode).
    + intros i. apply IH. destruct Hnode as [Hcomp _].
      exact (good_step c (evs i) (nx i) Hg (Hcomp i)).
  - apply rrz_halt. exact Hh.
  - apply (rrz_diverge segs (lift R)); [exact (trap_relim R HR) |].
    exists c. auto.
  - apply (rrz_retry segs (lift P) (lift Q)).
    + exact (prog_relim P Q true c Hprog Hg).
    + intros d (d0 & Hd0 & Hgd & ->). exact (prog_relim P Q true d0 (HP d0 Hd0) Hgd).
    + exact (reaches_relim Q c Hreach Hg).
    + intros d (d0 & Hd0 & Hgd & ->). exact (IH d0 Hd0 Hgd).
  - eapply rrz_conseq; [exact (IH Hg) | exact Heq].
Qed.

End Bridge.

(* [comment removed for export] *)
Theorem rrealizes_relim : forall segs c T L,
  rrealizes segs c T ->
  (L <= vm_limit (m_vmmaps (cfg_model c)))%Z ->
  maps_fit (cfg_model c) ->
  ~ reaches_budget_refused_cfg segs CfgStep.kit_cfg (relimc L c) ->
  rrealizes segs (relimc L c) T.
Proof.
  intros segs c T L H HL Hf Hn. apply (rrealizes_relim_good segs L c T H). split; [exact HL | tauto].
Qed.

(* [comment removed for export] *)

Lemma init_config_relim : forall segs pc ph sp brk0 mb rnd L1 L2 inp,
  init_config segs pc ph sp brk0 mb rnd L1 inp
  = relimc L1 (init_config segs pc ph sp brk0 mb rnd L2 inp).
Proof. reflexivity. Qed.


Lemma init_config_maps_fit : forall segs pc ph sp brk0 mb rnd L inp,
  maps_fit (cfg_model (init_config segs pc ph sp brk0 mb rnd L inp)).
Proof. intros segs pc ph sp brk0 mb rnd L inp a sz []. Qed.

(* [comment removed for export] *)
Theorem rrealizes_init_relim : forall segs pc ph sp brk0 mb rnd L1 L2 inp T,
  (L1 <= L2)%Z ->
  rrealizes segs (init_config segs pc ph sp brk0 mb rnd L2 inp) T ->
  ~ reaches_budget_refused_cfg segs CfgStep.kit_cfg (init_config segs pc ph sp brk0 mb rnd L1 inp) ->
  rrealizes segs (init_config segs pc ph sp brk0 mb rnd L1 inp) T.
Proof.
  intros segs pc ph sp brk0 mb rnd L1 L2 inp T HL H Hn.
  rewrite (init_config_relim segs pc ph sp brk0 mb rnd L1 L2 inp) in Hn |- *.
  apply rrealizes_relim; [exact H | exact HL | apply init_config_maps_fit | exact Hn].
Qed.
End BudgetMonoRun.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRoot.
Import BudgetMonoRun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Theorem root_obligation_core_mono : forall (img : Image) (lim lim' : Z) (S : ProcInput -> TSet),
  (lim <= lim')%Z ->
  root_obligation_core img lim' S ->
  forall sp brk0 mb rnd inp,
    valid_entry img (mkEntry sp brk0 mb rnd) inp ->
    valid_input_core inp ->
    ~ run_scfg_budget_refused CfgStep.kit_cfg img lim (mkEntry sp brk0 mb rnd) inp ->
    rrealizes (img_segments img)
      (init_config (img_segments img) (img_init_pc img) (img_phdrs img) sp brk0 mb rnd lim inp)
      (S inp).
Proof.
  intros [segs pc ph] lim lim' S HL H sp brk0 mb rnd inp He Hi Hb.
  cbn [img_segments img_init_pc img_phdrs] in *. cbn [run_scfg_budget_refused] in Hb.
  exact (rrealizes_init_relim segs pc ph sp brk0 mb rnd lim lim' inp (S inp) HL
           (H sp brk0 mb rnd inp He Hi) Hb).
Qed.

(* [comment removed for export] *)
Theorem rrealizes_universal_ef_budgets_abort_mono :
  forall (lim_s lim_s' lim_t : Z) (src tgt : Image) (S : ProcInput -> TSet),
  (lim_s <= lim_s')%Z ->
  root_obligation_core src lim_s' S ->
  root_obligation_core tgt lim_t S ->
  kill_free S ->
  strong_universal_error_free_T_scfg_budgets_abort CfgStep.kit_cfg lim_s lim_t src tgt.
Proof.
  intros lim_s lim_s' lim_t [ssegs spc sph] [tsegs tpc tph] S HL Hsrc Htgt Hkf.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hve_s Hve_t Hvi Hb.
  pose proof (valid_input_core_of_valid_input_abort _ Hvi) as Hci.
  pose proof (root_obligation_core_mono (mkImage ssegs spc sph) lim_s lim_s' S HL Hsrc
                rsp rbrk rmb rrnd inp Hve_s Hci Hb) as RS.
  cbn [img_segments img_init_pc img_phdrs] in RS.
  pose proof (Htgt asp abrk amb arnd inp Hve_t Hci) as RT.
  destruct (shape_strong_equiv_rr ssegs spc sph rsp rbrk rmb rrnd lim_s
              tsegs tpc tph asp abrk amb arnd lim_t (S inp) inp RS RT) as (EFs & EFt & TE).
  unfold strong_equiv_error_free_budgets_scfg_abort, error_free_unkilled.
  repeat split.
  - exact EFs.
  - eapply rrealizes_not_dies; [exact RS | intros tr sig fs; apply (Hkf inp); exact Hci].
  - exact EFt.
  - eapply rrealizes_not_dies; [exact RT | intros tr sig fs; apply (Hkf inp); exact Hci].
  - apply TE.
  - apply TE.
Qed.

(* [comment removed for export] *)
Lemma sanitizer_source_le_shipped : (SanitizerBudgets.lim_source <= source_alloc_limit)%Z.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Theorem rrealizes_universal_ef_sanitizer_budgets_abort :
  forall (src tgt : Image) (S : ProcInput -> TSet),
  root_obligation_core src source_alloc_limit S ->
  root_obligation_core tgt target_alloc_limit S ->
  kill_free S ->
  strong_universal_error_free_T_scfg_budgets_abort CfgStep.kit_cfg
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target src tgt.
Proof.
  intros src tgt S Hs Ht Hk.
  exact (rrealizes_universal_ef_budgets_abort_mono SanitizerBudgets.lim_source source_alloc_limit
           SanitizerBudgets.lim_target src tgt S sanitizer_source_le_shipped Hs Ht Hk).
Qed.
