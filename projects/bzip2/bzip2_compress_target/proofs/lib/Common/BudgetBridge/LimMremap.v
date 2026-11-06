(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall Uaccess SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mremap.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Common.BudgetBridge Require Import Relim LimVm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope sys_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition avoids (lo hi : Z) (l : list (word * word)) : Prop :=
  forall b s, In (b, s) l -> (bv_unsigned b + bv_unsigned s <= lo \/ hi <= bv_unsigned b)%Z.

Ltac u64 :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (bv_unsigned_Z_to_bv_u64 z) by lia end.

Ltac ivnorm :=
  cbn [maps_subtract maps_subtract_all app fst snd]; unfold iv_subtract; cbv zeta;
  cbn [maps_subtract maps_subtract_all app fst snd]; rewrite ?app_nil_r; u64.

(* [comment removed for export] *)
Ltac ivdecide :=
  match goal with
  | |- context [(?x <? ?y)%Z] =>
      first [ replace (x <? y)%Z with true by (symmetry; apply Z.ltb_lt; lia)
            | replace (x <? y)%Z with false by (symmetry; apply Z.ltb_ge; lia) ]
  end.

Ltac wordeq :=
  match goal with
  | |- ?w = Z_to_bv 64 ?z => is_var w; transitivity (Z_to_bv 64 (bv_unsigned w)); [symmetry; apply Z_to_bv_bv_unsigned| f_equal; lia]
  | |- Z_to_bv 64 ?z = ?w => is_var w; transitivity (Z_to_bv 64 (bv_unsigned w)); [f_equal; lia| apply Z_to_bv_bv_unsigned]
  | |- Z_to_bv 64 ?x = Z_to_bv 64 ?y => f_equal; lia
  end.

Ltac listeq :=
  repeat first [ reflexivity | lia | wordeq
               | lazymatch goal with |- @eq Z _ _ => fail | |- @eq (bv _) _ _ => fail | _ => progress f_equal end
               | exfalso; lia ].

Ltac ivsolve :=
  ivnorm; repeat (ivdecide; ivnorm);
  first [ solve [listeq]
        | match goal with |- context [(?x <? ?y)%Z] =>
            let C := fresh "C" in destruct (Z.lt_ge_cases x y) as [C|C]; ivsolve end
        | idtac "STUCK"; match goal with |- ?g => idtac g end ].

(* [comment removed for export] *)
Lemma cut_by_remnants_single : forall (wa ws ca cs : word) dlo dhi,
  (0 <= dlo)%Z -> (dlo <= dhi)%Z -> (dhi < two_pow_64)%Z ->
  (0 < bv_unsigned ws)%Z ->
  (bv_unsigned wa + bv_unsigned ws <= two_pow_64)%Z ->
  (bv_unsigned wa + bv_unsigned ws <= dlo \/ dhi <= bv_unsigned wa)%Z ->
  maps_subtract_all [(wa, ws)] (iv_subtract ca cs dlo dhi)
  = iv_subtract wa ws (bv_unsigned ca) (bv_unsigned ca + bv_unsigned cs).
Proof.
  intros wa ws ca cs dlo dhi HD0 HD1 HD2 Hws Hfit Hav.
  pose proof (bv_unsigned_range_u64 wa) as Rwa. pose proof (bv_unsigned_range_u64 ws) as Rws.
  pose proof (bv_unsigned_range_u64 ca) as Rca. pose proof (bv_unsigned_range_u64 cs) as Rcs.
  destruct Hav as [Hb|Ha]; ivsolve.
Qed.

Lemma maps_subtract_all_cuts_app : forall C1 C2 l,
  maps_subtract_all l (C1 ++ C2) = maps_subtract_all (maps_subtract_all l C1) C2.
Proof. induction C1 as [|[a n] C1 IH]; intros C2 l; [reflexivity|]. cbn [maps_subtract_all app]. apply IH. Qed.

Lemma avoids_maps_subtract lo hi l clo chi :
  maps_fit l -> avoids lo hi l -> avoids lo hi (maps_subtract l clo chi).
Proof.
  intros Hf Ha b s Hin. destruct (maps_subtract_In l clo chi b s Hin) as (a & sz & Hin0 & Hiv).
  pose proof (iv_subtract_within a sz clo chi b s (Hf a sz Hin0) Hiv). pose proof (Ha a sz Hin0). lia.
Qed.

Lemma cut_by_remnants : forall l (ca cs : word) dlo dhi,
  (0 <= dlo)%Z -> (dlo <= dhi)%Z -> (dhi < two_pow_64)%Z ->
  entries_nonzero l -> maps_fit l -> avoids dlo dhi l ->
  maps_subtract_all l (iv_subtract ca cs dlo dhi)
  = maps_subtract l (bv_unsigned ca) (bv_unsigned ca + bv_unsigned cs).
Proof.
  induction l as [|[wa ws] r IH]; intros ca cs dlo dhi HD0 HD1 HD2 Hnz Hf Ha.
  - apply maps_subtract_all_nil.
  - change ((wa, ws) :: r) with ([(wa, ws)] ++ r). rewrite maps_subtract_all_app, maps_subtract_app.
    rewrite (IH ca cs dlo dhi HD0 HD1 HD2); [| intros a n Hin; exact (Hnz a n (or_intror Hin))
      | intros a n Hin; exact (Hf a n (or_intror Hin)) | intros a n Hin; exact (Ha a n (or_intror Hin))].
    f_equal. cbn [maps_subtract]. rewrite app_nil_r.
    apply (cut_by_remnants_single wa ws ca cs dlo dhi HD0 HD1 HD2);
      [exact (Hnz wa ws (or_introl eq_refl))| exact (Hf wa ws (or_introl eq_refl))| exact (Ha wa ws (or_introl eq_refl))].
Qed.

(* [comment removed for export] *)
Lemma cut_by_remnant_list : forall KL l dlo dhi,
  (0 <= dlo)%Z -> (dlo <= dhi)%Z -> (dhi < two_pow_64)%Z ->
  entries_nonzero l -> maps_fit l -> avoids dlo dhi l ->
  maps_subtract_all l (maps_subtract KL dlo dhi) = maps_subtract_all l KL.
Proof.
  induction KL as [|[ca cs] rest IH]; intros l dlo dhi HD0 HD1 HD2 Hnz Hf Ha; [reflexivity|].
  cbn [maps_subtract maps_subtract_all]. rewrite maps_subtract_all_cuts_app.
  rewrite (cut_by_remnants l ca cs dlo dhi HD0 HD1 HD2 Hnz Hf Ha).
  apply IH; [exact HD0| exact HD1| exact HD2| apply maps_subtract_nonzero, Hnz| apply maps_fit_maps_subtract, Hf
    | apply avoids_maps_subtract; [exact Hf| exact Ha]].
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_inside : forall l lo hi,
  (forall b s, In (b, s) l -> (lo <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= hi)%Z) ->
  maps_subtract l lo hi = [].
Proof.
  induction l as [|[a sz] r IH]; intros lo hi H; [reflexivity|]. cbn [maps_subtract].
  rewrite (IH lo hi (fun b s Hin => H b s (or_intror Hin))).
  pose proof (H a sz (or_introl eq_refl)) as [H1 H2]. unfold iv_subtract. cbv zeta.
  rewrite (proj2 (Z.ltb_ge _ _) H1). rewrite (proj2 (Z.ltb_ge _ _) H2). reflexivity.
Qed.


Lemma region_free_In_avoids : forall l (d n : word),
  region_free l d n = true -> avoids (bv_unsigned d) (bv_unsigned d + bv_unsigned n) l.
Proof.
  intros l d n H b s Hin. pose proof (region_free_In l d n b s H Hin) as Hov.
  unfold iv_overlap in Hov. apply andb_false_iff in Hov. destruct Hov as [Hov|Hov]; apply Z.ltb_ge in Hov; lia.
Qed.

Lemma avoids_maps_subtract_all : forall cuts lo hi l,
  maps_fit l -> avoids lo hi l -> avoids lo hi (maps_subtract_all l cuts).
Proof.
  intros cuts lo hi l Hf Ha b s Hin.
  destruct (maps_subtract_all_within cuts l b s Hf Hin) as (a & sz & Hin0 & Hw). pose proof (Ha a sz Hin0). lia.
Qed.

Lemma maps_fit_maps_subtract_all : forall cuts l, maps_fit l -> maps_fit (maps_subtract_all l cuts).
Proof.
  intros cuts l Hf b s Hin.
  destruct (maps_subtract_all_within cuts l b s Hf Hin) as (a & sz & Hin0 & Hw). pose proof (Hf a sz Hin0). lia.
Qed.

(* [comment removed for export] *)
Lemma used_move_le : forall m old old_n dst new_n,
  maps_fit (vm_maps (m_vmmaps m)) -> entries_nonzero (vm_maps (m_vmmaps m)) ->
  (bv_unsigned dst mod page_size = 0)%Z ->
  (bv_unsigned new_n mod page_size = 0)%Z ->
  (0 < bv_unsigned new_n)%Z ->
  (bv_unsigned dst + bv_unsigned new_n < two_pow_64)%Z ->
  region_free (map_remove (vm_maps (m_vmmaps m)) old) dst new_n = true ->
  (vm_backing_used (mremap_model_next m old old_n dst new_n)
   <= mremap_move_charge m old old_n new_n)%Z.
Proof.
  intros m old old_n dst new_n Hfit0 Hnz0 Halign Hnalign Hpos Hend Hmaps.
  assert (P1 : forall L P m', m_vmmaps (with_vm_backing L P m') = m_vmmaps m') by reflexivity.
  assert (P2 : forall L P m', m_vm_lazy (with_vm_backing L P m') = L) by reflexivity.
  assert (P3 : forall L P m', m_vm_materialized (with_vm_backing L P m') = P) by reflexivity.
  assert (P4 : forall h m', m_vmmaps (with_vmmaps h m') = h) by reflexivity.
  assert (P5 : forall h m', m_vm_lazy (with_vmmaps h m') = m_vm_lazy m') by reflexivity.
  assert (P6 : forall h m', m_vm_materialized (with_vmmaps h m') = m_vm_materialized m') by reflexivity.
  unfold vm_backing_used, mremap_move_charge, mremap_model_next, vm_resize_backing, mremap_maps_next.
  cbv zeta. rewrite !P1, !P2, !P3, !P4, !P5, !P6.
  unfold vm_backed_maps. cbn [vm_maps vm_noaccess vm_limit].
  set (KL := maps_subtract (m_vm_lazy m) (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) in *.
  set (KP := List.filter (page_outside_range (bv_unsigned old) (bv_unsigned old + bv_unsigned old_n)) (m_vm_materialized m)) in *.
  set (R0 := map_remove (vm_maps (m_vmmaps m)) old) in *.
  set (NA := vm_noaccess (m_vmmaps m)) in *.
  pose proof (bv_unsigned_range_u64 dst) as Rd.
  assert (HfitR : maps_fit R0) by (intros a sz Hin; apply (Hfit0 a sz); unfold R0, map_remove in Hin; apply filter_In in Hin; tauto).
  assert (HnzR : entries_nonzero R0) by (intros a sz Hin; apply (Hnz0 a sz); unfold R0, map_remove in Hin; apply filter_In in Hin; tauto).
  set (M := maps_subtract_all R0 NA) in *.
  assert (HfM : maps_fit M) by (apply maps_fit_maps_subtract_all; exact HfitR).
  assert (HnM : entries_nonzero M) by (apply maps_subtract_all_nonzero; exact HnzR).
  assert (HaM : avoids (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n) M).
  { apply avoids_maps_subtract_all; [exact HfitR| apply region_free_In_avoids; exact Hmaps]. }
  assert (HB : maps_subtract_all M (maps_subtract KL (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n))
               = maps_subtract_all M KL).
  { apply cut_by_remnant_list; [lia| lia| lia| exact HnM| exact HfM| exact HaM]. }
  assert (HKP : (length (List.filter (page_outside_range (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n)) KP)
                 <= length KP)%nat) by apply filter_length_le.
  rewrite length_app.
  change ((dst, new_n) :: R0) with ([(dst, new_n)] ++ R0).
  rewrite maps_subtract_all_app. fold M. rewrite maps_subtract_all_app, live_bytes_app.
  (* [comment removed for export] *)
  assert (HA1 : (live_bytes (maps_subtract_all [(dst, new_n)] NA) <= bv_unsigned new_n)%Z).
  { pose proof (live_bytes_maps_subtract_all_le NA [(dst, new_n)]) as X. cbn [live_bytes] in X. lia. }
  assert (HAw : forall b s, In (b, s) (maps_subtract_all [(dst, new_n)] NA) ->
            (bv_unsigned dst <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= bv_unsigned dst + bv_unsigned new_n)%Z).
  { intros b s Hin. destruct (maps_subtract_all_within NA [(dst, new_n)] b s) as (a & sz & [E|[]] & Hw);
      [intros a sz [E|[]]; injection E as <- <-; lia| exact Hin|]. injection E as <- <-. exact Hw. }
  destruct (mremap_source_lazy_b m old old_n) eqn:Hsrc.
  - (* [comment removed for export] *)
    rewrite (lazy_interior_aligned dst new_n Halign Hnalign Hpos). rewrite length_map.
    change ([(dst, new_n)] ++ ?X) with ([(dst, new_n)] ++ X).
    rewrite !(maps_subtract_all_cuts_app [(dst, new_n)]). cbn [maps_subtract_all].
    rewrite (maps_subtract_inside _ _ _ HAw). rewrite maps_subtract_all_nil. cbn [live_bytes].
    rewrite (live_bytes_subtract_free _ M (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n) ltac:(lia) HaM).
    rewrite HB. unfold page_size. lia.
  - (* [comment removed for export] *)
    rewrite HB. cbn [length].
    pose proof (live_bytes_maps_subtract_all_le (maps_subtract KL (bv_unsigned dst) (bv_unsigned dst + bv_unsigned new_n))
                  (maps_subtract_all [(dst, new_n)] NA)). unfold page_size. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma region_free_app_r : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = true -> region_free l2 lo n = true.
Proof.
  induction l1 as [|[a sz] l1 IH]; intros l2 lo n H; [exact H|].
  cbn [region_free app] in H. apply andb_true_iff in H as [_ H]. exact (IH _ _ _ H).
Qed.

Lemma region_free_filter : forall f l (lo n : word),
  region_free l lo n = true -> region_free (List.filter f l) lo n = true.
Proof.
  induction l as [|[a sz] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free List.filter] in H |- *. apply andb_true_iff in H as [H1 H2].
  destruct (f (a, sz)); cbn [region_free]; [rewrite H1; exact (IH _ _ H2)| exact (IH _ _ H2)].
Qed.

Lemma page_round_up_Z_mod z : (page_round_up_Z z mod page_size = 0)%Z.
Proof. unfold page_round_up_Z. apply Z.mod_mul. unfold page_size. lia. Qed.

Lemma page_align_false_u64 len :
  page_align_is0_b len = false ->
  bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))) = page_round_up_Z (bv_unsigned len)
  /\ (0 < page_round_up_Z (bv_unsigned len))%Z.
Proof.
  intros H. unfold page_align_is0_b in H. apply orb_false_iff in H as [H0 H]. apply Z.leb_gt in H.
  pose proof (page_round_up_Z_pos len H0). rewrite u64_of_Z; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INV_mremap_model_next m old old_n dst new_n :
  (0 < bv_unsigned new_n)%Z -> (bv_unsigned dst + bv_unsigned new_n <= two_pow_64)%Z ->
  INV m -> INV (mremap_model_next m old old_n dst new_n).
Proof.
  intros Hn Hd [HF HN]. unfold INV in *.
  change (vm_maps (m_vmmaps (mremap_model_next m old old_n dst new_n))) with ((dst, new_n) :: map_remove (vm_maps (m_vmmaps m)) old).
  split; [apply maps_fit_cons; [exact Hd| apply maps_fit_map_remove, HF]
        | apply entries_nonzero_cons; [exact Hn| unfold map_remove; apply entries_nonzero_filter, HN]].
Qed.

Lemma mremap_model_next_relim l m old old_n dst new_n :
  mremap_model_next (relim l m) old old_n dst new_n = relim l (mremap_model_next m old old_n dst new_n).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac mremap_move m l H nav Hnew_u Hnew_pos Hgt Htoplt :=
  let dst := fresh "dst" in let HF := fresh "HF" in
  apply choose_modify_pure_iff in H as (dst & HF & ->);
  unfold mremap_fresh_b in HF;
  let Hfin := fresh "Hfin" in let Hrf := fresh "Hrf" in let Htopd := fresh "Htopd" in
  let Hpos := fresh "Hpos" in let Hal := fresh "Hal" in let Hne := fresh "Hne" in
  apply andb_true_iff in HF as [HF Hfin]; apply andb_true_iff in HF as [HF Hrf];
  apply andb_true_iff in HF as [HF Htopd]; apply andb_true_iff in HF as [HF Hpos];
  apply andb_true_iff in HF as [Hne Hal];
  pose proof (proj1 (Z.leb_le _ _) Htopd) as Htopd';
  split;
  [ split; [reflexivity|]; apply INV_mremap_model_next; rewrite Hnew_u; [exact Hnew_pos| lia]
  | let HI := fresh "HI" in let M1 := fresh "M1" in let M2 := fresh "M2" in
    intros HI M1 M2; syncall; synch M2; try rewrite Hgt in M1; try rewrite Hgt in M2;
    let F1 := fresh "F1" in let V1 := fresh "V1" in let F2 := fresh "F2" in let V2 := fresh "V2" in
    apply true_of_negb_false in M1; apply andb_true_iff in M1 as [F1 V1];
    apply true_of_negb_false in M2; apply andb_true_iff in M2 as [F2 V2];
    right;
    try (match goal with |- context [if mremap_inplace_grow_b (relim l m) ?a ?b ?c ?d ?e then _ else _] =>
           replace (mremap_inplace_grow_b (relim l m) a b c d e) with (mremap_inplace_grow_b m a b c d e)
             by (unfold mremap_inplace_grow_b; unrelim; rewrite F1, F2; reflexivity) end;
         match goal with E : mremap_inplace_grow_b m _ _ _ _ _ = _ |- _ => rewrite E end);
    nav;
    apply choose_modify_pure_iff; exists dst; split; [| reflexivity];
    unfold mremap_fresh_b; unrelim; rewrite Hne, Hal, Hpos, Htopd, Hrf; cbn [andb];
    unfold mremap_final_budget_b, vm_backing_within_limit;
    rewrite mremap_model_next_relim, vm_backing_used_relim;
    match goal with |- context [vm_limit (m_vmmaps (relim l ?X))] => change (vm_limit (m_vmmaps (relim l X))) with l end;
    apply Z.leb_le;
    unfold mremap_move_budget_b in V2;
    match type of V2 with context [mremap_move_charge (relim l m) ?a ?b ?c] =>
      change (mremap_move_charge (relim l m) a b c) with (mremap_move_charge m a b c) in V2 end;
    change (vm_limit (m_vmmaps (relim l m))) with l in V2; apply Z.leb_le in V2;
    eapply Z.le_trans; [| exact V2];
    apply used_move_le;
    [ exact (proj1 HI) | exact (proj2 HI) | apply Z.eqb_eq; exact Hal
    | rewrite Hnew_u; apply page_round_up_Z_mod | rewrite Hnew_u; exact Hnew_pos
    | rewrite Hnew_u; lia
    | unfold map_remove; apply region_free_filter; eapply region_free_app_r; exact Hrf ] ].

Lemma arm_216 : ARM 216 (fun i => mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof.
  intros i m o l Hno H. cbv beta in H. rewrite !(abr_216 _ _ Hno).
  unfold mremap_spec in H. leaves H.
  all: unfold mremap_budget_refused_b, mremap_spec;
       repeat match goal with E : ?b = _ |- context [if ?b then _ else _] => rewrite E end; cbv zeta.
  all: try (solve [leaf_li H]).
  mm_hyp H.
  { (* [comment removed for export] *) mm_atom H. }
  (* [comment removed for export] *)
  set (old := in_arg i 0) in *. set (old_nZ := page_round_up_Z (bv_unsigned (in_arg i 1))) in *.
  set (new_nZ := page_round_up_Z (bv_unsigned (in_arg i 2))) in *.
  set (old_n := Z_to_bv 64 old_nZ) in *. set (new_n := Z_to_bv 64 new_nZ) in *.
  match goal with E : page_align_is0_b (in_arg i 2) = false |- _ =>
    destruct (page_align_false_u64 _ E) as [Hnew_u Hnew_pos]; fold new_nZ in Hnew_u, Hnew_pos; fold new_n in Hnew_u end.
  match goal with E : negb (mremap_source_b _ _ _ _ && _) = false |- _ =>
    pose proof (true_of_negb_false _ E) as Hsrc; apply andb_true_iff in Hsrc as [Hsrc _];
    unfold mremap_source_b in Hsrc; apply andb_true_iff in Hsrc as [Hsrc _]; apply andb_true_iff in Hsrc as [Hsrc _];
    apply andb_true_iff in Hsrc as [Htop _]; apply Z.leb_le in Htop end.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htoplt. pose proof (word_range old) as Rold.
  match goal with E : (old_nZ =? new_nZ)%Z = false |- _ => apply Z.eqb_neq in E end.
  let b := cond_of H in destruct b eqn:Es; [apply Z.ltb_lt in Es| apply Z.ltb_ge in Es].
  - (* [comment removed for export] *)
    apply modify_pure_iff in H. subst. split.
    + split; [reflexivity|]. apply INV_mremap_model_next; rewrite Hnew_u; [exact Hnew_pos| lia].
    + intros HI M1 M2. syncall. right. apply modify_pure_iff. reflexivity.
  - (* [comment removed for export] *)
    assert (Hgt : (new_nZ <=? old_nZ)%Z = false) by (apply Z.leb_gt; lia).
    cbv zeta in H.
    match type of H with (if ?b then _ else _) _ _ _ => destruct b eqn:Eg end.
    + mm_hyp H.
      * (* [comment removed for export] *)
        apply modify_pure_iff in H. subst. split.
        -- split; [reflexivity|]. apply INV_mremap_model_next; rewrite Hnew_u; [exact Hnew_pos|].
           unfold mremap_inplace_grow_b in Eg. apply andb_true_iff in Eg as [Eg _]. apply andb_true_iff in Eg as [Eg _].
           apply Z.leb_le in Eg. lia.
        -- intros HI M1 M2. syncall. synch M2. try rewrite Hgt in M1; try rewrite Hgt in M2.
           apply true_of_negb_false in M1. apply andb_true_iff in M1 as [F1 V1].
           apply true_of_negb_false in M2. apply andb_true_iff in M2 as [F2 V2].
           right.
           match goal with |- context [if ?b then _ else _] => replace b with true end.
           2:{ symmetry. revert Eg F2. unfold mremap_inplace_grow_b. unrelim.
               intros Eg F2. rewrite F2. apply andb_true_iff in Eg as [Eg _]. rewrite Eg. reflexivity. }
           left. apply modify_pure_iff. reflexivity.
      * (* [comment removed for export] *)
        mremap_move m l H ltac:(right) Hnew_u Hnew_pos Hgt Htoplt.
    + (* [comment removed for export] *)
      mremap_move m l H ltac:(idtac) Hnew_u Hnew_pos Hgt Htoplt.
Qed.

