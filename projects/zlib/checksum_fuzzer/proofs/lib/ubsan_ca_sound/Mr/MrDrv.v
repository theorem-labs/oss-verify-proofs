(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Spec Require SM08. Import SM08. Import SM08.MallocCtrl.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Mr Require Import MrFeasNull MrFeasNull44 MrFeasSome1 MrTall MrShape.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma gmr_upd_same g f st : get_meta_rec (upd_meta g f st) g = f (get_meta_rec st g).
Proof. unfold get_meta_rec, upd_meta, put_meta. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma gmr_upd_other g g' f st : g <> g' -> get_meta_rec (upd_meta g f st) g' = get_meta_rec st g'.
Proof. intros H. unfold get_meta_rec, upd_meta, put_meta. cbn. rewrite lookup_insert_ne by exact H. reflexivity. Qed.
Lemma gmr_put_same g r st : get_meta_rec (put_meta g r st) g = r.
Proof. unfold get_meta_rec, put_meta. cbn. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma gmr_put_other g g' r st : g <> g' -> get_meta_rec (put_meta g r st) g' = get_meta_rec st g'.
Proof. intros H. unfold get_meta_rec, put_meta. cbn. rewrite lookup_insert_ne by exact H. reflexivity. Qed.

Definition solo_rec (r : meta) (b : aptr) : Prop :=
  m_mem r = Some b /\ m_avail r = 0 /\ m_freed r = 0 /\ m_last_idx r = 0 /\ m_freeable r = 1 /\ m_maplen r <> 0.
Definition big_rec (r : meta) (b : aptr) : Prop := solo_rec r b /\ m_sizeclass r = 63 /\ m_next r = None.
Definition act44_rec (r : meta) (b g : aptr) : Prop := solo_rec r b /\ m_sizeclass r = 44 /\ m_next r = Some g /\ m_prev r = Some g.

Definition fl_list (fl : optr) : list aptr := match fl with Some a => [a] | None => [] end.

Record KST (d : Z) (cs : mstate) (a44 fl : optr) (bl : list (aptr * aptr)) : Prop := mkKST {
  ks_act   : forall sc, active cs sc = if sc =? 44 then a44 else None;
  ks_fl    : c_free_meta_head (ctx cs) = fl;
  ks_flrec : forall a, fl = Some a -> m_next (get_meta_rec cs a) = Some a /\ m_prev (get_meta_rec cs a) = Some a;
  ks_blk   : forall g b, In (g, b) bl ->
               s_slots cs !! (aadd b UNIT) = Some (g, 0) /\ (fst b < s_next_rid cs)%N /\ snd b = 0 /\
               (big_rec (get_meta_rec cs g) b \/ a44 = Some g);
  ks_ndm   : NoDup (map fst bl ++ fl_list fl);
  ks_ndr   : NoDup (map (fun x => fst (snd x)) bl);
  ks_a44   : forall m, a44 = Some m -> exists b, In (m, b) bl /\ act44_rec (get_meta_rec cs m) b m;
  ks_avail : exists mf, c_avail_meta (ctx cs) = Some mf /\
               forall g, In g (map fst bl ++ fl_list fl) -> fst g <> fst mf \/ snd g < snd mf;
  ks_cnt   : d <= cnt cs
}.

Lemma KST_drv : forall d cs a44 fl bl, KST d cs a44 fl bl -> allnone cs \/ (none44 cs /\ full44 cs).
Proof.
  intros d cs a44 fl bl K. destruct a44 as [m|].
  - right. split.
    + intros sc Hsc. rewrite (ks_act _ _ _ _ _ K). destruct (Z.eqb_spec sc 44); [contradiction | reflexivity].
    + unfold full44. rewrite (ks_act _ _ _ _ _ K). cbn.
      destruct (ks_a44 _ _ _ _ _ K m eq_refl) as (b & _ & (_ & Ha & Hf & _) & _ & Hn & _). auto.
  - left. intros sc. rewrite (ks_act _ _ _ _ _ K). destruct (sc =? 44); reflexivity.
Qed.

Lemma KST_metaok : forall d cs a44 fl bl, KST d cs a44 fl bl -> metaok d cs.
Proof. intros d cs a44 fl bl K. exact (ks_cnt _ _ _ _ _ K). Qed.

Definition AMOUT (d : Z) (cs : mstate) (bl : list (aptr * aptr)) (g : aptr) (cs' : mstate) : Prop :=
  (forall sc, active cs' sc = active cs sc) /\ s_slots cs' = s_slots cs /\ s_next_rid cs' = s_next_rid cs /\
  c_free_meta_head (ctx cs') = None /\
  (forall g', g' <> g -> get_meta_rec cs' g' = get_meta_rec cs g') /\
  m_next (get_meta_rec cs' g) = None /\
  ~ In g (map fst bl) /\
  (exists mf', c_avail_meta (ctx cs') = Some mf' /\ forall g', In g' (g :: map fst bl) -> fst g' <> fst mf' \/ snd g' < snd mf') /\
  d - 1 <= cnt cs'.

Lemma alloc_meta_KST {R} d cs a44 fl bl (k : mstate -> optr -> M R) bail :
  KST d cs a44 fl bl -> 1 <= d ->
  exists g cs', alloc_meta cs k bail = k cs' (Some g) /\ AMOUT d cs bl g cs'.
Proof.
  intros K Hd. unfold alloc_meta.
  set (st0 := if c_init_done (ctx cs) =? 0 then _ else cs).
  assert (E0 : (forall sc, active st0 sc = active cs sc) /\ s_slots st0 = s_slots cs /\ s_next_rid st0 = s_next_rid cs /\
               c_free_meta_head (ctx st0) = c_free_meta_head (ctx cs) /\ s_metas st0 = s_metas cs /\
               c_avail_meta (ctx st0) = c_avail_meta (ctx cs) /\ cnt st0 = cnt cs).
  { subst st0. destruct (c_init_done (ctx cs) =? 0); repeat split; reflexivity. }
  clearbody st0. destruct E0 as (EA & ES & EN & EF & EM & EV & EC).
  pose proof (ks_cnt _ _ _ _ _ K) as HC. destruct (ks_avail _ _ _ _ _ K) as (mf & HMF & HABOVE).
  pose proof (ks_ndm _ _ _ _ _ K) as ND.
  rewrite EF, (ks_fl _ _ _ _ _ K). destruct fl as [a|].
  -
    exists a, (dequeue LFree a st0). split; [reflexivity|].
    destruct (ks_flrec _ _ _ _ _ K a eq_refl) as [Hn Hp].
    assert (Hn0 : m_next (get_meta_rec st0 a) = Some a) by (unfold get_meta_rec; rewrite EM; exact Hn).
    assert (DQ : dequeue LFree a st0 = upd_meta a (fun r => m_set_prev None (m_set_next None r)) (set_head LFree None st0)).
    { unfold dequeue. rewrite Hn0. cbn [optr_eqb]. rewrite aptr_eqb_refl. reflexivity. }
    rewrite DQ. unfold AMOUT. repeat split.
    + intros sc. rewrite <- EA. reflexivity.
    + rewrite <- ES. reflexivity.
    + rewrite <- EN. reflexivity.
    + intros g' Hg'. rewrite gmr_upd_other by congruence. unfold get_meta_rec. cbn. rewrite EM. reflexivity.
    + rewrite gmr_upd_same. reflexivity.
    + cbn [fl_list] in ND. apply NoDup_app in ND. destruct ND as (_ & ND2 & _). intros Hin.
      apply (ND2 a); [apply list_elem_of_In; exact Hin | apply list_elem_of_In; left; reflexivity].
    + exists mf. split; [cbn; rewrite <- HMF, <- EV; reflexivity|]. intros g' Hg'. apply HABOVE. cbn [fl_list].
      destruct Hg' as [<-|Hg']; [apply in_or_app; right; left; reflexivity | apply in_or_app; left; exact Hg'].
    + unfold cnt in *. cbn. change (c_avail_meta_count (ctx st0)) with (cnt st0). rewrite EC. unfold cnt. lia.
  -
    replace (c_avail_meta_count (ctx st0) =? 0) with false by (symmetry; apply Z.eqb_neq; unfold cnt in *; lia). cbn [negb].
    unfold am_take. rewrite EV, HMF.
    eexists mf, _. split; [reflexivity|]. unfold AMOUT. repeat split.
    + intros sc. rewrite <- EA. reflexivity.
    + rewrite <- ES. reflexivity.
    + rewrite <- EN. reflexivity.
    + cbn. change (c_free_meta_head (ctx st0) = None). rewrite EF. exact (ks_fl _ _ _ _ _ K).
    + intros g' Hg'. rewrite gmr_upd_other by congruence. unfold get_meta_rec. cbn. rewrite EM. reflexivity.
    + rewrite gmr_upd_same. reflexivity.
    + intros Hin. destruct (HABOVE mf) as [H|H]; [apply in_or_app; left; exact Hin | apply H; reflexivity | lia].
    + exists (aadd mf META_SIZE). split; [reflexivity|]. intros g' Hg'. cbn [aadd fst snd]. unfold META_SIZE.
      destruct Hg' as [<-|Hg']; [right; lia|]. destruct (HABOVE g') as [H|H]; [apply in_or_app; left; exact Hg' | left; exact H | right; lia].
    + unfold cnt in *. rewrite count_upd_meta, count_am_take_ctx. lia.
Qed.

Lemma KST_weaken_rid : forall d cs cs' a44 fl bl,
  KST d cs a44 fl bl ->
  (forall sc, active cs' sc = active cs sc) -> c_free_meta_head (ctx cs') = c_free_meta_head (ctx cs) ->
  s_metas cs' = s_metas cs -> s_slots cs' = s_slots cs -> (s_next_rid cs <= s_next_rid cs')%N ->
  c_avail_meta (ctx cs') = c_avail_meta (ctx cs) -> cnt cs' = cnt cs ->
  KST d cs' a44 fl bl.
Proof.
  intros d cs cs' a44 fl bl [K1 K2 K3 K4 K5 K6 K7 K8 K9] EA EF EM ES EN EV EC.
  assert (ER : forall g, get_meta_rec cs' g = get_meta_rec cs g) by (intros g; unfold get_meta_rec; rewrite EM; reflexivity).
  constructor.
  - intros sc. rewrite EA. apply K1.
  - rewrite EF. exact K2.
  - intros a Ha. rewrite ER. apply K3. exact Ha.
  - intros g b Hin. destruct (K4 g b Hin) as (S1 & S2 & S3 & S4). rewrite ES, ER. repeat split; try assumption. lia.
  - exact K5.
  - exact K6.
  - intros m Hm. destruct (K7 m Hm) as (b & Hb & Hr). exists b. rewrite ER. auto.
  - destruct K8 as (mf & H1 & H2). exists mf. rewrite EV. auto.
  - rewrite EC. exact K9.
Qed.

Lemma maplen_nz : forall n, MMAP_THRESHOLD <= n -> n < 2^62 -> Z.land ((n + IB + UNIT + 4095) / 4096) (2^52 - 1) <> 0.
Proof.
  intros n H1 H2. unfold MMAP_THRESHOLD, IB, UNIT in *. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
  assert (0 < (n + 4 + 16 + 4095) / 4096 < 2^52).
  { split; [apply Z.div_str_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma big_finish : forall d cs0 cs' a44 fl bl g rid (F : meta -> meta) ai stride,
  KST d cs0 a44 fl bl -> AMOUT d cs0 bl g cs' ->
  (forall g' b', In (g', b') bl -> (fst b' < rid)%N) -> (s_next_rid cs0 <= N.succ rid)%N -> (rid < s_next_rid cs0)%N ->
  (forall r, m_mem (F r) = Some (rid, 0) /\ m_avail (F r) = 0 /\ m_freed (F r) = 0 /\ m_last_idx (F r) = 0 /\ m_freeable (F r) = 1
             /\ m_maplen (F r) <> 0 /\ m_sizeclass (F r) = 63 /\ m_next (F r) = m_next r) ->
  let st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c)
               (add_slots g (rid, 0) stride 1 (put_group (rid, 0) (Some g) ai (upd_meta g F cs'))) in
  m_mem (get_meta_rec st7 g) = Some (rid, 0) /\ KST (d - 1) st7 a44 None ((g, (rid, 0)) :: bl).
Proof.
  intros d cs0 cs' a44 fl bl g rid F ai stride K AM HRID HNR HNR2 HF st7.
  destruct AM as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  destruct K as [K1 K2 K3 K4 K5 K6 K7 K8 K9].
  assert (EM7 : forall g', get_meta_rec st7 g' = get_meta_rec (upd_meta g F cs') g') by (intros g'; reflexivity).
  assert (ES7 : s_slots st7 = <[aadd (rid, 0) (UNIT + stride * 0) := (g, 0)]> (s_slots cs')) by reflexivity.
  assert (EKEY : aadd (rid, 0) (UNIT + stride * 0) = aadd (rid, 0) UNIT) by (unfold aadd; cbn [fst snd]; f_equal; lia).
  rewrite EKEY in ES7.
  assert (NG : forall g' b', In (g', b') bl -> g' <> g).
  { intros g' b' Hin E. apply A7. subst g'. apply (in_map fst) in Hin. exact Hin. }
  split; [rewrite EM7, gmr_upd_same; apply (HF (get_meta_rec cs' g))|].
  constructor.
  - intros sc. change (active st7 sc) with (active cs' sc). rewrite A1. apply K1.
  - change (c_free_meta_head (ctx st7)) with (c_free_meta_head (ctx cs')). exact A4.
  - intros a Ha. discriminate.
  - intros g' b' [Hin|Hin].
    + injection Hin as <- <-. rewrite ES7, lookup_insert_eq. split; [reflexivity|]. split; [cbn; change (s_next_rid st7) with (s_next_rid cs'); rewrite A3; exact HNR2|].
      split; [reflexivity|]. left. rewrite EM7, gmr_upd_same.
      destruct (HF (get_meta_rec cs' g)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
      repeat split; try assumption. rewrite F8. exact A6.
    + destruct (K4 g' b' Hin) as (S1 & S2 & S3 & S4).
      rewrite ES7, lookup_insert_ne.
      2:{ intros E. pose proof (HRID g' b' Hin) as X. apply (f_equal fst) in E. cbn in E. rewrite <- E in X. lia. }
      rewrite A2. split; [exact S1|]. split; [change (s_next_rid st7) with (s_next_rid cs'); rewrite A3; exact S2|]. split; [exact S3|].
      rewrite EM7, gmr_upd_other by (apply not_eq_sym; eapply NG; exact Hin). rewrite A5 by (eapply NG; exact Hin). exact S4.
  - cbn [map fst fl_list]. rewrite app_nil_r. constructor; [rewrite list_elem_of_In; exact A7|].
    apply NoDup_app in K5. exact (proj1 K5).
  - cbn [map fst snd]. constructor; [|exact K6].
    intros Hin. apply list_elem_of_In in Hin. apply in_map_iff in Hin. destruct Hin as ([g' b'] & E & Hin). cbn in E. pose proof (HRID g' b' Hin). lia.
  - intros m Hm. destruct (K7 m Hm) as (b & Hb & Hr). exists b. split; [right; exact Hb|].
    rewrite EM7, gmr_upd_other by (apply not_eq_sym; eapply NG; exact Hb). rewrite A5 by (eapply NG; exact Hb). exact Hr.
  - destruct A8 as (mf' & H1 & H2). exists mf'. split; [exact H1|]. cbn [map fst fl_list]. rewrite app_nil_r. exact H2.
  - change (cnt st7) with (cnt cs'). exact A9.
Qed.

Theorem malloc_core_big_KST d cs a44 fl bl n :
  KST d cs a44 fl bl -> 1 <= d -> MMAP_THRESHOLD <= n -> n < 2^62 ->
  uall (fun r => match snd r with
                 | Some (g, idx) => idx = 0 /\ exists b, m_mem (get_meta_rec (fst r) g) = Some b /\ KST (d - 1) (fst r) a44 None ((g, b) :: bl)
                 | None => True end)
       (malloc_core lay_none cs n).
Proof.
  intros K Hd Hn Hn2. unfold malloc_core. destruct (size_overflows n); [exact I|].
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hn).
  cbn [uall]. intros z. destruct (negb (mmap_answer_ok _ _ _ z)); [exact I|].
  destruct (is_err z); [exact I|].
  destruct (new_region RKGroup z (n + IB + UNIT) cs) as [st1 rid] eqn:E.
  assert (Erid : rid = s_next_rid cs) by (pose proof (f_equal snd E) as X; cbn in X; symmetry; exact X).
  assert (Est1 : st1 = fst (new_region RKGroup z (n + IB + UNIT) cs)) by (rewrite E; reflexivity).
  assert (K2 : KST d (step_seq st1) a44 fl bl).
  { eapply KST_weaken_rid; [exact K | | | | | | |]; rewrite Est1; unfold step_seq, new_region; cbn [fst];
      destruct (c_seq _ =? 255); try reflexivity; try (intros sc; reflexivity); cbn; lia. }
  assert (ENR : s_next_rid (step_seq st1) = N.succ rid).
  { rewrite Est1, Erid. unfold step_seq, new_region. cbn [fst]. destruct (c_seq _ =? 255); reflexivity. }
  match goal with |- uall _ (alloc_meta ?st ?k ?bail) =>
    destruct (alloc_meta_KST d st a44 fl bl k bail K2 Hd) as (g & cs' & EQ & AM) end.
  rewrite EQ. clear EQ.
  cbn [uall snd fst]. split; [reflexivity|].
  exists (rid, 0).
  apply (big_finish d (step_seq st1) cs' a44 fl bl g rid); [exact K2 | exact AM | | | |].
  - intros g' b' Hin. destruct (ks_blk _ _ _ _ _ K g' b' Hin) as (_ & S2 & _). rewrite Erid. exact S2.
  - rewrite ENR. lia.
  - rewrite ENR. lia.
  - intros r. repeat split; try reflexivity. cbn. apply maplen_nz; assumption.
Qed.

Lemma KST_strip : forall d st a44 fl bl, KST d st a44 fl bl -> KST d (strip st) a44 fl bl.
Proof.
  intros d st a44 fl bl K. eapply KST_weaken_rid; [exact K | | | | | | |]; try reflexivity; try (intros sc; reflexivity).
Qed.

Theorem cmalloc_big_KST d cs a44 fl bl n :
  KST d cs a44 fl bl -> 1 <= d -> MMAP_THRESHOLD <= n -> n < 2^62 ->
  uall (fun r => match snd r with
                 | Some c => exists g b, c = aadd b UNIT /\ KST (d - 1) (fst r) a44 None ((g, b) :: bl)
                 | None => True end)
       (cmalloc cs n).
Proof.
  intros K Hd Hn Hn2. unfold cmalloc. eapply uall_sbind; [apply (malloc_core_big_KST d cs a44 fl bl n K Hd Hn Hn2)|].
  intros [st1 [[g idx]|]] H; cbn [fst snd] in H |- *; [|exact I].
  destruct H as (-> & b & Hmem & K'). cbn [uall fst snd]. exists g, b. split; [|apply KST_strip; exact K'].
  unfold slot_of, slot_start'. rewrite Hmem. cbn [default]. unfold aadd, id. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.

Lemma aptr_eqb_eq : forall a b : aptr, aptr_eqb a b = true -> a = b.
Proof.
  intros [r o] [r' o'] H. unfold aptr_eqb in H. cbn in H. apply andb_true_iff in H. destruct H as [H1 H2].
  apply N.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

Definition bl_remove (g : aptr) (bl : list (aptr * aptr)) : list (aptr * aptr) :=
  List.filter (fun x => negb (aptr_eqb (fst x) g)) bl.

Lemma bl_remove_In : forall g bl x, In x (bl_remove g bl) <-> In x bl /\ fst x <> g.
Proof.
  intros g bl x. unfold bl_remove. rewrite filter_In. split; intros [H1 H2]; (split; [exact H1|]).
  - intros E. rewrite E, aptr_eqb_refl in H2. discriminate.
  - destruct (aptr_eqb (fst x) g) eqn:E; [apply aptr_eqb_eq in E; contradiction | reflexivity].
Qed.

Definition free_final (st : mstate) (g b : aptr) (sc stride : Z) : mstate :=
  let st1 := if sc <? 48 then set_usage sc (usage st sc - (m_last_idx (get_meta_rec st g) + 1)) st else st in
  let st2 := del_slots b stride 1 (del_group b st1) in
  let st3 := record_seq sc (step_seq st2) in
  let st5 := upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) (put_meta g meta0 st3) in
  drop_region (fst b) (set_head LFree (Some g) st5).

Lemma gmr_drop_region r st g : get_meta_rec (drop_region r st) g = get_meta_rec st g. Proof. reflexivity. Qed.
Lemma gmr_set_head_free v st g : get_meta_rec (set_head LFree v st) g = get_meta_rec st g. Proof. reflexivity. Qed.

Lemma free_final_proj : forall st g b sc stride,
  let stF := free_final st g b sc stride in
  (forall s', active stF s' = active st s') /\ c_free_meta_head (ctx stF) = Some g /\
  s_slots stF = delete (aadd b UNIT) (s_slots st) /\ s_next_rid stF = s_next_rid st /\
  c_avail_meta (ctx stF) = c_avail_meta (ctx st) /\ cnt stF = cnt st /\
  (forall g', g' <> g -> get_meta_rec stF g' = get_meta_rec st g') /\
  m_next (get_meta_rec stF g) = Some g /\ m_prev (get_meta_rec stF g) = Some g.
Proof.
  intros st g b sc stride stF. subst stF. unfold free_final.
  assert (EK : aadd b (UNIT + stride * 0) = aadd b UNIT) by (unfold aadd; f_equal; lia).
  unfold record_seq, step_seq.
  destruct (sc <? 48); destruct (sc_in_seq_range sc);
    match goal with |- context [c_seq ?c =? 255] => destruct (c_seq c =? 255) end;
    (repeat split; try reflexivity;
     first [ cbn; rewrite EK; reflexivity
           | intros g' Hg'; rewrite gmr_drop_region, gmr_set_head_free, gmr_upd_other by congruence; rewrite gmr_put_other by congruence; reflexivity
           | rewrite gmr_drop_region, gmr_set_head_free, gmr_upd_same; reflexivity ]).
Qed.

Lemma NoDup_map_In_inj {A B} (f : A -> B) (l : list A) x y :
  NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|a l IH]; intros ND Hx Hy E; [destruct Hx|].
  cbn in ND. apply NoDup_cons in ND. destruct ND as [Na ND].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy]; try reflexivity.
  - exfalso. apply Na. rewrite E. apply list_elem_of_In. apply in_map. exact Hy.
  - exfalso. apply Na. rewrite <- E. apply list_elem_of_In. apply in_map. exact Hx.
  - apply IH; assumption.
Qed.

Lemma NoDup_map_remove {B} (f : aptr * aptr -> B) g bl : NoDup (map f bl) -> NoDup (map f (bl_remove g bl)).
Proof.
  induction bl as [|a bl IH]; intros ND; [constructor|].
  cbn in ND. apply NoDup_cons in ND. destruct ND as [Na ND]. unfold bl_remove. cbn [List.filter].
  destruct (negb (aptr_eqb (fst a) g)); [|apply IH; exact ND].
  cbn [map]. apply NoDup_cons. split; [|apply IH; exact ND].
  intros Hin. apply Na. apply list_elem_of_In in Hin. apply in_map_iff in Hin. destruct Hin as (x & E & Hx).
  apply list_elem_of_In. rewrite <- E. apply in_map. apply (proj1 (bl_remove_In g bl x)) in Hx. exact (proj1 Hx).
Qed.

Lemma free_finish_KST : forall d cs st a44 a44' bl g b sc stride,
  KST d cs a44 None bl -> In (g, b) bl ->
  (forall s', active st s' = if s' =? 44 then a44' else None) -> c_free_meta_head (ctx st) = None ->
  s_slots st = s_slots cs -> s_next_rid st = s_next_rid cs -> c_avail_meta (ctx st) = c_avail_meta (ctx cs) -> cnt st = cnt cs ->
  (forall g', g' <> g -> get_meta_rec st g' = get_meta_rec cs g') ->
  ((a44' = a44 /\ a44 <> Some g) \/ (a44 = Some g /\ a44' = None)) ->
  KST d (free_final st g b sc stride) a44' (Some g) (bl_remove g bl).
Proof.
  intros d cs st a44 a44' bl g b sc stride [K1 K2 K3 K4 K5 K6 K7 K8 K9] Hin EA EF ES EN EV EC ER HA.
  destruct (free_final_proj st g b sc stride) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  constructor.
  - intros s'. rewrite P1. apply EA.
  - exact P2.
  - intros a Ha. injection Ha as <-. split; assumption.
  - intros g' b' Hin'. apply bl_remove_In in Hin'. destruct Hin' as [Hin' Hne]. cbn [fst] in Hne.
    destruct (K4 g' b' Hin') as (S1 & S2 & S3 & S4).
    assert (Hb : b' <> b).
    { intros ->. apply Hne. pose proof (NoDup_map_In_inj (fun x => fst (snd x)) bl (g', b) (g, b) K6 Hin' Hin eq_refl) as E.
      injection E as ->. reflexivity. }
    assert (Hfb : fst b' <> fst b).
    { intros E. apply Hb. pose proof (NoDup_map_In_inj (fun x => fst (snd x)) bl (g', b') (g, b) K6 Hin' Hin E) as E2.
      injection E2 as _ ->. reflexivity. }
    rewrite P3, lookup_delete_ne, ES by (intros E; apply Hfb; apply (f_equal fst) in E; cbn in E; symmetry; exact E).
    split; [exact S1|]. split; [rewrite P4, EN; exact S2|]. split; [exact S3|].
    rewrite P7, ER by exact Hne. destruct S4 as [S4|S4]; [left; exact S4|]. right.
    destruct HA as [[-> _]|[E _]]; [exact S4|]. rewrite E in S4. injection S4 as S4. symmetry in S4. contradiction.
  - apply NoDup_app. split; [apply NoDup_map_remove; apply NoDup_app in K5; exact (proj1 K5)|]. split.
    + intros x Hx Hx2. apply list_elem_of_In in Hx. apply in_map_iff in Hx. destruct Hx as (y & <- & Hy).
      apply bl_remove_In in Hy. destruct Hy as [_ Hy]. apply Hy. cbn [fl_list] in Hx2. apply list_elem_of_In in Hx2.
      destruct Hx2 as [E|[]]. symmetry. exact E.
    + cbn [fl_list]. apply NoDup_singleton.
  - apply NoDup_map_remove. exact K6.
  - intros m Hm. destruct HA as [[-> Hne]|[_ ->]]; [|discriminate].
    destruct (K7 m Hm) as (b0 & Hb0 & Hr). exists b0.
    assert (Hmg : m <> g) by (intros ->; apply Hne; exact Hm).
    split; [apply bl_remove_In; split; [exact Hb0 | exact Hmg]|]. rewrite P7, ER by exact Hmg. exact Hr.
  - destruct K8 as (mf & H1 & H2). exists mf. split; [rewrite P5, EV; exact H1|].
    intros g' Hg'. apply H2. cbn [fl_list]. rewrite app_nil_r. apply in_app_or in Hg'. destruct Hg' as [Hg'|Hg'].
    + apply in_map_iff in Hg'. destruct Hg' as (y & <- & Hy). apply bl_remove_In in Hy. apply in_map. exact (proj1 Hy).
    + cbn [fl_list] in Hg'. destruct Hg' as [<-|[]]. apply (in_map fst) in Hin. exact Hin.
  - rewrite P6, EC. exact K9.
Qed.

Lemma uall_free_group_solo : forall (P : mstate -> Prop) (REC : mstate -> aptr -> Z -> (mstate -> mapinfo -> M mstate) -> M mstate -> M mstate)
    (st cs0 : mstate) (g b : aptr),
  m_mem (get_meta_rec st g) = Some b -> m_last_idx (get_meta_rec st g) = 0 -> m_maplen (get_meta_rec st g) <> 0 ->
  c_free_meta_head (ctx st) = None ->
  P (free_final st g b (m_sizeclass (get_meta_rec st g)) (get_stride (get_meta_rec st g))) ->
  uall P (free_group mstate dec_slots REC st g
            (fun st2 mi => match mi with
               | Some (base, len) =>
                   if negb (len =? 0) then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret cs0))
                   else ret st2
               | None => ret st2 end) (ret cs0)).
Proof.
  intros P REC st cs0 g b Hmem Hli Hml Hfl HP. unfold free_group. rewrite Hmem, Hli.
  replace (m_maplen (get_meta_rec st g) =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hml). cbn [negb].
  unfold free_meta, queue.
  match goal with |- context [put_meta g meta0 ?s3] => set (st3 := s3) end.
  rewrite gmr_put_same. cbn [m_next m_prev meta0 optr_eqb]. unfold guard.
  assert (EH : get_head (put_meta g meta0 st3) LFree = None).
  { subst st3. unfold record_seq, step_seq. destruct (m_sizeclass (get_meta_rec st g) <? 48); destruct (sc_in_seq_range _);
      match goal with |- context [c_seq ?c =? 255] => destruct (c_seq c =? 255) end; exact Hfl. }
  rewrite EH.
  replace (m_maplen (get_meta_rec st g) * 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
  cbn [uall]. intros ru. destruct (munmap_answer_ok ru); [|exact I].
  unfold free_final in HP. rewrite Hli in HP. subst st3. exact HP.
Qed.

Lemma ntf_S {R} (dec : decoder R) f st g i k bail :
  nontrivial_free dec (S f) st g i k bail =
    let mr := get_meta_rec st g in
    let self := bit i in
    let sc := m_sizeclass mr in
    let mask := Z.lor (m_freed mr) (m_avail mr) in
    if (mask + self =? mask_upto (m_last_idx mr)) && okay_to_free st g then
      match m_next mr with
      | Some _ =>
        guard 50 (sc <? 48) (
          let activate_new := optr_eqb (active st sc) (Some g) in
          let st1 := dequeue (LActive sc) g st in
          match activate_new, active st1 sc with
          | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
          | _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
          end) bail
      | None => free_group R dec (nontrivial_free dec f) st g k bail
      end
    else if mask =? 0 then
      guard 51 (sc <? 48) (
        let aor (st : mstate) := k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) self) r) st) None in
        if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st aor bail
        else aor st) bail
    else
      k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) self) r) st) None.
Proof. reflexivity. Qed.

Lemma okay_solo : forall st g,
  m_freeable (get_meta_rec st g) = 1 -> m_maplen (get_meta_rec st g) <> 0 ->
  (m_sizeclass (get_meta_rec st g) = 63 \/ (m_sizeclass (get_meta_rec st g) = 44 /\ m_next (get_meta_rec st g) = Some g)) ->
  okay_to_free st g = true.
Proof.
  intros st g Hf Hm [H63 | [H44 Hn]]; unfold okay_to_free; rewrite Hf; cbn [Z.eqb].
  - rewrite H63. reflexivity.
  - rewrite H44. change (48 <=? 44) with false. cbn [orb].
    destruct (get_stride (get_meta_rec st g) <? UNIT * size_class 44); [reflexivity|].
    replace (m_maplen (get_meta_rec st g) =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hm).
    rewrite Hn. cbn [optr_eqb]. rewrite aptr_eqb_refl. cbn [negb]. reflexivity.
Qed.

Theorem cfree_KST d cs a44 bl g b :
  KST d cs a44 None bl -> In (g, b) bl ->
  uall (fun cs' => exists a44', KST d cs' a44' (Some g) (bl_remove g bl) /\ (a44' = a44 \/ a44' = None))
       (cfree cs (Some (aadd b UNIT))).
Proof.
  intros K Hin. destruct (ks_blk _ _ _ _ _ K g b Hin) as (HS & HRID & HB0 & HREC).
  unfold cfree. rewrite HS.
  eapply uall_sbind with (P1 := fun st1 => exists a44', KST d st1 a44' (Some g) (bl_remove g bl) /\ (a44' = a44 \/ a44' = None)).
  2:{ intros st1 (a' & K' & HA). cbn [uall]. exists a'. split; [apply KST_strip; exact K' | exact HA]. }
  assert (SOLO : solo_rec (get_meta_rec cs g) b /\
                 ((m_sizeclass (get_meta_rec cs g) = 63 /\ m_next (get_meta_rec cs g) = None /\ a44 <> Some g)
                  \/ (m_sizeclass (get_meta_rec cs g) = 44 /\ m_next (get_meta_rec cs g) = Some g /\ a44 = Some g))).
  { destruct HREC as [(HS0 & H63 & HN) | HA].
    - split; [exact HS0|]. left. split; [exact H63|]. split; [exact HN|]. intros E.
      destruct (ks_a44 _ _ _ _ _ K g E) as (b0 & _ & (_ & H44 & _)). rewrite H63 in H44. discriminate.
    - destruct (ks_a44 _ _ _ _ _ K g HA) as (b0 & Hb0 & (HS0 & H44 & HN & _)).
      assert (b0 = b).
      { pose proof (ks_ndm _ _ _ _ _ K) as ND. cbn [fl_list] in ND. rewrite app_nil_r in ND.
        pose proof (NoDup_map_In_inj fst bl (g, b0) (g, b) ND Hb0 Hin eq_refl) as E. injection E as ->. reflexivity. }
      subst b0. split; [exact HS0|]. right. auto. }
  destruct SOLO as ((Hmem & Hav & Hfr & Hli & Hfa & Hml) & CASE).
  unfold free_tail. rewrite Hfr, Hav, Hli.
  change (negb (testbit (Z.lor 0 0) 0)) with true. unfold guard at 1.
  change (negb ((0 =? 0) || (Z.lor 0 0 + bit 0 =? mask_upto 0))) with false. cbv iota.
  unfold FUEL. change 64%nat with (S 63). rewrite ntf_S. cbv zeta. rewrite Hfr, Hav, Hli.
  change (Z.lor 0 0 + bit 0 =? mask_upto 0) with true.
  rewrite (okay_solo cs g Hfa Hml) by (destruct CASE as [(H & _ & _) | (H & Hn & _)]; [left; exact H | right; split; assumption]).
  cbn [andb].
  destruct CASE as [(H63 & HN & HA) | (H44 & HN & HA)]; rewrite HN.
  -
    apply (uall_free_group_solo _ _ cs cs g b); try assumption; [exact (ks_fl _ _ _ _ _ K)|].
    exists a44. split; [|left; reflexivity].
    apply (free_finish_KST d cs cs a44 a44 bl g b); try assumption; try reflexivity.
    + exact (ks_act _ _ _ _ _ K).
    + exact (ks_fl _ _ _ _ _ K).
    + left. split; [reflexivity | exact HA].
  -
    rewrite H44. change (44 <? 48) with true. unfold guard at 1.
    rewrite (ks_act _ _ _ _ _ K 44). change (44 =? 44) with true. cbv iota. rewrite HA. cbn [optr_eqb]. rewrite aptr_eqb_refl.
    pose proof (active_dequeue_singleton 44 g cs 44 HN) as AD. change (44 =? 44) with true in AD. cbv iota in AD.
    cbv zeta. rewrite AD.
    set (st1 := dequeue (LActive 44) g cs).
    assert (DQ : st1 = upd_meta g (fun r => m_set_prev None (m_set_next None r)) (set_head (LActive 44) None cs)).
    { subst st1. unfold dequeue. rewrite HN. cbn [optr_eqb]. rewrite aptr_eqb_refl. reflexivity. }
    assert (R1 : get_meta_rec st1 g = m_set_prev None (m_set_next None (get_meta_rec cs g))) by (rewrite DQ, gmr_upd_same; reflexivity).
    apply (uall_free_group_solo _ _ st1 cs g b).
    + rewrite R1. exact Hmem.
    + rewrite R1. exact Hli.
    + rewrite R1. exact Hml.
    + rewrite DQ. exact (ks_fl _ _ _ _ _ K).
    + exists None. split; [|right; reflexivity].
      apply (free_finish_KST d cs st1 a44 None bl g b); try assumption.
      * intros s'. pose proof (active_dequeue_singleton 44 g cs s' HN) as X. fold st1 in X. rewrite X.
        rewrite (ks_act _ _ _ _ _ K s'). destruct (s' =? 44); reflexivity.
      * rewrite DQ. exact (ks_fl _ _ _ _ _ K).
      * rewrite DQ. reflexivity.
      * rewrite DQ. reflexivity.
      * rewrite DQ. reflexivity.
      * rewrite DQ. reflexivity.
      * intros g' Hg'. rewrite DQ, gmr_upd_other by congruence. reflexivity.
      * right. split; [exact HA | reflexivity].
Qed.
