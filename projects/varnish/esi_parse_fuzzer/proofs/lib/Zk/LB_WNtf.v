(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require STree Malloc Mall7vg KInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_List.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_S421.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Pres4 MI_WFree MI_Ws22.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WNtf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WNtf MI_WNtf2 LB_T80p LB_Inv LB_Sum.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.STree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malloc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall7vg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List.MI_Tree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Kit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Arith OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_List OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Geom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ext OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Ext2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_S421 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2.MI_Pres1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4.MI_Pres3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Pres4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Ws22 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf.MI_WKill OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WNtf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_T80p OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LB_Sum OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.LB_Dead.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LBCEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition geom (r : meta) : option aptr * Z * Z * Z := (m_mem r, m_sizeclass r, m_last_idx r, m_maplen r).

Lemma geom_stride r r' : geom r' = geom r -> get_stride r' = get_stride r.
Proof. unfold geom, get_stride. intros E. inversion E. rewrite H1, H2, H3. reflexivity. Qed.
Lemma geom_data r r' : data_of r' = data_of r -> geom r' = geom r.
Proof. intros D. apply data_of_eq in D as (E1 & E2 & E3 & E4 & E5 & E6 & E7). unfold geom. congruence. Qed.

Record FFR (st st' : mstate) : Prop := mkFFR {
  ffr_groups : forall b h', s_groups st' !! b = Some h' -> exists h, s_groups st !! b = Some h /\ g_meta h = g_meta h';
  ffr_slots : forall s v, s_slots st' !! s = Some v -> s_slots st !! s = Some v;
  ffr_meta : forall m, geom (MR st' m) = geom (MR st m) \/ (m_mem (MR st' m) = None /\ m_next (MR st' m) <> None);
  ffr_keepq : forall m, m_mem (MR st m) = None -> m_next (MR st m) <> None -> m_mem (MR st' m) = None /\ m_next (MR st' m) <> None;
  ffr_dom : forall m, s_metas st' !! m <> None <-> s_metas st !! m <> None;
  ffr_regions : s_regions st' = s_regions st;
  ffr_areas : s_areas st' = s_areas st;
  ffr_next_rid : s_next_rid st' = s_next_rid st;
  ffr_amc : c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st);
  ffr_amas : c_avail_meta_areas (s_ctx st') = c_avail_meta_areas (s_ctx st);
  ffr_amac : c_avail_meta_area_count (s_ctx st') = c_avail_meta_area_count (s_ctx st);
  ffr_shift : c_meta_alloc_shift (s_ctx st') = c_meta_alloc_shift (s_ctx st);
  ffr_brk : c_brk (s_ctx st') = c_brk (s_ctx st)
}.

Lemma FFR_refl st : FFR st st.
Proof. constructor; auto; try tauto. intros b h' H. exists h'. auto. Qed.

Lemma FFR_trans a b c : FFR a b -> FFR b c -> FFR a c.
Proof.
  intros [G1 S1 M1 K1 D1 R1 A1 N1 C1 C2 C3 C4 C5] [G2 S2 M2 K2 D2 R2 A2 N2 E1 E2 E3 E4 E5]. constructor; try congruence.
  - intros bb h'' H. destruct (G2 _ _ H) as (h' & H' & E'). destruct (G1 _ _ H') as (h & H0 & E0). exists h. split; [exact H0| congruence].
  - intros s v H. apply S1. apply S2. exact H.
  - intros m. destruct (M2 m) as [E|[Z2 N2']].
    + destruct (M1 m) as [E'|[Z1 N1']]; [left; congruence|]. right. apply K2; assumption.
    + right. auto.
  - intros m Z0 N0. destruct (K1 m Z0 N0) as [Z1 N1']. apply K2; assumption.
  - intros m. rewrite D2. apply D1.
Qed.

(* [comment removed for export] *)
Lemma FFR_ctx st f :
  (forall c, c_avail_meta_count (f c) = c_avail_meta_count c) -> (forall c, c_avail_meta_areas (f c) = c_avail_meta_areas c) ->
  (forall c, c_avail_meta_area_count (f c) = c_avail_meta_area_count c) -> (forall c, c_meta_alloc_shift (f c) = c_meta_alloc_shift c) ->
  (forall c, c_brk (f c) = c_brk c) ->
  FFR st (upd_ctx f st).
Proof.
  intros H1 H2 H3 H4 H5. constructor; cbn; auto; try tauto. intros b h' H. exists h'. auto.
Qed.

(* [comment removed for export] *)
Lemma FFR_record_seq st sc : FFR st (record_seq sc st).
Proof. unfold record_seq. destruct (sc_in_seq_range sc); [apply FFR_ctx; reflexivity| apply FFR_refl]. Qed.
Lemma FFR_step_seq st : FFR st (step_seq st).
Proof. unfold step_seq. destruct (c_seq (ctx st) =? 255); apply FFR_ctx; reflexivity. Qed.
Lemma FFR_set_head st h v : FFR st (set_head h v st).
Proof. destruct h; apply FFR_ctx; reflexivity. Qed.

(* [comment removed for export] *)
Lemma FFR_upd_meta st m f : s_metas st !! m <> None ->
  (forall r, geom (f r) = geom r) -> (forall r, m_next r <> None -> m_next (f r) <> None) -> FFR st (upd_meta m f st).
Proof.
  intros Hm Hg Hn. constructor; cbn -[get_meta_rec]; auto; try tauto.
  - intros b h' H. exists h'. auto.
  - intros x. unfold MR. rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x m) as [->|NE]; [left; apply Hg| left; reflexivity].
  - intros x Z0 N0. unfold MR in *. rewrite get_meta_rec_upd. destruct (aptr_eqb_spec x m) as [->|NE]; [| auto].
    split; [pose proof (Hg (get_meta_rec st m)) as E; unfold geom in E; congruence| apply Hn; exact N0].
  - intros x. rewrite lookup_metas_upd. destruct (aptr_eqb_spec x m) as [->|NE]; [| tauto]. split; [auto| intros; discriminate].
Qed.

Lemma FFR_del_group st b : FFR st (del_group b st).
Proof.
  constructor; cbn; auto; try tauto.
  intros bb h' H. rewrite lookup_del_group in H. destruct (aptr_eqb bb b); [discriminate|]. exists h'. auto.
Qed.

Lemma FFR_del_slots st p stride cnt : 0 <= cnt -> 0 < stride -> FFR st (del_slots p stride cnt st).
Proof.
  intros Hc Hs. constructor; cbn -[del_slots s_slots]; rewrite ?s_groups_del_slots, ?s_metas_del_slots, ?s_regions_del_slots, ?s_areas_del_slots, ?s_ctx_del_slots, ?s_next_rid_del_slots; auto; try tauto.
  - intros bb h' H. exists h'. auto.
  - intros s v H. rewrite (lookup_del_slots p stride cnt st s Hc Hs) in H. destruct (_ && _); [discriminate| exact H].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma FFR_dequeue st h m : s_metas st !! m <> None -> m_mem (MR st m) <> None -> m_next (MR st m) <> None ->
  (forall n, m_next (MR st m) = Some n -> s_metas st !! n <> None) ->
  (forall p, m_prev (MR st m) = Some p -> s_metas st !! p <> None) ->
  FFR st (dequeue h m st).
Proof.
  intros Hm Hmem Hl Hn Hp. destruct (dequeue_frame h m st) as (R1 & _ & R3 & R4 & R5 & R6 & _ & _ & _ & CB).
  constructor; rewrite ?R1, ?R4, ?R5, ?R6, ?R3; auto; try (destruct CB; congruence).
  - intros b h' H. exists h'. auto.
  - intros x. left. apply geom_data. apply dequeue_data.
  - intros x Z0 N0. pose proof (geom_data _ _ (dequeue_data h m st x)) as G. unfold geom in G.
    split; [congruence|]. rewrite dequeue_next. destruct (aptr_eqb_spec x m) as [->|NE]; [exfalso; apply Hmem; exact Z0|].
    destruct (optr_eqb (m_next (MR st m)) (Some m)); [exact N0|]. destruct (optr_eqb_spec (m_prev (MR st m)) (Some x)) as [E|NE2]; [| exact N0].
    exact Hl.
  - intros x. split; [| apply dequeue_keys_mono]. intros H. apply dequeue_keys in H as [H|[->|[H|H]]]; [exact H| exact Hm| apply Hp; exact H| apply Hn; exact H].
Qed.

(* [comment removed for export] *)
Lemma FFR_queue_st st h g : s_metas st !! g <> None -> m_mem (MR st g) <> None ->
  (forall a, get_head st h = Some a -> s_metas st !! a <> None /\ m_next (MR st a) <> None) ->
  (forall a z, get_head st h = Some a -> m_prev (MR st a) = Some z -> s_metas st !! z <> None) ->
  FFR st (queue_st h g st).
Proof.
  intros Hg Hmem Hh Hz. destruct (queue_frame h g st) as (R1 & _ & R3 & R4 & R5 & R6 & _ & _ & _ & CB).
  constructor; rewrite ?R1, ?R4, ?R5, ?R6, ?R3; auto; try (destruct CB; congruence).
  - intros b h' H. exists h'. auto.
  - intros x. left. apply geom_data. apply queue_data.
  - intros x Z0 N0. pose proof (geom_data _ _ (queue_data h g st x)) as G. unfold geom in G.
    split; [congruence|]. rewrite queue_next.
    destruct (get_head st h) as [a|] eqn:Ea.
    + destruct (aptr_eqb_spec x a) as [->|NE].
      * destruct (optr_eqb (m_prev (MR st a)) (Some a)); [discriminate|]. destruct (aptr_eqb a g); [discriminate| exact N0].
      * destruct (optr_eqb (m_prev (MR st a)) (Some x)); [discriminate|]. destruct (aptr_eqb x g); [discriminate| exact N0].
    + destruct (aptr_eqb x g); [discriminate| exact N0].
  - intros x. split; [| apply queue_keys_mono]. intros H. apply queue_keys in H as [H|[->|[H|(a & Ha & Hp)]]]; [exact H| exact Hg| exact (proj1 (Hh _ H))| exact (Hz _ _ Ha Hp)].
Qed.

(* [comment removed for export] *)
Lemma FFR_fm_st st g : s_metas st !! g <> None -> m_mem (MR st g) <> None ->
  (forall a, get_head st LFree = Some a -> s_metas st !! a <> None /\ m_next (MR st a) <> None /\ a <> g) ->
  (forall a z, get_head st LFree = Some a -> m_prev (MR st a) = Some z -> s_metas st !! z <> None) ->
  FFR st (fm_st st g).
Proof.
  intros Hg Hmem Hh Hz. unfold fm_st. set (st1 := put_meta g meta0 st).
  destruct (queue_frame LFree g st1) as (R1 & _ & R3 & R4 & R5 & R6 & _ & _ & _ & CB).
  assert (M1 : forall x, MR st1 x = if aptr_eqb x g then meta0 else MR st x) by (intros x; unfold st1, MR; apply get_meta_rec_put).
  assert (H1 : get_head st1 LFree = get_head st LFree) by reflexivity.
  constructor; rewrite ?R1, ?R4, ?R5, ?R6, ?R3; auto; try (destruct CB; cbn in *; congruence).
  - intros b h' H. exists h'. auto.
  - intros x. pose proof (geom_data _ _ (queue_data LFree g st1 x)) as G. rewrite M1 in G.
    destruct (aptr_eqb_spec x g) as [E|NE]; [| left; exact G]. rewrite E in G |- *. rewrite ?aptr_eqb_refl in G.
    right. unfold geom in G. cbn [m_mem meta0] in G. split; [congruence|]. rewrite queue_next, H1.
    destruct (get_head st LFree) as [a|] eqn:Ea.
    + destruct (Hh a eq_refl) as (_ & _ & NE). rewrite (aptr_eqb_neq g a) by congruence.
      destruct (optr_eqb (m_prev (MR st1 a)) (Some g)); [discriminate|]. rewrite aptr_eqb_refl. discriminate.
    + rewrite aptr_eqb_refl. discriminate.
  - intros x Z0 N0. pose proof (geom_data _ _ (queue_data LFree g st1 x)) as G. rewrite M1 in G. unfold geom in G.
    destruct (aptr_eqb_spec x g) as [E|NE]; [rewrite E in Z0; exfalso; exact (Hmem Z0)|].
    split; [congruence|]. rewrite queue_next, H1.
    destruct (get_head st LFree) as [a|] eqn:Ea.
    + rewrite !M1. destruct (Hh a eq_refl) as (_ & Na & NEa). rewrite (aptr_eqb_neq a g) by congruence.
      destruct (aptr_eqb_spec x a) as [->|NEx].
      * destruct (optr_eqb (m_prev (MR st a)) (Some a)); [discriminate|]. exact Na.
      * destruct (optr_eqb (m_prev (MR st a)) (Some x)); [discriminate|]. rewrite (aptr_eqb_neq x g) by congruence. exact N0.
    + rewrite M1, (aptr_eqb_neq x g) by congruence. exact N0.
  - intros x.
    assert (D1 : s_metas st1 !! x <> None <-> s_metas st !! x <> None).
    { unfold st1. rewrite lookup_metas_put. destruct (aptr_eqb_spec x g) as [->|NE]; [split; [auto| intros; discriminate]| tauto]. }
    split.
    + intros H. apply queue_keys in H as [H|[->|[H|(a & Ha & Hp)]]]; [apply D1; exact H| exact Hg| rewrite H1 in H; exact (proj1 (Hh _ H))|].
      rewrite H1 in Ha. rewrite M1 in Hp. destruct (Hh a Ha) as (_ & _ & NEa). rewrite (aptr_eqb_neq a g) in Hp by congruence. exact (Hz _ _ Ha Hp).
    + intros H. apply queue_keys_mono. apply D1. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma FFR_dequeue_INV X st L BL LS g bg sc : INVL X st L BL LS -> hosts st bg g -> In g (LS (LActive sc)) ->
  FFR st (dequeue (LActive sc) g st).
Proof.
  intros INV Hg Hin. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). destruct Hg as [ai Hg].
  apply FFR_dequeue.
  - exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)).
  - rewrite (hosts_mem _ _ _ IM _ _ (ex_intro _ ai Hg)). discriminate.
  - apply (lists_in_next_some _ _ (old_lists _ _ _ _ _ INV) (LActive sc)). exact Hin.
  - intros n Hn. apply (listed_present _ _ _ _ _ INV n (LActive sc)). exact (next_listed _ _ _ _ _ INV _ _ _ Hin Hn).
  - intros p Hp. apply (listed_present _ _ _ _ _ INV p (LActive sc)). exact (prev_listed _ _ _ _ _ INV _ _ _ Hin Hp).
Qed.

Lemma FFR_queue_INV X st L BL LS g bg h : INVL X st L BL LS -> hosts st bg g -> FFR st (queue_st h g st).
Proof.
  intros INV Hg. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH). destruct Hg as [ai Hg].
  apply FFR_queue_st.
  - exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)).
  - rewrite (hosts_mem _ _ _ IM _ _ (ex_intro _ ai Hg)). discriminate.
  - intros a Ha. pose proof (head_listed _ _ _ _ _ INV h a Ha) as Hin. split; [exact (listed_present _ _ _ _ _ INV a h Hin)| exact (lists_in_next_some _ _ (old_lists _ _ _ _ _ INV) h a Hin)].
  - intros a z Ha Hz. pose proof (head_listed _ _ _ _ _ INV h a Ha) as Hin. apply (listed_present _ _ _ _ _ INV z h). exact (prev_listed _ _ _ _ _ INV _ _ _ Hin Hz).
Qed.

Lemma FFR_fm_st_INV X st L BL LS g : INVL X st L BL LS -> In g (x_zomb X) -> FFR st (fm_st st g).
Proof.
  intros INV Hz. pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (im_zomb _ _ _ IM g Hz) as (NL & NX & NP & b & Hmem & Hb).
  apply FFR_fm_st.
  - intros E. unfold MR, get_meta_rec in Hmem. rewrite E in Hmem. cbn in Hmem. discriminate.
  - rewrite Hmem. discriminate.
  - intros a Ha. pose proof (head_listed _ _ _ _ _ INV LFree a Ha) as Hin.
    split; [exact (listed_present _ _ _ _ _ INV a LFree Hin)|]. split; [exact (lists_in_next_some _ _ (old_lists _ _ _ _ _ INV) LFree a Hin)|].
    intros ->. apply NL. exists LFree. exact Hin.
  - intros a z Ha Hz'. pose proof (head_listed _ _ _ _ _ INV LFree a Ha) as Hin. apply (listed_present _ _ _ _ _ INV z LFree). exact (prev_listed _ _ _ _ _ INV _ _ _ Hin Hz').
Qed.

Lemma FFR_kill st st1 g p : (exists U, st1 = upd_ctx (fun c => set_usage_map U c) st) -> 0 <= m_last_idx (MR st g) -> 0 < get_stride (MR st g) ->
  FFR st (del_slots p (get_stride (MR st g)) (m_last_idx (MR st g) + 1) (del_group p st1)).
Proof.
  intros [U ->] Hl Hs. eapply FFR_trans; [| apply FFR_del_slots; lia]. eapply FFR_trans; [| apply FFR_del_group]. apply FFR_ctx; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition NTF_ATQ (T : Type) (f : nat) : Prop :=
  forall (dec1 dec2 : decoder T), DEC_OK T dec1 -> DEC_OK T dec2 ->
  forall X st L BL LS g bg i (k : mstate -> mapinfo -> M T) (bail : M T),
  INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
  x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
  (1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
  exists st' mi LS',
    nontrivial_free dec1 f st g i k bail = k st' mi /\ nontrivial_free dec2 f st g i k bail = k st' mi /\
    (s_regions st' = s_regions st /\ s_secret st' = s_secret st) /\
    (FFR st st' /\
     (s_groups st' !! bg = None
      \/ (mi = None /\ s_groups st' = s_groups st
          /\ ((Z.lor (m_freed (MR st g)) (m_avail (MR st g)) + bit i =? mask_upto (m_last_idx (MR st g))) && okay_to_free st g) = false))) /\
    match mi with
    | None => INVL (xpend X None) st' L BL LS'
    | Some (base, len) =>
        exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
          /\ len = round_up_pg (r_len r) /\ 0 < len
          /\ INVL (xorph (xpend X None) (Some (fst base))) st' L BL LS'
    end.

Section FG.
Variables (T : Type) (f : nat).
Hypothesis IHf : NTF_ATQ T f.
Variables (dec1 dec2 : decoder T).
Hypothesis D1 : DEC_OK T dec1.
Hypothesis D2 : DEC_OK T dec2.
Variables (idle zomb : list aptr) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g bg : aptr) (ai i : Z).
Variables (k : mstate -> mapinfo -> M T) (bail : M T).
Let X := mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hg : s_groups st !! bg = Some (mkGhdr (Some g) ai).
Hypothesis NL : m_next (MR st g) = None.
Hypothesis Hi : 0 <= i <= m_last_idx (MR st g).
Hypothesis ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i ->
  tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true.
Hypothesis FUEL : 49 - m_sizeclass (MR st g) <= Z.of_nat (S f).

Theorem free_group_okQ :
  exists st' mi LS', free_group T dec1 (nontrivial_free dec1 f) st g k bail = k st' mi /\
    free_group T dec2 (nontrivial_free dec2 f) st g k bail = k st' mi /\
    (s_regions st' = s_regions st /\ s_secret st' = s_secret st) /\
    (FFR st st' /\ s_groups st' !! bg = None) /\
    match mi with
    | None => INVL (mkX idle zomb None None None) st' L BL LS'
    | Some (base, len) =>
        exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
          /\ len = round_up_pg (r_len r) /\ 0 < len
          /\ INVL (mkX idle zomb None (Some (fst base)) None) st' L BL LS'
    end.
Proof.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (KSEC : forall U, s_secret (del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1)
            (del_group bg (upd_ctx (fun c => set_usage_map U c) st))) = s_secret st) by (intros; reflexivity).
  assert (FMSEC : forall s, s_secret (fm_st s g) = s_secret s).
  { intros s0. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 s0)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
  assert (Hgh : hosts st bg g) by (exists ai; exact Hg).
  assert (NZ : ~ In g zomb) by (intros Hz; exact (zomb_not_live _ _ _ _ _ INV g Hz (ex_intro _ bg Hgh))).
  assert (NI : ~ In g idle) by (intros Hz; exact (idle_not_live _ _ _ _ _ INV g Hz (ex_intro _ bg Hgh))).
  destruct (fg_st1 X st L BL LS g bg ai INV Hg) as (S1 & U1 & U2). cbn zeta in S1, U1, U2.
  unfold free_group. fold (MR st g).
  set (st1 := if m_sizeclass (MR st g) <? 48 then set_usage (m_sizeclass (MR st g)) (usage st (m_sizeclass (MR st g)) - (m_last_idx (MR st g) + 1)) st else st) in *.
  rewrite (hosts_mem _ _ _ IM _ _ Hgh).
  set (stk := del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1) (del_group bg st1)).
  pose proof (INVL_kill X st st1 L BL LS g bg ai i INV Hg eq_refl NL eq_refl Hi eq_refl ALL S1 U1 U2) as INVK.
  cbn [x_idle x_zomb X] in INVK. fold stk in INVK.
  pose proof (K_MR st st1 g bg S1 U1 U2) as KMR. fold stk in KMR.
  assert (FK : FFR st stk) by (unfold stk; apply (FFR_kill st st1 g bg S1); [pose proof (g_li _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hg)); lia| pose proof (stride_ge _ _ _ IG _ _ Hgh); unfold UNIT in *; lia]).
  assert (GK : s_groups stk !! bg = None) by (unfold stk; rewrite s_groups_del_slots, lookup_del_group, aptr_eqb_refl; reflexivity).
  assert (GONE : forall s2, FFR stk s2 -> s_groups s2 !! bg = None).
  { intros s2 F2. destruct (s_groups s2 !! bg) as [h|] eqn:E; [| reflexivity]. destruct (ffr_groups _ _ F2 _ _ E) as (h0 & H0 & _). rewrite GK in H0. discriminate. }
  assert (GFM : forall s2, s_groups (fm_st s2 g) = s_groups s2).
  { intros s2. unfold fm_st. destruct (queue_frame LFree g (put_meta g meta0 s2)) as (_ & _ & _ & _ & Q5 & _). rewrite Q5. reflexivity. }
  destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [Hml|Hml]; cbn [negb].
  - (* [comment removed for export] *)
    destruct (dec_hdr_eq X st st1 L BL LS g bg ai i INV Hg Hi S1 U1 U2
                (fun m idx => nontrivial_free dec1 f stk m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail Hml)
      as (pm & ip & bpm & EQ & Hs' & Hpm' & Hf & Hip & Ep & Hsc).
    fold stk in EQ, Hs', Hpm'.
    assert (DQ : decodes T stk bg pm ip).
    { split; [exact Hs'|]. intros k' bail'.
      destruct (dec_hdr_eq X st st1 L BL LS g bg ai i INV Hg Hi S1 U1 U2 k' bail' Hml) as (pm' & ip' & bpm' & EQ' & Hs'' & _).
      fold stk in EQ', Hs''. rewrite Hs' in Hs''. inversion Hs''. subst. exact EQ'. }
    rewrite (D1 stk bg pm ip _ bail DQ), (D2 stk bg pm ip _ bail DQ).
    destruct (IHf dec1 dec2 D1 D2 (mkX idle (g :: zomb) (Some bg) None None) stk L BL LS pm bpm ip
                  (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail INVK Hpm')
      as (st3 & mi & LS3 & EQ3 & EQ3b & REG3 & [FFR3 _] & POST3).
    + rewrite KMR. exact Hip.
    + cbn. rewrite KMR, Ep. reflexivity.
    + reflexivity.
    + reflexivity.
    + lia.
    + rewrite KMR. lia.
    + rewrite EQ3, EQ3b. rewrite !free_meta_eq. exists (fm_st st3 g), mi.
      destruct mi as [[base len]|].
      * destruct POST3 as (r & B0 & Hr & Hk & Hlen & Hpos & INV3). cbn in INV3.
        destruct (INVL_free_zombie idle zomb None (Some (fst base)) st3 L BL LS3 g INV3 NZ NI) as [LS4 INV4].
        exists LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, FMSEC.
        split; [destruct REG3 as [R3a R3b]; rewrite R3a, R3b; split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]|].
        split; [split; [eapply FFR_trans; [exact FK|]; eapply FFR_trans; [exact FFR3|]; apply (FFR_fm_st_INV _ _ _ _ _ _ INV3); left; reflexivity| rewrite GFM; apply GONE; exact FFR3]|].
        exists r.
        split; [exact B0|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hpos| exact INV4].
      * cbn in POST3. destruct (INVL_free_zombie idle zomb None None st3 L BL LS3 g POST3 NZ NI) as [LS4 INV4].
        exists LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, FMSEC.
        split; [destruct REG3 as [R3a R3b]; rewrite R3a, R3b; split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]|].
        split; [split; [eapply FFR_trans; [exact FK|]; eapply FFR_trans; [exact FFR3|]; apply (FFR_fm_st_INV _ _ _ _ _ _ POST3); left; reflexivity| rewrite GFM; apply GONE; exact FFR3]| exact INV4].
  - (* [comment removed for export] *)
    rewrite !free_meta_eq.
    destruct (kill_top X st st1 L BL LS g bg ai INV Hg S1 U1 U2 Hml) as (r & B0 & Hr & Hk & Hlen & Hpos).
    fold stk in Hr.
    assert (INV2 : INVL (mkX idle (g :: zomb) None (Some (fst bg)) None) (record_seq (m_sizeclass (MR st g)) (step_seq stk)) L BL LS).
    { apply INVL_record_seq. apply INVL_step_seq. unfold stk. cbn [negb] in INVK. exact INVK. }
    destruct (INVL_free_zombie idle zomb None (Some (fst bg)) _ L BL LS g INV2 NZ NI) as [LS4 INV4].
    assert (RS : forall sc s, s_regions (record_seq sc (step_seq s)) = s_regions s).
    { intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
    assert (RSS : forall sc s, s_secret (record_seq sc (step_seq s)) = s_secret s).
    { intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
    eexists _, _, LS4. split; [reflexivity|]. split; [reflexivity|]. rewrite regions_fm_st, RS, FMSEC, RSS.
    split; [split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]|].
    assert (FRS : FFR stk (record_seq (m_sizeclass (MR st g)) (step_seq stk))) by (eapply FFR_trans; [apply FFR_step_seq| apply FFR_record_seq]).
    split; [split; [eapply FFR_trans; [exact FK|]; eapply FFR_trans; [exact FRS|]; apply (FFR_fm_st_INV _ _ _ _ _ _ INV2); left; reflexivity| rewrite GFM; apply GONE; exact FRS]|].
    cbn. exists r. cbn.
    split; [exact B0|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hpos| exact INV4].
Qed.
End FG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ntf_unfold {T} dec f st g i (k : mstate -> mapinfo -> M T) bail :
  nontrivial_free dec (S f) st g i k bail =
    (if (Z.lor (m_freed (MR st g)) (m_avail (MR st g)) + bit i =? mask_upto (m_last_idx (MR st g))) && okay_to_free st g then
      match m_next (MR st g) with
      | Some _ =>
        guard 50 (m_sizeclass (MR st g) <? 48) (
          match optr_eqb (active st (m_sizeclass (MR st g))) (Some g), active (dequeue (LActive (m_sizeclass (MR st g))) g st) (m_sizeclass (MR st g)) with
          | true, Some a => activate_group a (dequeue (LActive (m_sizeclass (MR st g))) g st)
                              (fun st2 _ => free_group T dec (nontrivial_free dec f) st2 g k bail) bail
          | _, _ => free_group T dec (nontrivial_free dec f) (dequeue (LActive (m_sizeclass (MR st g))) g st) g k bail
          end) bail
      | None => free_group T dec (nontrivial_free dec f) st g k bail
      end
    else if Z.lor (m_freed (MR st g)) (m_avail (MR st g)) =? 0 then
      guard 51 (m_sizeclass (MR st g) <? 48) (
        if negb (optr_eqb (active st (m_sizeclass (MR st g))) (Some g))
        then queue (LActive (m_sizeclass (MR st g))) g st (fun st' => k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st') None) bail
        else k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st) None) bail
    else
      k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st) None).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma data_same r r' i : data_of r' = data_of r ->
  sstart r' i = sstart r i /\ m_last_idx r' = m_last_idx r /\ m_avail r' = m_avail r /\ m_freed r' = m_freed r
  /\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r /\ m_mem r' = m_mem r.
Proof.
  intros D. pose proof (proj1 (data_of_eq r' r) D) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  unfold sstart, gbase. rewrite (get_stride_data _ _ D), E1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto.
Qed.

Lemma head_of_eq_app (l1 l2 : list aptr) g : NoDup (l1 ++ g :: l2) -> head_of (l1 ++ g :: l2) = Some g -> l1 = [].
Proof.
  intros ND H. destruct l1 as [|a l1']; [reflexivity|]. cbn in H. inversion H. subst a. exfalso.
  cbn in ND. apply NoDup_cons in ND as [N _]. apply N. apply elem_of_list_In || apply list_elem_of_In. apply in_app_iff. right. left. reflexivity.
Qed.

Theorem ntf_allQ T : forall f, NTF_ATQ T f.
Proof.
  induction f as [|f IH]; intros dec1 dec2 D1 D2 X st L BL LS g bg i k bail INV Hgh Hi HP HF HO F1 F2; [lia|].
  destruct X as [idle zomb pend orph fresh]. cbn in HP, HF, HO. subst pend orph fresh.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof Hgh as [ai Hg].
  pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  pose proof (g_li _ _ _ _ _ _ GO) as LI. pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  pose proof (is_part _ _ _ IS _ _ _ i Hg Hi) as Pi. cbn zeta in Pi. rewrite (slot_start'_eq _ _ _ IM _ _ _ Hgh) in Pi. cbn [x_pend] in Pi.
  assert (NA : tbit (m_avail (MR st g)) i = false) by (destruct (tbit (m_avail (MR st g)) i) eqn:E; [exfalso; unfold one5 in Pi; tauto| reflexivity]).
  assert (NB : tbit (m_freed (MR st g)) i = false) by (destruct (tbit (m_freed (MR st g)) i) eqn:E; [exfalso; unfold one5 in Pi; tauto| reflexivity]).
  clear Pi.
  rewrite !ntf_unfold.
  set (mask := Z.lor (m_freed (MR st g)) (m_avail (MR st g))).
  assert (MN : 0 <= mask) by (apply Z.lor_nonneg; auto).
  assert (MI : Z.testbit mask i = false) by (unfold mask; rewrite Z.lor_spec; unfold tbit in NA, NB; rewrite NA, NB; reflexivity).
  assert (MADD : mask + bit i = Z.lor mask (bit i)) by (rewrite bit_eq; apply add_bit_lor; auto; lia).
  (* [comment removed for export] *)
  assert (NU : okay_to_free st g = false -> m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g)).
  { intros OK Hsc. unfold okay_to_free in OK. fold (MR st g) in OK. rewrite (g_freeable _ _ _ _ _ _ GO) in OK. cbn [Z.eqb] in OK.
    destruct (Z.ltb_spec (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))); [| lia].
    rewrite Bool.orb_true_r in OK. discriminate. }
  destruct ((mask + bit i =? mask_upto (m_last_idx (MR st g))) && okay_to_free st g) eqn:C1.
  - (* [comment removed for export] *)
    apply Bool.andb_true_iff in C1 as [CM COK]. apply Z.eqb_eq in CM.
    assert (ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i -> tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true).
    { intros j Hj NE. assert (T1 : Z.testbit (mask + bit i) j = true) by (rewrite CM, testbit_mask_upto by lia; apply Z.leb_le; lia).
      rewrite MADD, Z.lor_spec, testbit_bit in T1 by lia. destruct (Z.eqb_spec i j); [lia|]. rewrite Bool.orb_false_r in T1.
      unfold mask in T1. rewrite Z.lor_spec in T1. unfold tbit. destruct (Z.testbit (m_freed (MR st g)) j); [right; reflexivity|]. left. exact T1. }
    pose proof (INVL_set_fresh _ st L BL LS (Some g) INV eq_refl) as INVf. cbn in INVf.
    (* [comment removed for export] *)
    assert (FGT : forall st2 LS2,
      INVL (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) st2 L BL LS2 ->
      s_groups st2 = s_groups st -> data_of (MR st2 g) = data_of (MR st g) -> m_next (MR st2 g) = None ->
      exists st' mi LS', free_group T dec1 (nontrivial_free dec1 f) st2 g k bail = k st' mi /\
        free_group T dec2 (nontrivial_free dec2 f) st2 g k bail = k st' mi /\
        (s_regions st' = s_regions st2 /\ s_secret st' = s_secret st2) /\
        (FFR st2 st' /\ s_groups st' !! bg = None) /\
        match mi with
        | None => INVL (mkX idle zomb None None None) st' L BL LS'
        | Some (base, len) => exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
            /\ len = round_up_pg (r_len r) /\ 0 < len /\ INVL (mkX idle zomb None (Some (fst base)) None) st' L BL LS'
        end).
    { intros st2 LS2 INV2 HG2 DD2 NL2. destruct (data_same _ _ i DD2) as (Es & El & Ea & Ef & Esc & Eml & Emem).
      rewrite <- Es in INV2.
      apply (free_group_okQ T f IH dec1 dec2 D1 D2 idle zomb st2 L BL LS2 g bg ai i k bail INV2).
      - rewrite HG2. exact Hg.
      - exact NL2.
      - rewrite El. exact Hi.
      - rewrite El, Ea, Ef. exact ALL.
      - rewrite Esc. exact F2. }
    destruct (m_next (MR st g)) as [nx|] eqn:NX.
    + (* [comment removed for export] *)
      assert (Lg : in_list LS g) by (apply (proj2 (proj1 (il_link _ _ IL g))); rewrite NX; discriminate).
      destruct Lg as [h Hin]. destruct h as [sc|]; [| exfalso; exact (free_not_live _ _ _ _ _ INV g Hin (ex_intro _ bg Hgh))].
      destruct (il_active _ _ IL sc g Hin) as (Hsc & _ & Esc). rewrite Esc.
      rewrite !(guard_true 50) by (apply Z.ltb_lt; lia).
      destruct (in_split _ _ Hin) as (l1 & l2 & HL).
      pose proof (il_nodup _ _ IL (LActive sc)) as ND. rewrite HL in ND.
      assert (INV1 : INVL (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) (dequeue (LActive sc) g st) L BL (fupd LS (LActive sc) (l1 ++ l2))).
      { apply (INVL_dequeue _ _ st L BL LS g (LActive sc) l1 l2 INV HL). left. exists sc. auto. }
      set (st1 := dequeue (LActive sc) g st) in *. set (LS1 := fupd LS (LActive sc) (l1 ++ l2)) in *.
      destruct (dequeue_frame (LActive sc) g st) as (RG1 & _ & _ & _ & G1 & _ & _ & SE1 & _). fold st1 in G1, RG1, SE1.
      pose proof (dequeue_data (LActive sc) g st) as DG1. fold st1 in DG1.
      assert (NL1 : m_next (MR st1 g) = None) by (unfold st1; rewrite dequeue_next, aptr_eqb_refl; reflexivity).
      assert (HD1 : active st1 sc = head_of (l1 ++ l2)).
      { pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV1)))) (LActive sc)) as H. unfold LS1 in H. rewrite fupd_eq in H. exact H. }
      destruct (optr_eqb (active st sc) (Some g)) eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1|].
      * (* [comment removed for export] *)
        destruct (optr_eqb_spec (active st sc) (Some g)) as [HD|]; [| discriminate].
        assert (El1 : l1 = []).
        { apply (head_of_eq_app l1 l2 g ND). rewrite <- HL. rewrite <- (il_head _ _ IL (LActive sc)). exact HD. }
        subst l1. cbn in HD1, HL, ND. destruct l2 as [|a' l2']; cbn in HD1; [discriminate|]. inversion HD1. subst a'.
        assert (Hain : In a (LS (LActive sc))) by (rewrite HL; right; left; reflexivity).
        assert (NEa : a <> g) by (intros ->; apply NoDup_cons in ND as [N _]; apply N; apply list_elem_of_In; left; reflexivity).
        destruct (il_active _ _ IL sc a Hain) as (_ & [ba [aia Ha]] & Esca).
        pose proof (g_rest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha) ltac:(discriminate) sc Hain ltac:(rewrite HL; cbn; congruence)) as [AZa FZa].
        pose proof (dequeue_data (LActive sc) g st a) as Da. fold st1 in Da.
        destruct (data_same _ _ 0 Da) as (_ & _ & Eaa & _ & Esa & _).
        assert (Ha1 : s_groups st1 !! ba = Some (mkGhdr (Some a) aia)) by (rewrite G1; exact Ha).
        assert (AV1 : m_avail (MR st1 a) = 0) by (rewrite Eaa; exact AZa).
        assert (HEAD1 : head_of (LS1 (LActive (m_sizeclass (MR st1 a)))) = Some a).
        { rewrite Esa, Esca. unfold LS1. rewrite fupd_eq. reflexivity. }
        rewrite !(activate_group_eq _ st1 L BL LS1 a ba aia INV1 Ha1 AV1).
        pose proof (INVL_activate _ st1 L BL LS1 a ba aia INV1 Ha1 AV1 HEAD1) as INV2.
        set (st2 := upd_meta a _ st1) in INV2 |- *.
        assert (F01 : FFR st st1) by (unfold st1; exact (FFR_dequeue_INV _ st L BL LS g bg sc INV Hgh Hin)).
        assert (F12 : FFR st1 st2).
        { unfold st2. apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ _ Ha1))| intros r; reflexivity| intros r N; exact N]. }
        destruct (FGT st2 LS1 INV2) as (st' & mi & LS' & EQ & EQb & REG & [FF GB] & POST).
        -- unfold st2. cbn. exact G1.
        -- unfold st2, MR. rewrite get_meta_rec_upd_other by congruence. exact (DG1 g).
        -- unfold st2, MR. rewrite get_meta_rec_upd_other by congruence. exact NL1.
        -- exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|].
           split; [destruct REG as [RA RB]; rewrite RA, RB; unfold st2; split; [etransitivity; [| exact RG1]; reflexivity| etransitivity; [| exact SE1]; reflexivity]|].
           split; [split; [eapply FFR_trans; [exact F01|]; eapply FFR_trans; [exact F12| exact FF]| left; exact GB]| exact POST].
      * assert (F01 : FFR st st1) by (unfold st1; exact (FFR_dequeue_INV _ st L BL LS g bg sc INV Hgh Hin)).
        destruct (FGT st1 LS1 INV1 G1 (DG1 g) NL1) as (st' & mi & LS' & EQ & EQb & REG & [FF GB] & POST). exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|]. split; [destruct REG as [RA RB]; rewrite RA, RB; split; [exact RG1| exact SE1]|]. split; [split; [eapply FFR_trans; [exact F01| exact FF]| left; exact GB]| exact POST].
      * assert (F01 : FFR st st1) by (unfold st1; exact (FFR_dequeue_INV _ st L BL LS g bg sc INV Hgh Hin)).
        destruct (FGT st1 LS1 INV1 G1 (DG1 g) NL1) as (st' & mi & LS' & EQ & EQb & REG & [FF GB] & POST). exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|]. split; [destruct REG as [RA RB]; rewrite RA, RB; split; [exact RG1| exact SE1]|]. split; [split; [eapply FFR_trans; [exact F01| exact FF]| left; exact GB]| exact POST].
    + (* [comment removed for export] *)
      destruct (FGT st LS INVf eq_refl eq_refl NX) as (st' & mi & LS' & EQ & EQb & REG & [FF GB] & POST). exists st', mi, LS'. split; [exact EQ|]. split; [exact EQb|]. split; [exact REG|]. split; [split; [exact FF| left; exact GB]| exact POST].
  - (* [comment removed for export] *)
    assert (OKF : m_last_idx (MR st g) = 0 -> okay_to_free st g = false).
    { intros L0. rewrite L0 in C1. assert (i = 0) by lia. subst i.
      assert (mask = 0).
      { apply Z.bits_inj'. intros j Hj. rewrite Z.bits_0. unfold mask. rewrite Z.lor_spec.
        destruct (Z.eq_dec j 0) as [->|NE]; [unfold tbit in NA, NB; rewrite NA, NB; reflexivity|].
        destruct (Z.testbit (m_freed (MR st g)) j) eqn:EF; [pose proof (M4 j Hj EF); lia|].
        destruct (Z.testbit (m_avail (MR st g)) j) eqn:EA; [pose proof (M3 j Hj EA); lia|]. reflexivity. }
      rewrite H in C1. cbn in C1. exact C1. }
    assert (C3 : m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g)).
    { intros Hsc. destruct (Z.eq_dec (m_last_idx (MR st g)) 0) as [L0|L0]; [exact (NU (OKF L0) Hsc)|].
      unfold get_stride. destruct (Z.eqb_spec (m_last_idx (MR st g)) 0); [lia|]. cbn. lia. }
    destruct (Z.eqb_spec mask 0) as [MZ|MNZ].
    + (* [comment removed for export] *)
      assert (AZ : m_avail (MR st g) = 0) by (unfold mask in MZ; apply Z.lor_eq_0_iff in MZ; tauto).
      assert (FZ : m_freed (MR st g) = 0) by (unfold mask in MZ; apply Z.lor_eq_0_iff in MZ; tauto).
      assert (Hsc : 0 <= m_sizeclass (MR st g) < 48).
      { destruct (g_sc _ _ _ _ _ _ GO) as [[H _]|(E63 & L0 & _)]; [exact H|]. exfalso.
        rewrite (OKF L0) in NU. unfold okay_to_free in OKF. fold (MR st g) in OKF. rewrite (g_freeable _ _ _ _ _ _ GO), E63 in OKF.
        cbn in OKF. discriminate (OKF L0). }
      rewrite !(guard_true 51) by (apply Z.ltb_lt; lia).
      destruct (optr_eqb_spec (active st (m_sizeclass (MR st g))) (Some g)) as [HD|NHD]; cbn [negb].
      * (* [comment removed for export] *)
        eexists _, None, LS. split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
        split. { split; [apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ GO)| intros r; reflexivity| intros r N; exact N]|]. right. split; [reflexivity|]. split; [reflexivity| first [reflexivity| exact C1]]. }
        cbn.
        apply (INVL_aor _ st L BL LS g bg ai i INV Hg Hi eq_refl).
        -- intros _ sc _ _. exact AZ.
        -- intros _ _. exists (LActive (m_sizeclass (MR st g))). apply (head_listed _ _ _ _ _ INV). exact HD.
        -- exact C3.
      * (* [comment removed for export] *)
        assert (NL : m_next (MR st g) = None).
        { destruct (m_next (MR st g)) as [nx|] eqn:NX; [| reflexivity]. exfalso.
          assert (Lg : in_list LS g) by (apply (proj1 (proj1 (il_link _ _ IL g))) || apply (proj2 (proj1 (il_link _ _ IL g))); rewrite NX; discriminate).
          destruct Lg as [h Hin]. destruct h as [sc|]; [| exact (free_not_live _ _ _ _ _ INV g Hin (ex_intro _ bg Hgh))].
          destruct (il_active _ _ IL sc g Hin) as (_ & _ & Esc). subst sc.
          apply NHD. rewrite <- Esc at 1 || idtac.
          destruct (g_rest _ _ _ _ _ _ GO ltac:(discriminate) _ Hin) as [_ FNZ]; [| exact (FNZ FZ) || congruence].
          rewrite <- (il_head _ _ IL (LActive (m_sizeclass (MR st g)))). intros E. apply NHD. exact (eq_sym E) || (symmetry; exact E). }
        assert (NP : m_prev (MR st g) = None) by (exact (proj2 (il_link _ _ IL g) NL)).
        rewrite !(queue_eq (LActive (m_sizeclass (MR st g))) g st _ bail NL NP).
        pose proof (INVL_set_fresh _ st L BL LS (Some g) INV eq_refl) as INVf. cbn in INVf.
        pose proof (INVL_queue _ st L BL LS g (LActive (m_sizeclass (MR st g))) INVf NL (g_present _ _ _ _ _ _ GO)) as INVq.
        cbn [x_fresh x_idle x_zomb] in INVq. specialize (INVq ltac:(OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia; fail)) || specialize (INVq (conj Hsc (conj (ex_intro _ bg Hgh) (conj eq_refl eq_refl)))).
        set (stq := queue_st (LActive (m_sizeclass (MR st g))) g st) in *.
        set (LSq := fupd LS (LActive (m_sizeclass (MR st g))) (LS (LActive (m_sizeclass (MR st g))) ++ [g])) in *.
        destruct (queue_frame (LActive (m_sizeclass (MR st g))) g st) as (RGq & _ & _ & _ & Gq & _ & _ & SEq & _). fold stq in Gq, RGq, SEq.
        pose proof (queue_data (LActive (m_sizeclass (MR st g))) g st g) as Dq. fold stq in Dq.
        destruct (data_same _ _ i Dq) as (Es & El & Ea & Ef & Esc & Eml & Emem).
        assert (INVa : INVL (mkX idle zomb None None (Some g)) (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) stq) L BL LSq).
        { apply (INVL_aor (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) stq L BL LSq g bg ai i INVq).
          - rewrite Gq. exact Hg.
          - rewrite El. exact Hi.
          - cbn. rewrite Es. reflexivity.
          - cbn. intros NF. exfalso. apply NF. reflexivity.
          - cbn. intros NF. exfalso. apply NF. reflexivity.
          - rewrite Esc. unfold stq, MR. rewrite (get_stride_data _ _ Dq). exact C3. }
        eexists _, None, LSq. split; [reflexivity|]. split; [reflexivity|]. split; [cbn; rewrite RGq, SEq; split; reflexivity|].
        split. { split; [| right; split; [reflexivity|]; split; [cbn; exact Gq| first [reflexivity| exact C1]]].
          eapply FFR_trans. 2:{ apply FFR_upd_meta; [unfold stq; apply queue_key_g| intros r; reflexivity| intros r N; exact N]. }
          unfold stq. exact (FFR_queue_INV _ st L BL LS g bg _ INV Hgh). }
        cbn.
        apply (INVL_clear_fresh _ _ L BL LSq g INVa eq_refl).
        intros b ai' Hb. unfold MR. rewrite get_meta_rec_upd_same. cbn [m_last_idx m_sizeclass m_avail m_freed m_set_freed]. fold (MR stq g). rewrite El, Esc, Ea, Ef.
        assert (ING : In g (LSq (LActive (m_sizeclass (MR st g))))) by (unfold LSq; rewrite fupd_eq; apply in_app_iff; right; left; reflexivity).
        split; [intros _; exact ING|]. split; [intros _ NI; exfalso; apply NI; eexists; exact ING|].
        split; [intros sc _ _; split; [exact AZ|]; rewrite FZ, Z.lor_0_l; unfold bit; pose proof (Z.pow_pos_nonneg 2 i); lia|].
        intros Hsc' LT. exfalso. pose proof (C3 Hsc') as GE.
        replace (get_stride (m_set_freed (Z.lor (m_freed (MR st g)) (bit i)) (MR stq g))) with (get_stride (MR stq g)) in LT by (destruct (MR stq g); reflexivity).
        rewrite (get_stride_data _ _ Dq) in LT. lia.
    + (* [comment removed for export] *)
      eexists _, None, LS. split; [reflexivity|]. split; [reflexivity|]. split; [split; reflexivity|].
      split. { split; [apply FFR_upd_meta; [exact (g_present _ _ _ _ _ _ GO)| intros r; reflexivity| intros r N; exact N]|]. right. split; [reflexivity|]. split; [reflexivity| first [reflexivity| exact C1]]. }
      cbn.
      apply (INVL_aor _ st L BL LS g bg ai i INV Hg Hi eq_refl).
      * intros _ sc Hin Hnh. exact (proj1 (g_rest _ _ _ _ _ _ GO ltac:(discriminate) sc Hin Hnh)).
      * intros _ Hsc. destruct (m_next (MR st g)) as [nx|] eqn:NX.
        -- apply (proj2 (proj1 (il_link _ _ IL g))). rewrite NX. discriminate.
        -- exfalso. destruct (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc (fun H => lists_notin st LS (old_lists _ _ _ _ _ INV) g NX _ (proj2 (In_nth _ _ g H) ))) || idtac.
           assert (NIL : ~ in_list LS g) by (intros [h Hin]; exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NX h Hin)).
           destruct (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc NIL) as [A0 F0]. apply MNZ. unfold mask. rewrite A0, F0. reflexivity.
      * exact C3.
Qed.

End LBCEIL.
