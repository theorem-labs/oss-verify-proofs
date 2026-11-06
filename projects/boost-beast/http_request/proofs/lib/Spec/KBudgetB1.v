(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Pres3 MI_Pres4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma count_incl {A} (l k : list A) : List.NoDup l -> (forall x, In x l -> In x k) -> (length l <= length k)%nat.
Proof.
  intros ND SUB. apply submseteq_length. apply NoDup_submseteq; [apply NoDup_ListNoDup; exact ND|].
  intros x Hx. apply list_elem_of_In. apply SUB. apply list_elem_of_In. exact Hx.
Qed.

Lemma In_keys `{Countable K} {V} (m : gmap K V) k : In k (map fst (map_to_list m)) <-> m !! k <> None.
Proof.
  split.
  - intros Hin. apply in_map_iff in Hin as ([k' v] & E & Hin). cbn in E. subst k'.
    apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin. rewrite Hin. discriminate.
  - intros Hk. destruct (m !! k) as [v|] eqn:E; [| congruence]. apply in_map_iff. exists (k, v). split; [reflexivity|].
    apply list_elem_of_In. apply elem_of_map_to_list. exact E.
Qed.

Lemma keys_nodup `{Countable K} {V} (m : gmap K V) : List.NoDup (map fst (map_to_list m)).
Proof. apply NoDup_ListNoDup. apply NoDup_fst_map_to_list. Qed.

Lemma keys_length `{Countable K} {V} (m : gmap K V) : length (map fst (map_to_list m)) = size m.
Proof. rewrite map_length. apply length_map_to_list. Qed.

(* [comment removed for export] *)
Lemma size_le_cover `{Countable K} {V} (m : gmap K V) (l : list K) :
  (forall k, m !! k <> None -> In k l) -> (size m <= length l)%nat.
Proof.
  intros COV. rewrite <- keys_length. apply count_incl; [apply keys_nodup|]. intros k Hk. apply COV. apply In_keys. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma size_ge_sub `{Countable K} {V} (m : gmap K V) (l : list K) :
  List.NoDup l -> (forall k, In k l -> m !! k <> None) -> (length l <= size m)%nat.
Proof.
  intros ND SUB. rewrite <- keys_length. apply count_incl; [exact ND|]. intros k Hk. apply In_keys. apply SUB. exact Hk.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma In_zseq n z : In z (zseq n) <-> 0 <= z < Z.of_nat n.
Proof.
  unfold zseq. rewrite in_map_iff. split.
  - intros (k & <- & Hk). apply in_seq in Hk. lia.
  - intros Hz. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia.
Qed.
Lemma zseq_nodup n : List.NoDup (zseq n).
Proof. unfold zseq. apply Finite.Injective_map_NoDup; [intros a b; lia| apply seq_NoDup]. Qed.
Lemma zseq_length n : length (zseq n) = n.
Proof. unfold zseq. rewrite map_length, seq_length. reflexivity. Qed.

Definition area_slots (a : aptr) : list aptr := map (mslot a) (zseq (Z.to_nat NSLOTS)).
Definition all_slots (st : mstate) : list aptr := flat_map (fun ar => area_slots (fst ar)) (map_to_list (s_areas st)).

Lemma length_all_slots st : length (all_slots st) = (size (s_areas st) * Z.to_nat NSLOTS)%nat.
Proof.
  unfold all_slots. rewrite (flat_map_constant_length (c:=Z.to_nat NSLOTS)).
  - rewrite length_map_to_list. reflexivity.
  - intros [a ar] _. unfold area_slots. rewrite map_length, zseq_length. reflexivity.
Qed.

Lemma In_all_slots st x : In x (all_slots st) <-> exists a ar k, s_areas st !! a = Some ar /\ 0 <= k < NSLOTS /\ x = mslot a k.
Proof.
  unfold all_slots. rewrite in_flat_map. split.
  - intros ([a ar] & Hin & Hx). apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin. cbn in Hx.
    unfold area_slots in Hx. apply in_map_iff in Hx as (k & <- & Hk). apply In_zseq in Hk. exists a, ar, k. unfold NSLOTS in *. repeat split; auto; lia.
  - intros (a & ar & k & Ha & Hk & ->). exists (a, ar). split; [apply list_elem_of_In; apply elem_of_map_to_list; exact Ha|].
    cbn. unfold area_slots. apply in_map_iff. exists k. split; [reflexivity|]. apply In_zseq. unfold NSLOTS in *. lia.
Qed.

Section COUNT.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
Hypothesis INV : INVL X st L BL LS.
Let IR := proj1 INV. Let IA := proj1 (proj2 INV). Let IM := proj1 (proj2 (proj2 INV)). Let IL := proj1 (proj2 (proj2 (proj2 INV))).
Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))). Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

(* [comment removed for export] *)
Lemma mslot_inj a1 a2 k1 k2 ar1 ar2 :
  s_areas st !! a1 = Some ar1 -> s_areas st !! a2 = Some ar2 -> 0 <= k1 < NSLOTS -> 0 <= k2 < NSLOTS ->
  mslot a1 k1 = mslot a2 k2 -> a1 = a2 /\ k1 = k2.
Proof.
  intros H1 H2 K1 K2 E.
  destruct (ia_areas _ IA _ _ H1) as ((r1 & _ & _ & P1 & _) & _). destruct (ia_areas _ IA _ _ H2) as ((r2 & _ & _ & P2 & _) & _).
  destruct a1 as [rid1 o1], a2 as [rid2 o2]. unfold mslot, aadd in E. cbn in E, P1, P2. injection E as Erid Eo.
  unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *.
  assert (Ho : o1 = o2).
  { pose proof (Z.div_mod o1 4096 ltac:(lia)) as D1. pose proof (Z.div_mod o2 4096 ltac:(lia)) as D2. rewrite P1 in D1. rewrite P2 in D2. nia. }
  subst. split; [reflexivity| lia].
Qed.

Lemma area_slots_nodup a ar : s_areas st !! a = Some ar -> List.NoDup (area_slots a).
Proof.
  intros Ha. unfold area_slots. apply Finite.Injective_map_NoDup_in; [| apply zseq_nodup].
  intros k1 k2 H1 H2 E. apply In_zseq in H1. apply In_zseq in H2.
  exact (proj2 (mslot_inj a a k1 k2 ar ar Ha Ha ltac:(unfold NSLOTS in *; lia) ltac:(unfold NSLOTS in *; lia) E)).
Qed.

Lemma all_slots_nodup : List.NoDup (all_slots st).
Proof.
  unfold all_slots. pose proof (keys_nodup (s_areas st)) as ND.
  remember (map_to_list (s_areas st)) as l eqn:El.
  assert (SUB : forall a ar, In (a, ar) l -> s_areas st !! a = Some ar).
  { intros a ar Hin. subst l. apply elem_of_map_to_list. apply list_elem_of_In. exact Hin. }
  clear El. induction l as [|[a ar] l IH]; cbn; [constructor|].
  cbn in ND. apply List.NoDup_cons_iff in ND as [NIa ND].
  apply List.NoDup_app.
  - apply (area_slots_nodup a ar). apply SUB. left. reflexivity.
  - apply IH; [exact ND| intros a' ar' H; apply SUB; right; exact H].
  - intros x Hx Hx2. unfold area_slots in Hx. apply in_map_iff in Hx as (k & <- & Hk). apply In_zseq in Hk.
    apply in_flat_map in Hx2 as ([a' ar'] & Hin & Hx2). cbn in Hx2. unfold area_slots in Hx2. apply in_map_iff in Hx2 as (k' & E & Hk'). apply In_zseq in Hk'.
    pose proof (mslot_inj a' a k' k ar' ar (SUB a' ar' ltac:(right; exact Hin)) (SUB a ar ltac:(left; reflexivity))
                  ltac:(unfold NSLOTS in *; lia) ltac:(unfold NSLOTS in *; lia) E) as [-> _].
    apply NIa. apply in_map_iff. exists (a, ar'). split; [reflexivity| exact Hin].
Qed.

(* [comment removed for export] *)
Lemma metas_ge_areas : c_avail_meta_count (s_ctx st) = 0 -> (size (s_areas st) * Z.to_nat NSLOTS <= size (s_metas st))%nat.
Proof.
  intros HC. rewrite <- length_all_slots. apply size_ge_sub; [apply all_slots_nodup|].
  intros x Hx. apply In_all_slots in Hx as (a & ar & k & Ha & Hk & ->).
  apply (ia_carved _ IA a ar k Ha Hk). intros _. rewrite HC. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition meta_of (bh : aptr * ghdr) : aptr := default (0%N, 0) (g_meta (snd bh)).

Lemma metas_le_groups : LS LFree = [] ->
  (size (s_metas st) <= size (s_groups st) + length (x_idle X) + length (x_zomb X))%nat.
Proof.
  intros HF.
  pose proof (size_le_cover (s_metas st) (map meta_of (map_to_list (s_groups st)) ++ x_idle X ++ x_zomb X)) as H.
  rewrite !app_length, map_length, length_map_to_list in H. eapply Nat.le_trans; [apply H| lia]. clear H.
  intros m Hm. rewrite !in_app_iff.
  assert (LG : live_group st m -> In m (map meta_of (map_to_list (s_groups st)))).
  { intros [b [ai Hb]]. apply in_map_iff. exists (b, mkGhdr (Some m) ai). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Hb. }
  destruct (im_all _ _ _ IM m Hm) as [A|[[h Hin]|[A|A]]]; [left; exact (LG A)| | right; left; exact A| right; right; exact A].
  destruct h as [sc|]; [| rewrite HF in Hin; destruct Hin].
  left. apply LG. exact (proj1 (proj2 (il_active _ _ IL sc m Hin))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition up (x : aptr) : option aptr :=
  match s_slots st !! x with Some (p, _) => m_mem (MR st p) | None => None end.
Fixpoint ups (x : aptr) (n : nat) : list aptr :=
  match n with O => [] | S n' => match up x with Some b => b :: ups b n' | None => [] end end.

Definition allfreeb (r : meta) : bool := Z.lor (m_avail r) (m_freed r) =? mask_upto (m_last_idx r).
Lemma allfreeb_spec r : allfreeb r = true <-> allfree r.
Proof. unfold allfreeb, allfree. rewrite Z.eqb_eq. tauto. Qed.

Definition af_list : list (aptr * ghdr) := List.filter (fun bh => allfreeb (MR st (meta_of bh))) (map_to_list (s_groups st)).
Definition AF : list aptr := map fst af_list.
Definition pend_list : list aptr := match x_pend X with Some s => [s] | None => [] end.
Definition leaves : list aptr := map bslot BL ++ pend_list ++ AF.
Definition DEPTH : nat := 49%nat.
Definition gcover : list aptr := AF ++ flat_map (fun l => ups l DEPTH) leaves.

Lemma ups_mono x k n : (k <= n)%nat -> forall b, In b (ups x k) -> In b (ups x n).
Proof.
  revert x n. induction k as [|k IH]; intros x n Hk b Hb; [destruct Hb|].
  destruct n as [|n]; [lia|]. cbn in Hb |- *. destruct (up x) as [b0|]; [| destruct Hb].
  destruct Hb as [<-|Hb]; [left; reflexivity| right]. apply (IH b0 n); [lia| exact Hb].
Qed.

Lemma up_slot s p i : s_slots st !! s = Some (p, i) -> exists bp, hosts st bp p /\ up s = Some bp.
Proof.
  intros Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _). exists bp. split; [exact Hp|].
  unfold up. rewrite Hs. exact (hosts_mem _ _ _ IM _ _ Hp).
Qed.

(* [comment removed for export] *)
Lemma group_cover_n : forall n b m ai, s_groups st !! b = Some (mkGhdr (Some m) ai) ->
  (m_sizeclass (MR st m) < 48 -> m_sizeclass (MR st m) < Z.of_nat n) ->
  In b AF \/ exists l k, In l leaves /\ (1 <= k <= S n)%nat /\ In b (ups l k).
Proof.
  induction n as [|n IH]; intros b m ai Hb Hn.
  - (* [comment removed for export] *)
    pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO.
    destruct (g_sc _ _ _ _ _ _ GO) as [[[S0 S48] _]|(E63 & L0 & _)]; [exfalso; specialize (Hn S48); lia|].
    destruct (g_big0 _ _ _ _ _ _ GO E63) as [A0 F0].
    pose proof (is_part _ _ _ IS b m ai 0 Hb ltac:(rewrite L0; lia)) as P. cbn zeta in P.
    unfold one5, tbit in P. rewrite A0, F0, !Z.bits_0 in P.
    destruct P as (P & _). set (s := slot_start' (MR st m) 0) in *.
    assert (Hs : s_slots st !! s = Some (m, 0)) by (apply (is_total _ _ _ IS b); [exists ai; exact Hb| rewrite L0; lia]).
    destruct (up_slot s m 0 Hs) as (bp & Hp & UP). pose proof (hosts_inj _ _ _ IM _ _ _ Hp (ex_intro _ ai Hb)) as ->.
    destruct P as [E|[E|[U|[NG|PE]]]]; [discriminate| discriminate| | |].
    + right. exists s, 1%nat. split; [unfold leaves; rewrite !in_app_iff; left; exact U|]. split; [lia|]. cbn. rewrite UP. left. reflexivity.
    + exfalso. destruct (s_groups st !! s) as [[[m'|] ai']|] eqn:Hs'; [| exact (ig_nometa _ _ _ IG _ _ Hs')| exact (NG eq_refl)].
      pose proof (ig_ok _ _ _ IG _ _ _ Hs') as GO'.
      destruct (Z.eq_dec (m_maplen (MR st m')) 0) as [ML|ML].
      * destruct (g_nest _ _ _ _ _ _ GO' ML) as (p & i & Hsp & _ & _ & SC & _). rewrite Hs in Hsp. injection Hsp as <- <-. lia.
      * destruct (g_top _ _ _ _ _ _ GO' ML) as [Z0 _].
        destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & _ & Es). rewrite (slot_start'_eq _ _ _ IM _ _ 0 (ex_intro _ ai Hb)) in Es.
        subst s. rewrite Es in Z0. cbn in Z0. pose proof (sstart0 _ _ _ IM _ _ (ex_intro _ ai Hb)). pose proof (g_align _ _ _ _ _ _ GO) as [B0 _]. unfold UNIT in *. lia.
    + right. exists s, 1%nat. split; [unfold leaves, pend_list; rewrite !in_app_iff; right; left; rewrite PE; left; reflexivity|]. split; [lia|]. cbn. rewrite UP. left. reflexivity.
  - destruct (allfreeb (MR st m)) eqn:AFm.
    + left. unfold AF, af_list. apply in_map_iff. exists (b, mkGhdr (Some m) ai). split; [reflexivity|].
      apply filter_In. split; [apply list_elem_of_In; apply elem_of_map_to_list; exact Hb|]. cbn. exact AFm.
    + (* [comment removed for export] *)
      pose proof (ig_ok _ _ _ IG _ _ _ Hb) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6). pose proof (g_li _ _ _ _ _ _ GO) as LI.
      assert (EXI : exists i, 0 <= i <= m_last_idx (MR st m) /\ tbit (m_avail (MR st m)) i = false /\ tbit (m_freed (MR st m)) i = false).
      { destruct (List.Exists_dec (fun i => tbit (m_avail (MR st m)) i = false /\ tbit (m_freed (MR st m)) i = false) (zseq (Z.to_nat (m_last_idx (MR st m) + 1)))) as [EX|NEX].
        - intros i. destruct (tbit (m_avail (MR st m)) i), (tbit (m_freed (MR st m)) i); [right| right| right| left]; try (intros [A B]; discriminate). auto.
        - apply List.Exists_exists in EX as (i & Hi & P). apply In_zseq in Hi. exists i. split; [lia| exact P].
        - exfalso. apply Bool.not_true_iff_false in AFm. apply AFm. apply allfreeb_spec. unfold allfree.
          apply Z.bits_inj'. intros j Hj. rewrite Z.lor_spec, testbit_mask_upto by lia.
          destruct (Z.le_gt_cases j (m_last_idx (MR st m))) as [LE|GT].
          + replace (j <=? m_last_idx (MR st m)) with true by (symmetry; apply Z.leb_le; lia).
            destruct (Z.testbit (m_avail (MR st m)) j) eqn:EA; [reflexivity|]. destruct (Z.testbit (m_freed (MR st m)) j) eqn:EF; [reflexivity|].
            exfalso. apply NEX. apply List.Exists_exists. exists j. split; [apply In_zseq; lia| unfold tbit; auto].
          + replace (j <=? m_last_idx (MR st m)) with false by (symmetry; apply Z.leb_gt; lia).
            destruct (Z.testbit (m_avail (MR st m)) j) eqn:EA; [pose proof (M3 j Hj EA); pose proof (g_ai _ _ _ _ _ _ GO); lia|].
            destruct (Z.testbit (m_freed (MR st m)) j) eqn:EF; [pose proof (M4 j Hj EF); lia|]. reflexivity. }
      destruct EXI as (i & Hi & NA & NF).
      pose proof (is_part _ _ _ IS b m ai i Hb Hi) as P. cbn zeta in P. unfold one5 in P. rewrite NA, NF in P.
      destruct P as (P & _). set (s := slot_start' (MR st m) i) in *.
      assert (Hs : s_slots st !! s = Some (m, i)) by (apply (is_total _ _ _ IS b); [exists ai; exact Hb| exact Hi]).
      destruct (up_slot s m i Hs) as (bp & Hp & UP). pose proof (hosts_inj _ _ _ IM _ _ _ Hp (ex_intro _ ai Hb)) as ->.
      destruct P as [E|[E|[U|[NG|PE]]]]; [discriminate| discriminate| | |].
      * right. exists s, 1%nat. split; [unfold leaves; rewrite !in_app_iff; left; exact U|]. split; [lia|]. cbn. rewrite UP. left. reflexivity.
      * destruct (s_groups st !! s) as [[[m'|] ai']|] eqn:Hs'; [| exfalso; exact (ig_nometa _ _ _ IG _ _ Hs')| exfalso; exact (NG eq_refl)].
        pose proof (ig_ok _ _ _ IG _ _ _ Hs') as GO'.
        assert (ML : m_maplen (MR st m') = 0).
        { destruct (Z.eq_dec (m_maplen (MR st m')) 0) as [ML|ML]; [exact ML|]. exfalso.
          destruct (g_top _ _ _ _ _ _ GO' ML) as [Z0 _].
          destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & _ & Es). rewrite (slot_start'_eq _ _ _ IM _ _ i (ex_intro _ ai Hb)) in Es.
          subst s. rewrite Es in Z0. cbn in Z0. pose proof (sstart0 _ _ _ IM _ _ (ex_intro _ ai Hb)).
          pose proof (sstart_mono _ _ _ IG _ _ 0 i (ex_intro _ ai Hb) ltac:(lia)). pose proof (g_align _ _ _ _ _ _ GO) as [B0 _]. unfold UNIT in *. lia. }
        destruct (g_nest _ _ _ _ _ _ GO' ML) as (p & i' & Hsp & _ & _ & SC & _). rewrite Hs in Hsp. injection Hsp as <- <-.
        destruct (IH s m' ai' Hs' ltac:(lia)) as [AFs|(l & k & Hl & Hk & Hin)].
        -- right. exists s, 1%nat. split; [unfold leaves; rewrite !in_app_iff; right; right; exact AFs|]. split; [lia|]. cbn. rewrite UP. left. reflexivity.
        -- right. exists l, (S k). split; [exact Hl|]. split; [lia|].
           clear -Hin UP. revert l Hin. induction k as [|k IHk]; intros l Hin; [destruct Hin|].
           cbn in Hin. cbn. destruct (up l) as [b0|]; [| destruct Hin]. destruct Hin as [<-|Hin].
           ++ right. cbn. rewrite UP. left. reflexivity.
           ++ right. apply IHk. exact Hin.
      * right. exists s, 1%nat. split; [unfold leaves, pend_list; rewrite !in_app_iff; right; left; rewrite PE; left; reflexivity|]. split; [lia|]. cbn. rewrite UP. left. reflexivity.
Qed.

Lemma ups_length x n : (length (ups x n) <= n)%nat.
Proof. revert x. induction n as [|n IH]; intros x; cbn; [lia|]. destruct (up x); cbn; [| lia]. specialize (IH a). lia. Qed.

(* [comment removed for export] *)
Lemma AF_length : (length AF <= 48)%nat.
Proof.
  unfold AF.
  assert (ND : List.NoDup (map fst af_list)).
  { unfold af_list. pose proof (keys_nodup (s_groups st)) as ND.
    remember (map_to_list (s_groups st)) as l eqn:El. clear El. revert ND. induction l as [|[b h] l IH]; cbn; intros ND; [constructor|].
    apply List.NoDup_cons_iff in ND as [NI ND].
    destruct (allfreeb (MR st (meta_of (b, h)))); cbn; [| apply IH; exact ND].
    apply List.NoDup_cons; [| apply IH; exact ND]. intros Hin. apply NI. apply in_map_iff in Hin as ([b' h'] & E & Hin). apply filter_In in Hin as [Hin _].
    apply in_map_iff. exists (b', h'). auto. }
  assert (FACTS : forall b h, In (b, h) af_list -> exists m ai, h = mkGhdr (Some m) ai /\ s_groups st !! b = Some h /\ allfree (MR st m) /\ 0 <= m_sizeclass (MR st m) < 48).
  { intros b h Hin. unfold af_list in Hin. apply filter_In in Hin as [Hin AFb]. apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
    destruct h as [[m|] ai]; [| exfalso; exact (ig_nometa _ _ _ IG _ _ Hin)]. exists m, ai. cbn in AFb. apply allfreeb_spec in AFb.
    split; [reflexivity|]. split; [exact Hin|]. split; [exact AFb|].
    pose proof (ig_ok _ _ _ IG _ _ _ Hin) as GO. destruct (g_sc _ _ _ _ _ _ GO) as [[S _]|(E63 & L0 & _)]; [exact S|].
    exfalso. destruct (g_big0 _ _ _ _ _ _ GO E63) as [A0 F0]. unfold allfree in AFb. rewrite A0, F0, L0 in AFb. cbn in AFb. discriminate. }
  pose proof (count_incl (map (fun bh => m_sizeclass (MR st (meta_of bh))) af_list) (zseq 48)) as C.
  rewrite map_length, zseq_length in C. rewrite map_length. apply C.
  - (* [comment removed for export] *)
    clear C. revert ND FACTS. generalize af_list. intros afl ND FACTS. induction afl as [|[b h] l IH]; cbn; [constructor|].
    cbn in ND. apply List.NoDup_cons_iff in ND as [NI ND]. apply List.NoDup_cons; [| apply IH; [exact ND| intros b' h' H'; apply FACTS; right; exact H']].
    intros Hin. apply in_map_iff in Hin as ([b' h'] & E & Hin').
    destruct (FACTS b h ltac:(left; reflexivity)) as (m & ai & -> & Hb & AFm & SCm).
    destruct (FACTS b' h' ltac:(right; exact Hin')) as (m' & ai' & -> & Hb' & AFm' & SCm'). cbn in E.
    pose proof (ig_oneempty _ _ _ IG m m' b b' ai ai' Hb Hb' (proj2 SCm) E AFm AFm') as <-.
    pose proof (hosts_inj _ _ _ IM _ _ _ (ex_intro _ ai Hb) (ex_intro _ ai' Hb')) as <-.
    apply NI. apply in_map_iff. exists (b, mkGhdr (Some m) ai'). auto.
  - intros z Hz. apply in_map_iff in Hz as ([b h] & <- & Hin). destruct (FACTS b h Hin) as (m & ai & -> & _ & _ & SC). apply In_zseq. replace (meta_of (b, mkGhdr (Some m) ai)) with m by reflexivity. lia.
Qed.

Lemma groups_le : (size (s_groups st) <= 48 + DEPTH * (length BL + 1 + 48))%nat.
Proof.
  pose proof AF_length as AFL.
  eapply Nat.le_trans; [apply (size_le_cover (s_groups st) gcover)|].
  - intros b Hb. destruct (s_groups st !! b) as [[[m|] ai]|] eqn:E; [| exfalso; exact (ig_nometa _ _ _ IG _ _ E)| congruence].
    unfold gcover. apply in_app_iff.
    destruct (group_cover_n 48 b m ai E ltac:(intros; lia)) as [A|(l & k & Hl & Hk & Hin)]; [left; exact A| right].
    apply in_flat_map. exists l. split; [exact Hl|]. apply (ups_mono l k); [unfold DEPTH; lia| exact Hin].
  - unfold gcover. rewrite app_length.
    assert (FL : forall ls, (length (flat_map (fun l => ups l DEPTH) ls) <= DEPTH * length ls)%nat).
    { induction ls as [|x ls IH]; [cbn; lia|]. cbn [flat_map]. rewrite app_length. cbn [length]. pose proof (ups_length x DEPTH). lia. }
    pose proof (FL leaves) as FLl. unfold leaves in FLl. rewrite !app_length, map_length in FLl.
    assert (PL : (length pend_list <= 1)%nat) by (unfold pend_list; destruct (x_pend X); cbn; lia).
    unfold leaves. nia.
Qed.

(* [comment removed for export] *)
Theorem carve_count : LS LFree = [] -> c_avail_meta_count (s_ctx st) = 0 ->
  (Z.to_nat NSLOTS * size (s_areas st) <= 48 + DEPTH * (length BL + 49) + length (x_idle X) + length (x_zomb X))%nat.
Proof.
  intros HF HC. pose proof (metas_ge_areas HC) as A. pose proof (metas_le_groups HF) as B. pose proof groups_le as C. lia.
Qed.

(* [comment removed for export] *)
End COUNT.
