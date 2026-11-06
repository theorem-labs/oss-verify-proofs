(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree MI_WFree2 MI_WKill MI_WNtf MI_WNtf2 MI_WSlot MI_Contracts MI_Ledger MShapeB MShape21.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ubits (r : meta) (j : Z) : bool := tbit (m_avail r) j || tbit (m_freed r) j.

Record FFR (st st' : mstate) : Prop := mkFFR {
  ffr_host : forall b x, hosts st' b x -> hosts st b x;
  ffr_geo : forall b x, hosts st' b x -> geo_of (MR st' x) = geo_of (MR st x);
  ffr_bits : forall b x j, hosts st' b x -> 0 <= j -> ubits (MR st x) j = true -> ubits (MR st' x) j = true;
  ffr_cnt : c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st)
}.

Lemma FFR_refl st : FFR st st.
Proof. constructor; auto. Qed.

Lemma FFR_trans a b c : FFR a b -> FFR b c -> FFR a c.
Proof.
  intros [H1 G1 B1 C1] [H2 G2 B2 C2]. constructor.
  - intros bb x Hx. exact (H1 _ _ (H2 _ _ Hx)).
  - intros bb x Hx. rewrite (G2 _ _ Hx). exact (G1 _ _ (H2 _ _ Hx)).
  - intros bb x j Hx Hj U. exact (B2 _ _ _ Hx Hj (B1 _ _ _ (H2 _ _ Hx) Hj U)).
  - rewrite C2. exact C1.
Qed.

Lemma geo_of_data r r' : data_of r' = data_of r -> geo_of r' = geo_of r.
Proof.
  intros D. cps_pose (proj1 (data_of_eq r' r) D) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  unfold geo_of. rewrite E1, E4, E6, E7. reflexivity.
Qed.

Lemma ubits_data r r' j : data_of r' = data_of r -> ubits r' j = ubits r j.
Proof.
  intros D. cps_pose (proj1 (data_of_eq r' r) D) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
  unfold ubits. rewrite E2, E3. reflexivity.
Qed.

Lemma FFR_data st st' :
  (forall b x, hosts st' b x -> hosts st b x) ->
  (forall b x, hosts st' b x -> data_of (MR st' x) = data_of (MR st x)) ->
  c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st) ->
  FFR st st'.
Proof.
  intros H D C. constructor; [exact H| | | exact C].
  - intros b x Hx. apply geo_of_data. exact (D _ _ Hx).
  - intros b x j Hx Hj U. rewrite (ubits_data _ _ j (D _ _ Hx)). exact U.
Qed.

Lemma FFR_same st st' :
  s_groups st' = s_groups st -> (forall x, data_of (MR st' x) = data_of (MR st x)) ->
  c_avail_meta_count (s_ctx st') = c_avail_meta_count (s_ctx st) -> FFR st st'.
Proof.
  intros G D C. apply FFR_data; [| intros; apply D| exact C].
  intros b x [ai Hb]. exists ai. rewrite <- G. exact Hb.
Qed.

Lemma hosts_upd_meta st m f b x : hosts (upd_meta m f st) b x <-> hosts st b x.
Proof. unfold hosts, upd_meta, put_meta. cbn. tauto. Qed.

Lemma hosts_upd_ctx st f b x : hosts (upd_ctx f st) b x <-> hosts st b x.
Proof. unfold hosts, upd_ctx. destruct st; cbn. tauto. Qed.

Lemma FFR_upd_ctx st f : c_avail_meta_count (f (s_ctx st)) = c_avail_meta_count (s_ctx st) -> FFR st (upd_ctx f st).
Proof.
  intros C. apply FFR_data.
  - intros b x Hx. apply hosts_upd_ctx in Hx. exact Hx.
  - intros b x _. unfold MR. rewrite (get_meta_rec_ext st (upd_ctx f st)) by (destruct st; reflexivity). reflexivity.
  - destruct st; cbn. exact C.
Qed.

(* [comment removed for export] *)
Lemma FFR_aor st g i : 0 <= i -> 0 <= m_freed (MR st g) ->
  FFR st (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st).
Proof.
  intros Hi HF. constructor.
  - intros b x Hx. apply hosts_upd_meta in Hx. exact Hx.
  - intros b x _. unfold MR. destruct (aptr_eq_dec x g) as [->|NE].
    + rewrite get_meta_rec_upd_same. destruct (get_meta_rec st g); reflexivity.
    + rewrite get_meta_rec_upd_other by exact NE. reflexivity.
  - intros b x j _ Hj U. unfold MR in *. destruct (aptr_eq_dec x g) as [->|NE].
    + rewrite get_meta_rec_upd_same. unfold ubits in *. fold (MR st g) in *.
      destruct (MR st g) as [pv nx mm av fr li fb sc ml]; cbn in *.
      unfold tbit in *. rewrite Z.lor_spec. destruct (Z.testbit av j); [reflexivity|]. cbn in U |- *. rewrite U. reflexivity.
    + rewrite get_meta_rec_upd_other by exact NE. exact U.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma FFR_act st a act : m_avail (MR st a) = 0 ->
  FFR st (upd_meta a (fun r => m_set_avail (Z.land (m_freed (MR st a)) act) (m_set_freed (Z.ldiff (m_freed (MR st a)) act) r)) st).
Proof.
  intros AV0. constructor.
  - intros b x Hx. apply hosts_upd_meta in Hx. exact Hx.
  - intros b x _. unfold MR. destruct (aptr_eq_dec x a) as [->|NE].
    + rewrite get_meta_rec_upd_same. destruct (get_meta_rec st a); reflexivity.
    + rewrite get_meta_rec_upd_other by exact NE. reflexivity.
  - intros b x j _ Hj U. unfold MR in *. destruct (aptr_eq_dec x a) as [->|NE].
    + rewrite get_meta_rec_upd_same. unfold ubits in *. fold (MR st a) in *.
      destruct (MR st a) as [pv nx mm av fr li fb sc ml]; cbn in *. subst av.
      unfold tbit in *. rewrite Z.bits_0 in U. cbn in U. rewrite Z.land_spec, Z.ldiff_spec, U. destruct (Z.testbit act j); reflexivity.
    + rewrite get_meta_rec_upd_other by exact NE. exact U.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma FFR_fm st g : (forall b, ~ hosts st b g) -> FFR st (fm_st st g).
Proof.
  intros NH. unfold fm_st.
  cps_destruct (queue_frame LFree g (put_meta g meta0 st)) as (_ & _ & _ & _ & G & _ & _ & _ & _ & CB).
  apply FFR_data.
  - intros b x [ai Hb]. rewrite G in Hb. exists ai. exact Hb.
  - intros b x Hx. assert (NE : x <> g).
    { intros ->. apply (NH b). destruct Hx as [ai Hb]. rewrite G in Hb. exists ai. exact Hb. }
    rewrite (queue_data LFree g (put_meta g meta0 st) x). unfold MR. rewrite get_meta_rec_put_other by exact NE. reflexivity.
  - rewrite (cb_amc _ _ CB). reflexivity.
Qed.

Lemma FFR_drop_region st rid : FFR st (drop_region rid st).
Proof.
  apply FFR_same; [reflexivity| | reflexivity]. intros x. unfold MR. rewrite (get_meta_rec_ext st (drop_region rid st)) by reflexivity. reflexivity.
Qed.

Lemma FFR_strip_l st st' : FFR st st' <-> FFR (strip st) st'.
Proof.
  split; intros [A B C D]; constructor; try assumption.
Qed.
Lemma FFR_strip_r st st' : FFR st st' <-> FFR st (strip st').
Proof.
  split; intros [A B C D]; constructor; try assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition NTF_FR (T : Type) (f : nat) : Prop :=
  forall (dec : decoder T), DEC_OK T dec ->
  forall X st L BL LS g bg i (k : mstate -> mapinfo -> M T) (bail : M T),
  INVL X st L BL LS -> hosts st bg g -> 0 <= i <= m_last_idx (MR st g) ->
  x_pend X = Some (fst bg, sstart (MR st g) i) -> x_fresh X = None -> x_orph X = None ->
  (1 <= f)%nat -> 49 - m_sizeclass (MR st g) <= Z.of_nat f ->
  exists st' mi LS',
    nontrivial_free dec f st g i k bail = k st' mi /\ FFR st st' /\
    (s_regions st' = s_regions st /\ s_secret st' = s_secret st) /\
    match mi with
    | None => INVL (xpend X None) st' L BL LS'
    | Some (base, len) =>
        exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
          /\ len = round_up_pg (r_len r) /\ 0 < len
          /\ INVL (xorph (xpend X None) (Some (fst base))) st' L BL LS'
    end.

Section FG.
Variables (T : Type) (f : nat).
Hypothesis IHf : NTF_FR T f.
Variables (dec : decoder T).
Hypothesis D1 : DEC_OK T dec.
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

Theorem free_group_fr :
  exists st' mi LS', free_group T dec (nontrivial_free dec f) st g k bail = k st' mi /\ FFR st st' /\
    (s_regions st' = s_regions st /\ s_secret st' = s_secret st) /\
    match mi with
    | None => INVL (mkX idle zomb None None None) st' L BL LS'
    | Some (base, len) =>
        exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
          /\ len = round_up_pg (r_len r) /\ 0 < len
          /\ INVL (mkX idle zomb None (Some (fst base)) None) st' L BL LS'
    end.
Proof.
  cps_pose INV as (IR & IA & IM & IL & IG & IS & ISH).
  assert (KSEC : forall U, s_secret (del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1)
            (del_group bg (upd_ctx (fun c => set_usage_map U c) st))) = s_secret st) by (intros; reflexivity).
  assert (FMSEC : forall s, s_secret (fm_st s g) = s_secret s).
  { intros s0. unfold fm_st. cps_destruct (queue_frame LFree g (put_meta g meta0 s0)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
  assert (Hgh : hosts st bg g) by (exists ai; exact Hg).
  assert (NZ : ~ In g zomb) by (intros Hz; exact (zomb_not_live _ _ _ _ _ INV g Hz (ex_intro _ bg Hgh))).
  assert (NI : ~ In g idle) by (intros Hz; exact (idle_not_live _ _ _ _ _ INV g Hz (ex_intro _ bg Hgh))).
  cps_destruct (fg_st1 X st L BL LS g bg ai INV Hg) as (S1 & U1 & U2). cbn zeta in S1, U1, U2.
  unfold free_group. fold (MR st g).
  set (st1 := if m_sizeclass (MR st g) <? 48 then set_usage (m_sizeclass (MR st g)) (usage st (m_sizeclass (MR st g)) - (m_last_idx (MR st g) + 1)) st else st) in *.
  rewrite (hosts_mem _ _ _ IM _ _ Hgh).
  set (stk := del_slots bg (get_stride (MR st g)) (m_last_idx (MR st g) + 1) (del_group bg st1)).
  pose proof (INVL_kill X st st1 L BL LS g bg ai i INV Hg eq_refl NL eq_refl Hi eq_refl ALL S1 U1 U2) as INVK.
  cbn [x_idle x_zomb X] in INVK. fold stk in INVK.
  pose proof (K_MR st st1 g bg S1 U1 U2) as KMR. fold stk in KMR.
  (* [comment removed for export] *)
  assert (FK : FFR st stk).
  { apply FFR_data.
    - intros b x Hx. exact (proj1 (proj1 (hosts_K st st1 g bg S1 U1 U2 b x) Hx)).
    - intros b x _. rewrite KMR. reflexivity.
    - pose proof (K_cf st st1 g bg S1) as KC. fold stk in KC. apply KC. }
  assert (NHK : forall s, s_groups s = s_groups stk -> forall b, ~ hosts s b g).
  { intros s Hs b Hb. destruct Hb as [ab Hb]. rewrite Hs in Hb.
    exact (hosts_K_neq X st st1 L BL LS g bg ai INV Hg S1 U1 U2 b g (ex_intro _ ab Hb) eq_refl). }
  destruct (Z.eqb_spec (m_maplen (MR st g)) 0) as [Hml|Hml]; cbn [negb].
  - (* [comment removed for export] *)
    cps_destruct (dec_hdr_eq X st st1 L BL LS g bg ai i INV Hg Hi S1 U1 U2
                (fun m idx => nontrivial_free dec f stk m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail Hml)
      as (pm & ip & bpm & EQ & Hs' & Hpm' & Hf & Hip & Ep & Hsc).
    fold stk in EQ, Hs', Hpm'.
    assert (DQ : decodes T stk bg pm ip).
    { split; [exact Hs'|]. intros k' bail'.
      cps_destruct (dec_hdr_eq X st st1 L BL LS g bg ai i INV Hg Hi S1 U1 U2 k' bail' Hml) as (pm' & ip' & bpm' & EQ' & Hs'' & _).
      fold stk in EQ', Hs''. rewrite Hs' in Hs''. inversion Hs''. subst. exact EQ'. }
    rewrite (D1 stk bg pm ip _ bail DQ).
    cps_destruct (IHf dec D1 (mkX idle (g :: zomb) (Some bg) None None) stk L BL LS pm bpm ip
                  (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail INVK Hpm')
      as (st3 & mi & LS3 & EQ3 & FR3 & REG3 & POST3).
    + rewrite KMR. exact Hip.
    + cbn. rewrite KMR, Ep. reflexivity.
    + reflexivity.
    + reflexivity.
    + lia.
    + rewrite KMR. lia.
    + rewrite EQ3. rewrite !free_meta_eq. exists (fm_st st3 g), mi.
      assert (FR4 : FFR st (fm_st st3 g)).
      { eapply FFR_trans; [exact FK|]. eapply FFR_trans; [exact FR3|]. apply FFR_fm.
        intros b Hb. apply (ffr_host _ _ FR3) in Hb. exact (NHK stk eq_refl b Hb). }
      destruct mi as [[base len]|].
      * cps_destruct POST3 as (r & B0 & Hr & Hk & Hlen & Hpos & INV3). cbn in INV3.
        destruct (INVL_free_zombie idle zomb None (Some (fst base)) st3 L BL LS3 g INV3 NZ NI) as [LS4 INV4].
        exists LS4. split; [reflexivity|]. split; [exact FR4|]. rewrite regions_fm_st, FMSEC.
        split; [destruct REG3 as [R3a R3b]; rewrite R3a, R3b; split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]|]. exists r.
        split; [exact B0|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hpos| exact INV4].
      * cbn in POST3. destruct (INVL_free_zombie idle zomb None None st3 L BL LS3 g POST3 NZ NI) as [LS4 INV4].
        exists LS4. split; [reflexivity|]. split; [exact FR4|]. rewrite regions_fm_st, FMSEC.
        split; [destruct REG3 as [R3a R3b]; rewrite R3a, R3b; split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]| exact INV4].
  - (* [comment removed for export] *)
    rewrite !free_meta_eq.
    cps_destruct (kill_top X st st1 L BL LS g bg ai INV Hg S1 U1 U2 Hml) as (r & B0 & Hr & Hk & Hlen & Hpos).
    fold stk in Hr.
    assert (INV2 : INVL (mkX idle (g :: zomb) None (Some (fst bg)) None) (record_seq (m_sizeclass (MR st g)) (step_seq stk)) L BL LS).
    { apply INVL_record_seq. apply INVL_step_seq. unfold stk. cbn [negb] in INVK. exact INVK. }
    destruct (INVL_free_zombie idle zomb None (Some (fst bg)) _ L BL LS g INV2 NZ NI) as [LS4 INV4].
    assert (RS : forall sc s, s_regions (record_seq sc (step_seq s)) = s_regions s).
    { intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
    assert (RSS : forall sc s, s_secret (record_seq sc (step_seq s)) = s_secret s).
    { intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
    assert (RSG : forall sc s, s_groups (record_seq sc (step_seq s)) = s_groups s).
    { intros sc s. unfold record_seq, step_seq. destruct (sc_in_seq_range sc); destruct (c_seq (ctx s) =? 255); reflexivity. }
    assert (FRS : forall sc s, FFR s (record_seq sc (step_seq s))).
    { intros sc s. apply (FFR_trans _ (step_seq s)).
      - unfold step_seq. destruct (c_seq (ctx s) =? 255);
          (first [apply (FFR_upd_ctx s (fun c => set_seq 1 (set_unmap_seq_map ∅ c)))| apply (FFR_upd_ctx s (fun c => set_seq (c_seq c + 1) c))]);
          destruct s as [c ? ? ? ? ? ? ? ? ? ?]; destruct c; reflexivity.
      - unfold record_seq. destruct (sc_in_seq_range sc); [| apply FFR_refl].
        apply (FFR_upd_ctx _ (fun c => set_unmap_seq_map (<[sc - 7:=c_seq c]> (c_unmap_seq c)) c)).
        destruct (step_seq s) as [c ? ? ? ? ? ? ? ? ? ?]; destruct c; reflexivity. }
    eexists _, _, LS4. split; [reflexivity|].
    split.
    { eapply FFR_trans; [exact FK|]. eapply FFR_trans; [apply FRS|]. apply FFR_fm.
      intros b Hb. apply (ffr_host _ _ (FRS (m_sizeclass (MR st g)) stk)) in Hb. exact (NHK stk eq_refl b Hb). }
    rewrite regions_fm_st, RS, FMSEC, RSS.
    split; [split; [exact (K_regions st st1 g bg S1 U1 U2)| destruct S1 as [U ->]; apply KSEC]|]. cbn. exists r. cbn.
    split; [exact B0|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hpos| exact INV4].
Qed.
End FG.

Theorem ntf_fr T : forall f, NTF_FR T f.
Proof.
  induction f as [|f IH]; intros dec D1 X st L BL LS g bg i k bail INV Hgh Hi HP HF HO F1 F2; [lia|].
  destruct X as [idle zomb pend orph fresh]. cbn in HP, HF, HO. subst pend orph fresh.
  cps_pose INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof Hgh as [ai Hg].
  pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO. cps_pose (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
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
  assert (NU : okay_to_free st g = false -> m_sizeclass (MR st g) < 48 -> UNIT * size_class (m_sizeclass (MR st g)) <= get_stride (MR st g)).
  { intros OK Hsc. unfold okay_to_free in OK. fold (MR st g) in OK. rewrite (g_freeable _ _ _ _ _ _ GO) in OK. cbn [Z.eqb] in OK.
    destruct (Z.ltb_spec (get_stride (MR st g)) (UNIT * size_class (m_sizeclass (MR st g)))); [| lia].
    rewrite Bool.orb_true_r in OK. discriminate. }
  assert (FAOR : forall s, data_of (MR s g) = data_of (MR st g) -> FFR s (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) s)).
  { intros s Ds. apply FFR_aor; [lia|]. cps_destruct (data_same _ _ i Ds) as (_ & _ & _ & Ef & _). rewrite Ef. exact M2. }
  destruct ((mask + bit i =? mask_upto (m_last_idx (MR st g))) && okay_to_free st g) eqn:C1.
  - (* [comment removed for export] *)
    apply Bool.andb_true_iff in C1 as [CM COK]. apply Z.eqb_eq in CM.
    assert (ALL : forall j, 0 <= j <= m_last_idx (MR st g) -> j <> i -> tbit (m_avail (MR st g)) j = true \/ tbit (m_freed (MR st g)) j = true).
    { intros j Hj NE. assert (T1 : Z.testbit (mask + bit i) j = true) by (rewrite CM, testbit_mask_upto by lia; apply Z.leb_le; lia).
      rewrite MADD, Z.lor_spec, testbit_bit in T1 by lia. destruct (Z.eqb_spec i j); [lia|]. rewrite Bool.orb_false_r in T1.
      unfold mask in T1. rewrite Z.lor_spec in T1. unfold tbit. destruct (Z.testbit (m_freed (MR st g)) j); [right; reflexivity|]. left. exact T1. }
    pose proof (INVL_set_fresh _ st L BL LS (Some g) INV eq_refl) as INVf. cbn in INVf.
    assert (FGT : forall st2 LS2,
      INVL (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) st2 L BL LS2 ->
      s_groups st2 = s_groups st -> data_of (MR st2 g) = data_of (MR st g) -> m_next (MR st2 g) = None ->
      exists st' mi LS', free_group T dec (nontrivial_free dec f) st2 g k bail = k st' mi /\ FFR st2 st' /\
        (s_regions st' = s_regions st2 /\ s_secret st' = s_secret st2) /\
        match mi with
        | None => INVL (mkX idle zomb None None None) st' L BL LS'
        | Some (base, len) => exists r, snd base = 0 /\ s_regions st' !! (fst base) = Some r /\ r_kind r = RKGroup
            /\ len = round_up_pg (r_len r) /\ 0 < len /\ INVL (mkX idle zomb None (Some (fst base)) None) st' L BL LS'
        end).
    { intros st2 LS2 INV2 HG2 DD2 NL2. cps_destruct (data_same _ _ i DD2) as (Es & El & Ea & Ef & Esc & Eml & Emem).
      rewrite <- Es in INV2.
      apply (free_group_fr T f IH dec D1 idle zomb st2 L BL LS2 g bg ai i k bail INV2).
      - rewrite HG2. exact Hg.
      - exact NL2.
      - rewrite El. exact Hi.
      - rewrite El, Ea, Ef. exact ALL.
      - rewrite Esc. exact F2. }
    destruct (m_next (MR st g)) as [nx|] eqn:NX.
    + assert (Lg : in_list LS g) by (apply (proj2 (proj1 (il_link _ _ IL g))); rewrite NX; discriminate).
      destruct Lg as [h Hin]. destruct h as [sc|]; [| exfalso; exact (free_not_live _ _ _ _ _ INV g Hin (ex_intro _ bg Hgh))].
      cps_destruct (il_active _ _ IL sc g Hin) as (Hsc & _ & Esc). rewrite Esc.
      rewrite !(guard_true 50) by (apply Z.ltb_lt; lia).
      cps_destruct (in_split _ _ Hin) as (l1 & l2 & HL).
      pose proof (il_nodup _ _ IL (LActive sc)) as ND. rewrite HL in ND.
      assert (INV1 : INVL (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) (dequeue (LActive sc) g st) L BL (fupd LS (LActive sc) (l1 ++ l2))).
      { apply (INVL_dequeue _ _ st L BL LS g (LActive sc) l1 l2 INV HL). left. exists sc. auto. }
      set (st1 := dequeue (LActive sc) g st) in *. set (LS1 := fupd LS (LActive sc) (l1 ++ l2)) in *.
      cps_destruct (dequeue_frame (LActive sc) g st) as (RG1 & _ & _ & _ & G1 & _ & _ & SE1 & _ & CB1). fold st1 in G1, RG1, SE1, CB1.
      pose proof (dequeue_data (LActive sc) g st) as DG1. fold st1 in DG1.
      assert (FR1 : FFR st st1) by (apply FFR_same; [exact G1| exact DG1| exact (cb_amc _ _ CB1)]).
      assert (NL1 : m_next (MR st1 g) = None) by (unfold st1; rewrite dequeue_next, aptr_eqb_refl; reflexivity).
      assert (HD1 : active st1 sc = head_of (l1 ++ l2)).
      { pose proof (il_head _ _ (proj1 (proj2 (proj2 (proj2 INV1)))) (LActive sc)) as H. unfold LS1 in H. rewrite fupd_eq in H. exact H. }
      destruct (optr_eqb (active st sc) (Some g)) eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1|].
      * destruct (optr_eqb_spec (active st sc) (Some g)) as [HD|]; [| discriminate].
        assert (El1 : l1 = []).
        { apply (head_of_eq_app l1 l2 g ND). rewrite <- HL. rewrite <- (il_head _ _ IL (LActive sc)). exact HD. }
        subst l1. cbn in HD1, HL, ND. destruct l2 as [|a' l2']; cbn in HD1; [discriminate|]. inversion HD1. subst a'.
        assert (Hain : In a (LS (LActive sc))) by (rewrite HL; right; left; reflexivity).
        assert (NEa : a <> g) by (intros ->; apply NoDup_cons in ND as [N _]; apply N; apply list_elem_of_In; left; reflexivity).
        cps_destruct (il_active _ _ IL sc a Hain) as (_ & [ba [aia Ha]] & Esca).
        pose proof (g_rest _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Ha) ltac:(discriminate) sc Hain ltac:(rewrite HL; cbn; congruence)) as [AZa FZa].
        pose proof (dequeue_data (LActive sc) g st a) as Da. fold st1 in Da.
        cps_destruct (data_same _ _ 0 Da) as (_ & _ & Eaa & _ & Esa & _).
        assert (Ha1 : s_groups st1 !! ba = Some (mkGhdr (Some a) aia)) by (rewrite G1; exact Ha).
        assert (AV1 : m_avail (MR st1 a) = 0) by (rewrite Eaa; exact AZa).
        assert (HEAD1 : head_of (LS1 (LActive (m_sizeclass (MR st1 a)))) = Some a).
        { rewrite Esa, Esca. unfold LS1. rewrite fupd_eq. reflexivity. }
        rewrite !(activate_group_eq _ st1 L BL LS1 a ba aia INV1 Ha1 AV1).
        pose proof (INVL_activate _ st1 L BL LS1 a ba aia INV1 Ha1 AV1 HEAD1) as INV2.
        pose proof (FFR_act st1 a (mask_upto aia) AV1) as FR2.
        set (st2 := upd_meta a _ st1) in INV2, FR2 |- *.
        cps_destruct (FGT st2 LS1 INV2) as (st' & mi & LS' & EQ & FR' & REG & POST).
        -- unfold st2. cbn. exact G1.
        -- unfold st2, MR. rewrite get_meta_rec_upd_other by congruence. exact (DG1 g).
        -- unfold st2, MR. rewrite get_meta_rec_upd_other by congruence. exact NL1.
        -- exists st', mi, LS'. split; [exact EQ|].
           split; [eapply FFR_trans; [exact FR1| eapply FFR_trans; [exact FR2| exact FR']]|].
           split; [destruct REG as [RA RB]; rewrite RA, RB; unfold st2; split; [etransitivity; [| exact RG1]; reflexivity| etransitivity; [| exact SE1]; reflexivity]| exact POST].
      * cps_destruct (FGT st1 LS1 INV1 G1 (DG1 g) NL1) as (st' & mi & LS' & EQ & FR' & REG & POST). exists st', mi, LS'. split; [exact EQ|].
        split; [eapply FFR_trans; [exact FR1| exact FR']|].
        split; [destruct REG as [RA RB]; rewrite RA, RB; split; [exact RG1| exact SE1]| exact POST].
      * cps_destruct (FGT st1 LS1 INV1 G1 (DG1 g) NL1) as (st' & mi & LS' & EQ & FR' & REG & POST). exists st', mi, LS'. split; [exact EQ|].
        split; [eapply FFR_trans; [exact FR1| exact FR']|].
        split; [destruct REG as [RA RB]; rewrite RA, RB; split; [exact RG1| exact SE1]| exact POST].
    + cps_destruct (FGT st LS INVf eq_refl eq_refl NX) as (st' & mi & LS' & EQ & POST). exists st', mi, LS'. split; [exact EQ| exact POST].
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
    + assert (AZ : m_avail (MR st g) = 0) by (unfold mask in MZ; apply Z.lor_eq_0_iff in MZ; tauto).
      assert (FZ : m_freed (MR st g) = 0) by (unfold mask in MZ; apply Z.lor_eq_0_iff in MZ; tauto).
      assert (Hsc : 0 <= m_sizeclass (MR st g) < 48).
      { destruct (g_sc _ _ _ _ _ _ GO) as [[H _]|(E63 & L0 & _)]; [exact H|]. exfalso.
        rewrite (OKF L0) in NU. unfold okay_to_free in OKF. fold (MR st g) in OKF. rewrite (g_freeable _ _ _ _ _ _ GO), E63 in OKF.
        cbn in OKF. discriminate (OKF L0). }
      rewrite !(guard_true 51) by (apply Z.ltb_lt; lia).
      destruct (optr_eqb_spec (active st (m_sizeclass (MR st g))) (Some g)) as [HD|NHD]; cbn [negb].
      * eexists _, None, LS. split; [reflexivity|]. split; [apply FAOR; reflexivity|]. split; [split; reflexivity|]. cbn.
        apply (INVL_aor _ st L BL LS g bg ai i INV Hg Hi eq_refl).
        -- intros _ sc _ _. exact AZ.
        -- intros _ _. exists (LActive (m_sizeclass (MR st g))). apply (head_listed _ _ _ _ _ INV). exact HD.
        -- exact C3.
      * assert (NL : m_next (MR st g) = None).
        { destruct (m_next (MR st g)) as [nx|] eqn:NX; [| reflexivity]. exfalso.
          assert (Lg : in_list LS g) by (apply (proj1 (proj1 (il_link _ _ IL g))) || apply (proj2 (proj1 (il_link _ _ IL g))); rewrite NX; discriminate).
          destruct Lg as [h Hin]. destruct h as [sc|]; [| exact (free_not_live _ _ _ _ _ INV g Hin (ex_intro _ bg Hgh))].
          cps_destruct (il_active _ _ IL sc g Hin) as (_ & _ & Esc). subst sc.
          apply NHD. rewrite <- Esc at 1 || idtac.
          destruct (g_rest _ _ _ _ _ _ GO ltac:(discriminate) _ Hin) as [_ FNZ]; [| exact (FNZ FZ) || congruence].
          rewrite <- (il_head _ _ IL (LActive (m_sizeclass (MR st g)))). intros E. apply NHD. exact (eq_sym E) || (symmetry; exact E). }
        assert (NP : m_prev (MR st g) = None) by (exact (proj2 (il_link _ _ IL g) NL)).
        rewrite !(queue_eq (LActive (m_sizeclass (MR st g))) g st _ bail NL NP).
        pose proof (INVL_set_fresh _ st L BL LS (Some g) INV eq_refl) as INVf. cbn in INVf.
        pose proof (INVL_queue _ st L BL LS g (LActive (m_sizeclass (MR st g))) INVf NL (g_present _ _ _ _ _ _ GO)) as INVq.
        cbn [x_fresh x_idle x_zomb] in INVq. specialize (INVq ltac:(repeat split; auto; lia; fail)) || specialize (INVq (conj Hsc (conj (ex_intro _ bg Hgh) (conj eq_refl eq_refl)))).
        set (stq := queue_st (LActive (m_sizeclass (MR st g))) g st) in *.
        set (LSq := fupd LS (LActive (m_sizeclass (MR st g))) (LS (LActive (m_sizeclass (MR st g))) ++ [g])) in *.
        cps_destruct (queue_frame (LActive (m_sizeclass (MR st g))) g st) as (RGq & _ & _ & _ & Gq & _ & _ & SEq & _ & CBq). fold stq in Gq, RGq, SEq, CBq.
        pose proof (queue_data (LActive (m_sizeclass (MR st g))) g st g) as Dq. fold stq in Dq.
        cps_destruct (data_same _ _ i Dq) as (Es & El & Ea & Ef & Esc & Eml & Emem).
        assert (FRq : FFR st stq).
        { apply FFR_same; [exact Gq| | exact (cb_amc _ _ CBq)]. intros x. unfold stq. apply queue_data. }
        assert (INVa : INVL (mkX idle zomb None None (Some g)) (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) stq) L BL LSq).
        { apply (INVL_aor (mkX idle zomb (Some (fst bg, sstart (MR st g) i)) None (Some g)) stq L BL LSq g bg ai i INVq).
          - rewrite Gq. exact Hg.
          - rewrite El. exact Hi.
          - cbn. rewrite Es. reflexivity.
          - cbn. intros NF. exfalso. apply NF. reflexivity.
          - cbn. intros NF. exfalso. apply NF. reflexivity.
          - rewrite Esc. unfold stq, MR. rewrite (get_stride_data _ _ Dq). exact C3. }
        eexists _, None, LSq. split; [reflexivity|].
        split; [eapply FFR_trans; [exact FRq| apply FAOR; exact Dq]|].
        split; [cbn; rewrite RGq, SEq; split; reflexivity|]. cbn.
        apply (INVL_clear_fresh _ _ L BL LSq g INVa eq_refl).
        intros b ai' Hb. unfold MR. rewrite get_meta_rec_upd_same. cbn [m_last_idx m_sizeclass m_avail m_freed m_set_freed]. fold (MR stq g). rewrite El, Esc, Ea, Ef.
        assert (ING : In g (LSq (LActive (m_sizeclass (MR st g))))) by (unfold LSq; rewrite fupd_eq; apply in_app_iff; right; left; reflexivity).
        split; [intros _; exact ING|]. split; [intros _ NI; exfalso; apply NI; eexists; exact ING|].
        split; [intros sc _ _; split; [exact AZ|]; rewrite FZ, Z.lor_0_l; unfold bit; pose proof (Z.pow_pos_nonneg 2 i); lia|].
        intros Hsc' LT. exfalso. pose proof (C3 Hsc') as GE.
        replace (get_stride (m_set_freed (Z.lor (m_freed (MR st g)) (bit i)) (MR stq g))) with (get_stride (MR stq g)) in LT by (destruct (MR stq g); reflexivity).
        rewrite (get_stride_data _ _ Dq) in LT. lia.
    + eexists _, None, LS. split; [reflexivity|]. split; [apply FAOR; reflexivity|]. split; [split; reflexivity|]. cbn.
      apply (INVL_aor _ st L BL LS g bg ai i INV Hg Hi eq_refl).
      * intros _ sc Hin Hnh. exact (proj1 (g_rest _ _ _ _ _ _ GO ltac:(discriminate) sc Hin Hnh)).
      * intros _ Hsc. destruct (m_next (MR st g)) as [nx|] eqn:NX.
        -- apply (proj2 (proj1 (il_link _ _ IL g))). rewrite NX. discriminate.
        -- exfalso.
           assert (NIL : ~ in_list LS g) by (intros [h Hin]; exact (lists_notin st LS (old_lists _ _ _ _ _ INV) g NX h Hin)).
           destruct (g_unlisted _ _ _ _ _ _ GO ltac:(discriminate) Hsc NIL) as [A0 F0]. apply MNZ. unfold mask. rewrite A0, F0. reflexivity.
      * exact C3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma strel_ret_invF {R1 R2} (RR : R1 -> R2 -> Prop) r1 (t2 : M R2) :
  strel RR (SRet r1) t2 -> exists r2, t2 = SRet r2 /\ RR r1 r2.
Proof. intros H. inversion H; subst. eexists. split; [reflexivity| assumption]. Qed.

Lemma strel_vis_invF {R1 R2} (RR : R1 -> R2 -> Prop) e K1 (t2 : M R2) :
  strel RR (SVis e K1) t2 -> exists K2, t2 = SVis e K2 /\ forall a, strel RR (K1 a) (K2 a).
Proof.
  intros H. inversion H; subst.
  match goal with H1 : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep_dec.inj_pair2_eq_dec in H1; [subst| apply ev_eq_dec] end || idtac.
  all: eexists; split; [reflexivity| assumption].
Qed.

Lemma prun_retF {R} (r : R) : prun pans0 pupd0 tt (SRet r) = SRet (tt, r).
Proof. unfold prun. apply eruns_ret. Qed.

Lemma prun_munmapF {R} a len (K : Z -> M R) : prun pans0 pupd0 tt (SVis (EMunmap a len) K) = SVis (EMunmap a len) (fun z => prun pans0 pupd0 tt (K z)).
Proof. unfold prun. rewrite eruns_vis_keep by reflexivity. reflexivity. Qed.

Theorem cfree_shape cs L c :
  SIMREL cs L -> In c (ld_live L) ->
  (exists cs', cfree cs (Some c) = SRet cs' /\ FFR cs cs')
  \/ exists a l0 K, cfree cs (Some c) = SVis (EMunmap a (round_up_pg l0)) K /\ In (a, l0) (ld_groups L) /\ 0 < round_up_pg l0 /\
       forall ru, munmap_answer_ok ru = true -> exists cs', K ru = SRet cs' /\ FFR cs cs'.
Proof.
  (cps_intros (st & BL & LS & Ecs & INV & LIVE); intros Hc).
  rewrite LIVE in Hc. cps_destruct (In_bslot _ _ Hc) as (off & n & Hk).
  cps_destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  cps_pose INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) as Ec.
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hm. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi.
  pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. unfold tbit in NA, NF.
  pose proof (ig_ok _ _ _ IG _ _ _ Hm) as GO. cps_pose (g_masks _ _ _ _ _ _ GO) as (M1 & M2 & M3 & M4 & M5 & M6).
  assert (INV1 : INVL (xpend x0 (Some c)) st L (bl_remove c BL) LS).
  { change c with (bslot ((c, off), n)) at 1 2.
    apply (INVL_remove_block x0 st st L BL LS ((c, off), n) INV Hk eq_refl (ctrl_eq_refl st) eq_refl).
    - intros; reflexivity.
    - exact (ish_dom _ _ ISH).
    - exact (ish_ticks _ _ ISH). }
  (* [comment removed for export] *)
  assert (Ecf : cfree cs (Some c) = sbind (free_tail dec_slots (strip st) m i) (fun x => ret (strip x))).
  { unfold cfree. rewrite <- Ecs, s_slots_strip, Hs. reflexivity. }
  rewrite Ecf.
  pose proof (free_tail_slots_control pans0 pupd0 st m i tt) as REL.
  assert (FS : forall x, FFR st x -> FFR cs (strip x)) by (intros x H; rewrite <- Ecs; apply (proj1 (FFR_strip_l _ _)), (proj1 (FFR_strip_r _ _)); exact H).
  (* [comment removed for export] *)
  set (TC := free_tail dec_slots (strip st) m i) in *.
  unfold free_tail in REL. fold (MR st m) in REL.
  rewrite (guard_true 60) in REL by (unfold testbit; rewrite Z.lor_spec; rewrite NA, NF; reflexivity).
  destruct (negb ((m_freed (MR st m) =? 0) || (Z.lor (m_freed (MR st m)) (m_avail (MR st m)) + bit i =? mask_upto (m_last_idx (MR st m))))) eqn:BR.
  - (* [comment removed for export] *)
    left. cbn [ret] in REL. rewrite prun_retF in REL.
    cps_destruct (strel_ret_invF _ _ _ REL) as (y & -> & Ey). cbn [snd] in Ey. rewrite sbind_ret_l. cbn [ret]. eexists. split; [reflexivity|].
    rewrite <- Ey. apply FS.
    assert (MADD : m_freed (MR st m) + bit i = Z.lor (m_freed (MR st m)) (bit i)).
    { rewrite bit_eq. apply add_bit_lor; [exact M2| lia| exact NF]. }
    replace (upd_meta m (m_set_freed (m_freed (MR st m) + bit i)) st)
      with (upd_meta m (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st).
    2:{ unfold upd_meta. fold (MR st m). rewrite MADD. reflexivity. }
    apply FFR_aor; [lia| exact M2].
  - (* [comment removed for export] *)
    set (Kt := fun (st2 : mstate) (mi : mapinfo) => match mi with
          | Some (base, len) => if negb (len =? 0) then SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st)) else ret st2
          | None => ret st2 end) in REL.
    cps_destruct (ntf_fr mstate FUEL dec_slots (dec_slots_ok mstate) (xpend x0 (Some c)) st L (bl_remove c BL) LS m bm i Kt (ret st)
                INV1 (ex_intro _ ai Hm) Hi ltac:(cbn; rewrite Ec; reflexivity) eq_refl eq_refl ltac:(unfold FUEL; lia)
                ltac:(pose proof (g_sc _ _ _ _ _ _ GO); unfold FUEL; lia))
      as (st' & mi & LS' & EQ & FR & REG & POST).
    rewrite EQ in REL.
    destruct mi as [[base len]|].
    + cps_destruct POST as (r & B0 & Hr & Hkd & Hlen & Hpos & INV').
      right. unfold Kt in REL. replace (negb (len =? 0)) with true in REL by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
      rewrite prun_munmapF in REL.
      cps_destruct (strel_vis_invF _ _ _ _ REL) as (K2 & E2 & RK). rewrite E2, sbind_vis.
      assert (CB : conc st' base = r_base r) by (unfold conc, get_region; rewrite Hr; lia).
      rewrite CB, Hlen. eexists (r_base r), (r_len r), _. split; [reflexivity|].
      split; [exact (group_region_in_ledger _ _ _ _ _ (proj1 INV') Hr Hkd)|]. split; [lia|].
      intros ru RU. specialize (RK ru). rewrite RU, prun_retF in RK.
      cps_destruct (strel_ret_invF _ _ _ RK) as (y & -> & Ey). cbn [snd] in Ey. rewrite sbind_ret_l. cbn [ret]. eexists. split; [reflexivity|].
      rewrite <- Ey. apply FS. eapply FFR_trans; [exact FR| apply FFR_drop_region].
    + left. unfold Kt in REL. cbn [ret] in REL. rewrite prun_retF in REL.
      cps_destruct (strel_ret_invF _ _ _ REL) as (y & -> & Ey). cbn [snd] in Ey. rewrite sbind_ret_l. cbn [ret]. eexists. split; [reflexivity|].
      rewrite <- Ey. apply FS. exact FR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FREEC21.
Variables (W W' : list cptr) (st st' : mstate) (L L' : mled) (BL BL' : list blk) (LS LS' : lhead -> list aptr) (c : cptr).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis INV' : INVL x0 st' L' BL' LS'.
Hypothesis FR : FFR st st'.
Hypothesis Hc : In c (map bslot BL).
Hypothesis HBL : forall x, In x (map bslot BL') -> In x (map bslot BL) /\ x <> c.
Hypothesis HW : forall x, In x W -> x <> c -> In x W'.
Hypothesis HC : C21 W st.

Let IMx := proj1 (proj2 (proj2 INV)).
Let IGx := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
Let ISx := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).
Let IMx' := proj1 (proj2 (proj2 INV')).
Let IGx' := proj1 (proj2 (proj2 (proj2 (proj2 INV')))).
Let ISx' := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV'))))).

Lemma C21_free : C21 W' st'.
Proof.
  destruct FR as [FH FG FB FC]. destruct HC as [T3 UQ OC].
  constructor.
  - intros g b Hh Hs. pose proof (FG _ _ Hh) as G. rewrite (geo_li _ _ G). apply (T3 g b (FH _ _ Hh)). rewrite <- (geo_sc _ _ G). exact Hs.
  - intros g g' b b' Hh Hh' Hs Hs'. apply (UQ g g' b b' (FH _ _ Hh) (FH _ _ Hh')).
    + rewrite <- (geo_sc _ _ (FG _ _ Hh)). exact Hs.
    + rewrite <- (geo_sc _ _ (FG _ _ Hh')). exact Hs'.
  - intros g b i Hh Hs Hi.
    pose proof (FG _ _ Hh) as G. pose proof (FH _ _ Hh) as Hh0.
    assert (Hs0 : m_sizeclass (MR st g) = FILE_CLASS) by (rewrite <- (geo_sc _ _ G); exact Hs).
    pose proof (T3 g b Hh0 Hs0) as L2.
    cps_destruct (hosts_ok x0 st' LS' IGx' b g Hh) as (ai' & Hb' & GO').
    cps_destruct (hosts_ok x0 st LS IGx b g Hh0) as (ai0 & Hb0 & GO0).
    pose proof (is_part _ _ _ ISx' b g ai' i Hb' ltac:(rewrite (geo_li _ _ G); lia)) as ONE'.
    rewrite (slot_start'_eq _ _ _ IMx' _ _ i Hh) in ONE'. cbn zeta in ONE'. cbn [x_pend x0] in ONE'.
    pose proof (is_part _ _ _ ISx b g ai0 i Hb0 ltac:(lia)) as ONE.
    rewrite (slot_start'_eq _ _ _ IMx _ _ i Hh0) in ONE. cbn zeta in ONE. cbn [x_pend x0] in ONE.
    rewrite (geo_ss _ _ i G) in ONE' |- *.
    set (x := (fst b, sstart (MR st g) i)) in *.
    destruct ONE' as (D5 & _).
    cps_destruct ONE as (_ & nAB & nAC & nAD & _ & nBC & nBD & _ & nCD & _).
    assert (OCC : ~ tbit (m_avail (MR st g)) i = true -> ~ tbit (m_freed (MR st g)) i = true -> In x W).
    { intros n1 n2. destruct (OC g b i Hh0 Hs0 Hi) as [H|[H|H]]; [exact (False_ind _ (n1 H))| exact (False_ind _ (n2 H))| exact H]. }
    destruct D5 as [Ha|[Hb2|[HCx|[HD|HE]]]]; [left; exact Ha| right; left; exact Hb2| | | discriminate].
    + right. right. destruct (HBL x HCx) as [Cx NE]. apply HW; [| exact NE]. apply OCC; intros H; [apply nAC| apply nBC]; auto.
    + right. right.
      destruct (s_groups st' !! x) as [[mm aa]|] eqn:EG; [| exact (False_ind _ (HD EG))].
      destruct mm as [y|]; [| exact (False_ind _ (ig_nometa _ _ _ IGx' _ _ EG))].
      assert (Hy : hosts st' x y) by (exists aa; exact EG). apply FH in Hy. destruct Hy as [ay Hy].
      assert (Dx : s_groups st !! x <> None) by (rewrite Hy; discriminate).
      apply HW; [apply OCC; intros H; [apply nAD| apply nBD]; auto|].
      intros E. apply nCD. split; [rewrite E; exact Hc| exact Dx].
Qed.
End FREEC21.

(* [comment removed for export] *)
Lemma INSLOT_free W st st' L L' BL BL' LS LS' x :
  INVL x0 st L BL LS -> INVL x0 st' L' BL' LS' -> FFR st st' -> C21 W st -> In x (map bslot BL') ->
  INSLOT st x -> INSLOT st' x.
Proof.
  (intros INV INV' [FH FG FB FC] HC Hx; cps_intros (g & b & i & Hh & Hs & Hi & ->)).
  pose proof (proj1 (proj2 (proj2 INV))) as IMx. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV)))))) as ISx.
  pose proof (proj1 (proj2 (proj2 INV'))) as IMx'. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV')))))) as ISx'.
  pose proof (c21_three _ _ HC g b Hh Hs) as L2.
  pose proof (is_total _ _ _ ISx b g i Hh ltac:(lia)) as T1. rewrite (slot_start'_eq _ _ _ IMx _ _ i Hh) in T1.
  apply in_map_iff in Hx as (k & Ek & Hk).
  cps_destruct (is_blocks _ _ _ ISx' k Hk) as (m0 & i0 & Sk & _).
  cps_destruct (is_valid _ _ _ ISx' _ _ _ Sk) as ([b0 Hm0] & Hi0 & Es). rewrite Ek in Sk, Es.
  pose proof (FH _ _ Hm0) as Hm00. pose proof (FG _ _ Hm0) as G0.
  rewrite (slot_start'_eq _ _ _ IMx' _ _ i0 Hm0) in Es.
  pose proof (is_total _ _ _ ISx b0 m0 i0 Hm00 ltac:(rewrite <- (geo_li _ _ G0); exact Hi0)) as T0.
  rewrite (slot_start'_eq _ _ _ IMx _ _ i0 Hm00), <- (geo_ss _ _ i0 G0), <- Es, T1 in T0.
  injection T0 as E1 E2. subst m0 i0.
  exists g, b0, i. split; [exact Hm0|]. split; [rewrite (geo_sc _ _ G0); exact Hs|]. split; [exact Hi| exact Es].
Qed.

End ACeilS1.
