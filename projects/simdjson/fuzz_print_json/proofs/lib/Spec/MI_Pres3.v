(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Pres1 MI_Pres2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Record ctx_scalars_eq (c c' : mctx) : Prop := mkCS {
  cs_secret : c_secret c' = c_secret c;
  cs_init : c_init_done c' = c_init_done c;
  cs_fmh : c_free_meta_head c' = c_free_meta_head c;
  cs_am : c_avail_meta c' = c_avail_meta c;
  cs_amc : c_avail_meta_count c' = c_avail_meta_count c;
  cs_amac : c_avail_meta_area_count c' = c_avail_meta_area_count c;
  cs_shift : c_meta_alloc_shift c' = c_meta_alloc_shift c;
  cs_mah : c_meta_area_head c' = c_meta_area_head c;
  cs_mat : c_meta_area_tail c' = c_meta_area_tail c;
  cs_amas : c_avail_meta_areas c' = c_avail_meta_areas c;
  cs_active : c_active c' = c_active c;
  cs_usage : c_usage c' = c_usage c;
  cs_brk : c_brk c' = c_brk c;

  cs_mc : 0 <= c_mmap_counter c' < 2^32;
  cs_seq : 0 <= c_seq c' < 256;
  cs_bounces : forall i v, c_bounces c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256;
  cs_unmap : forall i v, c_unmap_seq c' !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256
}.

Section CTX.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (f : mctx -> mctx).
Hypothesis INV : INVL X st L BL LS.
Hypothesis CS : ctx_scalars_eq (s_ctx st) (f (s_ctx st)).
Let st' := upd_ctx f st.

Theorem INVL_ctx_scalars : INVL X st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH). destruct CS as [cs_secret cs_init cs_fmh cs_am cs_amc cs_amac cs_shift cs_mah cs_mat cs_amas cs_active cs_usage cs_brk cs_mc cs_seq cs_bounces cs_unmap].
  assert (FR : forall rid r, frontier st' rid r = frontier st rid r) by (intros; unfold frontier, st'; cbn; rewrite cs_amas; reflexivity).
  assert (HE : forall h, get_head st' h = get_head st h) by (intros [sc|]; unfold st'; cbn; unfold active, ctx; cbn; rewrite ?cs_active, ?cs_fmh; reflexivity).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - destruct IR; constructor; unfold st'; cbn; rewrite ?cs_shift, ?cs_brk, ?cs_amac, ?cs_amas; try assumption.
    + eapply Permutation_trans; [exact ir_metas|]. erewrite map_ext; [apply Permutation_refl|]. intros [rid r]; cbn. rewrite FR. reflexivity.
    + intros rid r H1 H2. rewrite FR. exact (ir_metalen rid r H1 H2).
    + intros rid r H1 H2. rewrite FR. exact (ir_brkfront rid r H1 H2).
  - destruct IA; constructor; unfold st'; cbn; rewrite ?cs_secret, ?cs_init, ?cs_fmh, ?cs_am, ?cs_amc, ?cs_amac, ?cs_mah, ?cs_mat, ?cs_amas, ?cs_active, ?cs_usage; try assumption.
    + split; [exact cs_mc|]. split; [exact cs_seq|]. split; [exact cs_bounces| exact cs_unmap].
    + intros a ar Ha. destruct (ia_areas a ar Ha) as ((r & ? & ? & ? & ? & ?) & ? & ? & ?). split; [| auto]. exists r. rewrite FR. auto.
    + intros sc Hsc. unfold usage, ctx. cbn. rewrite cs_usage. exact (ia_usage sc Hsc).
  - apply (inv_M_ext X st st'); [reflexivity| reflexivity| exact IM].
  - apply (inv_L_ext st st'); [reflexivity| reflexivity| exact HE| exact IL].
  - destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
    intros m b ai Hb. apply (group_ok_ext X st st'); [reflexivity| reflexivity| auto|]. eapply G1. exact Hb.
  - apply (inv_S_ext X st st' BL); [reflexivity| reflexivity| reflexivity| exact IS].
  - apply (inv_SH_view st st'); try reflexivity. exact ISH.
Qed.
End CTX.

Lemma ctx_scalars_refl c :
  0 <= c_mmap_counter c < 2^32 -> 0 <= c_seq c < 256 ->
  (forall i v, c_bounces c !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256) ->
  (forall i v, c_unmap_seq c !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256) ->
  ctx_scalars_eq c c.
Proof. intros; constructor; auto. Qed.

Lemma ia_ctx_facts st : inv_A st ->
  0 <= c_mmap_counter (s_ctx st) < 2^32 /\ 0 <= c_seq (s_ctx st) < 256
  /\ (forall i v, c_bounces (s_ctx st) !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256)
  /\ (forall i v, c_unmap_seq (s_ctx st) !! i = Some v -> 0 <= i < 32 /\ 0 <= v < 256).
Proof. intros IA. exact (ia_ctx _ IA). Qed.

Lemma INVL_step_seq X st L BL LS : INVL X st L BL LS -> INVL X (step_seq st) L BL LS.
Proof.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold step_seq. destruct (Z.eqb_spec (c_seq (ctx st)) 255) as [E|NE]; apply INVL_ctx_scalars; auto; constructor; cbn; auto; try lia.
  - intros i v H. rewrite lookup_empty in H. discriminate.
  - unfold ctx in NE. lia.
Qed.

Lemma INVL_record_seq X st L BL LS sc : INVL X st L BL LS -> INVL X (record_seq sc st) L BL LS.
Proof.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold record_seq. destruct (sc_in_seq_range sc) eqn:E; [| exact INV].
  apply INVL_ctx_scalars; auto; constructor; cbn; auto.
  unfold sc_in_seq_range in E. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  intros i v. destruct (Z.eq_dec i (sc - 7)) as [->|NEi].
  - rewrite lookup_insert_eq. intros H. inversion H. subst. lia.
  - rewrite lookup_insert_ne by congruence. apply C4.
Qed.

Lemma INVL_set_bounce X st L BL LS i v : INVL X st L BL LS -> 0 <= i < 32 -> 0 <= v < 256 -> INVL X (set_bounce i v st) L BL LS.
Proof.
  intros INV Hi Hv. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  unfold set_bounce. apply INVL_ctx_scalars; auto; constructor; cbn; auto.
  intros j w. destruct (Z.eq_dec j i) as [->|NE].
  - rewrite lookup_insert_eq. intros H. inversion H. subst. lia.
  - rewrite lookup_insert_ne by congruence. apply C3.
Qed.

Lemma bounces_range st i : inv_A st -> 0 <= bounces st i < 256.
Proof.
  intros IA. pose proof (ia_ctx_facts st IA) as (_ & _ & C3 & _). unfold bounces, ctx.
  destruct (c_bounces (s_ctx st) !! i) as [v|] eqn:E; cbn; [| lia]. exact (proj2 (C3 _ _ E)).
Qed.

Lemma INVL_account_bounce X st L BL LS sc : INVL X st L BL LS -> INVL X (account_bounce sc st) L BL LS.
Proof.
  intros INV. unfold account_bounce. destruct (sc_in_seq_range sc) eqn:E; [| exact INV].
  unfold sc_in_seq_range in E. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  destruct (negb _ && _); [| exact INV].
  pose proof (bounces_range st (sc - 7) (proj1 (proj2 INV))).
  destruct (Z.ltb_spec (bounces st (sc - 7) + 1) 100); apply INVL_set_bounce; auto; lia.
Qed.

Lemma INVL_decay_bounces X st L BL LS sc : INVL X st L BL LS -> INVL X (decay_bounces sc st) L BL LS.
Proof.
  intros INV. unfold decay_bounces. destruct (sc_in_seq_range sc && _) eqn:E; [| exact INV].
  apply Bool.andb_true_iff in E as [E1 E2]. unfold sc_in_seq_range in E1. apply Bool.andb_true_iff in E1 as [E0 E1]. apply Z.leb_le in E0. apply Z.ltb_lt in E1.
  apply Bool.negb_true_iff in E2. apply Z.eqb_neq in E2.
  pose proof (bounces_range st (sc - 7) (proj1 (proj2 INV))).
  apply INVL_set_bounce; auto; lia.
Qed.

Lemma INVL_mmap_counter X st L BL LS : INVL X st L BL LS ->
  INVL X (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st) L BL LS.
Proof.
  intros INV. pose proof (ia_ctx_facts st (proj1 (proj2 INV))) as (C1 & C2 & C3 & C4).
  apply INVL_ctx_scalars; auto; constructor; cbn; auto. unfold u32. apply Z.mod_pos_bound. lia.
Qed.

Definition rem (g : aptr) (l : list aptr) : list aptr := remove (fun x y => aptr_eq_dec x y) g l.
Definition xzomb (X : extras) (l : list aptr) : extras := mkX (x_idle X) l (x_pend X) (x_orph X) (x_fresh X).
Definition xidle (X : extras) (l : list aptr) : extras := mkX l (x_zomb X) (x_pend X) (x_orph X) (x_fresh X).

Lemma in_rem x g l : In x (rem g l) <-> In x l /\ x <> g.
Proof. unfold rem. split; [apply in_remove|]. intros [H NE]. apply in_in_remove; auto. Qed.

Lemma present_of_mem st m b : m_mem (MR st m) = Some b -> s_metas st !! m <> None.
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; [discriminate| discriminate]. Qed.
Lemma present_of_next st m x : m_next (MR st m) = Some x -> s_metas st !! m <> None.
Proof. unfold MR, get_meta_rec. destruct (s_metas st !! m); cbn; [discriminate| discriminate]. Qed.

Lemma gcnt_ext_groups st st' :
  s_groups st' = s_groups st ->
  (forall b h m, s_groups st !! b = Some h -> g_meta h = Some m ->
     m_sizeclass (MR st' m) = m_sizeclass (MR st m) /\ cnt_of (MR st' m) = cnt_of (MR st m)) ->
  forall sc, gcnt st' sc = gcnt st sc.
Proof.
  intros HG HM sc. unfold gcnt. rewrite HG. f_equal. apply map_ext_in. intros [b h] Hin. cbn.
  destruct (g_meta h) as [m|] eqn:Eh; [| reflexivity].
  apply list_elem_of_In in Hin. apply elem_of_map_to_list in Hin.
  destruct (HM b h m Hin Eh) as [E1 E2]. rewrite E1, E2. reflexivity.
Qed.

Section UNZOMBIE.
Variables (X : extras) (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (g : aptr).
Hypothesis INV : INVL X st L BL LS.
Hypothesis Hz : In g (x_zomb X).
Let X' := xzomb X (rem g (x_zomb X)).
Let st' := put_meta g meta0 st.

Lemma uz_R x : MR st' x = if aptr_eqb x g then meta0 else MR st x.
Proof. unfold st', MR. apply get_meta_rec_put. Qed.
Lemma uz_R_other x : x <> g -> MR st' x = MR st x.
Proof. intros NE. rewrite uz_R, aptr_eqb_neq by exact NE. reflexivity. Qed.

Theorem INVL_unzombie : INVL X' st' L BL LS.
Proof.
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (im_zomb _ _ _ IM g Hz) as (NIg & Ng & Pg & bg & Mg & NGg).
  assert (NLg : forall b, ~ hosts st b g).
  { intros b [ai Hb]. destruct (im_hdr _ _ _ IM _ _ Hb) as (m & Em & Hm & _). cbn in Em. inversion Em. subst m. rewrite Mg in Hm. inversion Hm. subst. rewrite Hb in NGg. discriminate. }
  assert (RG : forall b m, hosts st b m -> MR st' m = MR st m).
  { intros b m Hm. apply uz_R_other. intros ->. exact (NLg b Hm). }
  assert (KEYS : forall x, s_metas st' !! x <> None <-> s_metas st !! x <> None).
  { intros x. unfold st'. rewrite lookup_metas_put. destruct (aptr_eqb_spec x g) as [->|NE]; [| tauto].
    split; [intros _; exact (present_of_mem st g bg Mg)| intros _; discriminate]. }
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - apply (inv_R_X X); [reflexivity|]. destruct IR; constructor; try assumption.
  - destruct IA; constructor; try assumption.
    + intros m mr Hm. assert (K : s_metas st' !! m <> None) by congruence. apply KEYS in K.
      destruct (s_metas st !! m) as [mr0|] eqn:E; [| congruence]. exact (ia_metas m mr0 E).
    + destruct ia_avail as [A1 A2]. split; [exact A1|]. intros Hc. destruct (A2 Hc) as (a & T & E & Hk). exists a. split; [exact T|]. split; [exact E|].
      intros k Hk2. destruct (s_metas st' !! mslot a k) eqn:E2; [| reflexivity]. exfalso.
      assert (K : s_metas st' !! mslot a k <> None) by congruence. apply KEYS in K. apply K. apply Hk. exact Hk2.
    + intros sc Hsc. change (usage st' sc) with (usage st sc). rewrite (ia_usage sc Hsc). symmetry. apply gcnt_ext_groups; [reflexivity|].
      intros b h m Hb Eh. destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Em & Hm & _). rewrite Eh in Em. inversion Em. subst m'.
      rewrite (RG b m); [auto|]. destruct h as [gm gai]. cbn in Eh. subst gm. exists gai. exact Hb.
  -   destruct IM as [M1 M2 M3 M4 M5]; constructor.
    + intros m Hm. rewrite uz_R in Hm |- *. destruct (aptr_eqb m g); [reflexivity|]. apply M1. exact Hm.
    + intros m b Hm. rewrite uz_R in Hm. destruct (aptr_eqb_spec m g) as [->|NE]; [cbn in Hm; discriminate|].
      destruct (M2 m b Hm) as [H|H]; [left; exact H| right]. cbn. apply in_rem. auto.
    + intros b h Hb. destruct (M3 b h Hb) as (m & Em & Hm & Hai). exists m.
      assert (NE : m <> g) by (intros ->; apply (NLg b); destruct h as [gm gai]; cbn in Em; subst gm; exists gai; exact Hb).
      rewrite (uz_R_other m NE). auto.
    + intros m Hm. cbn in Hm. destruct (M4 m Hm) as [E NI]. split; [| exact NI].
      unfold st'. rewrite lookup_metas_put. destruct (aptr_eqb_spec m g) as [->|NE]; [reflexivity| exact E].
    + intros z Hz'. cbn in Hz'. apply in_rem in Hz' as [Hz' NE]. destruct (M5 z Hz') as (A1 & A2 & A3 & b & A4 & A5).
      rewrite (uz_R_other z NE). repeat split; auto. exists b. auto.
  -   destruct IL as [L1 L2 L3 L4 L5 L6 L7 L9]; constructor; try assumption.
    + intros h. pose proof (L2 h) as D. destruct (LS h) as [|a l] eqn:E; [exact I|]. cbn [dll] in D |- *.
      eapply linked_ext; [| | exact D]; intros x Hx; rewrite uz_R_other; try reflexivity; intros ->; apply NIg; exists h; rewrite E.
      * apply In_removelast in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
      * apply In_tl in Hx. apply in_app_iff in Hx. cbn in Hx |- *. tauto.
    + intros m. destruct (aptr_eqb_spec m g) as [->|NE].
      * rewrite uz_R, aptr_eqb_refl. cbn. split; [| reflexivity]. split; [intros H; exfalso; exact (NIg H)| intros H; exfalso; apply H; reflexivity].
      * rewrite (uz_R_other m NE). apply L5.
    + intros m Hm. destruct (aptr_eqb_spec m g) as [->|NE]; [exfalso; apply NIg; exists LFree; exact Hm|]. rewrite (uz_R_other m NE). apply L6. exact Hm.
    + intros sc m Hm. destruct (L7 sc m Hm) as (A1 & A2 & A3).
      destruct (aptr_eqb_spec m g) as [->|NE]; [exfalso; apply NIg; exists (LActive sc); exact Hm|]. rewrite (uz_R_other m NE). auto.
  -   destruct IG as [G1 G2 G3 G4 G5]; constructor; try assumption.
    + intros m b ai Hb. pose proof (G1 m b ai Hb) as GO.
      assert (NE : m <> g) by (intros ->; exact (NLg b (ex_intro _ ai Hb))).
      destruct GO; constructor; rewrite ?(uz_R_other m NE); try assumption.
      * apply KEYS. exact g_present.
      * intros Hml. destruct (g_nest Hml) as (p & i & Hs & Hf & He & Hsc & Hst).
        destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _).
        assert (NEp : p <> g) by (intros ->; exact (NLg bp Hp)).
        exists p, i. rewrite (uz_R_other p NEp). auto 10.
    + intros m1 m2 b1 b2 ai1 ai2 H1 H2.
      rewrite (uz_R_other m1) by (intros ->; exact (NLg b1 (ex_intro _ ai1 H1))).
      rewrite (uz_R_other m2) by (intros ->; exact (NLg b2 (ex_intro _ ai2 H2))). eapply G3; eassumption.
    + intros rid r Hr Hk Ho. destruct (G4 rid r Hr Hk Ho) as (m & Hm & Hml). exists m. rewrite (RG _ _ Hm). auto.
  -   destruct IS as [S1 S2 S3 S4 S5 S6]; constructor; try assumption.
    + intros s m i Hs. destruct (S1 s m i Hs) as ([b Hb] & Hi & E). rewrite (RG _ _ Hb). split; [exists b; exact Hb| auto].
    + intros b m i Hb Hi. rewrite (RG _ _ Hb) in Hi |- *. apply (S2 b); auto.
    + intros b m ai i Hb Hi. rewrite (RG b m (ex_intro _ ai Hb)) in Hi |- *. apply (S3 b m ai i Hb Hi).
    + intros k Hk. destruct (S6 k Hk) as (m & i & Hs & rest). exists m, i. split; [exact Hs|].
      destruct (S1 _ _ _ Hs) as ([b Hb] & _). rewrite (RG _ _ Hb). exact rest.
  -   destruct ISH as [D1 D2 D3 D4 D5 D6]; constructor; try assumption.
    + intros b m i Hb Hi. rewrite (RG _ _ Hb) in Hi |- *. apply (D3 b m i Hb Hi).
    + intros b m p i Hb Hml Hs. rewrite (RG _ _ Hb) in Hml.
      destruct (is_valid _ _ _ IS _ _ _ Hs) as ([bp Hp] & _ & _). rewrite (RG _ _ Hp). apply (D5 b m p i Hb Hml Hs).
    + intros k m i Hk Hs. destruct (is_valid _ _ _ IS _ _ _ Hs) as ([b Hb] & _ & _). rewrite (RG _ _ Hb). apply (D6 k m i Hk Hs).
Qed.
End UNZOMBIE.
