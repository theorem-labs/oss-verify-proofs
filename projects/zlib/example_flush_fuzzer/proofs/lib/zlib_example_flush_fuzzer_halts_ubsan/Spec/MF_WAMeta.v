(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec Require Import STree Malloc MallocCtrl KInv
  MI_Tree MI_Inv MI_Kit MI_Arith MI_List MI_Geom MI_Ext MI_Ext2 MI_Shadow MI_Read MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4
  MI_WFree2 MI_Ledger MI_WAMeta MI_WAMeta2 MI_WTry2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Definition GEQ (st0 st1 : mstate) : Prop := forall x, same_geo (MR st1 x) (MR st0 x).
Lemma GEQ_refl st : GEQ st st. Proof. intros x. apply same_geo_refl. Qed.
Lemma GEQ_trans a b c : GEQ a b -> GEQ b c -> GEQ a c. Proof. intros H1 H2 x. exact (same_geo_trans _ _ _ (H2 x) (H1 x)). Qed.
Lemma GEQ_metas st0 st1 : s_metas st1 = s_metas st0 -> GEQ st0 st1.
Proof. intros E x. unfold MR, get_meta_rec. rewrite E. apply same_geo_refl. Qed.
Lemma GEQ_upd_meta st m f : (forall r, same_geo (f r) r) -> GEQ st (upd_meta m f st).
Proof.
  intros Hf x. unfold MR. destruct (aptr_eq_dec x m) as [->|NE]; [rewrite get_meta_rec_upd_same; apply Hf| rewrite get_meta_rec_upd_other by exact NE; apply same_geo_refl].
Qed.
Lemma GEQ_dequeue st h m : GEQ st (dequeue h m st).
Proof. intros x. apply same_geo_data. apply dequeue_data. Qed.
Lemma same_geo_links p n r : same_geo (m_set_prev p (m_set_next n r)) r.
Proof. destruct r; repeat split; reflexivity. Qed.

Local Ltac geqm := apply GEQ_metas; cbn; repeat (first [reflexivity | match goal with |- context [match ?x with _ => _ end] => destruct x end]).


Section AM.
Variables (T : Type) (BL : list blk) (Post : mled -> T -> Prop) (k : mstate -> optr -> M T) (bail : M T).
Variables (X : extras) (st0 : mstate) (L0 : mled).
Hypothesis KN : forall st1 L1 LS1, INVL X st1 L1 BL LS1 -> AM_frame st0 st1 -> GEQ st0 st1 -> L_frame L0 L1 -> ftree L1 (k st1 None) Post.
Hypothesis KS : forall st1 L1 LS1 m, INVL (xidle X (m :: x_idle X)) st1 L1 BL LS1 -> ~ In m (x_idle X) -> AM_frame st0 st1 -> GEQ st0 st1 -> L_frame L0 L1 ->
  ftree L1 (k st1 (Some m)) Post.

Lemma am_take_ftG st L LS : INVL X st L BL LS -> AM_frame st0 st -> GEQ st0 st -> L_frame L0 L ->
  0 < c_avail_meta_count (s_ctx st) -> ftree L (am_take st k bail) Post.
Proof.
  intros INV AF GE LF HC. destruct (am_take_ok X st L BL LS INV HC (fun s mo => ret (s, mo)) (ret (st, @None aptr))) as (m & st2 & E2 & INV2 & AF2 & NI).
  unfold am_take in E2 |- *. destruct (c_avail_meta (ctx st)) as [m0|]; [| discriminate E2].
  assert (Em : m0 = m) by (injection E2; auto). subst m0.
  assert (Es : upd_meta m (fun r => m_set_prev None (m_set_next None r))
                 (upd_ctx (fun c => set_avail_meta (Some (aadd m META_SIZE)) (set_avail_meta_count (c_avail_meta_count c - 1) c)) st) = st2) by (injection E2; auto).
  rewrite Es. eapply KS; [exact INV2| exact NI| exact (amf_trans _ _ _ AF AF2)| | exact LF].
  eapply GEQ_trans; [exact GE|]. rewrite <- Es. eapply GEQ_trans; [| apply GEQ_upd_meta; intros r; apply same_geo_links]. apply GEQ_metas; reflexivity.
Qed.

Lemma am_carve_ftG s p L LS : INVL X s L BL LS ->
  c_avail_meta_areas (s_ctx s) = Some (aadd p 4096) -> s_areas s !! p = None -> (forall k, 0 <= k < NSLOTS -> s_metas s !! mslot p k = None) ->
  PGSZ <= snd p -> snd p mod PGSZ = 0 -> c_init_done (s_ctx s) = 1 ->
  AM_frame st0 s -> GEQ st0 s -> L_frame L0 L -> ftree L (am_take (carve_rest s p) k bail) Post.
Proof.
  intros INV H1 H2 H3 H4 H5 H6 AF GE LF. destruct (INVL_carve X s L BL LS p INV H1 H2 H3 H4 H5 H6) as (INV' & AF' & HC).
  eapply am_take_ftG; [exact INV'| exact (amf_trans _ _ _ AF AF')| | exact LF| exact HC].
  eapply GEQ_trans; [exact GE|]. unfold carve_rest. geqm.
Qed.

Lemma am_finish_ftG st L LS : INVL X st L BL LS -> AM_frame st0 st -> GEQ st0 st -> L_frame L0 L ->
  0 < c_avail_meta_area_count (s_ctx st) -> c_init_done (s_ctx st) = 1 ->
  ftree L (am_finish st true k bail) Post.
Proof.
  intros INV AF GE LF HC HI.
  destruct (ir_cursor _ _ _ (proj1 INV)) as (C1 & C2 & C3).
  destruct (c_avail_meta_areas (ctx st)) as [[rid off]|] eqn:EC; [| exfalso; exact (C2 HC EC)].
  destruct (C3 _ _ EC) as (r & Hr & K & P1 & P2 & P3 & P4).
  unfold am_finish. rewrite EC. cbn [snd]. rewrite (proj2 (Z.eqb_eq _ _) P2). cbn [negb].
  apply ftree_vis; [reflexivity| reflexivity| exact (ma_event_pre X st L BL LS rid off INV EC HC)| |].
  - intros a Ha. cbn in Ha. rewrite Ha. cbn [negb].
    change (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None)
      with (if (a =? 0) || (a =? TWO64 - ENOSYS) then am_carve st (rid, off) k bail else k st None).
    cbn [event_post]. destruct ((a =? 0) || (a =? TWO64 - ENOSYS)).
    + rewrite am_carve_eq.
      destruct (INVL_meta_adv X st L BL LS rid off INV EC HC) as (INV' & F1 & F2 & F3 & F4 & F5 & F6 & AF').
      eapply am_carve_ftG; [exact INV'| exact F1| exact F2| exact F3| exact F4| exact F5| rewrite F6; exact HI| exact (amf_trans _ _ _ AF AF')| |].
      * eapply GEQ_trans; [exact GE|]. unfold adv. geqm.
      * destruct LF; constructor; assumption.
    + eapply KN; [exact INV| exact AF| exact GE| exact LF].
  - intros a Ha. cbn in Ha. rewrite Ha. exact I.
Qed.

Lemma am_after_brk_ftG st L LS : INVL X st L BL LS -> AM_frame st0 st -> GEQ st0 st -> L_frame L0 L ->
  c_init_done (s_ctx st) = 1 -> ftree L (am_after_brk st true k bail) Post.
Proof.
  intros INV AF GE LF HI. unfold am_after_brk.
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx st)) 0) as [HC|HC].
  - apply ftree_vis; [reflexivity| reflexivity| exact (nm_event_pre X st L BL LS INV)| |].
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. cbn [negb].
      unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true. change (PROT_NONE =? PROT_NONE) with true. cbn [andb].
      destruct (is_err a) eqn:NE.
      * eapply KN; [exact INV| exact AF| exact GE| exact LF].
      * destruct (INVL_new_meta X st L BL LS a INV HC Ha NE) as (INV' & HC' & HI' & AF').
        eapply am_finish_ftG; [exact INV'| exact (amf_trans _ _ _ AF AF')| | destruct LF; constructor; assumption| exact HC'| rewrite HI'; exact HI].
        eapply GEQ_trans; [exact GE|]. geqm.
    + intros a Ha. unfold answer_ok in Ha. change (Z.land (MAP_PRIVATE + MAP_ANON) MAP_FIXED =? 0) with true in Ha. cbn [andb] in Ha.
      rewrite (mmap_answer_ok_eq X st L (proj1 INV)) in Ha. unfold ctx. rewrite Ha. exact I.
  - eapply am_finish_ftG; [exact INV| exact AF| exact GE| exact LF| pose proof (proj1 (ir_cursor _ _ _ (proj1 INV))); unfold ctx in HC; lia| exact HI].
Qed.

Theorem alloc_meta_ftG st L LS : INVL X st L BL LS -> AM_frame st0 st -> GEQ st0 st -> L_frame L0 L -> ftree L (alloc_meta st k bail) Post.
Proof.
  intros INV0 AF0 GE0 LF.
  destruct (INVL_am_init X st L BL LS INV0) as (INV & HI & AFi).
  pose proof (amf_trans _ _ _ AF0 AFi) as AF.
  assert (GE : GEQ st0 (am_init st)) by (eapply GEQ_trans; [exact GE0| unfold am_init; destruct (_ =? 0); geqm]).
  clear AF0 AFi INV0 GE0.
  unfold alloc_meta. fold (am_init st). set (s := am_init st) in *. clearbody s.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (c_free_meta_head (ctx s)) as [m|] eqn:EFH.
  { pose proof (il_head _ _ IL LFree) as HH. cbn in HH. unfold ctx in EFH. rewrite EFH in HH.
    destruct (LS LFree) as [|m' rest] eqn:ELS; [discriminate|]. cbn in HH. inversion HH. subst m'.
    pose proof (INVL_dequeue X (xidle X (m :: x_idle X)) s L BL LS m LFree [] rest INV ltac:(rewrite ELS; reflexivity) ltac:(right; split; reflexivity)) as INV1.
    destruct (dequeue_frame LFree m s) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & FC).
    eapply KS; [exact INV1| | | | exact LF].
    { intros Hin. apply (proj2 (im_idle _ _ _ IM m Hin)). exists LFree. rewrite ELS. left. reflexivity. }
    2:{ eapply GEQ_trans; [exact GE| apply GEQ_dequeue]. }
    eapply amf_trans; [exact AF|]. destruct FC. constructor; auto; try congruence.
    all: try (intros sc; change (active (dequeue LFree m s) sc) with (get_head (dequeue LFree m s) (LActive sc)); rewrite dequeue_head;
              destruct (decide (LActive sc = LFree)); [discriminate| reflexivity]).
    all: try (intros sc; unfold usage, ctx; rewrite cb_usage; reflexivity).
    all: try (intros rid r H _; rewrite F1; exact H).
    all: rewrite ?F3; lia. }
  destruct (Z.eqb_spec (c_avail_meta_count (ctx s)) 0) as [HAC|HAC]; cbn [negb].
  2:{ eapply am_take_ftG; [exact INV| exact AF| exact GE| exact LF| pose proof (proj1 (ia_avail _ IA)); unfold ctx in HAC; lia]. }
  destruct (Z.eqb_spec (c_avail_meta_area_count (ctx s)) 0) as [HC|HC]; cbn [andb].
  2:{ eapply am_after_brk_ftG; [exact INV| exact AF| exact GE| exact LF| exact HI]. }
  pose proof (ir_brk _ _ _ IR) as IBK. unfold ctx. destruct (c_brk (s_ctx s)) as [| |rid off] eqn:EBRK; cbn [negb].
  -
    destruct IBK as [BP NB].
    apply ftree_vis; [reflexivity| reflexivity| left; auto| |].
    2:{ intros cur Hc. cbn in Hc. rewrite Hc. exact I. }
    intros cur Hc. cbn in Hc. rewrite Hc. cbn [negb]. cbn [event_post Z.eqb].
    set (L1 := KInv.set_brkph (BPQueried cur) L).
    set (base := round_up_pg cur). set (new := base + 2 * PGSZ).
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, base. pose proof (round_up_ge cur). unfold brk0_answer_ok in Hc.
      apply Bool.andb_true_iff in Hc as [Hc _]. apply Bool.andb_true_iff in Hc as [Hc _]. apply Z.ltb_lt in Hc. unfold PGSZ. lia. }
    apply ftree_vis; [reflexivity| reflexivity| right; left; exists cur; split; reflexivity| |].
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_true_iff in Hr as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ. unfold L1. cbn [KInv.ld_brk KInv.set_brkph].
      destruct (Z.eqb_spec r new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp.
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. cbn [negb].
        apply ftree_vis; [reflexivity| reflexivity| right; exists cur; cbn; repeat split; reflexivity| |].
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. cbn [negb]. unfold event_post. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false. cbn [andb].
           set (st1 := new_region RKBrk base (2 * PGSZ) s). destruct st1 as [s1 rid] eqn:ES1.
           assert (Erid : rid = s_next_rid s) by (unfold st1, new_region in ES1; inversion ES1; reflexivity).
           assert (Es1 : s1 = fst (new_region RKBrk base (2 * PGSZ) s)) by (unfold st1 in ES1; rewrite <- ES1 || idtac; unfold new_region in *; inversion ES1; reflexivity).
           subst rid s1.
           unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
           unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
           change (PGSZ mod PGSZ =? 0) with true. cbn [negb].
           rewrite am_carve_eq.
           destruct (INVL_brk_first X s L BL LS cur INV EBRK HC ltac:(exact Hp) (KInv.set_brkph (BPGuard cur) (KInv.set_brkph (BPQueried cur) L)) ltac:(repeat split; reflexivity))
             as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
           eapply am_carve_ftG; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')| |].
           ++ eapply GEQ_trans; [exact GE|]. unfold adv. geqm.
           ++ destruct LF; constructor; assumption.
        -- intros rg Hg. unfold answer_ok in Hg. change (Z.land (MAP_PRIVATE + MAP_ANON + MAP_FIXED) MAP_FIXED =? 0) with false in Hg. cbn [andb] in Hg.
           fold base in Hg. rewrite Hg. exact I.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead (KInv.set_brkph (BPQueried cur) L)) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ftG; [exact INV'| exact (amf_trans _ _ _ AF AF')| | destruct LF; constructor; assumption| cbn; exact HI].
        eapply GEQ_trans; [exact GE|]. geqm.
    + intros r Hr. unfold answer_ok in Hr. rewrite NZ in Hr. unfold L1 in Hr. cbn [KInv.ld_brk KInv.set_brkph] in Hr.
      apply Bool.andb_false_iff in Hr. destruct Hr as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok cur new r); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (lbrk_pages_ok_ext (KInv.set_brkph (BPQueried cur) L) L) in Hp by reflexivity.
        rewrite (brk_pages_ok_eq X s L IR) in Hp. fold base in Hp. rewrite Hp. exact I.
  - eapply am_after_brk_ftG; [exact INV| exact AF| exact GE| exact LF| exact HI].
  -
    destruct IBK as [BP (r & Hr & K & Elen)].
    pose proof (bg_event_pre X s L BL LS rid off INV EBRK) as PRE.
    set (old := conc s (rid, off)) in *. set (new := old + PGSZ) in *.
    assert (NZ : (new =? 0) = false).
    { apply Z.eqb_neq. unfold new, old, conc, get_region. rewrite Hr. cbn [fst snd]. pose proof (ir_shape _ _ _ IR _ _ Hr) as (S1 & _ & S3 & _). unfold PGSZ. lia. }
    assert (BR : ld_brkreg L = Some (r_base r, off)).
    { apply (proj2 (ir_brkreg _ _ _ IR (r_base r) off)). exists rid, r. auto. }
    assert (Eold : old = r_base r + off) by (unfold old, conc, get_region; rewrite Hr; cbn [fst snd]; reflexivity).
    apply ftree_vis; [reflexivity| reflexivity| exact PRE| |].
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_true_iff in Hz as [Hb Hp]. rewrite Hb. cbn [negb].
      unfold event_post. rewrite NZ, BP, BR.
      destruct (Z.eqb_spec z new) as [->|NE]; cbn [negb].
      * cbn [negb orb] in Hp. rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. cbn [negb].
        unfold am_after_brk, ctx. cbn [c_avail_meta_area_count s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk Z.eqb].
        unfold am_finish, ctx. cbn [c_avail_meta_areas s_ctx upd_ctx set_avail_meta_area_count set_avail_meta_areas set_brk snd].
        destruct (bg_region X s L BL LS rid off INV EBRK) as (r' & _ & _ & _ & _ & _ & _ & _ & OM & _).
        rewrite (proj2 (Z.eqb_eq _ _) OM). cbn [negb].
        rewrite am_carve_eq.
        destruct (INVL_brk_grow X s L BL LS rid off INV EBRK HC ltac:(exact Hp)) as (INV' & G1 & G2 & G3 & G4 & G5 & G6 & AF').
        replace (conc s (rid, off) - off) with (r_base r) in INV' by (unfold conc, get_region; rewrite Hr; cbn [fst snd]; lia).
        eapply am_carve_ftG; [exact INV'| exact G1| exact G2| exact G3| exact G4| exact G5| rewrite G6; exact HI| exact (amf_trans _ _ _ AF AF')| |].
        -- eapply GEQ_trans; [exact GE|]. unfold adv, upd_region. geqm.
        -- destruct LF; constructor; assumption.
      * destruct (INVL_brk_dead X s L (KInv.set_brkph BPDead L) BL LS INV eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl) as [INV' AF'].
        eapply am_after_brk_ftG; [exact INV'| exact (amf_trans _ _ _ AF AF')| | destruct LF; constructor; assumption| cbn; exact HI].
        eapply GEQ_trans; [exact GE|]. geqm.
    + intros z Hz. unfold answer_ok in Hz. rewrite NZ, BP, BR in Hz. rewrite <- Eold in Hz.
      apply Bool.andb_false_iff in Hz. destruct Hz as [Hb|Hp].
      * rewrite Hb. exact I.
      * destruct (brk_answer_ok old new z); [| exact I]. cbn [negb].
        apply Bool.orb_false_iff in Hp as [Hn Hp]. apply Bool.negb_false_iff in Hn. rewrite Hn. cbn [negb].
        rewrite (brk_pages_ok_eq X s L IR) in Hp. rewrite Hp. exact I.
Qed.
End AM.
