(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2 MI_WTry MI_WTry2 MI_WGroup.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_Bits.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_TF2 MI_WAMeta MI_WAMeta2 MI_WCreate MI_WCreate2 MI_WSlot MI_WSlot2 MI_Ledger MShapeA.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.KInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Tree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Inv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Kit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Arith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Geom OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_List OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Ext OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Shadow OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Pres1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Pres2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Pres3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Pres4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WFree2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WTry OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WTry2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WGroup OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Bits.MI_Cnt OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_TF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WAMeta OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WAMeta2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WCreate OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WCreate2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WSlot OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WSlot2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Ledger OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MShapeA.
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

Definition nonest (sc : Z) : bool :=
  forallb (fun c0 => PGSZ / 2 <? UNIT * size_class sc * bump (UNIT * size_class sc) c0 + UNIT) (cnt0_list sc).

Definition cost (sc : Z) : Z :=
  if nonest sc then 1 else if sc =? 19 then 2 else if sc =? 15 then 3 else 4.

Definition nchain_f (sc : Z) : bool :=
  let size := UNIT * size_class sc in
  forallb (fun c0 =>
    let c1 := bump size c0 in
    (PGSZ / 2 <? size * c1 + UNIT)
    || (let j := size_to_class (UNIT + c1 * size - IB) in
        ((j =? 15) || (j =? 19) || (j =? 23)) && (cost j <=? cost sc - 1)))
  (cnt0_list sc).

Lemma nchain_true : forallb nchain_f (zrange 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cost_range sc : 1 <= cost sc <= 4.
Proof. unfold cost. destruct (nonest sc); [lia|]. destruct (sc =? 19); [lia|]. destruct (sc =? 15); lia. Qed.

Lemma ag_cnt1_bump sc u : ag_cnt1 sc u = bump (UNIT * size_class sc) (cnt0_of sc u).
Proof. reflexivity. Qed.

Lemma nest_chain sc u : 0 <= sc < 48 ->
  UNIT * size_class sc * ag_cnt1 sc u + UNIT <= PGSZ / 2 ->
  let j := size_to_class (UNIT + ag_cnt1 sc u * (UNIT * size_class sc) - IB) in
  (j = 15 \/ j = 19 \/ j = 23) /\ cost j <= cost sc - 1.
Proof.
  intros Hsc HB. cbn zeta.
  pose proof (forallb_zrange nchain_f 0 48 sc nchain_true ltac:(lia) ltac:(lia)) as H. unfold nchain_f in H.
  rewrite forallb_forall in H. specialize (H _ (cnt0_in sc u)). cbn beta in H. rewrite <- ag_cnt1_bump in H.
  apply orb_true_iff in H. destruct H as [H|H]; [apply Z.ltb_lt in H; lia|].
  apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H2.
  split; [| exact H2].
  apply orb_true_iff in H1. destruct H1 as [H1|H1]; [apply orb_true_iff in H1; destruct H1 as [H1|H1]|]; apply Z.eqb_eq in H1; lia.
Qed.

(* [comment removed for export] *)
Lemma nonest_mmap sc u : nonest sc = true -> PGSZ / 2 < UNIT * size_class sc * ag_cnt1 sc u + UNIT.
Proof.
  intros H. unfold nonest in H. rewrite forallb_forall in H. specialize (H _ (cnt0_in sc u)). rewrite <- ag_cnt1_bump in H.
  apply Z.ltb_lt in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition midclass (c : Z) : Prop := c = 15 \/ c = 19 \/ c = 23.

Record AFR (C : Z -> Prop) (d : Z) (e : optr) (st st' : mstate) : Prop := mkAFR {
  afr_cnt : c_avail_meta_count (s_ctx st') >= c_avail_meta_count (s_ctx st) - d;
  afr_usage : forall sc, ~ C sc -> usage st' sc = usage st sc;
  afr_host : forall b x, hosts st b x -> hosts st' b x /\ geo_of (MR st' x) = geo_of (MR st x);
  afr_new : forall b x, hosts st' b x -> hosts st b x \/
      (C (m_sizeclass (MR st' x)) /\ (midclass (m_sizeclass (MR st' x)) \/ Some x = e) /\
       ((s_regions st !! (fst b) = None /\ snd b = 0)
        \/ (nonest (m_sizeclass (MR st' x)) = false /\
            exists p bp i, hosts st' bp p /\ midclass (m_sizeclass (MR st' p)) /\ 0 <= i <= m_last_idx (MR st' p) /\ b = (fst bp, sstart (MR st' p) i))));
  afr_regions : forall rid r, s_regions st !! rid = Some r -> s_regions st' !! rid = Some r
}.

Lemma geo_sc r r' : geo_of r' = geo_of r -> m_sizeclass r' = m_sizeclass r.
Proof. unfold geo_of. congruence. Qed.
Lemma geo_li r r' : geo_of r' = geo_of r -> m_last_idx r' = m_last_idx r.
Proof. unfold geo_of. congruence. Qed.
Lemma geo_ss r r' i : geo_of r' = geo_of r -> sstart r' i = sstart r i.
Proof. intros H. exact (proj1 (geo_facts _ _ H) i). Qed.

Lemma hosts_gm st b x : hosts st b x <-> gm st b = Some x.
Proof.
  unfold hosts, gm. split.
  - intros [ai ->]. reflexivity.
  - destruct (s_groups st !! b) as [[mm ai]|]; [| discriminate]. cbn. intros ->. exists ai. reflexivity.
Qed.

Lemma AFR_of_PF C d e st st' : 0 <= d -> PF st st' -> AFR C d e st st'.
Proof.
  intros Hd [A B G D E F]. constructor.
  - lia.
  - intros; apply F.
  - intros b x H. split; [| apply B]. apply hosts_gm. rewrite G. apply hosts_gm. exact H.
  - intros b x H. left. apply hosts_gm. rewrite <- G. apply hosts_gm. exact H.
  - intros rid r H. rewrite D. exact H.
Qed.

(* [comment removed for export] *)

Lemma AFR_trans C d1 d2 e1 e2 a b c : AFR C d1 e1 a b -> AFR C d2 e2 b c ->
  (forall x bx, e1 = Some x -> hosts b bx x -> midclass (m_sizeclass (MR b x)) \/ e2 = Some x) -> AFR C (d1 + d2) e2 a c.
Proof.
  intros [A1 A2 A3 A4 A5] [B1 B2 B3 B4 B5] HE1. constructor.
  - lia.
  - intros sc Hs. rewrite (B2 sc Hs). apply A2. exact Hs.
  - intros bb x H. destruct (A3 bb x H) as [H1 G1]. destruct (B3 bb x H1) as [H2 G2]. split; [exact H2| congruence].
  - intros bb x H. destruct (B4 bb x H) as [H1|(HC & HE & HW)].
    + destruct (A4 bb x H1) as [H0|(HC & HE & HW)]; [left; exact H0| right].
      destruct (B3 bb x H1) as [_ G2].
      assert (EC : m_sizeclass (MR c x) = m_sizeclass (MR b x)) by (unfold geo_of in G2; congruence).
      rewrite EC. split; [exact HC|]. split.
      * destruct HE as [HM|HE]; [left; exact HM|]. destruct (HE1 x bb (eq_sym HE) H1) as [HM|HM]; [left; exact HM| right; symmetry; exact HM].
      * destruct HW as [HW|(NN & p & bp & i & Hp & Cp & Hi & ->)]; [left; exact HW| right]. split; [exact NN|].
        destruct (B3 bp p Hp) as [Hp' Gp]. pose proof (geo_facts _ _ Gp) as (SS & _).
        assert (ECp : m_sizeclass (MR c p) = m_sizeclass (MR b p)) by (unfold geo_of in Gp; congruence).
        assert (ELp : m_last_idx (MR c p) = m_last_idx (MR b p)) by (unfold geo_of in Gp; congruence).
        exists p, bp, i. rewrite ECp, ELp, SS. auto.
    + right. split; [exact HC|]. split; [exact HE|]. destruct HW as [[HW H0]|HW]; [left| right; exact HW].
      split; [| exact H0]. destruct (s_regions a !! bb.1) as [r|] eqn:E; [| reflexivity]. rewrite (A5 _ _ E) in HW. discriminate.
  - intros rid r H. apply B5. apply A5. exact H.
Qed.

Lemma AFR_mono C d d' e st st' : AFR C d e st st' -> d <= d' -> AFR C d' e st st'.
Proof. intros [A1 A2 A3 A4 A5] Hd. constructor; [lia| exact A2| exact A3| exact A4| exact A5]. Qed.

Lemma AFR_monoC (C C' : Z -> Prop) d e st st' : AFR C d e st st' -> (forall c, C c -> C' c) -> AFR C' d e st st'.
Proof.
  intros [A1 A2 A3 A4 A5] HC. constructor.
  - exact A1.
  - intros sc Hs. apply A2. intros H. apply Hs. apply HC. exact H.
  - exact A3.
  - intros b x H. destruct (A4 b x H) as [H1|(H2 & H3 & H4)]; [left; exact H1| right]. split; [apply HC; exact H2|]. split; [exact H3| exact H4].
  - exact A5.
Qed.

(* [comment removed for export] *)
Definition chain (sc : Z) (c : Z) : Prop := c = sc \/ c = 15 \/ c = 19 \/ c = 23.

Lemma chain_sub sc j c : (j = 15 \/ j = 19 \/ j = 23) -> chain j c -> chain sc c.
Proof. unfold chain. intros Hj Hc. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nest_nonest_false sc u : UNIT * size_class sc * ag_cnt1 sc u + UNIT <= PGSZ / 2 -> nonest sc = false.
Proof. intros H. destruct (nonest sc) eqn:E; [| reflexivity]. exfalso. pose proof (nonest_mmap sc u E). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma idle_nohost X st L BL LS m b : INVL X st L BL LS -> In m (x_idle X) -> ~ hosts st b m.
Proof.
  intros INV Hin Hh. cps_pose INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (hosts_mem X st LS IM b m Hh) as M1.
  pose proof (proj1 (im_idle _ _ _ IM m Hin)) as M0.
  unfold MR, get_meta_rec in M1. rewrite M0 in M1. cbn in M1. discriminate.
Qed.

(* [comment removed for export] *)
Lemma hosts_region X st L BL LS b x : INVL X st L BL LS -> hosts st b x -> s_regions st !! (fst b) <> None.
Proof.
  intros INV [ai Hb]. cps_destruct (ig_region _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ Hb) as (r & Hr & _). congruence.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma agt_gm st sc m p cnt ai b :
  gm (agt st sc m p cnt ai) b = if aptr_eqb b p then Some m else gm st b.
Proof.
  unfold gm. rewrite agt_groups. destruct (aptr_eqb_spec b p) as [->|NE].
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma agt_cnt st sc m p cnt ai : c_avail_meta_count (s_ctx (agt st sc m p cnt ai)) = c_avail_meta_count (s_ctx st).
Proof. rewrite agt_ctx. reflexivity. Qed.

(* [comment removed for export] *)
Lemma PF_queue_st s h g : PF s (queue_st h g s).
Proof.
  unfold queue_st, q_link, q_single. destruct (get_head s h) as [hd|].
  - destruct (m_prev (get_meta_rec s hd)).
    + eapply PF_trans; [apply PF_upd_meta; intros r; rewrite geo_set_prev, geo_set_next; reflexivity|].
      eapply PF_trans; [apply PF_upd_meta; intros; apply geo_set_next| apply PF_upd_meta; intros; apply geo_set_prev].
    + eapply PF_trans; [apply PF_upd_meta; intros r; rewrite geo_set_prev, geo_set_next; reflexivity|].
      apply PF_upd_meta; intros; apply geo_set_prev.
  - eapply PF_trans; [apply PF_upd_meta; intros r; rewrite geo_set_prev, geo_set_next; reflexivity| apply PF_set_head].
Qed.

Lemma PF_step_seq_account_bounce st sc : PF st (step_seq (account_bounce sc st)).
Proof.
  apply (PF_trans _ (account_bounce sc st)).
  - unfold account_bounce. destruct (sc_in_seq_range sc); [| apply PF_refl].
    destruct (negb (unmap_seq st (sc - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10)); [| apply PF_refl].
    destruct (bounces st (sc - 7) + 1 <? 100); apply PF_set_bounce.
  - unfold step_seq. destruct (_ =? 255); apply PF_upd_ctx; reflexivity.
Qed.

Lemma geo_set_maplen_other st m ml x : x <> m -> MR (upd_meta m (m_set_maplen ml) st) x = MR st x.
Proof. intros NE. unfold MR. apply get_meta_rec_upd_other. exact NE. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SLOT.
Variable T : Type.

Definition MAPF0 : Z := MAP_PRIVATE + MAP_ANON.

(* [comment removed for export] *)
Definition NEWCNT (sc req u0 li : Z) : Prop :=
  (exists u1 ns, li = fst (ag_cn3 sc req (ag_cnt2 sc (ag_cnt1 sc u0) u1 ns) u1 ns) - 1 /\ PGSZ / 2 < UNIT * size_class sc * ag_cnt1 sc u0 + UNIT)
  \/ (li = ag_cnt1 sc u0 - 1 /\ UNIT * size_class sc * ag_cnt1 sc u0 + UNIT <= PGSZ / 2).

(* [comment removed for export] *)
Definition GNX (P : mstate -> aptr -> Z -> Prop) (sc : Z) (st1 : mstate) : Prop :=
  forall g, active st1 sc = Some g -> P st1 g (m_last_idx (MR st1 g)).

(* [comment removed for export] *)
Definition OPURE (sc : Z) (st : mstate) (st1 : mstate) (g : aptr) (li : Z) : Prop :=
  ((exists b, hosts st b g) /\ c_avail_meta_count (s_ctx st1) = c_avail_meta_count (s_ctx st))
  \/ (li = ag_cnt1 sc (usage st sc) - 1 /\ UNIT * size_class sc * ag_cnt1 sc (usage st sc) + UNIT <= PGSZ / 2).
(* [comment removed for export] *)
Definition OMMAP (sc req : Z) (st : mstate) (st1 : mstate) (g : aptr) (li : Z) : Prop := NEWCNT sc req (usage st sc) li.

Definition QPURE (sc : Z) (idle : list aptr) (st : mstate) (L : mled) (BL : list blk) (req : Z)
  (k : mstate -> Z -> M T) (t : M T) : Prop :=
  exists st1 idx LS1, t = k st1 idx /\ 0 <= idx /\ SLOT_POST idle sc req st L BL st1 idx L LS1 /\ AFR (chain sc) (cost sc) (active st1 sc) st st1 /\ GNX (OPURE sc st) sc st1.

Definition QFAIL (sc : Z) (idle : list aptr) (st : mstate) (L : mled) (BL : list blk) (req : Z)
  (k : mstate -> Z -> M T) (t : M T) : Prop :=
  exists st1 LS1, t = k st1 (-1) /\ SLOT_POST idle sc req st L BL st1 (-1) L LS1 /\ AFR (chain sc) (cost sc) None st st1.

Definition QSUCC (sc : Z) (idle : list aptr) (st : mstate) (L : mled) (BL : list blk) (req : Z)
  (k : mstate -> Z -> M T) (len r : Z) (t : M T) : Prop :=
  exists st1 idx LS1, t = k st1 idx /\ 0 <= idx
    /\ SLOT_POST idle sc req st L BL st1 idx (KInv.set_groups ((r, len) :: ld_groups L) L) LS1 /\ AFR (chain sc) (cost sc) (active st1 sc) st st1 /\ GNX (OMMAP sc req st) sc st1.

Definition MM (B : Z) (L : mled) (len : Z) (K : Z -> M T) (QF : M T -> Prop) (QS : Z -> M T -> Prop) : Prop :=
  0 < len <= B /\ event_pre L (EMmap 0 len PROT_RW MAPF0)
  /\ forall r, answer_ok L (EMmap 0 len PROT_RW MAPF0) r = true ->
       (is_err r = true -> QF (K r)) /\ (is_err r = false -> QS r (K r)).

Lemma answer_ok_mmap L len r : answer_ok L (EMmap 0 len PROT_RW MAPF0) r = mmap_answer_ok (lranges L) len r.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma finish_facts (P : aptr -> Z -> Prop) idle st st2 L L2 BL LS2 sc req m b ai last ml (k : mstate -> Z -> M T) bail :
  INVL (mkX idle [] None None (Some m)) st2 L2 BL LS2 ->
  s_groups st2 !! b = Some (mkGhdr (Some m) ai) ->
  MR st2 m = mkMeta None None (Some b) (mask_upto ai) (mask_upto last - mask_upto ai) last 1 sc ml ->
  0 <= ai <= last -> last <= 31 -> 0 <= sc < 48 -> active st2 sc = None ->
  (get_stride (MR st2 m) < UNIT * size_class sc -> ai = 0 /\ last = 0) -> TF2 st2 ->
  req + IB <= get_stride (MR st2 m) -> (sc < 28 -> get_stride (MR st2 m) = UNIT * size_class sc) ->
  (forall sc', sc' < sc -> active st2 sc' = active st sc') -> ld_live L2 = ld_live L -> GP st st2 ->
  AFR (chain sc) (cost sc) (Some m) st st2 -> P m last ->
  exists st4 LS4,
    queue (LActive sc) m (upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st2) (fun st4 => k st4 0) bail = k st4 0
    /\ SLOT_POST idle sc req st L BL st4 0 L2 LS4 /\ AFR (chain sc) (cost sc) (active st4 sc) st st4 /\ GNX (fun _ => P) sc st4.
Proof.
  intros INV2 Hb Em Hai Hl Hsc HA UND TF2' FIT STR ACT2 LIVE2 GP2 AF2 HN.
  cps_destruct (slot_finish_ok T idle st2 L2 BL LS2 m b ai last sc ml (fun st4 => k st4 0) bail INV2 Hb Em Hai Hl Hsc HA UND TF2')
    as (LS4 & EQ & INV4 & TF4 & HA4 & ACT4 & G4 & TK4 & SH4 & L4 & SC4 & STR4 & SS4 & RG4 & SE4).
  set (st4 := queue_st (LActive sc) m (upd_meta m (fun r => m_set_avail (m_avail r - 1) r) st2)) in *.
  exists st4, LS4. split; [exact EQ|]. split.
  - split; [intros sc' Hs; rewrite ACT4 by lia; apply ACT2; exact Hs|]. split; [exact LIVE2|].
    split; [eapply GP_trans; [exact GP2| apply GP_eq; [exact RG4| exact SE4]]|].
    right. exists m, b, ai. rewrite L4, SC4, STR4, G4, SS4.
    split; [lia|]. split; [exact HA4|]. split; [exact Hb|]. split; [reflexivity|]. split; [exact FIT|]. split; [exact STR|].
    split; [exact INV4| exact TF4].
  - assert (P24 : PF st2 st4).
    { unfold st4. eapply PF_trans; [apply PF_upd_meta; intros; apply geo_set_avail| apply PF_queue_st]. }
    rewrite HA4. split; [replace (cost sc) with (cost sc + 0) by lia; apply (AFR_trans _ _ _ (Some m) (Some m) _ st2); [exact AF2| apply AFR_of_PF; [lia| exact P24]| intros x bx Ex _; right; exact Ex]|].
    intros g Hg. assert (Eg : g = m) by congruence. subst g. rewrite L4. exact HN.
Qed.

End SLOT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SLOT_SHAPE.
Variable T : Type.

(* [comment removed for export] *)
Lemma fail_facts idle sc req st st1 stF L BL LSF m (k : mstate -> Z -> M T) :
  INVL (X_as (m :: idle)) stF L BL LSF -> ~ In m idle -> TF0 stF ->
  (forall sc', sc' < sc -> active stF sc' = active st sc') -> GP st stF ->
  INVL (X_as idle) st1 L BL (fun h => match h with LActive _ => [] | LFree => [] end) \/ True ->
  AFR (chain sc) (cost sc) None st stF -> (forall b, ~ hosts st b m) ->
  QFAIL T sc idle st L BL req k (k (fm_st stF m) (-1)).
Proof.
  intros INVF NIm TFF ACT GPF _ AF NH.
  cps_destruct (free_idle_ok idle m stF L BL LSF INVF NIm) as (INV3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
  cps_destruct (fm_st_facts stF m) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  eexists (fm_st stF m), _. split; [reflexivity|]. split.
  - split; [intros sc' Hs; rewrite F7; apply ACT; exact Hs|]. split; [reflexivity|].
    split.
    { eapply GP_trans; [exact GPF| apply GP_eq; [exact F5|]].
      unfold fm_st. cps_destruct (queue_frame LFree m (put_meta m meta0 stF)) as (_ & _ & _ & _ & _ & _ & _ & Q8 & _). rewrite Q8. reflexivity. }
    left. split; [reflexivity|]. split; [exact INV3| exact (TF0_ctrl stF _ F1 F2 TFF)].
  - destruct AF as [A1 A2 A3 A4 A5]. constructor.
    + rewrite G2. exact A1.
    + intros sc' Hs. rewrite G6. apply A2. exact Hs.
    + intros b x Hh. destruct (A3 b x Hh) as [H1 H2].
      assert (NE : x <> m) by (intros ->; exact (NH b Hh)).
      split; [apply hosts_gm; rewrite G3; apply hosts_gm; exact H1|]. rewrite (G1 x NE). exact H2.
    + intros b x Hh. assert (Hh' : hosts stF b x) by (apply hosts_gm; rewrite <- G3; apply hosts_gm; exact Hh).
      destruct (A4 b x Hh') as [H1|(HC & HE & HW)]; [left; exact H1| right].
      assert (NEx : x <> m) by (intros ->; exact (idle_nohost _ _ _ _ _ m b INVF ltac:(left; reflexivity) Hh')).
      rewrite (geo_sc _ _ (G1 x NEx)). split; [exact HC|]. split; [exact HE|].
      destruct HW as [HW|(NN & p & bp & i & Hp & Cp & Hi & ->)]; [left; exact HW| right]. split; [exact NN|].
      assert (NEp : p <> m) by (intros ->; exact (idle_nohost _ _ _ _ _ m bp INVF ltac:(left; reflexivity) Hp)).
      exists p, bp, i. rewrite (geo_sc _ _ (G1 p NEp)), (geo_li _ _ (G1 p NEp)), (geo_ss _ _ i (G1 p NEp)).
      split; [apply hosts_gm; rewrite G3; apply hosts_gm; exact Hp|]. auto.
    + intros rid r Hr. rewrite G4. apply A5. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma AFR_create_top (C : Z -> Prop) d idle st stA L BL LS m a len sc cnt ai ml MC :
  AFR C d None st stA -> INVL (X_as (m :: idle)) stA L BL LS -> (forall b, ~ hosts st b m) -> C sc ->
  (forall c, c_usage (MC c) = c_usage c) -> (forall c, c_avail_meta_count (MC c) = c_avail_meta_count c) ->
  let rid := s_next_rid stA in
  let st3 := fst (new_region RKGroup a len stA) in
  let st5 := agt (upd_meta m (m_set_maplen ml) (upd_ctx MC st3)) sc m (rid, 0) cnt ai in
  m_sizeclass (MR st5 m) = sc ->
  AFR C d (Some m) st st5 /\ (forall b x, hosts stA b x -> hosts st5 b x /\ MR st5 x = MR stA x).
Proof.
  intros AF INVA NHm Csc MCu MCc rid st3 st5 SCm.
  pose proof (ng_fresh _ stA L BL LS INVA) as FR. fold rid in FR.
  assert (GM4 : forall b, gm (upd_meta m (m_set_maplen ml) (upd_ctx MC st3)) b = gm stA b) by (intros b; reflexivity).
  assert (GM5 : forall b, gm st5 b = if aptr_eqb b (rid, 0) then Some m else gm stA b).
  { intros b. unfold st5. rewrite agt_gm. rewrite GM4. reflexivity. }
  assert (MR5 : forall x, x <> m -> MR st5 x = MR stA x).
  { intros x NE. unfold st5. rewrite agt_MR_other by exact NE. rewrite geo_set_maplen_other by exact NE. reflexivity. }
  assert (RG5 : forall q rq, s_regions stA !! q = Some rq -> s_regions st5 !! q = Some rq).
  { intros q rq Hq. unfold st5. rewrite agt_regions. cbn. unfold st3. apply (ng_keep _ _ _ _ _ _ _ INVA). exact Hq. }
  assert (NB : forall b x, hosts stA b x -> aptr_eqb b (rid, 0) = false).
  { intros b x Hh. apply aptr_eqb_neq. intros ->. apply (hosts_region _ _ _ _ _ _ _ INVA Hh). exact FR. }
  assert (HOST : forall b x, hosts stA b x -> hosts st5 b x /\ MR st5 x = MR stA x).
  { intros b x Hh. split.
    - apply hosts_gm. rewrite GM5, (NB b x Hh). apply hosts_gm. exact Hh.
    - apply MR5. intros ->. exact (idle_nohost _ _ _ _ _ m b INVA ltac:(left; reflexivity) Hh). }
  split; [| exact HOST].
  destruct AF as [A1 A2 A3 A4 A5]. constructor.
  - unfold st5. rewrite agt_cnt. cbn. rewrite MCc. exact A1.
  - intros sc' Hs. unfold st5. rewrite agt_usage. destruct (Z.eqb_spec sc' sc) as [->|NE]; [exfalso; exact (Hs Csc)|].
    rewrite Z.add_0_r. unfold usage, ctx. cbn. rewrite MCu. fold (ctx stA). fold (usage stA sc'). apply A2. exact Hs.
  - intros b x Hh. destruct (A3 b x Hh) as [H1 H2]. destruct (HOST b x H1) as [H3 H4]. split; [exact H3|]. rewrite H4. exact H2.
  - intros b x Hh. apply hosts_gm in Hh. rewrite GM5 in Hh. destruct (aptr_eqb_spec b (rid, 0)) as [->|NE].
    + inversion Hh; subst x. right. rewrite SCm. split; [exact Csc|]. split; [right; reflexivity|]. left. cbn [fst snd]. split; [| reflexivity].
      destruct (s_regions st !! rid) as [r|] eqn:E; [| reflexivity]. rewrite (A5 _ _ E) in FR. discriminate.
    + apply hosts_gm in Hh. destruct (A4 b x Hh) as [H1|(HC & HE & HW)]; [left; exact H1| right].
      destruct (HOST b x Hh) as [_ H4]. rewrite H4. split; [exact HC|]. split; [destruct HE as [HE|HE]; [left; exact HE| discriminate]|].
      destruct HW as [HW|(NN & p & bp & i & Hp & Cp & Hi & ->)]; [left; exact HW| right]. split; [exact NN|].
      destruct (HOST bp p Hp) as [H5 H6]. exists p, bp, i. rewrite H6. auto.
  - intros q rq Hq. apply RG5. apply A5. exact Hq.
Qed.

Theorem alloc_slot_shape (f : nat) : forall sc idle st L BL LS req (k : mstate -> Z -> M T) bail,
  49 - sc <= Z.of_nat f ->
  INVL (X_as idle) st L BL LS -> TF0 st -> NoDup idle -> 0 <= sc < 48 -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  (ZC sc st -> cost sc <= c_avail_meta_count (s_ctx st)) ->
  QPURE T sc idle st L BL req k (alloc_slot full_lay f st sc req k bail)
  \/ exists len K, alloc_slot full_lay f st sc req k bail = SVis (EMmap 0 len PROT_RW MAPF0) K
       /\ MM T (2^20) L len K (QFAIL T sc idle st L BL req k) (QSUCC T sc idle st L BL req k len) /\ ZC sc st.
Proof.
  induction f as [|f IH]; intros sc idle st L BL LS req k bail Hf INV TF ND Hsc Hreq Hfit HCNT.
  { exfalso. cbn in Hf. lia. }
  pose proof (cost_range sc) as CR.
  change (alloc_slot full_lay (S f) st sc req k bail) with
    (try_avail sc st (fun st1 first =>
       if negb (first =? 0) then k st1 (ctz32 first)
       else alloc_group T full_lay (alloc_slot full_lay f) st1 sc req (fun st2 go =>
              match go with
              | None => k st2 (-1)
              | Some g => let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
                          queue (LActive sc) g st3 (fun st4 => k st4 0) bail
              end) bail) bail).
  cps_destruct (try_avail_okC (X_as idle) L BL sc st LS eq_refl eq_refl Hsc INV) as (st1 & first & LS1 & E & [TAF RES] & P1 & ZC1).
  rewrite E. clear E. cbn beta.
  assert (ACT1 : forall sc', sc' < sc -> active st1 sc' = active st sc').
  { intros sc' Hs. change (active st1 sc') with (get_head st1 (LActive sc')). rewrite (taf_heads _ _ _ TAF) by (intros EQ; inversion EQ; lia). reflexivity. }
  assert (TF1 : TF0 st1) by exact (TF0_ctrl st st1 (taf_shadow _ _ _ TAF) (taf_tick _ _ _ TAF) TF).
  destruct RES as [(-> & HA & INV1)|(g & bg & ai & idx & NZ & POS & Eidx & HA & Hg & Hidx & SC & STR & INV1)].
  2:{ (* [comment removed for export] *)
      replace (negb (first =? 0)) with true by (symmetry; apply negb_true_iff; apply Z.eqb_neq; exact NZ).
      cbn iota. left. rewrite Eidx. exists st1, idx, LS1. split; [reflexivity|]. split; [lia|]. split.
      - split; [exact ACT1|]. split; [reflexivity|]. split; [exact (GP_taf _ _ _ TAF)|]. right.
        pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV1))))) _ _ _ Hg) as GO.
        cps_pose (g_stride _ _ _ _ _ _ GO ltac:(rewrite SC; lia)) as (GS & _ & _). rewrite SC in GS.
        exists g, bg, ai. split; [exact Hidx|]. split; [exact HA|]. split; [exact Hg|]. split; [exact SC|].
        split; [lia|]. split; [intros Hs28; destruct GS; lia|]. split; [exact INV1|]. apply TF0_TF2. exact TF1.
      - split; [apply AFR_of_PF; [lia| exact P1]|].
        intros g' Hg'. rewrite HA in Hg'. injection Hg' as <-. left. split; [| exact (pf_cnt _ _ P1)]. exists bg. apply hosts_gm. rewrite <- (pf_gm _ _ P1). apply hosts_gm. exists ai. exact Hg. }
  (* [comment removed for export] *)
  assert (ZC0 : ZC sc st) by (destruct ZC1 as [[_ Z0]|NZ]; [exact Z0| exfalso; apply NZ; reflexivity]).
  change (negb (0 =? 0)) with false. cbn iota.
  unfold alloc_group.
  specialize (HCNT ZC0).
  assert (HC1 : 0 < c_avail_meta_count (s_ctx st1)) by (rewrite (pf_cnt _ _ P1); lia).
  cps_destruct (alloc_meta_okC (X_as idle) st1 L BL LS1 INV1 HC1) as (st2 & m & LS2 & E2 & P2 & INV2 & NIm & AF2).
  rewrite E2. clear E2. cbn beta iota zeta.
  change (xidle (X_as idle) (m :: x_idle (X_as idle))) with (X_as (m :: idle)) in INV2. cbn [x_idle X_as] in NIm.
  change (if sc <? 9 then small_cnt_pick sc (usage st2 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st2 sc)) (UNIT * size_class sc))
    with (cnt0_of sc (usage st2 sc)).
  change (if (cnt0_of sc (usage st2 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st2 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st2 sc))
    with (ag_cnt1 sc (usage st2 sc)).
  change (lh_nest full_lay) with nest_layout.
  assert (HA2 : forall sc', active st2 sc' = active st1 sc') by (intros; apply (amf_active _ _ AF2)).
  assert (TF2x : TF0 st2) by exact (TF0_ctrl st1 st2 (amf_shadow _ _ AF2) (amf_tick _ _ AF2) TF1).
  assert (NHm : forall b, ~ hosts st b m).
  { intros b Hh. apply (idle_nohost _ _ _ _ _ m b INV2 ltac:(left; reflexivity)).
    apply hosts_gm. rewrite (pf1_gm _ _ P2), (pf_gm _ _ P1). apply hosts_gm. exact Hh. }
  (* [comment removed for export] *)
  assert (AF02 : AFR (chain sc) 1 None st st2).
  { destruct P2 as [Q1 Q2 Q3 Q4 Q5 Q6]. destruct P1 as [R1 R2 R3 R4 R5 R6]. constructor.
    - rewrite <- R1. exact Q1.
    - intros sc' _. rewrite Q6. apply R6.
    - intros b x Hh. split; [apply hosts_gm; rewrite Q3, R3; apply hosts_gm; exact Hh| rewrite Q2; apply R2].
    - intros b x Hh. left. apply hosts_gm. rewrite <- R3, <- Q3. apply hosts_gm. exact Hh.
    - intros rid r Hr. rewrite Q4, R4. exact Hr. }
  pose proof (ag_arith sc req (usage st2 sc)) as AR.
  set (c1 := ag_cnt1 sc (usage st2 sc)) in *.
  destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1 + UNIT)) as [HB|HB].
  - (* [comment removed for export] *)
    set (ns := is_bouncing sc st2).
    set (st2' := step_seq (account_bounce sc st2)).
    set (u1 := if Z.even sc && (sc <? 32) then usage st2 sc + usage st2' (sc + 1) else usage st2 sc).
    change (if (u1 <? 4 * c1) && negb ns
            then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1) then 2
                 else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1) then 3
                 else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1) then 3
                 else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1) then 5
                 else c1
            else c1) with (ag_cnt2 sc c1 u1 ns).
    set (c2 := ag_cnt2 sc c1 u1 ns).
    specialize (AR u1 ns).
    pose proof (PF_step_seq_account_bounce st2 sc) as P2'. fold st2' in P2'.
    assert (INV2' : INVL (X_as (m :: idle)) st2' L BL LS2) by (unfold st2'; apply INVL_step_seq; apply INVL_account_bounce; exact INV2).
    assert (TF2' : TF0 st2').
    { cps_destruct (account_bounce_fields sc st2) as (A1 & A2 & _). cps_destruct (step_seq_fields (account_bounce sc st2)) as (B1 & B2 & _).
      apply (TF0_ctrl st2 st2'); [unfold st2'; rewrite B1, A1; reflexivity| unfold st2'; rewrite B2, A2; reflexivity| exact TF2x]. }
    assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
      QPURE T sc idle st L BL req k
        (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
          if negb (mmap_answer_ok (live_ranges st2') n3 r) then bad_answer bail
          else if is_err r then free_meta m st2' (fun st3 => k st3 (-1)) bail
          else let '(st3, rid) := new_region RKGroup r n3 st2' in
               ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st3)) sc m (rid, 0) c3
                 (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai)
                 (fun st5 go => match go with
                                | None => k st5 (-1)
                                | Some g0 => queue (LActive sc) g0 (upd_meta g0 (fun r0 => m_set_avail (m_avail r0 - 1) r0) st5) (fun st6 => k st6 0) bail
                                end)))
      \/ exists len K,
          SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
            if negb (mmap_answer_ok (live_ranges st2') n3 r) then bad_answer bail
            else if is_err r then free_meta m st2' (fun st3 => k st3 (-1)) bail
            else let '(st3, rid) := new_region RKGroup r n3 st2' in
                 ag_tail full_lay (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st3)) sc m (rid, 0) c3
                   (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai)
                   (fun st5 go => match go with
                                  | None => k st5 (-1)
                                  | Some g0 => queue (LActive sc) g0 (upd_meta g0 (fun r0 => m_set_avail (m_avail r0 - 1) r0) st5) (fun st6 => k st6 0) bail
                                  end))
          = SVis (EMmap 0 len PROT_RW MAPF0) K
          /\ MM T (2^20) L len K (QFAIL T sc idle st L BL req k) (QSUCC T sc idle st L BL req k len) /\ ZC sc st).
    { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
      pose proof (grp_ok_sound sc c3 n3 GRP) as G. cbn zeta in G. cps_destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
      right. eexists n3, _. split; [reflexivity|]. split; [| exact ZC0].
      split; [lia|]. split.
      { cbn. left. split; [exact (brk_quiet_of _ _ _ (proj1 INV2'))|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|]. unfold LEN_MAX. lia. }
      intros a Ha. rewrite answer_ok_mmap in Ha. rewrite (mmap_answer_ok_eq _ _ _ (proj1 INV2')) in Ha. rewrite Ha. cbn [negb].
      split.
      + (* [comment removed for export] *)
        intros ER. rewrite ER. rewrite MI_List.free_meta_eq.
        apply (fail_facts idle sc req st st1 st2' L BL LS2 m k INV2' NIm TF2'); [| | right; exact I| |exact NHm].
        * intros sc' Hs. cps_destruct (account_bounce_fields sc st2) as (_ & _ & A3 & _). cps_destruct (step_seq_fields (account_bounce sc st2)) as (_ & _ & B3 & _).
          unfold st2'. rewrite B3, A3, HA2. apply ACT1. exact Hs.
        * eapply GP_trans; [exact (GP_taf _ _ _ TAF)| eapply GP_trans; [exact (GP_amf _ _ AF2)|]].
          apply GP_eq; [apply (pf_regions _ _ P2')|].
          unfold st2', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity.
        * apply (AFR_mono _ (1 + 0)); [apply (AFR_trans _ 1 0 None None _ st2); [exact AF02| apply AFR_of_PF; [lia| exact P2']| intros; discriminate]| lia].
      + (* [comment removed for export] *)
        intros ER. rewrite ER.
        destruct (new_region RKGroup a n3 st2') as [st3 rid] eqn:EN.
        assert (Erid : rid = s_next_rid st2') by (unfold new_region in EN; inversion EN; reflexivity).
        assert (Est3 : st3 = fst (new_region RKGroup a n3 st2')) by (rewrite EN; reflexivity).
        pose proof (INVL_new_group_region (X_as (m :: idle)) st2' L BL LS2 a n3 INV2' eq_refl Ha ER ltac:(unfold LEN_MAX; lia)) as INV3.
        rewrite <- Est3, <- Erid in INV3. cbn [xorph X_as x_idle x_zomb x_pend x_fresh] in INV3.
        assert (Hr : s_regions st3 !! rid = Some (mkRegion RKGroup a n3)).
        { rewrite Est3, ng_lookup, Erid, N.eqb_refl. reflexivity. }
        assert (NS : s_shadow st3 !! rid = None).
        { rewrite Est3, Erid. change (s_shadow (fst (new_region RKGroup a n3 st2'))) with (s_shadow st2'). exact (shadow_next_rid_none _ _ _ _ _ INV2'). }
        assert (ACT2' : forall sc', active st2' sc' = active st1 sc').
        { intros sc'. cps_destruct (account_bounce_fields sc st2) as (_ & _ & A3 & _). cps_destruct (step_seq_fields (account_bounce sc st2)) as (_ & _ & B3 & _).
          unfold st2'. rewrite B3, A3. apply HA2. }
        assert (ACT3 : forall sc', active st3 sc' = active st1 sc') by (intros sc'; rewrite Est3; change (active (fst (new_region RKGroup a n3 st2')) sc') with (active st2' sc'); apply ACT2').
        assert (EMP : LS2 (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INV3); rewrite ACT3; exact HA).
        assert (TF3 : TF0 st3) by (apply (TF0_ctrl st2'); [rewrite Est3; reflexivity| rewrite Est3; reflexivity| exact TF2']).
        set (AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai).
        pose proof (clamp_ai (UNIT * size_class sc) c3 ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
        assert (HAI0 : sc = 0 -> AI = c3 - 1).
        { intros Hsc0. unfold AI. rewrite Hsc0. change (UNIT * size_class 0) with 16. change ((4096 - UNIT) / 16 - 1) with 254.
          replace (c3 - 1 <? 254) with true by (symmetry; apply Z.ltb_lt; lia). replace (c3 - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
        rewrite ag_tail_eq.
        set (MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c).
        change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st3)) with (upd_meta m (m_set_maplen (Z.shiftr n3 12)) (upd_ctx MC st3)).
        cps_destruct (ag_top_ok idle st3 (KInv.set_groups ((a, n3) :: ld_groups L) L) BL LS2 m rid (mkRegion RKGroup a n3) sc c3 n3 AI
                    INV3 Hr eq_refl eq_refl NS GRP Hsc HAI HAI0 EMP TF3 NIm) as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
        pose proof (top_facts rid sc c3 n3 AI GRP Hsc) as TFX. cbn zeta in TFX.
        cps_destruct TFX as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & Emr).
        rewrite Emr in MR', F4, F5, F7, F8, F9. rewrite <- MR' in F4, F5, F7, F8, F9.
        set (st5 := agt (upd_meta m (m_set_maplen (Z.shiftr n3 12)) (upd_ctx MC st3)) sc m (rid, 0) c3 AI) in *.
        cbn iota.
        assert (STR5 : get_stride (MR st5 m) = if (c3 - 1 =? 0) && negb (Z.shiftr n3 12 =? 0) then Z.shiftr n3 12 * 4096 - UNIT else UNIT * size_class sc).
        { rewrite MR'. unfold get_stride. cbn. reflexivity. }
        assert (NZ12 : (Z.shiftr n3 12 =? 0) = false) by (apply Z.eqb_neq; lia).
        rewrite NZ12 in STR5. cbn [negb] in STR5. rewrite andb_true_r in STR5.
        assert (E12 : Z.shiftr n3 12 * 4096 = n3) by (rewrite F2; pose proof (Z.div_mod n3 4096 ltac:(lia)); lia).
        assert (SC5 : m_sizeclass (MR st5 m) = sc) by (rewrite MR'; reflexivity).
        destruct (AFR_create_top (chain sc) 1 idle st st2' L BL LS2 m a n3 sc c3 AI (Z.shiftr n3 12) MC
                    (AFR_trans _ 1 0 None None _ st2 _ AF02 (AFR_of_PF _ 0 None _ _ ltac:(lia) P2') ltac:(intros; discriminate))
                    INV2' NHm ltac:(left; reflexivity) ltac:(intros c; reflexivity) ltac:(intros c; reflexivity))
          as [AF5 HOST5].
        { rewrite <- Erid, <- Est3. exact SC5. }
        rewrite <- Erid, <- Est3 in AF5, HOST5. fold st5 in AF5, HOST5.
        cps_destruct (finish_facts T (fun g li => NEWCNT sc req (usage st sc) li) idle st st5 L (KInv.set_groups ((a, n3) :: ld_groups L) L) BL LS2 sc req m (rid, 0) AI (c3 - 1) (Z.shiftr n3 12) k bail
                    INV' GR' MR' HAI ltac:(lia) Hsc ltac:(rewrite ACT', ACT3; exact HA) ltac:(intros UNDER; rewrite STR5 in UNDER; destruct RED as [(C1 & _ & _)|NR]; [clear -HAI C1; lia| exfalso; destruct (Z.eqb_spec (c3 - 1) 0); [rewrite E12 in UNDER; assert (c3 = 1) by lia; subst c3; lia| lia]])
                    ltac:(apply TF0_TF2; exact TF'))
          as (st6 & LS6 & EQ6 & SP6 & AF6).
        * destruct RED as [(C1 & Nd & S28)|NR].
          -- rewrite STR5. replace (c3 - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). rewrite E12, Nd.
             pose proof (proj1 (round_up_pg_spec (req + IB + UNIT))). unfold UNIT, IB in *. lia.
          -- rewrite STR5. destruct (Z.eqb_spec (c3 - 1) 0); [rewrite E12; unfold UNIT in *; nia| lia].
        * intros S28. destruct RED as [(C1 & Nd & S28')|NR]; [lia|].
          rewrite STR5 in F5 |- *. destruct (Z.eqb_spec (c3 - 1) 0) as [C1|]; [| reflexivity].
          destruct F5 as [F5|]; [| lia]. rewrite E12 in F5 |- *. assert (c3 = 1) by lia. subst c3. lia.
        * intros sc' Hs. rewrite ACT', ACT3. apply ACT1. exact Hs.
        * reflexivity.
        * eapply GP_trans; [exact (GP_taf _ _ _ TAF)| eapply GP_trans; [exact (GP_amf _ _ AF2)|]]. split.
          -- intros q rq Hq Kq. unfold st5. rewrite agt_regions. cbn. rewrite Est3. apply (ng_keep _ _ _ _ _ _ _ INV2'). rewrite (pf_regions _ _ P2'). exact Hq.
          -- unfold st5. rewrite agt_secret. cbn. rewrite Est3. cbn.
             unfold st2', step_seq, account_bounce. destruct (sc_in_seq_range sc); [destruct (negb _ && _); [destruct (_ <? 100)|]|]; destruct (c_seq _ =? 255); reflexivity.
        * apply (AFR_mono _ (1 + 0)); [exact AF5| lia].
        * left. exists u1, ns. rewrite <- (pf_usage _ _ P1 sc), <- (pf1_usage _ _ P2 sc). fold c1. fold c2. rewrite E3. split; [reflexivity| exact HB].
        * exists st6, 0, LS6. rewrite EQ6. split; [reflexivity|]. split; [lia|]. split; [exact SP6|]. exact AF6. }
    unfold ag_cn3 in GO. cbn zeta in GO.
    destruct (negb ns && (c2 <=? 7)).
    + destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
      * cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    + cbn beta iota. exact (GO _ _ eq_refl).
  - (* [comment removed for export] *)
    pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
    pose proof (nest_ok_sound sc c1 NEST) as N0. cbn zeta in N0. cps_destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
    pose proof (nest_chain sc (usage st2 sc) Hsc HB) as [Hj Hcost]. fold c1 in Hj, Hcost.
    set (size := UNIT * size_class sc) in *.
    set (j := size_to_class (UNIT + c1 * size - IB)) in *.
    set (KK := fun st5 (go : optr) => match go with
                                      | None => k st5 (-1)
                                      | Some g0 => queue (LActive sc) g0 (upd_meta g0 (fun r0 => m_set_avail (m_avail r0 - 1) r0) st5) (fun st6 => k st6 0) bail
                                      end).
    set (KK' := fun st3 idx => if idx <? 0 then free_meta m st3 (fun st4 => KK st4 None) bail
                               else match active st3 j with
                                    | None => SVis (EUndef UBadPtr) (fun _ => bail)
                                    | Some g => ag_tail full_lay (upd_meta m (m_set_maplen 0) (nest_layout st3 g idx j size c1)) sc m (slot_of st3 g idx) c1 (c1 - 1) KK
                                    end).
    change (alloc_slot full_lay f st2 j (UNIT + c1 * size - IB) _ bail) with (alloc_slot full_lay f st2 j (UNIT + c1 * size - IB) KK' bail).
    assert (ND' : NoDup (m :: idle)) by (apply NoDup_cons; split; [intros Hin; apply NIm; apply list_elem_of_In; exact Hin| exact ND]).
    assert (HCNT2 : cost j <= c_avail_meta_count (s_ctx st2)) by (pose proof (pf1_cnt _ _ P2); pose proof (pf_cnt _ _ P1); lia).
    specialize (IH j (m :: idle) st2 L BL LS2 (UNIT + c1 * size - IB) KK' bail ltac:(lia) INV2 TF2x ND' ltac:(lia) ltac:(lia) ltac:(lia) (fun _ => HCNT2)).
    (* [comment removed for export] *)
    assert (FIN : forall stS idx LSS L2, 0 <= idx ->
      SLOT_POST (m :: idle) j (UNIT + c1 * size - IB) st2 L BL stS idx L2 LSS -> AFR (chain j) (cost j) (active stS j) st2 stS ->
      exists st6 LS6, KK' stS idx = k st6 0 /\ SLOT_POST idle sc req st L BL st6 0 L2 LS6 /\ AFR (chain sc) (cost sc) (active st6 sc) st st6
        /\ GNX (fun _ _ li => li = ag_cnt1 sc (usage st sc) - 1 /\ UNIT * size_class sc * ag_cnt1 sc (usage st sc) + UNIT <= PGSZ / 2) sc st6).
    { (intros stS idx LSS L2 Hidx; cps_intros (ACT & LIVE & GP2 & RES); intros AFS).
      destruct RES as [(Eneg & _ & _)|(g & bg & aig & Hidx' & HAj & Hg & SCg & FIT & STR & INVS & TFS)]; [lia|].
      unfold KK'. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HAj.
      assert (Hgh : hosts stS bg g) by (exists aig; exact Hg).
      assert (Ep : slot_of stS g idx = (fst bg, sstart (MR stS g) idx)).
      { unfold slot_of. fold (MR stS g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INVS))) _ _ idx Hgh). }
      rewrite Ep. rewrite ag_tail_eq. unfold KK.
      specialize (STR ltac:(lia)).
      assert (EMP : LSS (LActive sc) = []) by (apply (LS_empty_of _ _ _ _ _ _ INVS); rewrite ACT by lia; rewrite HA2; exact HA).
      cps_destruct (ag_nested_ok idle stS L2 BL LSS m g bg aig idx sc c1 INVS Hg Hidx' SCg STR NEST Hsc EMP TFS NIm)
        as (INV' & TF' & MR' & GR' & ACT' & HD' & TK').
      pose proof (nst_facts stS g bg idx sc c1 NEST Hsc) as NF. cbn zeta in NF.
      cps_destruct NF as (_ & _ & _ & _ & _ & _ & _ & Emr & Es).
      fold size in MR', GR', ACT', INV', TF', Emr, Es |- *. fold j in MR', GR', ACT', INV', TF' |- *.
      rewrite Emr in MR'. rewrite Emr in Es.
      set (st5 := agt (upd_meta m (m_set_maplen 0) (nest_layout stS g idx j size c1)) sc m (fst bg, sstart (MR stS g) idx) c1 (c1 - 1)) in *.
      (* [comment removed for export] *)
      assert (GMn : forall b, gm (upd_meta m (m_set_maplen 0) (nest_layout stS g idx j size c1)) b = gm stS b).
      { intros b. unfold gm. rewrite s_groups_upd_meta. change (s_groups (nest_layout stS g idx j size c1)) with (s_groups (strip (nest_layout stS g idx j size c1))).
        rewrite strip_nest_layout. reflexivity. }
      assert (MRn : forall x, x <> m -> MR (upd_meta m (m_set_maplen 0) (nest_layout stS g idx j size c1)) x = MR stS x).
      { intros x NE. rewrite geo_set_maplen_other by exact NE. unfold MR. rewrite <- (get_meta_rec_strip (nest_layout stS g idx j size c1)), strip_nest_layout, get_meta_rec_strip. reflexivity. }
      assert (GM5 : forall b, gm st5 b = if aptr_eqb b (fst bg, sstart (MR stS g) idx) then Some m else gm stS b).
      { intros b. unfold st5. rewrite agt_gm, GMn. reflexivity. }
      assert (MR5 : forall x, x <> m -> MR st5 x = MR stS x) by (intros x NE; unfold st5; rewrite agt_MR_other by exact NE; apply MRn; exact NE).
      assert (RG5 : s_regions st5 = s_regions stS).
      { unfold st5. rewrite agt_regions, s_regions_upd_meta. rewrite <- (s_regions_strip (nest_layout stS g idx j size c1)), strip_nest_layout, s_regions_strip. reflexivity. }
      assert (PEND : gm stS (fst bg, sstart (MR stS g) idx) = None).
      { pose proof (is_part _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INVS)))))) bg g aig idx Hg Hidx') as ONE.
        rewrite (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INVS))) _ _ idx Hgh) in ONE. cbn zeta in ONE.
        cps_destruct ONE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DE).
        unfold gm. match goal with |- match ?t with _ => _ end = None => destruct t eqn:EG end; [| reflexivity]. exfalso. apply DE. split; [congruence| reflexivity]. }
      assert (HOST5 : forall b x, hosts stS b x -> hosts st5 b x /\ MR st5 x = MR stS x).
      { intros b x Hh. split.
        - apply hosts_gm. rewrite GM5. destruct (aptr_eqb_spec b (fst bg, sstart (MR stS g) idx)) as [->|NE]; [| apply hosts_gm; exact Hh].
          exfalso. apply hosts_gm in Hh. rewrite PEND in Hh. discriminate.
        - apply MR5. intros ->. exact (idle_nohost _ _ _ _ _ m b INVS ltac:(left; reflexivity) Hh). }
      assert (SC5 : m_sizeclass (MR st5 m) = sc) by (rewrite MR'; reflexivity).
      assert (AF25 : AFR (chain sc) (cost j) (Some m) st2 st5).
      { rewrite HAj in AFS. pose proof (AFR_monoC (chain j) (chain sc) (cost j) (Some g) st2 stS AFS (fun c => chain_sub sc j c Hj)) as [A1 A2 A3 A4 A5]. constructor.
        - unfold st5. rewrite agt_cnt, s_ctx_upd_meta. rewrite <- (s_ctx_strip (nest_layout stS g idx j size c1)), strip_nest_layout, s_ctx_strip. exact A1.
        - intros sc' Hs. unfold st5. rewrite agt_usage. destruct (Z.eqb_spec sc' sc) as [->|NE]; [exfalso; apply Hs; left; reflexivity|].
          rewrite Z.add_0_r. rewrite usage_upd_meta. rewrite <- (usage_strip (nest_layout stS g idx j size c1)), strip_nest_layout, usage_strip. apply A2. exact Hs.
        - intros b x Hh. destruct (A3 b x Hh) as [H1 H2]. destruct (HOST5 b x H1) as [H3 H4]. split; [exact H3|]. rewrite H4. exact H2.
        - intros b x Hh. apply hosts_gm in Hh. rewrite GM5 in Hh. destruct (aptr_eqb_spec b (fst bg, sstart (MR stS g) idx)) as [->|NE].
          + inversion Hh; subst x. right. rewrite SC5. split; [left; reflexivity|]. split; [right; reflexivity|]. right.
            split; [exact (nest_nonest_false sc (usage st2 sc) HB)|].
            destruct (HOST5 bg g Hgh) as [H5 H6]. exists g, bg, idx. rewrite H6, SCg. split; [exact H5|]. split; [exact Hj|]. split; [exact Hidx'| reflexivity].
          + apply hosts_gm in Hh. destruct (A4 b x Hh) as [H1|(HC & HE & HW)]; [left; exact H1| right].
            destruct (HOST5 b x Hh) as [_ H4]. rewrite H4. split; [exact HC|]. split.
            * left. destruct HE as [HE|HE]; [exact HE|]. injection HE as <-. rewrite SCg. exact Hj.
            * destruct HW as [HW|(NN & p & bp & i & Hp & Cp & Hi & ->)]; [left; exact HW| right]. split; [exact NN|].
              destruct (HOST5 bp p Hp) as [H5 H6]. exists p, bp, i. rewrite H6. auto.
        - intros q rq Hq. rewrite RG5. apply A5. exact Hq. }
      assert (AF5 : AFR (chain sc) (cost sc) (Some m) st st5).
      { apply (AFR_mono _ (1 + cost j)); [exact (AFR_trans _ 1 (cost j) None (Some m) _ st2 _ AF02 AF25 ltac:(intros; discriminate))| lia]. }
      cps_destruct (finish_facts T (fun _ li => li = ag_cnt1 sc (usage st sc) - 1 /\ UNIT * size_class sc * ag_cnt1 sc (usage st sc) + UNIT <= PGSZ / 2)
                  idle st st5 L L2 BL LSS sc req m (fst bg, sstart (MR stS g) idx) (c1 - 1) (c1 - 1) 0 k bail
                  INV' GR' ltac:(rewrite Z.sub_diag; exact MR') ltac:(lia) ltac:(lia) Hsc ltac:(rewrite ACT', ACT by lia; rewrite HA2; exact HA)
                  ltac:(rewrite MR', Es; unfold size; intros; lia) ltac:(exact TF')
                  ltac:(rewrite MR', Es; unfold size; lia) ltac:(intros _; rewrite MR', Es; reflexivity)
                  ltac:(intros sc' Hs; rewrite ACT', ACT by lia; rewrite HA2; apply ACT1; exact Hs) LIVE
                  ltac:(eapply GP_trans; [exact (GP_taf _ _ _ TAF)| eapply GP_trans; [exact (GP_amf _ _ AF2)| eapply GP_trans; [exact GP2| apply GP_eq]]];
                        [exact RG5| unfold st5; rewrite agt_secret, s_secret_upd_meta;
                                     rewrite <- (s_secret_strip (nest_layout stS g idx j size c1)), strip_nest_layout, s_secret_strip; reflexivity])
                  AF5 ltac:(rewrite <- (pf_usage _ _ P1 sc), <- (pf1_usage _ _ P2 sc); fold c1; split; [reflexivity| exact HB])) as (st6 & LS6 & EQ6 & SP6 & AF6).
      exists st6, LS6. split; [exact EQ6|]. split; [exact SP6| exact AF6]. }
    destruct IH as [(stS & idx & LSS & ER & Hidx & SP & AFS & _)|(len & K & ER & (LEN & PRE & MMK) & _)].
    + (* [comment removed for export] *)
      left. rewrite ER. cps_destruct (FIN stS idx LSS L Hidx SP AFS) as (st6 & LS6 & EQ6 & SP6 & AF6 & GN6).
      exists st6, 0, LS6. split; [exact EQ6|]. split; [lia|]. split; [exact SP6|]. split; [exact AF6|]. intros g0 Hg0. right. exact (GN6 g0 Hg0).
    + (* [comment removed for export] *)
      right. exists len, K. split; [exact ER|]. split; [| exact ZC0]. split; [exact LEN|]. split; [exact PRE|].
      intros r Hr. destruct (MMK r Hr) as [QF QS]. split.
      * intros ERR. cps_destruct (QF ERR) as (stF & LSF & EK & SPF & AFF). rewrite EK. unfold KK'. change (-1 <? 0) with true. cbn iota.
        rewrite MI_List.free_meta_eq. unfold KK.
        cps_destruct SPF as (ACTF & _ & GPF & [(_ & INVF & TFF)|(g & _ & _ & Hneg & _)]); [| lia].
        apply (fail_facts idle sc req st st1 stF L BL LSF m k INVF NIm TFF); [| | right; exact I| | exact NHm].
        -- intros sc' Hs. rewrite ACTF by lia. rewrite HA2. apply ACT1. exact Hs.
        -- eapply GP_trans; [exact (GP_taf _ _ _ TAF)| eapply GP_trans; [exact (GP_amf _ _ AF2)| exact GPF]].
        -- apply (AFR_mono _ (1 + cost j)); [exact (AFR_trans _ 1 (cost j) None None _ st2 _ AF02 (AFR_monoC _ _ _ _ _ _ AFF (fun c => chain_sub sc j c Hj)) ltac:(intros; discriminate))| lia].
      * intros OK. cps_destruct (QS OK) as (stS & idx & LSS & EK & Hidx & SP & AFS & _). rewrite EK.
        cps_destruct (FIN stS idx LSS _ Hidx SP AFS) as (st6 & LS6 & EQ6 & SP6 & AF6 & GN6).
        exists st6, 0, LS6. split; [exact EQ6|]. split; [lia|]. split; [exact SP6|]. split; [exact AF6|]. intros g0 Hg0. unfold OMMAP. right. exact (GN6 g0 Hg0).
Qed.
End SLOT_SHAPE.

End ACeilS1.
