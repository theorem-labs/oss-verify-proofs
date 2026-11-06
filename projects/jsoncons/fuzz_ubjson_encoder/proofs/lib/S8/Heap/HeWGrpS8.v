(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import KInvS8 MI_InvS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Kit MI_Arith.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MI_ListS8 MI_ExtS8 MI_Ext2S8 MI_GeomS8 KStepS8 MI_WAMetaS8 MI_Pres4S8 MI_WFree2S8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import MI_Bits MI_Cnt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Spec Require Import MI_WSlot2S8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Lib Require Import DecodeS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.CJ.Bridge Require Import BrResS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Heap Require Import HeTreeS8 HeAbsS8 HeEmptyS8 HeWNtfS8 HeMetaS8 HeWSlotS8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMWGRP.
Context {RUNp : RunP}.

Lemma add_slots_vals m p stride cnt st s v :
  s_slots (add_slots m p stride cnt st) !! s = Some v -> s_slots st !! s = Some v \/ fst v = m.
Proof.
  unfold add_slots. intros Hs.
  set (F := fun acc : Z * gmap aptr (aptr * Z) => let (i, tb) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> tb)) in Hs.
  change (snd (Z.iter cnt F (0, s_slots st)) !! s = Some v) in Hs.
  set (Inv := fun acc : Z * gmap aptr (aptr * Z) => forall s v, snd acc !! s = Some v -> s_slots st !! s = Some v \/ fst v = m).
  assert (STEP : forall acc, Inv acc -> Inv (F acc)).
  { intros [i tb] IH s' v' Hs'. cbn in Hs'. destruct (decide (s' = aadd p (UNIT + stride * i))) as [->|NE].
    - rewrite lookup_insert_eq in Hs'. injection Hs' as <-. right. reflexivity.
    - rewrite lookup_insert_ne in Hs' by congruence. exact (IH s' v' Hs'). }
  assert (I : Inv (Z.iter cnt F (0, s_slots st))).
  { unfold Z.iter. destruct cnt as [|q|q]; try (intros s' v' H; left; exact H).
    apply Pos.iter_invariant; [exact STEP| intros s' v' H; left; exact H]. }
  exact (I s v Hs).
Qed.

Lemma MW_weaken st0 LS0 st LS N sc sc' : MW st0 LS0 st LS N sc -> sc <= sc' -> MW st0 LS0 st LS N sc'.
Proof.
  intros [A F Ab Ac Ao Fn] H. constructor; auto.
  - intros b m Hb Hc. apply Ab; [exact Hb| lia].
  - intros s Hs. apply Ac. lia.
Qed.

Lemma NEWG_data st st' x : data_of (MR st' x) = data_of (MR st x) -> NEWG st x -> NEWG st' x.
Proof.
  intros D (NE & C & M & F). unfold NEWG, gempty in *. rewrite (fmask_data _ _ D).
  apply data_of_eq in D as (Em & _ & _ & Eli & _ & Esc & _). rewrite Eli, Esc, Em. auto.
Qed.

Definition NEWS (st : mstate) (m : aptr) : Prop := NEWG st m /\ m_sizeclass (MR st m) < 48.

Lemma NEWS_data st st' x : data_of (MR st' x) = data_of (MR st x) -> NEWS st x -> NEWS st' x.
Proof.
  intros D [G C]. split; [exact (NEWG_data st st' x D G)|]. pose proof D as D'. apply data_of_eq in D' as (_ & _ & _ & _ & _ & Esc & _). rewrite Esc. exact C.
Qed.

Lemma PEND_move st LS st' LS' x : data_of (MR st' x) = data_of (MR st x) -> (forall b, hosts st' b x -> hosts st b x) ->
  (forall h, In x (LS' h) -> In x (LS h)) -> PEND st LS x -> PEND st' LS' x.
Proof.
  intros D H L (P1 & P2 & P3). split; [rewrite D; exact P1|]. split.
  - intros [b Hb]. apply P2. exists b. exact (H b Hb).
  - intros h Hh. exact (P3 h (L h Hh)).
Qed.

Lemma skipn_S_of {A} k (l : list A) x r : skipn k l = x :: r -> skipn (S k) l = r /\ firstn (S k) l = firstn k l ++ [x].
Proof.
  revert l. induction k as [|k IH]; intros l E; destruct l as [|y l]; cbn in E |- *; try discriminate.
  - injection E as -> ->. split; [reflexivity|]. reflexivity.
  - destruct (IH l E) as [E1 E2]. split; [exact E1| rewrite E2; reflexivity].
Qed.

Lemma nmeta_add_key st st1 m : (forall x, s_metas st1 !! x <> None <-> (s_metas st !! x <> None \/ x = m)) -> s_metas st !! m = None ->
  nmeta st1 = nmeta st + 1.
Proof.
  intros K Hm. unfold nmeta. rewrite <- !size_dom.
  assert (E : dom (s_metas st1) = {[m]} ∪ dom (s_metas st)).
  { apply set_eq. intros x. rewrite elem_of_union, elem_of_singleton, !elem_of_dom.
    pose proof (K x) as Kx. split.
    - intros [r Hr]. assert (P : s_metas st1 !! x <> None) by (rewrite Hr; discriminate). apply Kx in P as [P|P]; [right| left; exact P].
      destruct (s_metas st !! x) as [r'|]; [exists r'; reflexivity| congruence].
    - intros [->|[r Hr]].
      + destruct (s_metas st1 !! m) as [r|] eqn:E1; [exists r; reflexivity|]. exfalso. apply (proj2 (K m)); [right; reflexivity| exact E1].
      + destruct (s_metas st1 !! x) as [r'|] eqn:E1; [exists r'; reflexivity|]. exfalso. apply (proj2 Kx); [left; rewrite Hr; discriminate| reflexivity]. }
  rewrite E. rewrite size_union.
  - rewrite size_singleton. lia.
  - apply disjoint_singleton_l. rewrite elem_of_dom. intros [r Hr]. congruence.
Qed.

Record SCAL (s s' : mstate) : Prop := mkSC {
  sc_metas : s_metas s' = s_metas s;
  sc_groups : s_groups s' = s_groups s;
  sc_slots : s_slots s' = s_slots s;
  sc_heads : forall h, get_head s' h = get_head s h;
  sc_mfr : MFR s s'
}.

Lemma SCAL_bounce_seq sc s : SCAL s (step_seq (account_bounce sc s)).
Proof.
  constructor.
  - autorewrite with mst. reflexivity.
  - autorewrite with mst. reflexivity.
  - autorewrite with mst. reflexivity.
  - intros h. destruct h; unfold get_head, active, ctx; autorewrite with mst; reflexivity.
  - constructor; autorewrite with mst; try reflexivity; tauto.
Qed.

Lemma SCAL_ctx f s : (forall c, c_active (f c) = c_active c) -> (forall c, c_free_meta_head (f c) = c_free_meta_head c) ->
  (forall c, c_avail_meta_count (f c) = c_avail_meta_count c) -> (forall c, c_avail_meta_area_count (f c) = c_avail_meta_area_count c) ->
  (forall c, c_avail_meta (f c) = c_avail_meta c) -> (forall c, c_avail_meta_areas (f c) = c_avail_meta_areas c) ->
  (forall c, c_meta_area_tail (f c) = c_meta_area_tail c) -> (forall c, c_meta_alloc_shift (f c) = c_meta_alloc_shift c) ->
  (forall c, c_brk (f c) = c_brk c) -> (forall c, c_init_done (f c) = c_init_done c) -> SCAL s (upd_ctx f s).
Proof.
  intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10. constructor; try reflexivity.
  - intros h. destruct h; unfold get_head, active, ctx; cbn; [rewrite E1| rewrite E2]; reflexivity.
  - constructor; cbn; auto; tauto.
Qed.

Lemma newreg_lookup k a len st q : s_regions (fst (new_region k a len st)) !! q =
  if (q =? s_next_rid st)%N then Some (mkRegion k a len) else s_regions st !! q.
Proof.
  unfold new_region. cbn. destruct (N.eqb_spec q (s_next_rid st)) as [->|NE]; [apply lookup_insert_eq| rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma CURI_newgrp st a len : CURI st -> 0 < len -> CURI (fst (new_region RKGroup a len st)).
Proof.
  intros C Hl. set (st' := fst (new_region RKGroup a len st)).
  assert (L2 : forall q, s_regions st' !! q = if (q =? s_next_rid st)%N then Some (mkRegion RKGroup a len) else s_regions st !! q) by (intros q; apply newreg_lookup).
  assert (Nrid : s_regions st !! s_next_rid st = None).
  { destruct (s_regions st !! s_next_rid st) as [r0|] eqn:E; [| reflexivity]. pose proof (cu_ids _ C _ r0 E). lia. }
  assert (OLD : forall q r, s_regions st !! q = Some r -> s_regions st' !! q = Some r).
  { intros q r H. rewrite L2. destruct (N.eqb_spec q (s_next_rid st)) as [->|NE]; [rewrite Nrid in H; discriminate| exact H]. }
  assert (NEW : forall q r, s_regions st' !! q = Some r -> r_kind r <> RKGroup -> s_regions st !! q = Some r).
  { intros q r H K. rewrite L2 in H. destruct (N.eqb_spec q (s_next_rid st)) as [->|NE]; [injection H as <-; exfalso; apply K; reflexivity| exact H]. }
  assert (FR : forall q r, frontier st' q r = frontier st q r) by reflexivity.
  assert (CX : s_ctx st' = s_ctx st) by reflexivity.
  destruct C as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12]. constructor; rewrite ?CX.
  - intros q r0 H. rewrite L2 in H. cbn [st' new_region fst s_next_rid set_next_rid set_regions]. destruct (N.eqb_spec q (s_next_rid st)) as [->|NE]; [lia|].
    pose proof (C1 q r0 H). lia.
  - destruct C2 as (D1 & D2 & D3). split; [exact D1|]. split; [exact D2|]. intros rid off E. destruct (D3 rid off E) as (r & Hr & R).
    exists r. split; [exact (OLD _ _ Hr)| exact R].
  - intros q r0 H K. rewrite FR. apply C3; [apply NEW; [exact H| rewrite K; discriminate]| exact K].
  - destruct (c_brk (s_ctx st)) as [| |rid0 off].
    + intros q r0 H. rewrite L2 in H. destruct (N.eqb_spec q (s_next_rid st)) as [->|NE]; [injection H as <-; discriminate| exact (C4 q r0 H)].
    + exact I.
    + destruct C4 as (r0 & H0 & K0 & E0). exists r0. split; [exact (OLD _ _ H0)|]. auto.
  - intros q1 q2 r1 r2 H1 H2 K1 K2. apply (C5 q1 q2 r1 r2); [apply NEW; [exact H1| rewrite K1; discriminate]| apply NEW; [exact H2| rewrite K2; discriminate]| exact K1| exact K2].
  - intros q r0 H. rewrite L2 in H. destruct (N.eqb_spec q (s_next_rid st)) as [->|NE].
    + injection H as <-. cbn. split; [exact Hl|]. intros [K|K]; discriminate.
    + exact (C6 q r0 H).
  - intros a' ar H. destruct (C7 a' ar H) as (r0 & H0 & R). exists r0. split; [exact (OLD _ _ H0)| rewrite FR; exact R].
  - exact C8.
  - exact C9.
  - exact C10.
  - exact C11.
  - exact C12.
Qed.

Lemma MARITH_newgrp st a len : CURI st -> MARITH st -> MARITH (fst (new_region RKGroup a len st)).
Proof.
  intros C M. set (st' := fst (new_region RKGroup a len st)).
  assert (Nrid : s_regions st !! s_next_rid st = None).
  { destruct (s_regions st !! s_next_rid st) as [r0|] eqn:E; [| reflexivity]. pose proof (cu_ids _ C _ r0 E). lia. }
  assert (R2 : s_regions st' = <[s_next_rid st := mkRegion RKGroup a len]> (s_regions st)) by reflexivity.
  destruct M as [M1 M2 M3 M4 M5 M6]. constructor.
  - exact M1.
  - exact M2.
  - exact M3.
  - rewrite (regsum_insert_fresh metalen st st' _ _ Nrid R2). cbn [metalen r_kind]. change (c_meta_alloc_shift (s_ctx st')) with (c_meta_alloc_shift (s_ctx st)). lia.
  - intros q r H K. rewrite newreg_lookup in H. destruct (N.eqb_spec q (s_next_rid st)) as [->|NE]; [injection H as <-; discriminate| exact (M5 q r H K)].
  - exact M6.
Qed.

Lemma Phi_newgrp st a len : CURI st -> Phi (fst (new_region RKGroup a len st)) = Phi st + mmap_len len.
Proof.
  intros C. assert (Nrid : s_regions st !! s_next_rid st = None).
  { destruct (s_regions st !! s_next_rid st) as [r0|] eqn:E; [| reflexivity]. pose proof (cu_ids _ C _ r0 E). lia. }
  rewrite !Phi_regsum. rewrite (regsum_insert_fresh wreg st (fst (new_region RKGroup a len st)) (s_next_rid st) (mkRegion RKGroup a len) Nrid eq_refl).
  change (brk_dead_w (fst (new_region RKGroup a len st))) with (brk_dead_w st). cbn [wreg r_kind r_len]. lia.
Qed.

Lemma Psi_newgrp st a len : CURI st -> Psi (fst (new_region RKGroup a len st)) = Psi st + 1.
Proof.
  intros C. assert (Nrid : s_regions st !! s_next_rid st = None).
  { destruct (s_regions st !! s_next_rid st) as [r0|] eqn:E; [| reflexivity]. pose proof (cu_ids _ C _ r0 E). lia. }
  unfold Psi. rewrite !ngreg_regsum. rewrite (regsum_insert_fresh isgreg st (fst (new_region RKGroup a len st)) (s_next_rid st) (mkRegion RKGroup a len) Nrid eq_refl). cbn [isgreg r_kind].
  change (nareas (fst (new_region RKGroup a len st))) with (nareas st). lia.
Qed.

Definition agR (sc : Z) (p : aptr) (cnt ai : Z) (r : meta) : meta :=
  m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
    (m_set_mem (Some p) (m_set_freed (mask_upto (cnt - 1) - mask_upto ai) (m_set_avail (mask_upto ai) r))))).

Definition agtn (st : mstate) (sc : Z) (m p : aptr) (cnt ai : Z) : mstate :=
  let st1 := set_usage sc (usage st sc + cnt) st in
  let st2 := upd_meta m (agR sc p cnt ai) st1 in
  let st3 := put_group p (Some m) ai st2 in
  add_slots m p (get_stride (get_meta_rec st3 m)) cnt st3.

Lemma ag_tail_none_eq {T} st sc m p cnt ai (k : mstate -> optr -> M T) :
  ag_tail lay_none st sc m p cnt ai k = k (agtn st sc m p cnt ai) (Some m).
Proof. reflexivity. Qed.

Lemma testbit_pred_mask a i : 0 <= a -> 0 <= i -> Z.testbit (mask_upto a - 1) i = ((1 <=? i) && (i <=? a)).
Proof.
  intros Ha Hi. replace (mask_upto a - 1) with (Z.ldiff (mask_upto a) 1).
  2:{ symmetry. apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros j Hj. rewrite Z.ldiff_spec, Z.bits_0, testbit_mask_upto by lia.
      destruct (Z.eq_dec j 0) as [->|NZ].
      - cbn. replace (0 <=? a) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      - replace (Z.testbit 1 j) with false; [reflexivity|]. symmetry. change 1 with (2 ^ 0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
  rewrite Z.ldiff_spec, testbit_mask_upto by lia. change 1 with (2 ^ 0) at 1. rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.leb_spec i a); destruct (Z.leb_spec 1 i); destruct (Z.eqb_spec 0 i); cbn; try reflexivity; lia.
Qed.

Lemma created_newg sc p cnt ai r : 0 <= sc < 48 -> 1 <= cnt <= 32 -> 0 <= ai <= cnt - 1 ->
  let r' := m_set_avail (m_avail (agR sc p cnt ai r) - 1) (agR sc p cnt ai r) in
  fmask r' <> mask_upto (m_last_idx r') /\ m_sizeclass r' < 48 /\ m_mem r' <> None /\ fsub (fmask r') (mask_upto (m_last_idx r'))
  /\ m_sizeclass r' = sc /\ m_next r' = m_next r /\ m_prev r' = m_prev r /\ m_last_idx r' = cnt - 1.
Proof.
  intros Hsc Hc Ha. cbv zeta.
  set (r0 := agR sc p cnt ai r).
  set (r' := m_set_avail (m_avail r0 - 1) r0).
  assert (LI : Z.land (cnt - 1) 31 = cnt - 1).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 5) with 32. lia. }
  assert (SC : Z.land sc 63 = sc).
  { change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 6) with 64. lia. }
  assert (Eav : m_avail r' = mask_upto ai - 1) by reflexivity.
  assert (Efr : m_freed r' = mask_upto (cnt - 1) - mask_upto ai) by reflexivity.
  assert (Eli : m_last_idx r' = cnt - 1) by (change (m_last_idx r') with (Z.land (cnt - 1) 31); exact LI).
  assert (Esc : m_sizeclass r' = sc) by (change (m_sizeclass r') with (Z.land sc 63); exact SC).
  assert (Emem : m_mem r' = Some p) by reflexivity.
  assert (En : m_next r' = m_next r) by reflexivity.
  assert (Ep : m_prev r' = m_prev r) by reflexivity.
  unfold fmask. rewrite Eav, Efr, Eli, Esc, Emem, En, Ep. clearbody r' r0.
  destruct (created_masks ai (cnt - 1) ltac:(lia) ltac:(lia)) as (_ & _ & _ & _ & _ & _ & _ & EF). cbn zeta in EF. rewrite EF.
  assert (TB : forall i, 0 <= i -> Z.testbit (Z.ldiff (mask_upto (cnt - 1)) (mask_upto ai)) i = (ai <? i) && (i <=? cnt - 1)).
  { intros i Hi. rewrite Z.ldiff_spec, !testbit_mask_upto by lia. destruct (Z.leb_spec i (cnt - 1)); destruct (Z.leb_spec i ai); destruct (Z.ltb_spec ai i); cbn; try reflexivity; lia. }
  split; [| split; [lia| split; [discriminate| split; [| split; [reflexivity| split; [reflexivity| split; reflexivity]]]]]].
  - intros E. assert (T0 := f_equal (fun z => Z.testbit z 0) E). cbn beta in T0.
    rewrite Z.lor_spec, testbit_pred_mask, TB, testbit_mask_upto in T0 by lia. cbn in T0.
    replace (ai <? 0) with false in T0 by (symmetry; apply Z.ltb_ge; lia). replace (0 <=? cnt - 1) with true in T0 by (symmetry; apply Z.leb_le; lia).
    discriminate.
  - intros i Hi T. rewrite Z.lor_spec, testbit_pred_mask, TB in T by lia. rewrite testbit_mask_upto by lia.
    apply Z.leb_le. destruct (Z.leb_spec 1 i); destruct (Z.leb_spec i ai); destruct (Z.ltb_spec ai i); destruct (Z.leb_spec i (cnt - 1)); cbn in T; try discriminate; lia.
Qed.

Section W.
Variables (st0 : mstate) (L0 : mled) (BL0 : list blk) (LS0 : lhead -> list aptr).
Hypothesis INV0 : INVC x0 st0 L0 BL0 LS0.

Lemma fl0_facts m : In m (LS0 LFree) -> s_metas st0 !! m <> None /\ ~ live_group st0 m.
Proof.
  intros Hm. pose proof INV0 as (IR & IA & IM & IL & IG & IS). split.
  - apply present_of_next. apply (proj1 (proj1 (il_link _ _ IL m))). exists LFree. exact Hm.
  - intros [b [ai Hb]]. pose proof (il_free _ _ IL m Hm) as F. destruct (im_hdr _ _ _ IM _ _ Hb) as (m' & Hm' & Hmem & _).
    cbn in Hm'. injection Hm' as <-. rewrite F in Hmem. discriminate.
Qed.

Lemma hosted0_present b m : hosts st0 b m -> s_metas st0 !! m <> None.
Proof.
  intros [ai Hb]. pose proof INV0 as (IR & IA & IM & IL & IG & IS). exact (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG _ _ _ Hb)).
Qed.

Lemma fl0_nodup : NoDup (LS0 LFree).
Proof. pose proof INV0 as (IR & IA & IM & IL & IG & IS). exact (il_nodup _ _ IL LFree). Qed.

Lemma MW_am st LS N sc st1 LS1 m dc dn : MW st0 LS0 st LS N sc -> AMPOST st LS st1 LS1 (Some m) dc dn ->
  MW st0 LS0 st1 LS1 (m :: N) sc /\ PEND st1 LS1 m /\ ~ In m N
  /\ (forall x, In x N -> PEND st LS x -> PEND st1 LS1 x) /\ (forall x, NEWG st x -> NEWG st1 x).
Proof.
  intros [[A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14] F1 F2 F3 F4 F5]
         [P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20].
  destruct (P10 m eq_refl) as (R1 & R2 & R3 & R4).
  assert (HO : forall b x, hosts st1 b x <-> hosts st b x) by (intros b x; unfold hosts; rewrite P1; tauto).
  destruct A4 as (k & K1 & K2 & K3 & K4).
  assert (LSUB : forall h x, In x (LS1 h) -> In x (LS h)).
  { intros h x Hx. destruct h as [sc'|]; [rewrite P8 in Hx; exact Hx|]. destruct P9 as [E|(m' & E & _)]; [rewrite <- E; exact Hx| rewrite E; right; exact Hx]. }

  assert (SRC : (LS LFree = m :: LS1 LFree) \/ (s_metas st !! m = None /\ LS LFree = [] /\ LS1 LFree = [])).
  { destruct P9 as [E|(m' & E & Em)].
    - right. destruct R4 as [Hh|(Ha1 & Ha2)].
      + exfalso. destruct (LS LFree) as [|y r] eqn:EL; [discriminate|]. cbn in Hh. injection Hh as ->. apply (R2 LFree). rewrite E. left. reflexivity.
      + split; [exact Ha1|]. split; [exact Ha2|]. rewrite E. exact Ha2.
    - injection Em as <-. left. exact E. }
  assert (NH0 : ~ (exists b, hosts st0 b m)).
  { intros [b Hb]. destruct SRC as [E|(Ha & _)].
    - rewrite K1 in E. assert (In m (LS0 LFree)) by (rewrite <- (firstn_skipn k (LS0 LFree)), E; apply in_app_iff; right; left; reflexivity).
      apply (proj2 (fl0_facts m H)). exists b. exact Hb.
    - exact (A10 m (hosted0_present b m Hb) Ha). }
  assert (NH : ~ live_group st1 m).
  { intros [b Hb]. apply HO in Hb. destruct SRC as [E|(Ha & _)].
    - apply (F5 m); [rewrite E; left; reflexivity| exists b; exact Hb].
    - destruct (A6 b m Hb) as [H0|HN]; [exact (NH0 (ex_intro _ b H0))| exact (proj1 (proj2 (A7 m HN)) Ha)]. }
  assert (NIN : ~ In m N).
  { intros HN. destruct SRC as [E|(Ha & _)].
    - rewrite K1 in E. destruct (K3 m HN) as [Hf|Ha0].
      + pose proof fl0_nodup as ND. rewrite <- (firstn_skipn k (LS0 LFree)), E in ND.
        exact (NoDup_app_In _ _ m ND Hf ltac:(left; reflexivity)).
      + assert (In m (LS0 LFree)) by (rewrite <- (firstn_skipn k (LS0 LFree)), E; apply in_app_iff; right; left; reflexivity).
        exact (proj1 (fl0_facts m H) Ha0).
    - exact (proj1 (proj2 (A7 m HN)) Ha). }
  assert (PPRES : forall x, In x N -> PEND st LS x -> PEND st1 LS1 x).
  { intros x _ Px. apply (PEND_move st LS); [exact (P3 x)| intros b Hb; apply HO; exact Hb| exact (fun h => LSUB h x)| exact Px]. }
  assert (NPRES : forall x, NEWG st x -> NEWG st1 x) by (intros x; apply NEWG_data; exact (P3 x)).
  split; [| split; [| split; [exact NIN| split; [exact PPRES| exact NPRES]]]].
  2:{ split; [rewrite R1; reflexivity|]. split; [exact NH| exact R2]. }
  constructor; [constructor| | | | |].
  - exact P7.
  - exact P18.
  - exact P19.
  - destruct SRC as [E|(Ha & E0 & E1)].
    + rewrite K1 in E. destruct (skipn_S_of k (LS0 LFree) m (LS1 LFree) E) as [S1 S2]. exists (S k). split; [symmetry; exact S1|].
      assert (NM : nmeta st1 = nmeta st).
      { destruct P13 as [P|(_ & P)]; [exact P| rewrite K1 in P; rewrite P in E; discriminate]. }
      split; [intros x Hx; rewrite S2 in Hx; apply in_app_iff in Hx as [Hx|[<-|[]]]; [right; exact (K2 x Hx)| left; reflexivity]|].
      split; [intros x [<-|Hx]; [left; rewrite S2; apply in_app_iff; right; left; reflexivity| destruct (K3 x Hx) as [H|H]; [left; rewrite S2; apply in_app_iff; left; exact H| right; exact H]]|].
      cbn [length]. rewrite NM. lia.
    + exists k. rewrite E1. split; [rewrite <- K1; symmetry; exact E0|].
      assert (NM : nmeta st1 = nmeta st + 1).
      { apply (nmeta_add_key st st1 m); [| exact Ha]. intros x. split.
        - intros Hx. destruct (P12 x Hx) as [H|H]; [left; exact H| injection H as ->; right; reflexivity].
        - intros [H|Ex]; [exact (P11 x H)| subst x; exact R3]. }
      split; [intros x Hx; right; exact (K2 x Hx)|].
      split; [intros x [<-|Hx]; [right; destruct (s_metas st0 !! m) eqn:E0'; [exfalso; apply (A10 m); [rewrite E0'; discriminate| exact Ha]| reflexivity]| exact (K3 x Hx)]|].
      cbn [length]. rewrite NM. lia.
  - intros b x Hb. destruct (A5 b x Hb) as (N1 & G1 & S1). split; [intros [E|Hx]; [subst x; exact (NH0 (ex_intro _ b Hb))| exact (N1 Hx)]|].
    rewrite (GEOM_data _ _ (P3 x)), (fmask_data _ _ (P3 x)). split; assumption.
  - intros b x Hb. apply HO in Hb. destruct (A6 b x Hb) as [H|H]; [left; exact H| right; right; exact H].
  - intros x [<-|Hx].
    + split; [exact NH0|]. split; [exact R3|]. right. split; [rewrite R1; reflexivity|]. split; [exact NH| exact R2].
    + destruct (A7 x Hx) as (N1 & Pr & C). split; [exact N1|]. split; [exact (P11 x Pr)|].
      destruct C as [C|C]; [left; exact (NPRES x C)| right; exact (PPRES x Hx C)].
  - apply NoDup_cons. split; [intros Hin; apply NIN; apply list_elem_of_In; exact Hin| exact A8].
  - intros x Hx. destruct (P12 x Hx) as [H|H]; [destruct (A9 x H) as [H'|H']; [left; exact H'| right; right; exact H']| injection H as ->; right; left; reflexivity].
  - intros x Hx. exact (P11 x (A10 x Hx)).
  - destruct SRC as [E|(_ & E0 & E1)]; [| right; exact E1]. left.
    destruct P13 as [P|(_ & P)]; [| rewrite P in E; discriminate]. rewrite P. destruct A11 as [A|A]; [exact A| rewrite A in E; discriminate].
  - intros rid r H K. exact (P14 rid r (A12 rid r H K) K).
  - exact (N.le_trans _ _ _ A13 P17).
  - intros s v H. rewrite P2 in H. destruct (A14 s v H) as [H'|H']; [left; exact H'| right; right; exact H'].
  - intros x Hx. rewrite (P3 x). apply F1. exact (LSUB LFree x Hx).
  - intros b x Hb Hc. destruct (F2 b x Hb Hc) as [D H]. split; [rewrite (P3 x); exact D| apply HO; exact H].
  - intros sc' Hs. rewrite P4, P8. exact (F3 sc' Hs).
  - intros sc' x Hx. rewrite P8 in Hx. destruct (F4 sc' x Hx) as ([b Hb] & Ec). split; [exists b; apply HO; exact Hb|].
    pose proof (P3 x) as D. apply data_of_eq in D as (_ & _ & _ & _ & _ & Esc & _). rewrite Esc. exact Ec.
  - intros x Hx [b Hb]. apply (F5 x (LSUB LFree x Hx)). exists b. apply HO. exact Hb.
Qed.

Lemma MWA_scal st LS N st' : MWA st0 LS0 st LS N -> SCAL st st' ->
  MWA st0 LS0 st' LS N /\ Phi st' = Phi st /\ Psi st' = Psi st /\ (forall x, MR st' x = MR st x) /\ (forall b x, hosts st' b x <-> hosts st b x).
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14] [E1 E2 E3 E4 MF].
  assert (MRe : forall x, MR st' x = MR st x) by (intros x; unfold MR, get_meta_rec; rewrite E1; reflexivity).
  assert (HO : forall b x, hosts st' b x <-> hosts st b x) by (intros b x; unfold hosts; rewrite E2; tauto).
  assert (NM : nmeta st' = nmeta st) by (unfold nmeta; rewrite E1; reflexivity).
  split; [| split; [| split; [| split; [exact MRe| exact HO]]]].
  - constructor.
    + apply (lists_ok_links st st' LS A1 E4). intros x. rewrite MRe. split; reflexivity.
    + exact (CURI_frame _ _ A2 MF).
    + exact (MARITH_frame _ _ A3 MF).
    + rewrite NM. exact A4.
    + intros b x Hb. rewrite MRe. exact (A5 b x Hb).
    + intros b x Hb. apply HO in Hb. exact (A6 b x Hb).
    + intros x Hx. destruct (A7 x Hx) as (N1 & P1 & C1). split; [exact N1|]. split; [rewrite E1; exact P1|].
      destruct C1 as [C1|C1]; [left; apply (NEWG_data st); [rewrite MRe; reflexivity| exact C1]|].
      right. apply (PEND_move st LS); [rewrite MRe; reflexivity| intros b Hb; apply HO; exact Hb| auto| exact C1].
    + exact A8.
    + intros x Hx. apply A9. rewrite <- E1. exact Hx.
    + intros x Hx. rewrite E1. exact (A10 x Hx).
    + rewrite NM. exact A11.
    + intros rid r H K. rewrite (mf_regions _ _ MF). exact (A12 rid r H K).
    + rewrite (mf_rid _ _ MF). exact A13.
    + intros s v H. rewrite E3 in H. exact (A14 s v H).
  - rewrite !Phi_regsum, (regsum_ext _ _ _ (mf_regions _ _ MF)). unfold brk_dead_w. rewrite (mf_brk _ _ MF). reflexivity.
  - unfold Psi, nareas. rewrite !ngreg_regsum, (regsum_ext _ _ _ (mf_regions _ _ MF)), (mf_areas _ _ MF). reflexivity.
Qed.

Lemma MWA_newgrp st LS N a len : MWA st0 LS0 st LS N -> 0 < len ->
  let st' := fst (new_region RKGroup a len st) in
  MWA st0 LS0 st' LS N /\ Phi st' = Phi st + mmap_len len /\ Psi st' = Psi st + 1 /\ (forall x, MR st' x = MR st x)
  /\ (forall b x, hosts st' b x <-> hosts st b x).
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14] Hl. cbv zeta.
  set (st' := fst (new_region RKGroup a len st)).
  assert (MRe : forall x, MR st' x = MR st x) by reflexivity.
  assert (HO : forall b x, hosts st' b x <-> hosts st b x) by (intros b x; reflexivity).
  assert (NM : nmeta st' = nmeta st) by reflexivity.
  assert (Nrid : s_regions st !! s_next_rid st = None).
  { destruct (s_regions st !! s_next_rid st) as [r0|] eqn:E; [| reflexivity]. pose proof (cu_ids _ A2 _ r0 E). lia. }
  split; [| split; [exact (Phi_newgrp st a len A2)| split; [exact (Psi_newgrp st a len A2)| split; [exact MRe| exact HO]]]].
  constructor.
  - apply (lists_ok_links st st' LS A1); [intros h; destruct h; reflexivity| intros x; split; reflexivity].
  - exact (CURI_newgrp st a len A2 Hl).
  - exact (MARITH_newgrp st a len A2 A3).
  - exact A4.
  - exact A5.
  - exact A6.
  - exact A7.
  - exact A8.
  - exact A9.
  - exact A10.
  - exact A11.
  - intros rid r H K. unfold st'. rewrite newreg_lookup. destruct (N.eqb_spec rid (s_next_rid st)) as [->|NE]; [| exact (A12 rid r H K)].
    rewrite (A12 _ r H K) in Nrid. discriminate.
  - cbn [st' new_region fst s_next_rid set_next_rid set_regions]. lia.
  - exact A14.
Qed.

Lemma MR_agtn_m st sc m p cnt ai : MR (agtn st sc m p cnt ai) m = agR sc p cnt ai (MR st m).
Proof. unfold agtn, MR, get_meta_rec. autorewrite with mst. rewrite !lookup_insert_eq. reflexivity. Qed.
Lemma MR_agtn_other st sc m p cnt ai x : x <> m -> MR (agtn st sc m p cnt ai) x = MR st x.
Proof. intros NE. unfold agtn, MR, get_meta_rec. autorewrite with mst. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma groups_agtn st sc m p cnt ai : s_groups (agtn st sc m p cnt ai) = <[p := mkGhdr (Some m) (Z.land ai 31)]> (s_groups st).
Proof. reflexivity. Qed.

Lemma MWA_create st LS N m sc p cnt ai X :
  MWA st0 LS0 st LS N -> In m N -> PEND st LS m -> 0 <= sc < 48 -> 1 <= cnt <= 32 -> 0 <= ai <= cnt - 1 ->
  let stF := upd_meta m (fun r => m_set_avail (m_avail r - 1) r) (agtn (upd_meta m (m_set_maplen X) st) sc m p cnt ai) in
  MWA st0 LS0 stF LS N /\ NEWG stF m /\ m_next (MR stF m) = None /\ m_sizeclass (MR stF m) = sc
  /\ (forall x, x <> m -> MR stF x = MR st x) /\ (forall b x, x <> m -> hosts stF b x -> hosts st b x)
  /\ Phi stF = Phi st /\ Psi stF = Psi st
  /\ hosts stF p m /\ m_last_idx (MR stF m) = cnt - 1 /\ (forall c, active stF c = active st c).
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14] Hm (P1 & P2 & P3) Hsc Hc Ha. cbv zeta.
  set (s1 := upd_meta m (m_set_maplen X) st).
  set (s2 := agtn s1 sc m p cnt ai).
  set (stF := upd_meta m (fun r => m_set_avail (m_avail r - 1) r) s2).
  assert (Pm : s_metas st !! m <> None) by exact (proj1 (proj2 (A7 m Hm))).
  assert (MRm : MR stF m = m_set_avail (m_avail (agR sc p cnt ai (m_set_maplen X (MR st m))) - 1) (agR sc p cnt ai (m_set_maplen X (MR st m)))).
  { unfold stF, MR. rewrite get_meta_rec_upd_same. fold (MR s2 m). unfold s2. rewrite MR_agtn_m. unfold s1, MR. rewrite get_meta_rec_upd_same. reflexivity. }
  assert (MRo : forall x, x <> m -> MR stF x = MR st x).
  { intros x NE. unfold stF, MR. rewrite get_meta_rec_upd_other by exact NE. fold (MR s2 x). unfold s2. rewrite MR_agtn_other by exact NE.
    unfold s1, MR. rewrite get_meta_rec_upd_other by exact NE. reflexivity. }
  destruct (created_newg sc p cnt ai (m_set_maplen X (MR st m)) Hsc Hc Ha) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  rewrite <- MRm in G1, G2, G3, G4, G5, G6, G7, G8.
  assert (NXm : m_next (MR st m) = None).
  { destruct (m_next (MR st m)) eqn:E; [| reflexivity]. exfalso. destruct (proj2 (proj1 (lo_link _ _ A1 m))) as [h Hh]; [rewrite E; discriminate|]. exact (P3 h Hh). }
  assert (PVm : m_prev (MR st m) = None) by exact (proj2 (lo_link _ _ A1 m) NXm).
  assert (KEYS0 : forall x, s_metas stF !! x = None <-> s_metas st !! x = None).
  { intros x. unfold stF, s2, agtn, s1. autorewrite with mst. destruct (decide (x = m)) as [->|NE].
    - rewrite lookup_insert_eq. split; [discriminate| intros E; exfalso; exact (Pm E)].
    - rewrite !lookup_insert_ne by congruence. reflexivity. }
  assert (KEYS : forall x, s_metas stF !! x <> None <-> s_metas st !! x <> None) by (intros x; rewrite (KEYS0 x); tauto).
  assert (NM : nmeta stF = nmeta st) by exact (nmeta_keys _ _ KEYS0).
  assert (GR : s_groups stF = <[p := mkGhdr (Some m) (Z.land ai 31)]> (s_groups st)) by reflexivity.
  assert (HOF : forall b x, hosts stF b x -> (b = p /\ x = m) \/ hosts st b x).
  { intros b x [ai' Hb]. rewrite GR in Hb. destruct (aptr_eqb_spec b p) as [->|NE].
    - rewrite lookup_insert_eq in Hb. injection Hb as -> _. left. split; reflexivity.
    - rewrite lookup_insert_ne in Hb by congruence. right. exists ai'. exact Hb. }
  assert (HD : forall h, get_head stF h = get_head st h) by (intros h; destruct h; reflexivity).
  assert (MF : MFR st stF) by (constructor; try reflexivity; exact KEYS0).
  assert (PHI : Phi stF = Phi st).
  { rewrite !Phi_regsum, (regsum_ext _ stF st eq_refl). change (brk_dead_w stF) with (brk_dead_w st). reflexivity. }
  assert (PSI : Psi stF = Psi st).
  { unfold Psi. rewrite !ngreg_regsum, (regsum_ext _ stF st eq_refl). change (nareas stF) with (nareas st). reflexivity. }
  split; [| split; [| split; [rewrite G6; exact NXm| split; [exact G5| split; [exact MRo| split; [| split; [exact PHI| split; [exact PSI|]]]]]]]].
  2:{ unfold NEWG, gempty. split; [exact G1| split; [left; exact G2| split; [exact G3| exact G4]]]. }
  2:{ intros b x NE Hb. destruct (HOF b x Hb) as [(_ & E)|H]; [congruence| exact H]. }
  2:{ split; [exists (Z.land ai 31); rewrite GR, lookup_insert_eq; reflexivity|]. split; [exact G8| intros c; reflexivity]. }
  constructor.
  - apply (lists_ok_links st stF LS A1 HD). intros x. destruct (aptr_eqb_spec x m) as [->|NE].
    + rewrite G6, G7. split; reflexivity.
    + rewrite (MRo x NE). split; reflexivity.
  - exact (CURI_frame _ _ A2 MF).
  - exact (MARITH_frame _ _ A3 MF).
  - rewrite NM. exact A4.
  - intros b x Hb. destruct (A5 b x Hb) as (N1 & G & F). assert (NE : x <> m) by (intros ->; exact (N1 Hm)).
    rewrite (MRo x NE). split; [exact N1| split; assumption].
  - intros b x Hb. destruct (HOF b x Hb) as [(_ & ->)|H]; [right; exact Hm| exact (A6 b x H)].
  - intros x Hx. destruct (A7 x Hx) as (N1 & Px & C). split; [exact N1|]. split; [apply KEYS; exact Px|].
    destruct (aptr_eqb_spec x m) as [->|NE].
    + left. unfold NEWG, gempty. split; [exact G1| split; [left; exact G2| split; [exact G3| exact G4]]].
    + destruct C as [C|C].
      * left. apply (NEWG_data st); [rewrite (MRo x NE); reflexivity| exact C].
      * right. apply (PEND_move st LS); [rewrite (MRo x NE); reflexivity| | auto| exact C].
        intros b Hb. destruct (HOF b x Hb) as [(_ & E)|H]; [congruence| exact H].
  - exact A8.
  - intros x Hx. apply A9. apply KEYS. exact Hx.
  - intros x Hx. apply KEYS. exact (A10 x Hx).
  - rewrite NM. exact A11.
  - exact A12.
  - exact A13.
  - intros s v Hs. destruct (add_slots_vals _ _ _ _ _ s v Hs) as [H|H]; [exact (A14 s v H)| right; rewrite H; exact Hm].
Qed.

Lemma MWA_queue st LS N g sc : MWA st0 LS0 st LS N -> In g N -> NEWG st g -> m_next (MR st g) = None ->
  let st' := queue_st (LActive sc) g st in let LS' := fupd LS (LActive sc) (LS (LActive sc) ++ [g]) in
  MWA st0 LS0 st' LS' N /\ (forall x, data_of (MR st' x) = data_of (MR st x)) /\ (forall b x, hosts st' b x <-> hosts st b x)
  /\ Phi st' = Phi st /\ Psi st' = Psi st /\ (forall x h, x <> g -> In x (LS' h) -> In x (LS h)).
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14] Hg NG Hn. cbv zeta.
  set (st' := queue_st (LActive sc) g st). set (LS' := fupd LS (LActive sc) (LS (LActive sc) ++ [g])).
  assert (Pg : s_metas st !! g <> None) by exact (proj1 (proj2 (A7 g Hg))).
  pose proof (lists_queue st LS A1 (LActive sc) g Hn) as LO'. fold st' LS' in LO'.
  destruct (queue_frame (LActive sc) g st) as (R1 & _ & R3 & R4 & R5 & R6 & _ & _ & _ & CB). fold st' in R1, R3, R4, R5, R6, CB.
  assert (DATA : forall x, data_of (MR st' x) = data_of (MR st x)) by (intros x; apply queue_data).
  assert (HO : forall b x, hosts st' b x <-> hosts st b x) by (intros b x; unfold hosts; rewrite R5; tauto).
  assert (LIN : forall h x, In x (LS h) -> s_metas st !! x <> None) by (intros h x Hx; apply present_of_next; exact (lists_in_next_some _ _ A1 h x Hx)).
  assert (KEYS0 : forall x, s_metas st' !! x = None <-> s_metas st !! x = None).
  { intros x. split.
    - intros E. destruct (s_metas st !! x) eqn:E0; [| reflexivity]. exfalso. apply (queue_keys_mono (LActive sc) g st x); [rewrite E0; discriminate| exact E].
    - intros E. destruct (s_metas st' !! x) eqn:E1; [| reflexivity]. exfalso.
      destruct (queue_keys (LActive sc) g st x ltac:(fold st'; rewrite E1; discriminate)) as [H|[->|[H|(a & Ha & Hp)]]].
      + exact (H E).
      + exact (Pg E).
      + rewrite (lo_head _ _ A1) in H. destruct (LS (LActive sc)) as [|y r] eqn:EL; [discriminate|]. cbn in H. injection H as ->.
        apply (LIN (LActive sc) x); [rewrite EL; left; reflexivity| exact E].
      + rewrite (lo_head _ _ A1) in Ha. destruct (LS (LActive sc)) as [|y r] eqn:EL; [discriminate|]. cbn in Ha. injection Ha as ->.
        destruct (lists_head_prev _ _ A1 (LActive sc) a r EL) as [Hpa _]. rewrite Hp in Hpa. injection Hpa as ->.
        apply (LIN (LActive sc) (List.last r a)); [rewrite EL; apply last_In| exact E]. }
  assert (KEYS : forall x, s_metas st' !! x <> None <-> s_metas st !! x <> None) by (intros x; rewrite (KEYS0 x); tauto).
  assert (NM : nmeta st' = nmeta st) by exact (nmeta_keys _ _ KEYS0).
  assert (MF : MFR st st').
  { destruct CB. constructor; auto. }
  assert (LFR : LS' LFree = LS LFree) by (unfold LS'; rewrite fupd_ne by discriminate; reflexivity).
  assert (LSUB : forall x h, x <> g -> In x (LS' h) -> In x (LS h)).
  { intros x h NE Hx. unfold LS', fupd in Hx. destruct (decide (h = LActive sc)) as [->|NEh]; [| exact Hx].
    apply in_app_iff in Hx as [Hx|[E|[]]]; [exact Hx| congruence]. }
  split; [| split; [exact DATA| split; [exact HO| split; [| split; [| exact LSUB]]]]].
  - constructor.
    + exact LO'.
    + exact (CURI_frame _ _ A2 MF).
    + exact (MARITH_frame _ _ A3 MF).
    + rewrite LFR, NM. exact A4.
    + intros b x Hb. rewrite (GEOM_data _ _ (DATA x)), (fmask_data _ _ (DATA x)). exact (A5 b x Hb).
    + intros b x Hb. apply HO in Hb. exact (A6 b x Hb).
    + intros x Hx. destruct (A7 x Hx) as (N1 & Px & C). split; [exact N1|]. split; [apply KEYS; exact Px|].
      destruct (aptr_eqb_spec x g) as [->|NE]; [left; exact (NEWG_data st st' g (DATA g) NG)|].
      destruct C as [C|C]; [left; exact (NEWG_data st st' x (DATA x) C)|].
      right. apply (PEND_move st LS); [exact (DATA x)| intros b Hb; apply HO; exact Hb| intros h Hh; exact (LSUB x h NE Hh)| exact C].
    + exact A8.
    + intros x Hx. apply A9. apply KEYS. exact Hx.
    + intros x Hx. apply KEYS. exact (A10 x Hx).
    + rewrite LFR, NM. exact A11.
    + intros rid r H K. rewrite R1. exact (A12 rid r H K).
    + rewrite R3. exact A13.
    + intros s v H. rewrite R6 in H. exact (A14 s v H).
  - rewrite !Phi_regsum, (regsum_ext _ _ _ R1). unfold brk_dead_w. rewrite (cb_brk _ _ CB). reflexivity.
  - unfold Psi, nareas. rewrite !ngreg_regsum, (regsum_ext _ _ _ R1), R4. reflexivity.
Qed.

Definition SRES (st' : mstate) (sc idx : Z) : Prop :=
  exists g bg, active st' sc = Some g /\ hosts st' bg g /\ 0 <= idx <= m_last_idx (MR st' g) /\ m_sizeclass (MR st' g) = sc.

Definition BELOW (st : mstate) (LS : lhead -> list aptr) (st' : mstate) (LS' : lhead -> list aptr) (sc : Z) : Prop :=
  forall c', c' < sc -> active st' c' = active st c' /\ LS' (LActive c') = LS (LActive c').

Lemma active_of_lists st LS st' LS' h : lists_ok st LS -> lists_ok st' LS' -> LS' (LActive h) = LS (LActive h) -> active st' h = active st h.
Proof.
  intros L1 L2 E. change (active st' h) with (get_head st' (LActive h)). change (active st h) with (get_head st (LActive h)).
  rewrite (lo_head _ _ L1), (lo_head _ _ L2), E. reflexivity.
Qed.

Section AS.
Variables (T : Type) (Q : Z -> nat -> T -> Prop).

Definition SPOST (st : mstate) (LS : lhead -> list aptr) (N : list aptr) (c : Z) (n : nat)
  (st' : mstate) (LS' : lhead -> list aptr) (N' : list aptr) (c' : Z) (n' : nat) : Prop :=
  MWA st0 LS0 st' LS' N' /\ incl N N' /\ (forall m, In m N -> PEND st LS m -> PEND st' LS' m)
  /\ (forall m, In m N' -> ~ In m N -> NEWS st' m) /\ c' - c <= Phi st' - Phi st /\ Z.of_nat n' - Z.of_nat n <= Psi st' - Psi st.

Definition ASW (f : nat) : Prop := forall sc st LS N req (k : mstate -> Z -> M T) bail c n,
  0 <= sc < 48 -> MW st0 LS0 st LS N sc -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  (forall st' LS' N' c' n' idx, 0 <= idx -> SPOST st LS N c n st' LS' N' c' n' -> SRES st' sc idx -> BELOW st LS st' LS' sc ->
     apw ecost (k st' idx) c' n' Q) ->
  (forall st' c' n', apw ecost (k st' (-1)) c' n' Q) ->
  apw ecost (alloc_slot lay_none f st sc req k bail) c n Q.

Definition AGPOST (sc : Z) (st : mstate) (LS : lhead -> list aptr) (N : list aptr) (c : Z) (n : nat)
  (st2 : mstate) (LS2 : lhead -> list aptr) (N2 : list aptr) (g : aptr) (c2 : Z) (n2 : nat) : Prop :=
  let st2' := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
  MWA st0 LS0 st2' LS2 N2 /\ In g N2 /\ ~ In g N /\ incl N N2 /\ NEWG st2' g /\ m_next (MR st2' g) = None
  /\ (forall m, In m N -> PEND st LS m -> PEND st2' LS2 m) /\ (forall m, In m N2 -> ~ In m N -> NEWS st2' m)
  /\ c2 - c <= Phi st2' - Phi st /\ Z.of_nat n2 - Z.of_nat n <= Psi st2' - Psi st
  /\ (exists bg, hosts st2' bg g) /\ m_sizeclass (MR st2' g) = sc /\ 0 <= m_last_idx (MR st2' g) /\ BELOW st LS st2' LS2 (sc + 1).

Lemma ecost_grp n3 : ecost (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) = mmap_len n3.
Proof. reflexivity. Qed.

Lemma ag_walk f : ASW f -> forall sc st LS N req (k : mstate -> optr -> M T) bail c n,
  0 <= sc < 48 -> MW st0 LS0 st LS N (sc + 1) -> 0 <= req -> req + IB <= UNIT * size_class sc ->
  (forall st2 LS2 N2 g c2 n2, AGPOST sc st LS N c n st2 LS2 N2 g c2 n2 -> apw ecost (k st2 (Some g)) c2 n2 Q) ->
  (forall st2 c2 n2, apw ecost (k st2 None) c2 n2 Q) ->
  apw ecost (alloc_group T lay_none (alloc_slot lay_none f) st sc req k bail) c n Q.
Proof.
  intros REC sc st LS N req k bail c n Hsc W Hreq Hfit CONT CONTN. unfold alloc_group.
  pose proof W as [WA WF _ _ _ _].
  apply (am_walk T st LS _ bail c n Q).
  { split; [exact (ma_curi _ _ _ _ _ WA)| split; [exact (ma_marith _ _ _ _ _ WA)| split; [exact (ma_lists _ _ _ _ _ WA)| exact WF]]]. }
  intros st1 LS1 mo c1 n1 AP. destruct mo as [m|]; [| apply CONTN].
  destruct (MW_am st LS N (sc + 1) st1 LS1 m _ _ W AP) as (W1 & PM & NIm & PPR & NPR).
  destruct (ap_cost _ _ _ _ _ _ _ AP ltac:(discriminate)) as [DC DN].
  pose proof W1 as [WA1 _ _ _ _ _].
  cbn beta iota zeta.
  change (if sc <? 9 then small_cnt_pick sc (usage st1 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st1 sc)) (UNIT * size_class sc))
    with (cnt0_of sc (usage st1 sc)).
  change (if (cnt0_of sc (usage st1 sc) =? 1) && (UNIT * size_class sc * cnt0_of sc (usage st1 sc) + UNIT <=? PGSZ / 2) then 2 else cnt0_of sc (usage st1 sc))
    with (ag_cnt1 sc (usage st1 sc)).
  pose proof (ag_arith sc req (usage st1 sc)) as AR.
  set (c1' := ag_cnt1 sc (usage st1 sc)) in *.
  destruct (Z.ltb_spec (PGSZ / 2) (UNIT * size_class sc * c1' + UNIT)) as [HB|HB].
  -
    set (ns := is_bouncing sc st1).
    set (st1' := step_seq (account_bounce sc st1)).
    set (u1 := if Z.even sc && (sc <? 32) then usage st1 sc + usage st1' (sc + 1) else usage st1 sc).
    change (if (u1 <? 4 * c1') && negb ns
            then if (Z.land sc 3 =? 1) && (8 * PGSZ <? UNIT * size_class sc * c1') then 2
                 else if (Z.land sc 3 =? 2) && (4 * PGSZ <? UNIT * size_class sc * c1') then 3
                 else if (Z.land sc 3 =? 0) && (8 * PGSZ <? UNIT * size_class sc * c1') then 3
                 else if (Z.land sc 3 =? 0) && (2 * PGSZ <? UNIT * size_class sc * c1') then 5
                 else c1'
            else c1') with (ag_cnt2 sc c1' u1 ns).
    set (c2 := ag_cnt2 sc c1' u1 ns).
    specialize (AR u1 ns).

    destruct (MWA_scal st1 LS1 (m :: N) st1' WA1 (SCAL_bounce_seq sc st1)) as (WA2 & PH2 & PS2 & MR2 & HO2).
    assert (PM2 : PEND st1' LS1 m) by (apply (PEND_move st1 LS1); [rewrite MR2; reflexivity| intros b Hb; apply HO2; exact Hb| auto| exact PM]).
    assert (GO : forall c3 n3, ag_cn3 sc req c2 u1 ns = (c3, n3) ->
      apw ecost (SVis (EMmap 0 n3 PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (live_ranges st1') n3 r) then bad_answer bail
        else if is_err r then free_meta m st1' (fun st2 => k st2 None) bail
        else let '(st2, rid) := new_region RKGroup r n3 st1' in
             ag_tail lay_none (upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta m (m_set_maplen (Z.shiftr n3 12)) st2)) sc m (rid, 0) c3
               (let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai) k)) c1 n1 Q).
    { intros c3 n3 E3. destruct (proj1 (AR c3 n3 Hsc Hreq Hfit) HB E3) as [GRP RED].
      pose proof (grp_ok_sound sc c3 n3 GRP) as G. cbn zeta in G. destruct G as (G1 & G2 & G3 & _).
      apply apw_vis. intros r. destruct (negb (mmap_answer_ok (live_ranges st1') n3 r)); [apply apw_bad|].
      destruct (is_err r).
      - rewrite free_meta_eq. apply CONTN.
      - unfold new_region. cbv zeta. cbn iota.
        set (s2 := set_next_rid (N.succ (s_next_rid st1')) (set_regions (<[s_next_rid st1' := mkRegion RKGroup r n3]> (s_regions st1')) st1')).
        destruct (MWA_newgrp st1' LS1 (m :: N) r n3 WA2 ltac:(lia)) as (WA3 & PH3 & PS3 & MR3 & HO3). fold s2 in WA3, PH3, PS3, MR3, HO3.
        assert (PM3 : PEND s2 LS1 m) by (apply (PEND_move st1' LS1); [rewrite MR3; reflexivity| intros b Hb; apply HO3; exact Hb| auto| exact PM2]).
        set (MC := fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c).
        destruct (MWA_scal s2 LS1 (m :: N) (upd_ctx MC s2) WA3 (SCAL_ctx MC s2 (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)
                    (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl) (fun _ => eq_refl)))
          as (WA4 & PH4 & PS4 & MR4 & HO4).
        assert (PM4 : PEND (upd_ctx MC s2) LS1 m) by (apply (PEND_move s2 LS1); [rewrite MR4; reflexivity| intros b Hb; apply HO4; exact Hb| auto| exact PM3]).
        set (AI := let ai := (4096 - UNIT) / (UNIT * size_class sc) - 1 in let ai := if c3 - 1 <? ai then c3 - 1 else ai in if ai <? 0 then 0 else ai).
        pose proof (clamp_ai (UNIT * size_class sc) c3 ltac:(lia)) as HAI. cbn zeta in HAI. fold AI in HAI.
        change (upd_ctx MC (upd_meta m (m_set_maplen (Z.shiftr n3 12)) s2)) with (upd_meta m (m_set_maplen (Z.shiftr n3 12)) (upd_ctx MC s2)).
        rewrite ag_tail_none_eq.
        destruct (MWA_create (upd_ctx MC s2) LS1 (m :: N) m sc (s_next_rid st1', 0) c3 AI (Z.shiftr n3 12) WA4 ltac:(left; reflexivity) PM4 Hsc ltac:(lia) HAI)
          as (WA5 & NG5 & NX5 & SC5 & MR5 & HO5 & PH5 & PS5 & HG5 & LI5 & AC5).
        apply (CONT _ LS1 (m :: N)). split; [exact WA5|]. split; [left; reflexivity|]. split; [exact NIm|]. split; [intros x Hx; right; exact Hx|].
        split; [exact NG5|]. split; [exact NX5|].
        split.
        + intros x Hx Px. assert (NE : x <> m) by (intros ->; exact (NIm Hx)).
          apply (PEND_move (upd_ctx MC s2) LS1); [rewrite (MR5 x NE); reflexivity| intros b Hb; exact (HO5 b x NE Hb)| auto|].
          apply (PEND_move s2 LS1); [rewrite MR4; reflexivity| intros b Hb; apply HO4; exact Hb| auto|].
          apply (PEND_move st1' LS1); [rewrite MR3; reflexivity| intros b Hb; apply HO3; exact Hb| auto|].
          apply (PEND_move st1 LS1); [rewrite MR2; reflexivity| intros b Hb; apply HO2; exact Hb| auto|].
          exact (PPR x Hx Px).
        + split; [intros x [<-|Hx] Hn; [split; [exact NG5| rewrite SC5; lia]| exfalso; exact (Hn Hx)]|].
          rewrite ecost_grp. rewrite PH5, PS5, PH4, PS4, PH3, PS3, PH2, PS2. split; [clear - DC DN; lia|]. split; [clear - DC DN; lia|].
          split; [eexists; exact HG5|]. split; [exact SC5|]. split; [rewrite LI5; lia|].
          intros c' Hc'. rewrite AC5. split.
          -- change (active (upd_ctx MC s2) c') with (active st1' c'). change (active st1' c') with (get_head st1' (LActive c')).
             rewrite (sc_heads _ _ (SCAL_bounce_seq sc st1)). change (get_head st1 (LActive c')) with (active st1 c'). apply (ap_active _ _ _ _ _ _ _ AP).
          -- apply (ap_lsa _ _ _ _ _ _ _ AP). }
    unfold ag_cn3 in GO. cbn zeta in GO.
    destruct (negb ns && (c2 <=? 7)).
    + destruct ((round_up_pg (req + IB + UNIT) <? UNIT * size_class sc + UNIT) || ((4 * PGSZ <=? round_up_pg (req + IB + UNIT)) && (u1 <? 2 * c2))).
      * cbn beta iota. exact (GO _ _ eq_refl).
      * cbn beta iota. exact (GO _ _ eq_refl).
    + cbn beta iota. exact (GO _ _ eq_refl).
  -
    pose proof (proj2 (AR 0 false 0 0 Hsc Hreq Hfit) HB) as NEST.
    pose proof (nest_ok_sound sc c1' NEST) as N0. cbn zeta in N0. destruct N0 as (N1 & N2 & N3 & N4 & N5 & N6).
    set (j := size_to_class (UNIT + c1' * (UNIT * size_class sc) - IB)) in *.
    apply (REC j st1 LS1 (m :: N) (UNIT + c1' * (UNIT * size_class sc) - IB) _ bail c1 n1 ltac:(lia) (MW_weaken _ _ _ _ _ (sc + 1) j W1 ltac:(lia)) N5 ltac:(lia)).
    + intros st' LS' N' c' n' idx Hidx (SA & SI & SP & SN & SC' & SN') SR SB.
      replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct SR as (g & bgj & HAj & _). rewrite HAj.
      change (lh_nest lay_none st' g idx j (UNIT * size_class sc) c1') with st'.
      rewrite ag_tail_none_eq.
      assert (PM' : PEND st' LS' m) by exact (SP m ltac:(left; reflexivity) PM).
      destruct (MWA_create st' LS' N' m sc (slot_of st' g idx) c1' (c1' - 1) 0 SA (SI m ltac:(left; reflexivity)) PM' Hsc ltac:(lia) ltac:(lia))
        as (WA5 & NG5 & NX5 & SC5 & MR5 & HO5 & PH5 & PS5 & HG5 & LI5 & AC5).
      apply (CONT _ LS' N'). split; [exact WA5|]. split; [exact (SI m ltac:(left; reflexivity))|]. split; [exact NIm|].
      split; [intros x Hx; apply SI; right; exact Hx|]. split; [exact NG5|]. split; [exact NX5|].
      split.
      * intros x Hx Px. assert (NE : x <> m) by (intros ->; exact (NIm Hx)).
        apply (PEND_move st' LS'); [rewrite (MR5 x NE); reflexivity| intros b Hb; exact (HO5 b x NE Hb)| auto|].
        exact (SP x ltac:(right; exact Hx) (PPR x Hx Px)).
      * split.
        -- intros x Hx Hn. destruct (aptr_eqb_spec x m) as [->|NE]; [split; [exact NG5| rewrite SC5; lia]|].
           apply (NEWS_data st'); [rewrite (MR5 x NE); reflexivity|]. apply SN; [exact Hx| intros [E|H]; [exact (NE (eq_sym E))| exact (Hn H)]].
        -- split; [lia|]. split; [lia|]. split; [eexists; exact HG5|]. split; [exact SC5|]. split; [rewrite LI5; lia|].
           intros c'' Hc''. rewrite AC5. destruct (SB c'' ltac:(lia)) as [E1 E2]. rewrite E1, E2.
           split; [apply (ap_active _ _ _ _ _ _ _ AP)| apply (ap_lsa _ _ _ _ _ _ _ AP)].
    + intros st' c' n'. change (-1 <? 0) with true. cbn iota. rewrite free_meta_eq. apply CONTN.
Qed.

Theorem as_walk : forall f, ASW f.
Proof.
  induction f as [|f IH]; intros sc st LS N req k bail c n Hsc W Hreq Hfit CONT CONTF.
  - apply apw_undef.
  - cbn [alloc_slot].
    apply (ta_walk st0 L0 BL0 LS0 INV0 T sc st LS N _ bail c n Q W Hsc).
    intros st1 LS1 first W1 TP PH PS (TF1 & TF2) (TO1 & TZ1).
    assert (PPR : forall x, In x N -> PEND st LS x -> PEND st1 LS1 x).
    { intros x _ (P1 & P2 & P3). destruct (TF1 x P3) as [E L]. split; [rewrite E; exact P1|]. split; [| exact L].
      intros [b Hb]. apply P2. exists b. apply TF2. exact Hb. }
    destruct (Z.eqb_spec first 0) as [F0|F0]; cbn [negb].
    +
      apply (ag_walk f IH sc st1 LS1 N req _ bail c n Hsc W1 Hreq Hfit).
      * intros st2 LS2 N2 g c2 n2 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14).
        cbv zeta in A1, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14.
        set (st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2) in *.
        assert (PV : m_prev (MR st3 g) = None) by exact (proj2 (lo_link _ _ (ma_lists _ _ _ _ _ A1) g) A6).
        rewrite queue_eq by assumption.
        destruct (MWA_queue st3 LS2 N2 g sc A1 A2 A5 A6) as (B1 & B2 & B3 & B4 & B5 & B6).
        assert (E3 : LS2 (LActive sc) = []).
        { pose proof (lo_head _ _ (ma_lists _ _ _ _ _ A1) (LActive sc)) as HH. change (get_head st3 (LActive sc)) with (active st3 sc) in HH.
          rewrite (proj1 (A14 sc ltac:(lia))), (TZ1 F0) in HH. destruct (LS2 (LActive sc)); [reflexivity| discriminate]. }
        apply (CONT _ (fupd LS2 (LActive sc) (LS2 (LActive sc) ++ [g])) N2); [lia| | |].
        2:{ exists g. destruct A11 as [bg Hbg]. exists bg.
            split; [change (active (queue_st (LActive sc) g st3) sc) with (get_head (queue_st (LActive sc) g st3) (LActive sc));
                    rewrite (lo_head _ _ (ma_lists _ _ _ _ _ B1) (LActive sc)), fupd_eq, E3; reflexivity|].
            split; [apply B3; exact Hbg|]. pose proof (proj1 (data_of_eq _ _) (B2 g)) as (_ & _ & _ & Eli & _ & Esc & _). rewrite Eli, Esc.
            split; [lia| exact A12]. }
        2:{ intros c' Hc'. assert (EL : fupd LS2 (LActive sc) (LS2 (LActive sc) ++ [g]) (LActive c') = LS2 (LActive c')) by (rewrite fupd_ne by (intros E; injection E; lia); reflexivity).
            destruct (A14 c' ltac:(lia)) as [E1 E2]. destruct (TO1 c' ltac:(lia)) as [E3' E4].
            split; [| rewrite EL, E2; exact E4].
            rewrite (active_of_lists st3 LS2 _ _ c' (ma_lists _ _ _ _ _ A1) (ma_lists _ _ _ _ _ B1) EL), E1. exact E3'. }
        split; [exact B1|]. split; [exact A4|].
        split.
        -- intros x Hx Px. assert (NE : x <> g) by (intros ->; exact (A3 Hx)).
           apply (PEND_move st3 LS2); [exact (B2 x)| intros b Hb; apply B3; exact Hb| intros h Hh; exact (B6 x h NE Hh)|].
           exact (A7 x Hx (PPR x Hx Px)).
        -- split; [intros x Hx Hn; exact (NEWS_data st3 _ x (B2 x) (A8 x Hx Hn))|].
           rewrite B4, B5, <- PH, <- PS. split; lia.
      * intros st2 c2 n2. apply CONTF.
    +
      destruct (TP F0) as (g & bg & HA & Hb1 & Hb0 & Esc & Hidx & _).
      apply (CONT _ LS1 N); [lia| | exists g, bg; auto| intros c' Hc'; apply TO1; lia].
      split; [exact (mw_a _ _ _ _ _ _ W1)|]. split; [intros x Hx; exact Hx|].
      split; [exact PPR|]. split; [intros x Hx Hn; exfalso; exact (Hn Hx)|]. rewrite PH, PS. split; lia.
Qed.

End AS.

End W.
End HMWGRP.
