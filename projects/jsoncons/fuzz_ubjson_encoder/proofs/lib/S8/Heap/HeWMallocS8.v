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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Heap Require Import HeTreeS8 HeAbsS8 HeEmptyS8 HeWNtfS8 HeMetaS8 HeWSlotS8 HeWGrpS8.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMWMALLOC.
Context {RUNp : RunP}.

Lemma gok_fsub X st LS m b ai : group_ok X st LS m b ai -> fsub (fmask (MR st m)) (mask_upto (m_last_idx (MR st m))).
Proof.
  intros GO i Hi T. pose proof (g_masks _ _ _ _ _ _ GO) as (A0 & F0 & Ab & Fb & _ & _). pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  pose proof (g_li _ _ _ _ _ _ GO) as LI.
  unfold fmask in T. rewrite Z.lor_spec in T. apply Bool.orb_true_iff in T as [T|T].
  - pose proof (Ab i Hi T). rewrite testbit_mask_upto by lia. apply Z.leb_le. lia.
  - pose proof (Fb i Hi T). rewrite testbit_mask_upto by lia. apply Z.leb_le. lia.
Qed.

Section W.
Variables (st0 : mstate) (L0 : mled) (BL0 : list blk) (LS0 : lhead -> list aptr).
Hypothesis INV0 : INVC x0 st0 L0 BL0 LS0.
Hypothesis MA0 : MARITH st0.

Let CU0 : CURI st0 := CURI_of _ _ _ _ _ INV0.

Lemma MW_scal st LS N sc st' : MW st0 LS0 st LS N sc -> SCAL st st' ->
  MW st0 LS0 st' LS N sc /\ Phi st' = Phi st /\ Psi st' = Psi st /\ (forall x, MR st' x = MR st x) /\ (forall b x, hosts st' b x <-> hosts st b x).
Proof.
  intros W SC. pose proof W as [WA F1 F2 F3 F4 F5].
  destruct (MWA_scal st0 LS0 st LS N st' WA SC) as (WA' & PH & PS & MRe & HO).
  split; [| split; [exact PH| split; [exact PS| split; [exact MRe| exact HO]]]].
  constructor.
  - exact WA'.
  - intros m Hm. rewrite MRe. exact (F1 m Hm).
  - intros b m Hb Hc. destruct (F2 b m Hb Hc) as [E H]. rewrite MRe. split; [exact E| apply HO; exact H].
  - intros sc' Hc. destruct (F3 sc' Hc) as [E1 E2]. split; [| exact E2].
    change (active st' sc') with (get_head st' (LActive sc')). rewrite (sc_heads _ _ SC). exact E1.
  - intros sc' m Hm. destruct (F4 sc' m Hm) as [[b Hb] E]. rewrite MRe. split; [exists b; apply HO; exact Hb| exact E].
  - intros m Hm [b Hb]. apply (F5 m Hm). exists b. apply HO. exact Hb.
Qed.

Lemma MW_newgrp st LS N sc a len : MW st0 LS0 st LS N sc -> 0 < len ->
  let st' := fst (new_region RKGroup a len st) in
  MW st0 LS0 st' LS N sc /\ Phi st' = Phi st + mmap_len len /\ Psi st' = Psi st + 1 /\ (forall x, MR st' x = MR st x)
  /\ (forall b x, hosts st' b x <-> hosts st b x).
Proof.
  intros W Hl. pose proof W as [WA F1 F2 F3 F4 F5]. cbv zeta.
  destruct (MWA_newgrp st0 LS0 st LS N a len WA Hl) as (WA' & PH & PS & MRe & HO).
  split; [| split; [exact PH| split; [exact PS| split; [exact MRe| exact HO]]]].
  constructor.
  - exact WA'.
  - intros m Hm. rewrite MRe. exact (F1 m Hm).
  - intros b m Hb Hc. destruct (F2 b m Hb Hc) as [E H]. rewrite MRe. split; [exact E| apply HO; exact H].
  - intros sc' Hc. exact (F3 sc' Hc).
  - intros sc' m Hm. destruct (F4 sc' m Hm) as [[b Hb] E]. rewrite MRe. split; [exists b; apply HO; exact Hb| exact E].
  - intros m Hm [b Hb]. apply (F5 m Hm). exists b. apply HO. exact Hb.
Qed.

Definition MQ (nreq : Z) (c : Z) (n : nat) (r : mstate * option (aptr * Z)) : Prop :=
  match snd r with
  | None => True
  | Some (g, idx) => let st' := fst r in
      exists LS N bg, MWA st0 LS0 st' LS N /\ (forall m, In m N -> NEWG st' m)
        /\ c <= Phi st' - Phi st0 /\ Z.of_nat n <= Psi st' - Psi st0
        /\ hosts st' bg g /\ 0 <= idx <= m_last_idx (MR st' g)
        /\ ((m_sizeclass (MR st' g) < 48 /\ forall m, In m N -> m_sizeclass (MR st' m) < 48)
            \/ (m_sizeclass (MR st' g) = 63 /\ (idx = 0 /\ m_last_idx (MR st' g) = 0) /\ snd bg = 0 /\ m_mem (MR st' g) = Some bg /\ N = [g]
                /\ exists r, s_regions st' !! (fst bg) = Some r /\ r_kind r = RKGroup /\ r_len r = nreq + IB + UNIT))
  end.

Lemma hd0 sc gp : active st0 sc = Some gp ->
  In gp (LS0 (LActive sc)) /\ (exists bg ai, s_groups st0 !! bg = Some (mkGhdr (Some gp) ai) /\ group_ok x0 st0 LS0 gp bg ai) /\ m_sizeclass (MR st0 gp) = sc.
Proof.
  intros HA. pose proof INV0 as (IR & IA & IM & IL & IG & IS).
  pose proof (il_head _ _ IL (LActive sc)) as HH. change (get_head st0 (LActive sc)) with (active st0 sc) in HH. rewrite HA in HH.
  assert (Hin : In gp (LS0 (LActive sc))) by (destruct (LS0 (LActive sc)) as [|y r]; cbn in HH; [discriminate| injection HH as ->; left; reflexivity]).
  destruct (il_active _ _ IL sc gp Hin) as (_ & [bg [ai Hbg]] & Esc).
  split; [exact Hin|]. split; [exists bg, ai; split; [exact Hbg| exact (ig_ok _ _ _ IG _ _ _ Hbg)]| exact Esc].
Qed.

Lemma fast_ok sc gp : 0 <= sc < 48 -> active st0 sc = Some gp -> m_avail (MR st0 gp) <> 0 ->
  let mask := m_avail (MR st0 gp) in let first := lowbit mask in
  let st' := upd_meta gp (m_set_avail (mask - first)) st0 in
  MWA st0 LS0 st' LS0 [] /\ Phi st' = Phi st0 /\ Psi st' = Psi st0
  /\ (exists bg, hosts st' bg gp) /\ 0 <= ctz32 first <= m_last_idx (MR st' gp) /\ m_sizeclass (MR st' gp) = sc.
Proof.
  intros Hsc HA ANZ. cbv zeta. pose proof INV0 as (IR & IA & IM & IL & IG & IS).
  set (mask := m_avail (MR st0 gp)). set (st' := upd_meta gp (m_set_avail (mask - lowbit mask)) st0).
  pose proof (MW_init st0 L0 BL0 LS0 INV0 sc CU0 MA0) as W0.

  pose proof (il_head _ _ IL (LActive sc)) as HH. change (get_head st0 (LActive sc)) with (active st0 sc) in HH. rewrite HA in HH.
  assert (Hin : In gp (LS0 (LActive sc))) by (destruct (LS0 (LActive sc)) as [|y r]; cbn in HH; [discriminate| injection HH as ->; left; reflexivity]).
  destruct (il_active _ _ IL sc gp Hin) as (_ & [bg [ai Hbg]] & Esc).
  pose proof (ig_ok _ _ _ IG _ _ _ Hbg) as GO. pose proof (g_masks _ _ _ _ _ _ GO) as (A0 & F0 & Ab & Fb & _ & _).
  pose proof (g_ai _ _ _ _ _ _ GO) as AI.
  destruct (lowbit_idiom mask ltac:(unfold mask in *; lia)) as (kk & Hk & Elb & Ectz & Tk & Pos & Tsub).
  assert (MRm : MR st' gp = m_set_avail (mask - lowbit mask) (MR st0 gp)) by (unfold st', MR; apply get_meta_rec_upd_same).
  assert (MRo : forall x, x <> gp -> MR st' x = MR st0 x) by (intros x NE; unfold st', MR; apply get_meta_rec_upd_other; exact NE).
  assert (Pm : s_metas st0 !! gp <> None) by exact (g_present _ _ _ _ _ _ GO).
  assert (FS : fsub (fmask (MR st' gp)) (fmask (MR st0 gp))).
  { rewrite MRm. unfold fmask, m_set_avail. cbn. intros i Hi. rewrite !Z.lor_spec, Tsub by exact Hi. fold mask.
    destruct (Z.testbit mask i); cbn; [reflexivity| tauto]. }
  assert (HO : forall b m, hosts st' b m <-> hosts st0 b m) by (intros; apply hosts_ext; reflexivity).
  assert (MF : MFR st0 st').
  { constructor; try reflexivity. intros x. unfold st'. rewrite s_metas_upd_meta, lookup_insert_None.
    split; [intros [H _]; exact H| intros H; split; [exact H| intros <-; exact (Pm H)]]. }
  assert (W1 : MW st0 LS0 st' LS0 [] (sc + 1)).
  { apply (MW_step st0 LS0 st0 LS0 [] sc st' LS0 W0).
    - apply (lists_ok_links st0 st' LS0 (ma_lists _ _ _ _ _ (mw_a _ _ _ _ _ _ W0))); [intros h; unfold st'; apply get_head_upd_meta|].
      intros x. destruct (aptr_eqb_spec x gp) as [->|NE]; [rewrite MRm; split; reflexivity| rewrite (MRo x NE); split; reflexivity].
    - intros; reflexivity.
    - intros x Hx; exact Hx.
    - intros x. destruct (aptr_eqb_spec x gp) as [->|NE]; [| left; exact (MRo x NE)].
      right. split; [exact Hin|]. split; [rewrite MRm; apply GEOM_set_avail| exact FS].
    - exact HO.
    - exact MF.
    - intros sc' _. unfold st'. apply active_upd_meta.
    - reflexivity. }
  split; [exact (mw_a _ _ _ _ _ _ W1)|].
  split; [rewrite !Phi_regsum, (regsum_ext _ _ _ (mf_regions _ _ MF)); unfold brk_dead_w; rewrite (mf_brk _ _ MF); reflexivity|].
  split; [unfold Psi, nareas; rewrite !ngreg_regsum, (regsum_ext _ _ _ (mf_regions _ _ MF)), (mf_areas _ _ MF); reflexivity|].
  split; [exists bg; apply HO; exists ai; exact Hbg|].
  rewrite MRm. cbn [m_last_idx m_sizeclass m_set_avail]. rewrite Ectz. split; [| exact Esc].
  pose proof (Ab kk Hk Tk). lia.
Qed.

Lemma ms_walk nreq : 0 <= nreq < MMAP_THRESHOLD ->
  apw ecost (malloc_small_ctrl lay_none st0 nreq (fun st1 r => ret (st1, r)) (ret (st0, @None (aptr * Z)))) 0 0 (MQ nreq).
Proof.
  intros Hn. pose proof (size_to_class_ok nreq Hn) as [SC FIT].
  unfold malloc_small_ctrl.
  set (sc0 := size_to_class nreq) in *.
  set (sc := match active st0 sc0 with Some _ => sc0 | None => _ end).
  assert (SC' : 0 <= sc < 48 /\ nreq + IB <= UNIT * size_class sc).
  { subst sc. destruct (active st0 sc0); [auto|].
    destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st0 sc0 =? 0)) eqn:E; [| auto].
    match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [| auto].
    apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    rewrite (lor1_even sc0 ltac:(lia) EV). split; [lia|].
    pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia. }
  clearbody sc. destruct SC' as [SC' FIT'].

  match goal with |- context [alloc_slot ?l ?f ?s ?cl ?r ?kk ?b] =>
    assert (SLOT : apw ecost (alloc_slot l f s cl r kk b) 0 0 (MQ nreq)) end.
  { apply (as_walk st0 L0 BL0 LS0 INV0 _ (MQ nreq) FUEL sc st0 LS0 [] nreq _ _ 0 0%nat SC' (MW_init st0 L0 BL0 LS0 INV0 sc CU0 MA0) ltac:(lia) FIT').
    - intros st' LS' N' c' n' idx Hidx (SA & _ & _ & SN & SC2 & SN2) (g & bg & HA' & Hg & Hidx' & Esc) _.
      replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA'. apply apw_ret. unfold MQ. cbn [fst snd].
      exists LS', N', bg. split; [exact SA|]. split; [intros m Hm; exact (proj1 (SN m Hm ltac:(intros [])))|].
      split; [lia|]. split; [lia|]. split; [exact Hg|]. split; [exact Hidx'|]. left. rewrite Esc. split; [lia|].
      intros m Hm. exact (proj2 (SN m Hm ltac:(intros []))).
    - intros st' c' n'. change (-1 <? 0) with true. cbn iota. apply apw_ret. exact I. }
  destruct (active st0 sc) as [gp|] eqn:HA.
  - fold (MR st0 gp) in *. destruct (Z.eqb_spec (m_avail (MR st0 gp)) 0) as [AZ|ANZ].
    + rewrite AZ in *. change (lowbit 0) with 0 in *. cbn [negb Z.eqb] in *. exact SLOT.
    + destruct (fast_ok sc gp SC' HA ANZ) as (WA & PH & PS & [bg Hbg] & Hidx & Esc).
      destruct (hd0 sc gp HA) as (_ & (bg' & ai' & _ & GO) & _). pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0.
      destruct (lowbit_idiom (m_avail (MR st0 gp)) ltac:(lia)) as (kk & Hk & LB & _).
      assert (LNZ : (lowbit (m_avail (MR st0 gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 kk ltac:(lia) Hk); lia).
      rewrite LNZ. cbn [negb]. apply apw_ret. unfold MQ. cbn [fst snd].
      exists LS0, [], bg. split; [exact WA|]. split; [intros m []|]. split; [lia|]. split; [lia|]. split; [exact Hbg|]. split; [exact Hidx|]. left.
      split; [lia| intros m []].
  - change (lowbit 0) with 0 in *. cbn [negb Z.eqb] in *. exact SLOT.
Qed.

Lemma SCAL_step_seq st : SCAL st (step_seq st).
Proof.
  unfold step_seq. destruct (c_seq (ctx st) =? 255); (apply SCAL_ctx; intros; reflexivity).
Qed.

Lemma MWA_build st LS N m stF p ai :
  MWA st0 LS0 st LS N -> In m N -> PEND st LS m ->
  (forall x, s_metas stF !! x = None <-> s_metas st !! x = None) ->
  (forall x, x <> m -> MR stF x = MR st x) ->
  m_next (MR stF m) = m_next (MR st m) -> m_prev (MR stF m) = m_prev (MR st m) ->
  NEWG stF m ->
  s_groups stF = <[p := mkGhdr (Some m) ai]> (s_groups st) ->
  (forall s v, s_slots stF !! s = Some v -> s_slots st !! s = Some v \/ fst v = m) ->
  (forall h, get_head stF h = get_head st h) ->
  MFR st stF ->
  MWA st0 LS0 stF LS N /\ Phi stF = Phi st /\ Psi stF = Psi st /\ hosts stF p m /\ (forall b x, x <> m -> hosts stF b x -> hosts st b x).
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14] Hm (P1 & P2 & P3) KEYS0 MRo NX PV NG GR SL HD MF.
  assert (Pm : s_metas st !! m <> None) by exact (proj1 (proj2 (A7 m Hm))).
  assert (KEYS : forall x, s_metas stF !! x <> None <-> s_metas st !! x <> None) by (intros x; rewrite (KEYS0 x); tauto).
  assert (NM : nmeta stF = nmeta st) by exact (nmeta_keys _ _ KEYS0).
  assert (HOF : forall b x, hosts stF b x -> (b = p /\ x = m) \/ hosts st b x).
  { intros b x [ai' Hb]. rewrite GR in Hb. destruct (aptr_eqb_spec b p) as [->|NE].
    - rewrite lookup_insert_eq in Hb. injection Hb as -> _. left. split; reflexivity.
    - rewrite lookup_insert_ne in Hb by congruence. right. exists ai'. exact Hb. }
  assert (PHI : Phi stF = Phi st).
  { rewrite !Phi_regsum, (regsum_ext _ st stF (mf_regions _ _ MF)). unfold brk_dead_w. rewrite (mf_brk _ _ MF). reflexivity. }
  assert (PSI : Psi stF = Psi st).
  { unfold Psi, nareas. rewrite !ngreg_regsum, (regsum_ext _ st stF (mf_regions _ _ MF)), (mf_areas _ _ MF). reflexivity. }
  split; [| split; [exact PHI| split; [exact PSI| split]]].
  2:{ exists ai. rewrite GR, lookup_insert_eq. reflexivity. }
  2:{ intros b x NE Hb. destruct (HOF b x Hb) as [(_ & E)|H]; [congruence| exact H]. }
  constructor.
  - apply (lists_ok_links st stF LS A1 HD). intros x. destruct (aptr_eqb_spec x m) as [->|NE].
    + rewrite NX, PV. split; reflexivity.
    + rewrite (MRo x NE). split; reflexivity.
  - exact (CURI_frame _ _ A2 MF).
  - exact (MARITH_frame _ _ A3 MF).
  - rewrite NM. exact A4.
  - intros b x Hb. destruct (A5 b x Hb) as (N1 & G & F). assert (NE : x <> m) by (intros ->; exact (N1 Hm)).
    rewrite (MRo x NE). split; [exact N1| split; assumption].
  - intros b x Hb. destruct (HOF b x Hb) as [(_ & ->)|H]; [right; exact Hm| exact (A6 b x H)].
  - intros x Hx. destruct (A7 x Hx) as (N1 & Px & C). split; [exact N1|]. split; [apply KEYS; exact Px|].
    destruct (aptr_eqb_spec x m) as [->|NE]; [left; exact NG|].
    destruct C as [C|C].
    + left. apply (NEWG_data st); [rewrite (MRo x NE); reflexivity| exact C].
    + right. apply (PEND_move st LS); [rewrite (MRo x NE); reflexivity| | auto| exact C].
      intros b Hb. destruct (HOF b x Hb) as [(_ & E)|H]; [congruence| exact H].
  - exact A8.
  - intros x Hx. apply A9. apply KEYS. exact Hx.
  - intros x Hx. apply KEYS. exact (A10 x Hx).
  - rewrite NM. exact A11.
  - intros rid r H K. rewrite (mf_regions _ _ MF). exact (A12 rid r H K).
  - rewrite (mf_rid _ _ MF). exact A13.
  - intros s0 v Hs. destruct (SL s0 v Hs) as [H|H]; [exact (A14 s0 v H)| right; rewrite H; exact Hm].
Qed.

Lemma create63 st LS N g rid needed ai :
  MWA st0 LS0 st LS N -> In g N -> PEND st LS g ->
  let F := fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
             (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr)))))) in
  let st4 := upd_meta g F st in
  let st5 := put_group (rid, 0) (Some g) ai st4 in
  let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
  let st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6 in
  MWA st0 LS0 st7 LS N /\ NEWG st7 g /\ Phi st7 = Phi st /\ Psi st7 = Psi st /\ hosts st7 (rid, 0) g
  /\ m_sizeclass (MR st7 g) = 63 /\ m_last_idx (MR st7 g) = 0 /\ m_mem (MR st7 g) = Some (rid, 0) /\ s_regions st7 = s_regions st.
Proof.
  intros WA Hg PG. cbv zeta.
  set (F := fun mr => m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
             (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))).
  set (st4 := upd_meta g F st). set (st5 := put_group (rid, 0) (Some g) ai st4).
  set (st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5).
  set (st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6).
  assert (Pm : s_metas st !! g <> None) by exact (proj1 (proj2 (ma_new _ _ _ _ _ WA g Hg))).
  assert (MRg : MR st7 g = F (MR st g)).
  { unfold st7, st6, st5, st4, MR, get_meta_rec. autorewrite with mst. rewrite lookup_insert_eq. reflexivity. }
  assert (MRo : forall x, x <> g -> MR st7 x = MR st x).
  { intros x NE. unfold st7, st6, st5, st4, MR, get_meta_rec. autorewrite with mst. rewrite lookup_insert_ne by congruence. reflexivity. }
  assert (KEYS0 : forall x, s_metas st7 !! x = None <-> s_metas st !! x = None).
  { intros x. unfold st7, st6, st5, st4. autorewrite with mst. destruct (decide (x = g)) as [->|NE].
    - rewrite lookup_insert_eq. split; [discriminate| intros E; exfalso; exact (Pm E)].
    - rewrite lookup_insert_ne by congruence. reflexivity. }
  assert (Esc : m_sizeclass (MR st7 g) = 63) by (rewrite MRg; reflexivity).
  assert (Eli : m_last_idx (MR st7 g) = 0) by (rewrite MRg; reflexivity).
  assert (Emem : m_mem (MR st7 g) = Some (rid, 0)) by (rewrite MRg; reflexivity).
  assert (Efm : fmask (MR st7 g) = 0) by (rewrite MRg; reflexivity).
  assert (NG : NEWG st7 g).
  { unfold NEWG, gempty. rewrite Efm, Eli, Esc, Emem. split; [cbn; discriminate|]. split; [right; reflexivity|]. split; [discriminate|].
    intros i Hi T. rewrite Z.bits_0 in T. discriminate. }
  destruct (MWA_build st LS N g st7 (rid, 0) (Z.land ai 31) WA Hg PG KEYS0 MRo ltac:(rewrite MRg; reflexivity) ltac:(rewrite MRg; reflexivity) NG
              eq_refl ltac:(intros s0 v Hs; exact (add_slots_vals _ _ _ _ _ s0 v Hs)) ltac:(intros h; destruct h; reflexivity)
              ltac:(constructor; try reflexivity; exact KEYS0)) as (WA7 & PH & PS & HG & _).
  split; [exact WA7|]. split; [exact NG|]. split; [exact PH|]. split; [exact PS|]. split; [exact HG|].
  split; [exact Esc|]. split; [exact Eli|]. split; [exact Emem| reflexivity].
Qed.

Theorem core_walk nreq : 0 <= nreq -> apw ecost (malloc_core lay_none st0 nreq) 0 0 (MQ nreq).
Proof.
  intros Hn. unfold malloc_core.
  destruct (size_overflows nreq) eqn:Hov; [apply apw_ret; exact I|].
  destruct (Z.leb_spec MMAP_THRESHOLD nreq) as [Hbig|Hsmall]; [| exact (ms_walk nreq ltac:(lia))].
  unfold size_overflows in Hov. apply Z.leb_gt in Hov.
  set (needed := nreq + IB + UNIT).
  assert (HN : 131072 <= needed < 2 ^ 63 - 4000) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
  apply apw_vis. intros a. rewrite ecost_grp. cbn beta.
  destruct (negb (mmap_answer_ok (live_ranges st0) needed a)); [apply apw_bad|].
  destruct (is_err a); [apply apw_ret; exact I|].
  unfold new_region. cbv zeta. cbn iota.
  set (rid := s_next_rid st0).
  set (s1 := set_next_rid (N.succ rid) (set_regions (<[rid := mkRegion RKGroup a needed]> (s_regions st0)) st0)).
  pose proof (MW_init st0 L0 BL0 LS0 INV0 48 CU0 MA0) as W0.
  destruct (MW_newgrp st0 LS0 [] 48 a needed W0 ltac:(lia)) as (W1 & PH1 & PS1 & MR1 & HO1). fold rid s1 in W1, PH1, PS1, MR1, HO1.
  destruct (MW_scal s1 LS0 [] 48 (step_seq s1) W1 (SCAL_step_seq s1)) as (W2 & PH2 & PS2 & MR2 & HO2).
  assert (R2 : s_regions (step_seq s1) !! rid = Some (mkRegion RKGroup a needed)).
  { rewrite (mf_regions _ _ (sc_mfr _ _ (SCAL_step_seq s1))). unfold s1. autorewrite with mst. apply lookup_insert_eq. }
  pose proof W2 as [WA2 FD2 _ _ _ _].
  apply (am_walk _ (step_seq s1) LS0 _ _ (0 + mmap_len needed) 1%nat (MQ nreq)).
  { split; [exact (ma_curi _ _ _ _ _ WA2)| split; [exact (ma_marith _ _ _ _ _ WA2)| split; [exact (ma_lists _ _ _ _ _ WA2)| exact FD2]]]. }
  intros st3 LS3 mo c3 n3 AP. destruct mo as [g|].
  2:{ apply apw_vis. intros ru. destruct (munmap_answer_ok ru); [apply apw_ret; exact I| apply apw_bad]. }
  destruct (MW_am st0 L0 BL0 LS0 INV0 (step_seq s1) LS0 [] 48 st3 LS3 g _ _ W2 AP) as (W3 & PM & _ & _ & _).
  destruct (ap_cost _ _ _ _ _ _ _ AP ltac:(discriminate)) as [DC DN].
  assert (R3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (ap_regions _ _ _ _ _ _ _ AP); [exact R2| discriminate]).
  cbn beta iota zeta. change (lh_hdr lay_none ?s ?b) with s.
  lazymatch goal with |- context [put_group (rid, 0) (Some g) ?ai _] =>
    destruct (create63 st3 LS3 [g] g rid needed ai (mw_a _ _ _ _ _ _ W3) ltac:(left; reflexivity) PM)
      as (WA7 & NG7 & PH7 & PS7 & HG7 & SC7 & LI7 & MM7 & RG7) end.
  apply apw_ret. unfold MQ. cbn [fst snd].
  eexists LS3, [g], (rid, 0). split; [exact WA7|]. split; [intros m [<-|[]]; exact NG7|].
  split; [rewrite PH7; rewrite PH2, PH1 in DC; lia|]. split; [rewrite PS7; rewrite PS2, PS1 in DN; lia|].
  split; [exact HG7|]. split; [rewrite LI7; lia|].
  right. split; [exact SC7|]. split; [split; [reflexivity| exact LI7]|]. split; [reflexivity|]. split; [exact MM7|]. split; [reflexivity|].
  exists (mkRegion RKGroup a needed). rewrite RG7. split; [exact R3|]. split; reflexivity.
Qed.

End W.

Lemma MWA_strip st0 LS0 st LS N : MWA st0 LS0 st LS N -> MWA st0 LS0 (strip st) LS N.
Proof.
  intros [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14].
  assert (MF : MFR st (strip st)) by (constructor; try reflexivity; intros x; split; intros H; exact H).
  constructor.
  - apply (lists_ok_links st (strip st) LS A1); [intros h; destruct h; reflexivity| intros x; split; reflexivity].
  - exact (CURI_frame _ _ A2 MF).
  - exact (MARITH_frame _ _ A3 MF).
  - exact A4.
  - exact A5.
  - exact A6.
  - exact A7.
  - exact A8.
  - exact A9.
  - exact A10.
  - exact A11.
  - exact A12.
  - exact A13.
  - exact A14.
Qed.

Definition MQC (cs : mstate) (LS : lhead -> list aptr) (nreq c : Z) (n : nat) (r : mstate * option cptr) : Prop :=
  match snd r with
  | None => True
  | Some p => let cs' := fst r in
      exists LS' N g idx bg, MWA cs LS cs' LS' N /\ (forall m, In m N -> NEWG cs' m)
        /\ c <= Phi cs' - Phi cs /\ Z.of_nat n <= Psi cs' - Psi cs
        /\ p = slot_start' (MR cs' g) idx /\ hosts cs' bg g /\ 0 <= idx <= m_last_idx (MR cs' g)
        /\ ((m_sizeclass (MR cs' g) < 48 /\ forall m, In m N -> m_sizeclass (MR cs' m) < 48)
            \/ (m_sizeclass (MR cs' g) = 63 /\ (idx = 0 /\ m_last_idx (MR cs' g) = 0) /\ snd bg = 0 /\ m_mem (MR cs' g) = Some bg /\ N = [g]
                /\ exists r, s_regions cs' !! (fst bg) = Some r /\ r_kind r = RKGroup /\ r_len r = nreq + IB + UNIT))
  end.

Theorem cmalloc_walk cs L BL LS nreq : INVC x0 cs L BL LS -> MARITH cs -> 0 <= nreq ->
  apw ecost (cmalloc cs nreq) 0 0 (MQC cs LS nreq).
Proof.
  intros INV MA Hn. unfold cmalloc. eapply apw_bind; [exact (core_walk cs L BL LS INV MA nreq Hn)|].
  intros c' n' [st1 r] H. apply apw_ret. unfold MQ in H. unfold MQC. cbn [fst snd] in H |- *.
  destruct r as [[g idx]|]; [| exact I].
  destruct H as (LS' & N & bg & WA & NG & HC & HN & Hg & Hidx & CASES).
  exists LS', N, g, idx, bg. split; [apply MWA_strip; exact WA|]. split; [exact NG|]. split; [exact HC|]. split; [exact HN|].
  split; [reflexivity|]. split; [exact Hg|]. split; [exact Hidx|]. exact CASES.
Qed.

Theorem malloc_end cs L BL LS nreq c n cs' p L' BL' LS' SZ :
  INVC x0 cs L BL LS -> EINV cs -> NLK cs -> L63 cs SZ -> (forall q k, In (q, k) SZ -> In q (map bslot BL)) ->
  MQC cs LS nreq c n (cs', Some p) -> INVC x0 cs' L' BL' LS' -> map bslot BL' = p :: map bslot BL ->
  EINV cs' /\ NLK cs' /\ L63 cs' ((p, nreq) :: SZ) /\ MARITH cs'
  /\ c <= Phi cs' - Phi cs /\ Z.of_nat n <= Psi cs' - Psi cs
  /\ (nmeta cs' = nmeta cs \/ LS' LFree = [])
  /\ (forall b m, hosts cs b m -> hosts cs' b m /\ GEOM (MR cs' m) = GEOM (MR cs m)).
Proof.
  intros INV E0 NL0 L630 SZB MQ0 INV' EBL. unfold MQC in MQ0. cbn [fst snd] in MQ0.
  destruct MQ0 as (LSw & N & g & idx & bg & WA & NG & HC & HN & Ep & Hg & Hidx & CASES).
  pose proof INV as (IR & IA & IM & IL & IG & IS). pose proof INV' as (IR' & IA' & IM' & IL' & IG' & IS').
  pose proof WA as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14].

  assert (ELS : forall h, LSw h = LS' h).
  { intros h. apply (dll_det cs'); [exact (lo_nodup _ _ A1 h)| exact (il_nodup _ _ IL' h)| exact (lo_dll _ _ A1 h)| exact (il_dll _ _ IL' h)|].
    rewrite <- (lo_head _ _ A1 h), <- (il_head _ _ IL' h). reflexivity. }

  assert (OLD : forall b m, hosts cs b m -> hosts cs' b m /\ GEOM (MR cs' m) = GEOM (MR cs m)).
  { intros b m Hb. destruct (A5 b m Hb) as (_ & G & _). split; [| exact G].
    apply GEOM_eq in G as (Gm & _). pose proof (hosts_mem x0 cs LS IM b m Hb) as Mm. rewrite <- Gm in Mm.
    destruct (im_group _ _ _ IM' m b Mm) as [H|[]]. exact H. }
  split.
  { apply (EINV_after cs cs' L BL LS (fun _ => False) INV E0); [| intros m1 m2 []].
    intros b m Hb He. destruct (A6 b m Hb) as [Hb0|HmN].
    - destruct (A5 b m Hb0) as (_ & G & F). split; [split; [exact Hb0| exact G]|]. left.
      destruct (hosts_ok x0 cs LS IG b m Hb0) as (ai & _ & GO).
      unfold gempty in He |- *. exact (gempty_fsub_mono _ _ G F (gok_fsub _ _ _ _ _ _ GO) He).
    - exfalso. exact (proj1 (NG m HmN) He). }
  split.
  { intros m Pm'. destruct (in_dec aptr_eq_dec m N) as [HmN|NmN]; [left; exact (proj1 (proj2 (proj2 (NG m HmN))))|].
    destruct (A9 m Pm') as [Pm0|HmN]; [| exfalso; exact (NmN HmN)].
    assert (HOSTED : forall b, hosts cs b m -> m_mem (MR cs' m) <> None).
    { intros b Hb. destruct (OLD b m Hb) as [Hb' _]. rewrite (hosts_mem x0 cs' LS' IM' b m Hb'). discriminate. }
    destruct (NL0 m Pm0) as [Mm|Nx].
    - left. destruct (m_mem (MR cs m)) as [b|] eqn:Em; [| exfalso; exact (Mm eq_refl)].
      destruct (im_group _ _ _ IM m b Em) as [Hb|[]]. exact (HOSTED b Hb).
    - destruct (proj2 (proj1 (il_link _ _ IL m)) Nx) as [h Hh]. destruct h as [sc|].
      + left. destruct (il_active _ _ IL sc m Hh) as (_ & [b Hb] & _). exact (HOSTED b Hb).
      + right. destruct A4 as (k & K1 & K2 & K3 & K4).
        rewrite <- (firstn_skipn k (LS LFree)) in Hh. apply in_app_iff in Hh as [Hh|Hh]; [exfalso; exact (NmN (K2 m Hh))|].
        rewrite <- K1 in Hh. apply (proj1 (proj1 (lo_link _ _ A1 m))). exists LFree. exact Hh. }
  split.
  { intros q k m i Hin Hsl Hsc. destruct Hin as [E|Hin].
    - injection E as <- <-. rewrite Ep in Hsl |- *.
      pose proof (is_total _ _ _ IS' bg g idx Hg Hidx) as Ht. rewrite Ht in Hsl. injection Hsl as <- <-.
      destruct CASES as [[SC _]|(SC & [-> LI] & Sb & Mm & _ & r & Hr & Hk & Hl)]; [lia|].
      exists r. unfold slot_start'. rewrite Mm. cbn [default fst aadd]. unfold aadd. cbn [fst]. split; [exact Hr| split; [exact Hk| exact Hl]].
    - destruct (A14 q (m, i) Hsl) as [Hsl0|HmN].
      + destruct (is_valid _ _ _ IS q m i Hsl0) as ([b Hb] & _ & _). destruct (A5 b m Hb) as (_ & G & _).
        apply GEOM_eq in G as (_ & _ & _ & Gs & _). rewrite Gs in Hsc.
        destruct (L630 q k m i Hin Hsl0 Hsc) as (r & Hr & Hk & Hl). exists r. split; [| split; [exact Hk| exact Hl]].
        apply A12; [exact Hr| rewrite Hk; discriminate].
      + cbn [fst] in HmN. exfalso. destruct CASES as [[_ SM]|(SC & [-> LI] & Sb & Mm & EN & _)]; [pose proof (SM m HmN); lia|].
        rewrite EN in HmN. destruct HmN as [<-|[]].
        destruct (is_valid _ _ _ IS' q g i Hsl) as (_ & Hi & Eq). rewrite LI in Hi. assert (i = 0) by lia. subst i.
        rewrite <- Ep in Eq. subst q.
        pose proof (is_nodup _ _ _ IS') as ND. rewrite EBL in ND. apply NoDup_cons in ND as [NI _]. apply NI. apply list_elem_of_In.
        exact (SZB p k Hin). }
  split; [exact A3|]. split; [exact HC|]. split; [exact HN|]. split; [rewrite <- (ELS LFree); exact A11| exact OLD].
Qed.

End HMWMALLOC.
