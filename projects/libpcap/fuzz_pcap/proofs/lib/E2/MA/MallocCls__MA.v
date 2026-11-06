(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool Lia.
From stdpp Require gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WAMeta__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WEnframe2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MSecret.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MallocCls.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres4. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WAMeta__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WGroup. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WEnframe2. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres4 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WAMeta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WAMeta2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_WTry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WTry2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WGroup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WAMeta__Spec.MI_WCreate2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WSlot2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WSlot3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_WEnframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WEnframe2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Bits OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Definition CORE_POSTc (st0 : mstate) (n : Z) (L : mled) (BL : list blk) (L1 : mled) (r : mstate * option (aptr * Z)) : Prop :=
  ld_live L1 = ld_live L /\ GP st0 (fst r) /\
  match snd r with
  | None => exists LS1, INVL x0 (fst r) L1 BL LS1
  | Some (g, idx) => exists LS1 bg, let st1 := fst r in
      hosts st1 bg g /\ 0 <= idx <= m_last_idx (MR st1 g)
      /\ INVL (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1
      /\ n + IB <= get_stride (MR st1 g) /\ TF2 st1 /\ get_stride (MR st1 g) - IB - n < 2 ^ 32
      /\ exists sc, m_sizeclass (MR st1 g) = sc /\ (size_to_class n = sc \/ size_to_class n = sc - 1)
                    /\ (sc < 28 -> UNIT * size_class sc <= get_stride (MR st1 g))
  end.

Section CORE.
Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr) (n : Z).
Hypothesis INV : INVL x0 st L BL LS.
Hypothesis TF : TF0 st.
Hypothesis Hn : 0 <= n.

(* [comment removed for export] *)
#[using="LS INV TF Hn"] Lemma malloc_small_ft_cls : n < MMAP_THRESHOLD ->
  ftree L (malloc_small_ctrl full_lay st n (fun st1 r => ret (st1, r)) (ret (st, @None (aptr * Z)))) (CORE_POSTc st n L BL).
Proof.
  intros Hlt. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT].
  unfold malloc_small_ctrl.
  set (sc0 := size_to_class n) in *.
  set (sc := match active st sc0 with Some _ => sc0 | None => _ end).
  assert (SC' : (0 <= sc < 48 /\ n + IB <= UNIT * size_class sc) /\ (size_to_class n = sc \/ size_to_class n = sc - 1)).
  { subst sc. destruct (active st sc0); [auto|].
    destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| auto].
    match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [| auto].
    apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    rewrite (lor1_even sc0 ltac:(lia) EV). split; [| right; lia]. split; [lia|].
    pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *. lia. }
  clearbody sc. destruct SC' as [[SC' FIT'] SCREL].
  destruct (active st sc) as [gp|] eqn:HA.
  - (* [comment removed for export] *)
    destruct (Z.eqb_spec (m_avail (get_meta_rec st gp)) 0) as [AZ|ANZ].
    + rewrite AZ. change (lowbit 0) with 0. cbn [negb Z.eqb].
      (* [comment removed for export] *)
      apply (alloc_slot_ft (mstate * option (aptr * Z)) (CORE_POSTc st n L BL) FUEL sc [] st L BL LS n); try assumption.
      * unfold FUEL. cbn. lia.
      * apply NoDup_nil_2.
      * intros st1 idx L1 LS1 (ACT & LIVE & GP1 & RES). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
        -- cbn [ftree ret]. unfold CORE_POSTc. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. exists LS1. exact INV1.
        -- replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POSTc. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|].
           exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
           split; [pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)); unfold IB; lia|].
           exists sc. split; [exact SCg|]. split; [exact SCREL|]. intros Hs28. rewrite (STR1 Hs28). lia.
    + (* [comment removed for export] *)
      destruct (hd_facts x0 st L BL LS sc gp INV HA) as (_ & Esc & bm & ai & Hbm).
      pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm) as GO.
      pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0. fold (MR st gp) in ANZ |- *.
      destruct (lowbit_idiom (m_avail (MR st gp)) ltac:(lia)) as (k & Hk & LB & CTZ & TB & _).
      assert (LNZ : (lowbit (m_avail (MR st gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
      rewrite LNZ. cbn [negb ftree ret]. unfold CORE_POSTc. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_eq; reflexivity|].
      pose proof (ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Esc; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ) as (INV1 & Hidx & _ & _ & STR).
      set (st1 := upd_meta gp (m_set_avail (m_avail (MR st gp) - lowbit (m_avail (MR st gp)))) st) in *.
      assert (MR1 : forall x, x <> gp -> MR st1 x = MR st x) by (intros x NE; unfold st1, MR; apply get_meta_rec_upd_other; exact NE).
      assert (MRg : m_last_idx (MR st1 gp) = m_last_idx (MR st gp) /\ get_stride (MR st1 gp) = get_stride (MR st gp) /\ (forall i, sstart (MR st1 gp) i = sstart (MR st gp) i) /\ m_sizeclass (MR st1 gp) = m_sizeclass (MR st gp)).
      { unfold st1, MR. rewrite get_meta_rec_upd_same. destruct (get_meta_rec st gp); cbn; repeat split; reflexivity. }
      destruct MRg as (ML & MS & MSS & MSC).
      exists LS, bm. rewrite ML, MS, MSS. split; [exists ai; exact Hbm|]. split; [exact Hidx|]. split; [exact INV1|].
      rewrite Esc in STR. split; [lia|].
      split; [apply TF0_TF2; apply (TF0_ctrl st st1); [reflexivity| reflexivity| exact TF]|].
      split; [pose proof (small_stride _ _ _ _ _ bm gp INV (ex_intro _ ai Hbm) ltac:(lia)); unfold IB; lia|].
      exists sc. rewrite MSC. split; [exact Esc|]. split; [exact SCREL|]. intros _. exact STR.
  - (* [comment removed for export] *)
    change (lowbit 0) with 0. cbn [negb Z.eqb].
    apply (alloc_slot_ft (mstate * option (aptr * Z)) (CORE_POSTc st n L BL) FUEL sc [] st L BL LS n); try assumption.
    + unfold FUEL. cbn. lia.
    + apply NoDup_nil_2.
    + intros st1 idx L1 LS1 (ACT & LIVE & GP1 & RES). destruct RES as [(-> & INV1 & TF1)|(g & bg & ai & Hidx & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)].
      * cbn [ftree ret]. unfold CORE_POSTc. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. exists LS1. exact INV1.
      * replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1. cbn [ftree ret]. unfold CORE_POSTc. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|].
        exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
        split; [pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)); unfold IB; lia|].
        exists sc. split; [exact SCg|]. split; [exact SCREL|]. intros Hs28. rewrite (STR1 Hs28). lia.
Qed.


End CORE.

(* [comment removed for export] *)
#[using="Type"] Theorem malloc_ft_cls st L BL LS n :
  INVL x0 st L BL LS -> 0 <= n < MMAP_THRESHOLD ->
  ftree L (malloc st n) (fun L' r =>
    match snd r with
    | None => True
    | Some p => exists c off g idx sc LS', p = aadd c (UNIT * off) /\ 0 <= off <= 255
        /\ INVL x0 (fst r) L' (((c, off), n) :: BL) LS'
        /\ s_slots (fst r) !! c = Some (g, idx)
        /\ m_sizeclass (MR (fst r) g) = sc /\ (size_to_class n = sc \/ size_to_class n = sc - 1)
        /\ (sc < 28 -> UNIT * size_class sc <= get_stride (MR (fst r) g))
    end).
Proof.
  intros INV Hn. unfold malloc.
  set (st0 := set_tick (N.succ (s_tick st)) st).
  assert (INV0 : INVL x0 st0 L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV]).
  assert (TF0' : TF0 st0) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV)| cbn; lia]).
  assert (CORE : ftree L (malloc_core full_lay st0 n) (CORE_POSTc st0 n L BL)).
  { unfold malloc_core. destruct (size_overflows n) eqn:Hov.
    - cbn [ftree ret]. unfold CORE_POSTc. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_refl|]. exists LS. exact INV0.
    - destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hbig|Hsmall]; [lia|]. exact (malloc_small_ft_cls st0 L BL LS n INV0 TF0' ltac:(lia) Hsmall). }
  eapply ftree_bind; [exact CORE|].
  intros L1 [st1 r] (LIVE & GP1 & RES). cbn [fst snd] in RES, GP1 |- *.
  destruct r as [[g idx]|].
  - destruct RES as (LS1 & bg & Hg & Hidx & INV1 & FIT & TF1 & RES32 & sc & SCg & SCREL & STR).
    apply (enframe_ft (xpend x0 (Some (fst bg, sstart (MR st1 g) idx))) st1 L1 BL LS1 g bg idx n INV1 Hg Hidx eq_refl ltac:(lia) FIT TF1 RES32).
    intros off st' Ho Hf INV' CE TK. cbn [fst snd].
    exists (fst bg, sstart (MR st1 g) idx), off, g, idx, sc, LS1. split; [reflexivity|]. split; [exact Ho|]. split; [exact INV'|].
    assert (MRE : MR st' g = MR st1 g) by (apply MR_ext; exact (ce_metas _ _ CE)).
    rewrite MRE. split; [| split; [exact SCg| split; [exact SCREL| exact STR]]].
    rewrite (ce_slots _ _ CE).
    pose proof (is_total _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1)))))) bg g idx Hg Hidx) as SL.
    rewrite slot_start'_sstart in SL. rewrite (hosts_gbase _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ Hg) in SL. exact SL.
  - cbn [ftree ret fst snd]. exact I.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stc_le26_true : forallb (fun k => stc_k k <=? 26) (zrange 0 204) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma size_to_class_le26 n : 0 <= n <= 3260 -> size_to_class n <= 26.
Proof.
  intros Hn. rewrite size_to_class_k. rewrite Z.shiftr_div_pow2 by lia. unfold IB in *.
  set (k := (n + 4 - 1) / 2 ^ 4).
  assert (Hk : 0 <= k < 204) by (subst k; change (2 ^ 4) with 16; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  pose proof (forallb_zrange (fun k => stc_k k <=? 26) 0 204 k stc_le26_true ltac:(lia) ltac:(lia)) as H. cbn beta in H.
  apply Z.leb_le in H. exact H.
Qed.

End WithCeil.
End MallocCls.

(* [comment removed for export] *)
Module MallocReS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2 MI_WGroup. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WEnframe2 MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WNtf2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Pres1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WGroup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_WEnframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WEnframe2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WNtf2__Spec.MI_WNtf2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Stable OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.MI_Realloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Realloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Realloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KPin__Spec.LB_WRealloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
(* [comment removed for export] *) Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_cheap_cleanup ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_split_ranges; OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_spec_trivial.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope stree_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
#[using="Type"] Lemma ftree_aleaf {R} (t : M R) (P : mled -> R -> Prop) (Q : R -> Prop) : forall L,
  ftree L t P -> aleaf Q t -> ftree L t (fun L' r => P L' r /\ Q r).
Proof.
  induction t as [r|e k IH]; intros L FT AL; cbn [ftree aleaf] in *; [split; assumption|].
  destruct e; try (destruct FT as [He Hk]; split; [exact He|]; intros a; specialize (Hk a);
    case_ans; [apply IH; [exact Hk| apply AL]| exact Hk]).
  - intros v Hv. apply IH; [apply FT; exact Hv| apply AL].
  - destruct FT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Secret.
Let SP (st : mstate) := fun st' : mstate => s_secret st' = s_secret st.

#[using="Type"] Lemma queue_aleaf_s {R} (P : R -> Prop) h m st (k : mstate -> M R) bail :
  (forall st', s_secret st' = s_secret st -> aleaf P (k st')) -> aleaf P (queue h m st k bail).
Proof.
  intros Hk. unfold queue. apply aleaf_guard, aleaf_guard.
  destruct (get_head st h) as [hd|]; [destruct (m_prev (get_meta_rec st hd))|]; apply Hk; (destruct h; reflexivity).
Qed.

#[using="Type"] Lemma free_meta_aleaf_s {R} (P : R -> Prop) m st (k : mstate -> M R) bail :
  (forall st', s_secret st' = s_secret st -> aleaf P (k st')) -> aleaf P (free_meta m st k bail).
Proof. intros Hk. unfold free_meta. apply queue_aleaf_s. intros st' E. apply Hk. rewrite E. reflexivity. Qed.

#[using="Type"] Lemma activate_group_aleaf_s {R} (P : R -> Prop) m st (k : mstate -> Z -> M R) bail :
  (forall st' z, s_secret st' = s_secret st -> aleaf P (k st' z)) -> aleaf P (activate_group m st k bail).
Proof. intros Hk. unfold activate_group. apply aleaf_guard. apply Hk. reflexivity. Qed.

#[using="Type"] Lemma free_group_aleaf_s {R} (P : R -> Prop) (rec : mstate -> aptr -> Z -> (mstate -> mapinfo -> M R) -> M R -> M R) st g (k : mstate -> mapinfo -> M R) bail :
  (forall st1 m i k1 bail1, (forall st' mi, s_secret st' = s_secret st1 -> aleaf P (k1 st' mi)) -> aleaf P (rec st1 m i k1 bail1)) ->
  (forall st' mi, s_secret st' = s_secret st -> aleaf P (k st' mi)) ->
  aleaf P (free_group R (@dec_hdr R) rec st g k bail).
Proof.
  intros Hrec Hk. unfold free_group.
  set (st1 := if m_sizeclass (get_meta_rec st g) <? 48 then _ else _).
  assert (E1 : s_secret st1 = s_secret st) by (subst st1; destruct (_ <? 48); reflexivity).
  destruct (m_mem _) as [p|]; [| exact I].
  destruct (negb (m_maplen _ =? 0)).
  - apply free_meta_aleaf_s. intros st' E'. apply Hk. rewrite E', s_secret_record_seq, s_secret_step_seq, s_secret_del_slots. unfold del_group. rewrite s_secret_set_groups. exact E1.
  - apply dec_hdr_aleaf. intros m idx. apply Hrec. intros st3 mi E3. apply free_meta_aleaf_s. intros st4 E4. apply Hk.
    rewrite E4, E3, s_secret_del_slots. unfold del_group. rewrite s_secret_set_groups. exact E1.
Qed.

#[using="Type"] Lemma nontrivial_free_aleaf_s {R} (P : R -> Prop) : forall fuel st g i (k : mstate -> mapinfo -> M R) bail,
  (forall st' mi, s_secret st' = s_secret st -> aleaf P (k st' mi)) -> aleaf P (nontrivial_free (@dec_hdr R) fuel st g i k bail).
Proof.
  induction fuel as [|f IH]; intros st g i k bail Hk; cbn [nontrivial_free]; [exact I|].
  match goal with |- aleaf P (if ?c then _ else _) => destruct c end.
  - assert (FG : forall st', s_secret st' = s_secret st -> aleaf P (free_group R (@dec_hdr R) (nontrivial_free (@dec_hdr R) f) st' g k bail)).
    { intros st' E'. apply free_group_aleaf_s; [intros; apply IH; assumption|]. intros st'' mi E''. apply Hk. congruence. }
    destruct (m_next _); [| apply FG; reflexivity]. apply aleaf_guard.
    destruct (optr_eqb _ _); [| apply FG; apply s_secret_dequeue]. destruct (active _ _); [| apply FG; apply s_secret_dequeue].
    apply activate_group_aleaf_s. intros st' z E'. apply FG. rewrite E'. apply s_secret_dequeue.
  - destruct (_ =? 0); [| apply Hk; apply s_secret_upd_meta]. apply aleaf_guard.
    destruct (negb _); [| apply Hk; apply s_secret_upd_meta].
    apply queue_aleaf_s. intros st' E'. apply Hk. rewrite s_secret_upd_meta. exact E'.
Qed.

#[using="Type"] Theorem free_secret st p : aleaf (fun st' => s_secret st' = s_secret st) (free st (Some p)).
Proof.
  unfold free. eapply aleaf_bind with (P := fun r => match r with Some (st1, _, _) => s_secret st1 = s_secret st | None => True end).
  { unfold free_hdr. apply get_meta_aleaf. intros m off idx. destruct (slot_start _ _); [| exact I].
    apply get_nominal_size_aleaf. intros v. cbn. reflexivity. }
  intros [[[st1 g] idx]|] E1; [| reflexivity].
  unfold free_tail. apply aleaf_guard. destruct (negb _).
  { cbn. try rewrite s_secret_upd_meta. exact E1. }
  apply nontrivial_free_aleaf_s. intros st2 [[base len]|] E2.
  - destruct (negb (len =? 0)).
    + cbn. intros z. destruct (munmap_answer_ok z); [| exact I]. cbn. try rewrite s_secret_drop_region. congruence.
    + cbn. congruence.
  - cbn. congruence.
Qed.
End Secret.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition realloc_postS (st : mstate) (BL : list blk) (c : cptr) (n' : Z) (L' : mled) (r : mstate * optr) : Prop :=
  realloc_post st BL c n' L' r
  /\ cstable st (match snd r with None => BL | Some _ => bl_remove c BL end) (fst r)
  /\ s_secret (fst r) = s_secret st.

#[using="Type"] Lemma realloc_postS_ctrl st0 st BL c n' L' r : ctrl_eq st0 st -> realloc_postS st BL c n' L' r -> realloc_postS st0 BL c n' L' r.
Proof.
  intros CE (A & C & S). split; [exact A|]. split.
  - eapply cstable_trans; [apply cstable_ctrl; exact CE| exact C].
  - rewrite S. exact (ce_secret _ _ CE).
Qed.

#[using="Type"] Lemma fallback_ftS st L BL LS c off n n' :
  INVL x0 st L BL LS -> In ((c, off), n) BL -> 0 <= n' ->
  ftree L ('(st2, q) <-- malloc st n' ;;
           match q with
           | None => ret (st2, None)
           | Some q => st3 <-- free st2 (Some (aadd c (UNIT * off))) ;; ret (st3, Some q)
           end)
        (realloc_postS st BL c n').
Proof.
  intros INV Hk Hn'.
  eapply ftree_bind; [exact (malloc_INVL st L BL LS n' INV Hn')|].
  intros L1 [st2 [q|]] (LIVE & GP1 & RES); cbn [fst snd] in RES.
  - destruct RES as (c' & off' & LS1 & Eq & Hoff & INV1 & Hni).
    assert (NE : c' <> c) by (intros ->; apply Hni; change c with (bslot ((c, off), n)); apply in_map; exact Hk).
    eapply ftree_bind.
    { apply ftree_aleaf; [apply ftree_aleaf; [exact (free_INVL_closed st2 L1 (((c', off'), n') :: BL) LS1 c off n INV1 ltac:(right; exact Hk))| apply free_regions]| apply free_secret]. }
    intros L2 st3 [[[LS2 INV2] RS] SE3]. cbn beta in RS, SE3. apply ftree_ret. unfold realloc_postS, realloc_post. cbn [fst snd].
    rewrite (bl_remove_cons_ne c c' off' n' BL NE) in INV2.
    split; [exists c', off', LS2; split; [exact Eq|]; split; [exact Hoff|]; split; [exact INV2| right; exact Hni]|].
    split.
    + eapply cstable_trans.
      * eapply cstable_sub; [exact (cstable_GP x0 st L BL LS st2 INV GP1)| intros k Hk0; exact (In_bl_remove_w _ _ _ Hk0)].
      * eapply (cstable_rsub x0 st2 L2 _ LS2 st3 _ INV2 RS). intros k Hk0. right. exact Hk0.
    + rewrite SE3. exact (proj2 GP1).
  - destruct RES as (LS1 & INV1). apply ftree_ret. unfold realloc_postS, realloc_post. cbn [fst snd].
    split; [exists LS1; exact INV1|]. split; [exact (cstable_GP x0 st L BL LS st2 INV GP1)| exact (proj2 GP1)].
Qed.

#[using="Type"] Theorem realloc_ftS st0 L BL LS c off n n' :
  INVL x0 st0 L BL LS -> In ((c, off), n) BL -> 0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX ->
  ftree L (realloc st0 (Some (aadd c (UNIT * off))) n') (realloc_postS st0 BL c n').
Proof.
  intros INV0 Hk Hn' Hov Hnx.
  set (st := set_tick (N.succ (s_tick st0)) st0).
  assert (CE0 : ctrl_eq st0 st) by apply ctrl_eq_set_tick.
  assert (INV : INVL x0 st L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV0]).
  assert (TF : TF0 st) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV0)| cbn; lia]).
  apply (ftree_mono _ _ (fun L' r => realloc_postS_ctrl st0 st BL c n' L' r CE0)).
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  rewrite (realloc_eq st0 c off n m bm i ai a ar ka n' BF Hov). fold st.
  assert (MRE : MR st m = MR st0 m) by reflexivity.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 _]. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Ho.
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hg.
  pose proof (ip_ea_snd st c off m bm i (gbase_bm st c off n m bm i ai a ar ka BF) (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) n') as EAS. cbn zeta in EAS.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  unfold realloc_body.
  match goal with |- ftree _ (if ?cnd then _ else _) _ => destruct cnd eqn:EC end.
  - (* [comment removed for export] *)
    apply andb_prop in EC as [EC E3]. apply andb_prop in EC as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Z.leb_le in E3.
    rewrite EAS in E1. cbn [aadd snd] in E1.
    assert (Hsc : m_sizeclass (MR st m) < 48).
    { pose proof (size_to_class_ok n' ltac:(lia)) as [ST _]. destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(H48 & _)|H63]; lia. }
    pose proof (stride_small x0 st L BL LS c off n m bm i ai a ar ka INV BF Hsc) as SS.
    set (stX := havoc _ n' (set_size _ _ n' i st)).
    assert (CEX : ctrl_eq st stX) by (eapply ctrl_eq_trans; [apply ctrl_eq_set_size| apply ctrl_eq_havoc]).
    apply ftree_ret. unfold realloc_postS, realloc_post. cbn [fst snd]. split; [| split; [apply cstable_ctrl; exact CEX| exact (ce_secret _ _ CEX)]].
    exists c, off, LS. split; [reflexivity|]. split; [exact Ho|]. split; [| left; reflexivity].
    apply (inplace_INVL x0 st L BL LS c off n m bm i ai a ar ka INV eq_refl Hk BF TF n' Hn'); unfold IB, UNIT in *; lia.
  - match goal with |- ftree _ (if ?cnd then _ else _) _ => destruct cnd eqn:EB end.
    + (* [comment removed for export] *)
      apply andb_prop in EB as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
      assert (H63 : m_sizeclass (MR st m) = 63) by (destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(H48 & _)|H]; [lia| exact H]).
      apply ftree_guard; [apply Z.eqb_eq; exact H63|].
      rewrite (start_eq st c off n m bm i ai a ar ka BF). cbn [aadd fst snd].
      replace (snd c + UNIT * off - snd c) with (UNIT * off) by lia.
      destruct (b_facts st L BL LS c off n m bm i ai a ar ka INV BF H63 n') as (L0 & ML & NL & I0).
      destruct (b_region st L BL LS c off n m bm i ai a ar ka INV BF H63 n') as (r & Hr & KG & OL).
      pose proof (needed_facts st c off n m bm i ai a ar ka BF n' B2 Hov Hnx) as (NF & NM & NP & NX). cbv zeta in NF, NM, NP, NX.
      set (needed := round_up_pg (n' + UNIT * off + UNIT + IB)) in *.
      set (oldlen := m_maplen (MR st m) * 4096) in *.
      assert (Ebase : conc st (fst c, 0) = r_base r) by (rewrite (conc_eq st (fst c, 0) r Hr); cbn; lia).
      rewrite Ebase.
      pose proof (ir_shape _ _ _ IR _ _ Hr) as (RS1 & RS2 & RS3 & RS4 & RS5 & _).
      destruct (Z.eqb_spec oldlen needed) as [EQ|NEQ].
      * set (stX := resize63 st (fst c) needed _ n' i).
        assert (CEX : ctrl_eq st stX) by apply ctrl_eq_resize63.
        apply ftree_ret. unfold realloc_postS, realloc_post. cbn [fst snd]. split; [| split; [apply cstable_ctrl; exact CEX| exact (ce_secret _ _ CEX)]].
        exists c, off, LS. split; [reflexivity|]. split; [exact Ho|]. split; [| left; reflexivity].
        exact (resize63_INVL st L BL LS c off n m bm i ai a ar ka INV Hk BF H63 TF n' B2 Hov Hnx EQ).
      * cbn [ftree is_peek is_undef]. split.
        -- (* [comment removed for export] *)
           split; [exact (brk_quiet_of _ _ _ IR)|]. split; [exists (r_len r); split; [exact (group_region_in_ledger _ _ _ _ _ IR Hr KG)| symmetry; exact OL]|].
           split; [split; [unfold PGSZ in NP; lia| exact NX]|]. split; [exact NM| exact NEQ].
        -- intros z. cbn [answer_ok]. rewrite (mremap_answer_ok_eq x0 st L IR (fst c) r Hr KG oldlen needed z).
           destruct (mremap_answer_ok st (fst c) (r_base r) oldlen needed z) eqn:OK; cbn [negb]; [| exact I].
           cbn [event_post]. destruct (is_err z) eqn:ERR.
           ++ apply (fallback_ftS st L BL LS c off n n' INV Hk Hn').
           ++ (* [comment removed for export] *)
              pose proof OK as OKz. unfold mremap_answer_ok in OK. rewrite (is_err_false_not_errno z ERR) in OK. cbn [orb] in OK.
              assert (PLACE : (0 < z /\ z mod PGSZ = 0 /\ z + needed <= alloc_ceiling)
                      /\ (forall rid' r', s_regions st !! rid' = Some r' -> rid' <> fst c -> let '(b', l') := region_live_range r' in z + needed <= b' \/ b' + l' <= z)).
              { split.
                ** apply Bool.orb_true_iff in OK. destruct OK as [OK1|OK1].
                   +++ apply andb_prop in OK1 as [Ez OK1]. apply Z.eqb_eq in Ez. subst z. split; [lia|]. split; [exact RS2|].
                       apply Bool.orb_true_iff in OK1. destruct OK1 as [LE|OK1]; [apply Z.leb_le in LE; rewrite OL in *; fold needed in LE |- *; lia|].
                       apply andb_prop in OK1 as [CE1 _]. apply Z.leb_le in CE1. exact CE1.
                   +++ apply andb_prop in OK1 as [OK1 RFz]. apply andb_prop in OK1 as [OK1 CE1]. apply andb_prop in OK1 as [OK1 AL]. apply andb_prop in OK1 as [NEz POS].
                       apply Z.ltb_lt in POS. apply Z.eqb_eq in AL. apply Z.leb_le in CE1. repeat split; assumption.
                ** intros rid' r' Hr' NE'. apply Bool.orb_true_iff in OK. destruct OK as [OK1|OK1].
                   +++ apply andb_prop in OK1 as [Ez OK1]. apply Z.eqb_eq in Ez. subst z.
                       pose proof (ir_disj _ _ _ IR (fst c) rid' r r' Hr Hr' ltac:(congruence)) as D. unfold region_live_range at 1 in D. rewrite KG in D. rewrite <- OL in D.
                       destruct (region_live_range r') as [b' l'] eqn:ER.
                       apply Bool.orb_true_iff in OK1. destruct OK1 as [LE|OK1]; [apply Z.leb_le in LE; lia|].
                       apply andb_prop in OK1 as [_ RF]. pose proof (ranges_free_regions_wo st (fst c) _ _ rid' r' RF Hr' NE') as D2. rewrite ER in D2.
                       pose proof (region_live_range_pos x0 st L rid' r' IR Hr') as P2. rewrite ER in P2. lia.
                   +++ apply andb_prop in OK1 as [OK1 RFz]. pose proof (ranges_free_regions st _ _ rid' r' RFz Hr') as D2. destruct (region_live_range r') as [b' l']. exact D2. }
              destruct PLACE as [PL1 DISJ].
              (* [comment removed for export] *)
              set (st' := wr8 (fst c, needed - IB) 0 (upd_meta m (fun rg => m_set_maplen (needed / 4096) rg) (upd_region (fst c) (fun rg => mkRegion (r_kind rg) z needed) st))).
              set (stX := big_resize st m (fst c) z needed _ n' i).
              assert (EX : stX = resize63 (upd_meta m (m_set_maplen (needed / 4096)) (upd_region (fst c) (fun rg => mkRegion (r_kind rg) z needed) st)) (fst c) needed (aadd c (UNIT * off)) n' i) by reflexivity.
              assert (CEX : ctrl_eq st' stX).
              { rewrite EX. eapply ctrl_eq_trans; [apply ctrl_eq_sym; apply (ctrl_eq_wr8 _ (fst c, needed - IB) 0)| apply ctrl_eq_resize63]. }
              pose proof (b_c st L BL LS c off n m bm i ai a ar ka INV BF H63 n') as Ec. cbv zeta in Ec.
              pose proof (b_bm st L BL LS c off n m bm i ai a ar ka INV BF H63 n') as Ebm. cbv zeta in Ebm.
              assert (HNB : 0 < z /\ z mod PGSZ = 0) by (split; [exact (proj1 PL1)| exact (proj1 (proj2 PL1))]).
              assert (HND : PGSZ <= needed /\ needed mod PGSZ = 0 /\ needed < LEN_MAX /\ z + needed <= alloc_ceiling) by (repeat split; try assumption; exact (proj2 (proj2 PL1))).
              (* [comment removed for export] *)
              assert (INV1 : INVL (mkX [] [] (Some c) None None) st L (bl_remove c BL) LS).
              { change c with (bslot ((c, off), n)) at 1 2.
                apply (INVL_remove_block x0 st st L BL LS ((c, off), n) INV Hk eq_refl (ctrl_eq_refl st) eq_refl).
                - intros; reflexivity.
                - exact (DOMS_of _ _ _ _ _ INV).
                - exact (TKS_of _ _ _ _ _ INV). }
              assert (INV1c : INVL (mkX [] [] (Some (fst c, UNIT)) None None) st L (bl_remove c BL) LS) by (rewrite <- Ec; exact INV1).
              assert (Hg0 : s_groups st !! (fst c, 0) = Some (mkGhdr (Some m) ai)) by (rewrite <- Ebm; exact Hg).
              apply ftree_ret. unfold realloc_postS, realloc_post. cbn [fst snd]. split; [| split].
              ** exists c, off, LS. split; [reflexivity|]. split; [exact Ho|]. split; [| left; reflexivity].
                 exact (big_resize_INVL st L BL LS c off n m bm i ai a ar ka INV Hk BF H63 TF n' B2 Hov Hnx r Hr z PL1 DISJ).
              ** (* [comment removed for export] *)
                 intros k d Hk1. rewrite !conc_aadd. unfold get_region. rewrite (ce_regions _ _ CEX). unfold st'.
                 pose proof (is_blocks _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1c)))))) k Hk1) as (x & ix & Hsx & _).
                 destruct (blocks_other st L (bl_remove c BL) LS m (fst c) ai z needed INV1c Hg0 H63 HNB k x ix Hk1 Hsx) as [_ NEr].
                 rewrite (st'_region_other st m (fst c) r z needed Hr (fst (bslot k)) NEr). reflexivity.
              ** rewrite (ce_secret _ _ CEX). unfold st'. apply st'_secret.
    + apply (fallback_ftS st L BL LS c off n n' INV Hk Hn').
Qed.

End WithCeil.
End MallocReS.
