(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Arith MI_Geom MI_List MI_Ext MI_Shadow MI_Pres1 MI_Pres2 MI_Pres3 MI_Pres4 MI_WFree2 MI_WTry MI_WTry2 MI_WGroup.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_Bits.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec Require MI_TF2 MI_WAMeta MI_WAMeta2 MI_WCreate MI_WCreate2 MI_WSlot MI_WSlot2 MI_WMalloc MI_Ledger MI_Contracts MI_Bits MI_WEnframe MShapeA MShapeB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.KInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Tree OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Inv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Kit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Arith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Geom OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_List OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Ext OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Shadow OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Pres1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Pres2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Pres3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Pres4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WFree2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WTry OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WTry2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WGroup OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Bits.MI_Cnt OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_TF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WAMeta OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WAMeta2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WCreate OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WCreate2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WSlot OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WSlot2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WMalloc OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Ledger OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Contracts OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_Bits OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MI_WEnframe OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MShapeA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.MShapeB.
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

Definition eff_class (st : mstate) (n : Z) : Z :=
  let sc := size_to_class n in
  match active st sc with
  | Some _ => sc
  | None =>
    if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) then
      let usage1 := usage st (Z.lor sc 1) in
      let usage1 := match active st (Z.lor sc 1) with
                    | None => usage1 + 3
                    | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                    end in
      if usage1 <=? 12 then Z.lor sc 1 else sc
    else sc
  end.

Lemma eff_class_cases st n : 0 <= n < MMAP_THRESHOLD ->
  (eff_class st n = size_to_class n \/ (eff_class st n = size_to_class n + 1 /\ Z.even (size_to_class n) = true /\ 4 <= size_to_class n < 32))
  /\ 0 <= eff_class st n < 48 /\ n + IB <= UNIT * size_class (eff_class st n).
Proof.
  intros Hn. pose proof (size_to_class_ok n ltac:(lia)) as [SC FIT]. unfold eff_class.
  set (sc0 := size_to_class n) in *.
  destruct (active st sc0); [split; [left; reflexivity| auto]|].
  destruct ((4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6) && Z.even sc0 && (usage st sc0 =? 0)) eqn:E; [| split; [left; reflexivity| auto]].
  match goal with |- context [if ?c then Z.lor sc0 1 else sc0] => destruct c end; [| split; [left; reflexivity| auto]].
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E EV]. apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  rewrite (lor1_even sc0 ltac:(lia) EV).
  pose proof (size_class_lt sc0 (sc0 + 1) ltac:(lia) ltac:(lia) ltac:(lia)). unfold UNIT in *.
  split; [right; auto|]. split; lia.
Qed.

Lemma eff_class_strip st n : eff_class (strip st) n = eff_class st n.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CORE.
Let T := (mstate * option (aptr * Z))%type.

(* [comment removed for export] *)
Definition CSUCC (st : mstate) (n : Z) (L : mled) (BL : list blk) (L1 : mled) (C : Z -> Prop) (d sc : Z) (O : mstate -> aptr -> Z -> Prop) (u : M T) : Prop :=
  exists st1 g idx bg, u = SRet (st1, Some (g, idx))
    /\ CORE_POST st n L BL L1 (st1, Some (g, idx)) /\ AFR C d (Some g) st st1
    /\ hosts st1 bg g /\ m_sizeclass (MR st1 g) = sc /\ 0 <= idx <= m_last_idx (MR st1 g)
    /\ O st1 g (m_last_idx (MR st1 g)).

Definition CFAIL (st : mstate) (n : Z) (L : mled) (BL : list blk) (C : Z -> Prop) (d : Z) (u : M T) : Prop :=
  exists st1, u = SRet (st1, None) /\ CORE_POST st n L BL L (st1, None) /\ AFR C d None st st1.

Theorem malloc_small_shape st L BL LS n :
  INVL x0 st L BL LS -> TF0 st -> 0 <= n < MMAP_THRESHOLD -> (ZC (eff_class st n) st -> cost (eff_class st n) <= c_avail_meta_count (s_ctx st)) ->
  let sc := eff_class st n in
  let t := malloc_small_ctrl full_lay st n (fun st1 r => ret (st1, r)) (ret (st, @None (aptr * Z))) in
  CSUCC st n L BL L (chain sc) (cost sc) sc (OPURE sc st) t
  \/ exists len K, t = SVis (EMmap 0 len PROT_RW MAPF0) K
       /\ MM T (2^20) L len K (CFAIL st n L BL (chain sc) (cost sc)) (fun r => CSUCC st n L BL (KInv.set_groups ((r, len) :: ld_groups L) L) (chain sc) (cost sc) sc (OMMAP sc n st))
       /\ ZC sc st.
Proof.
  intros INV TF Hn HCNT. cps_pose (eff_class_cases st n Hn) as (_ & SC' & FIT').
  cbn zeta. unfold malloc_small_ctrl.
  assert (ESC : match active st (size_to_class n) with
                | Some _ => size_to_class n
                | None => if (4 <=? size_to_class n) && (size_to_class n <? 32) && negb (size_to_class n =? 6) && Z.even (size_to_class n) && (usage st (size_to_class n) =? 0)
                          then if match active st (Z.lor (size_to_class n) 1) with
                                  | Some _ => let ar := get_meta_rec st (default (0%N, -1) (active st (Z.lor (size_to_class n) 1))) in
                                              if (m_avail ar =? 0) && (m_freed ar =? 0) then usage st (Z.lor (size_to_class n) 1) + 3 else usage st (Z.lor (size_to_class n) 1)
                                  | None => usage st (Z.lor (size_to_class n) 1) + 3
                                  end <=? 12
                               then Z.lor (size_to_class n) 1 else size_to_class n
                          else size_to_class n
                end = eff_class st n) by reflexivity.
  rewrite ESC. set (sc := eff_class st n) in *. clearbody sc. destruct SC' as [SC0 SC1].
  pose proof (cost_range sc) as CR.
  assert (SLOT : forall K B,
    (forall st1 idx, K st1 idx = if idx <? 0 then SRet (st1, @None (aptr * Z)) else match active st1 sc with Some gp => SRet (st1, Some (gp, idx)) | None => SVis (EUndef UBadPtr) (fun _ => B) end) ->
    CSUCC st n L BL L (chain sc) (cost sc) sc (OPURE sc st) (alloc_slot full_lay FUEL st sc n K B)
    \/ exists len K', alloc_slot full_lay FUEL st sc n K B = SVis (EMmap 0 len PROT_RW MAPF0) K'
         /\ MM T (2^20) L len K' (CFAIL st n L BL (chain sc) (cost sc)) (fun r => CSUCC st n L BL (KInv.set_groups ((r, len) :: ld_groups L) L) (chain sc) (cost sc) sc (OMMAP sc n st))
         /\ ZC sc st).
  { intros K B HK.
    assert (SUCC : forall (O : mstate -> aptr -> Z -> Prop) st1 idx LS1 L1, 0 <= idx -> SLOT_POST [] sc n st L BL st1 idx L1 LS1 -> AFR (chain sc) (cost sc) (active st1 sc) st st1 -> GNX O sc st1 ->
              CSUCC st n L BL L1 (chain sc) (cost sc) sc O (K st1 idx)).
    { (intros O st1 idx LS1 L1 Hidx; cps_intros (ACT & LIVE & GP1 & RES); intros AF HGN).
      destruct RES as [(Eneg & _ & _)|(g & bg & ai & Hidx' & HA1 & Hg & SCg & FIT1 & STR1 & INV1 & TF1)]; [lia|].
      rewrite HK. replace (idx <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite HA1.
      exists st1, g, idx, bg. split; [reflexivity|]. split.
      - unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|].
        exists LS1, bg. split; [exists ai; exact Hg|]. split; [exact Hidx'|]. split; [exact INV1|]. split; [exact FIT1|]. split; [exact TF1|].
        pose proof (small_stride _ _ _ _ _ bg g INV1 (ex_intro _ ai Hg) ltac:(lia)). unfold IB. lia.
      - rewrite HA1 in AF. split; [eapply AFR_mono; [exact AF| lia]|]. split; [exists ai; exact Hg|]. split; [exact SCg|]. split; [exact Hidx'|]. exact (HGN g HA1). }
    destruct (alloc_slot_shape T FUEL sc [] st L BL LS n K B ltac:(unfold FUEL; cbn; lia) INV TF ltac:(apply NoDup_nil_2) (conj SC0 SC1) ltac:(lia) FIT' HCNT)
      as [(st1 & idx & LS1 & E & Hidx & SP & AF & HGN)|(len & K' & E & (LEN & PRE & MMK) & ZC0)].
    - left. rewrite E. exact (SUCC _ st1 idx LS1 L Hidx SP AF HGN).
    - right. exists len, K'. split; [exact E|]. split; [| exact ZC0]. split; [exact LEN|]. split; [exact PRE|].
      intros r Hr. destruct (MMK r Hr) as [QF QS]. split.
      + intros ER. cps_destruct (QF ER) as (st1 & LS1 & EK & (ACT & LIVE & GP1 & RES) & AF). rewrite EK, HK. change (-1 <? 0) with true. cbn iota.
        destruct RES as [(_ & INV1 & TF1)|(g & bg & ai & Hneg & _)]; [| lia].
        exists st1. split; [reflexivity|]. split; [| eapply AFR_mono; [exact AF| lia]].
        unfold CORE_POST. cbn [fst snd]. split; [exact LIVE|]. split; [exact GP1|]. exists LS1. exact INV1.
      + intros OK. cps_destruct (QS OK) as (st1 & idx & LS1 & EK & Hidx & SP & AF & HGN). rewrite EK. exact (SUCC _ st1 idx LS1 _ Hidx SP AF HGN). }
  destruct (active st sc) as [gp|] eqn:HA.
  - destruct (Z.eqb_spec (m_avail (get_meta_rec st gp)) 0) as [AZ|ANZ].
    + rewrite AZ. change (lowbit 0) with 0. cbn [negb Z.eqb]. apply SLOT. intros; reflexivity.
    + (* [comment removed for export] *)
      cps_destruct (hd_facts x0 st L BL LS sc gp INV HA) as (_ & Esc & bm & ai & Hbm).
      pose proof (ig_ok _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 INV))))) _ _ _ Hbm) as GO.
      pose proof (proj1 (g_masks _ _ _ _ _ _ GO)) as A0. fold (MR st gp) in ANZ |- *.
      cps_destruct (lowbit_idiom (m_avail (MR st gp)) ltac:(lia)) as (kk & Hk & LB & CTZ & TB & _).
      assert (LNZ : (lowbit (m_avail (MR st gp)) =? 0) = false) by (apply Z.eqb_neq; rewrite LB; pose proof (Z.pow_pos_nonneg 2 kk ltac:(lia) Hk); lia).
      rewrite LNZ. cbn [negb]. left.
      cps_pose (ta_fin_ok x0 st L BL LS gp bm ai INV eq_refl eq_refl Hbm ltac:(rewrite Esc; exact (hd_head x0 st L BL LS sc gp INV HA)) ANZ) as (INV1 & Hidx & _ & _ & STR).
      set (st1 := upd_meta gp (m_set_avail (m_avail (MR st gp) - lowbit (m_avail (MR st gp)))) st) in *.
      assert (MRg : m_last_idx (MR st1 gp) = m_last_idx (MR st gp) /\ get_stride (MR st1 gp) = get_stride (MR st gp) /\ (forall i, sstart (MR st1 gp) i = sstart (MR st gp) i) /\ m_sizeclass (MR st1 gp) = m_sizeclass (MR st gp)).
      { unfold st1, MR. rewrite get_meta_rec_upd_same. destruct (get_meta_rec st gp); cbn; repeat split; reflexivity. }
      cps_destruct MRg as (ML & MS & MSS & MSC).
      exists st1, gp, (ctz32 (lowbit (m_avail (MR st gp)))), bm. split; [reflexivity|]. split.
      * unfold CORE_POST. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_eq; reflexivity|].
        exists LS, bm. rewrite ML, MS, MSS. split; [exists ai; exact Hbm|]. split; [exact Hidx|]. split; [exact INV1|].
        rewrite Esc in STR. split; [lia|].
        split; [apply TF0_TF2; apply (TF0_ctrl st st1); [reflexivity| reflexivity| exact TF]|].
        pose proof (small_stride _ _ _ _ _ bm gp INV (ex_intro _ ai Hbm) ltac:(lia)). unfold IB. lia.
      * split; [apply AFR_of_PF; [lia| unfold st1; apply PF_upd_meta; intros; apply geo_set_avail]|].
        split; [exists ai; exact Hbm|]. rewrite MSC, ML. split; [exact Esc|]. split; [exact Hidx|]. unfold OPURE. left. split; [exists bm; exists ai; exact Hbm| reflexivity].
  - change (lowbit 0) with 0. cbn [negb Z.eqb]. apply SLOT. intros; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem malloc_big_shape st L BL LS n :
  INVL x0 st L BL LS -> TF0 st -> MMAP_THRESHOLD <= n -> size_overflows n = false -> 1 <= c_avail_meta_count (s_ctx st) ->
  exists K, malloc_core full_lay st n = SVis (EMmap 0 (n + IB + UNIT) PROT_RW MAPF0) K
    /\ MM T (n + IB + UNIT) L (n + IB + UNIT) K
         (fun u => u = SRet (st, None))
         (fun r u => exists st1 g, u = SRet (st1, Some (g, 0)) /\ CORE_POST st n L BL (KInv.set_groups ((r, n + IB + UNIT) :: ld_groups L) L) (st1, Some (g, 0))
                     /\ AFR (fun c => c = 63) 1 (Some g) st st1 /\ hosts st1 (s_next_rid st, 0) g /\ m_sizeclass (MR st1 g) = 63 /\ m_last_idx (MR st1 g) = 0).
Proof.
  intros INV TF Hbig Hov HCNT. pose proof Hov as Hov'. unfold size_overflows in Hov. apply Z.leb_gt in Hov.
  set (needed := n + IB + UNIT).
  assert (HN : 131072 <= needed < 2 ^ 63 - 4000) by (unfold needed, IB, UNIT, MMAP_THRESHOLD in *; lia).
  cps_pose INV as (IR & IA & IM & IL & IG & IS & ISH).
  unfold malloc_core. rewrite Hov'. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact Hbig).
  fold needed. eexists. split; [reflexivity|].
  split; [clear -HN; lia|]. split.
  { cbn. left. split; [exact (brk_quiet_of _ _ _ IR)|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; reflexivity|]. unfold LEN_MAX. clear -HN. lia. }
  intros a Ha. rewrite answer_ok_mmap in Ha. rewrite (mmap_answer_ok_eq _ _ _ IR) in Ha. rewrite Ha. cbn [negb].
  split; [intros ER; rewrite ER; reflexivity|].
  intros ER. rewrite ER.
  destruct (new_region RKGroup a needed st) as [st1 rid] eqn:EN.
  assert (Erid : rid = s_next_rid st) by (unfold new_region in EN; inversion EN; reflexivity).
  assert (Est1 : st1 = fst (new_region RKGroup a needed st)) by (rewrite EN; reflexivity).
  pose proof (INVL_new_group_region x0 st L BL LS a needed INV eq_refl Ha ER ltac:(unfold LEN_MAX; clear -HN; lia)) as INV1.
  rewrite <- Est1, <- Erid in INV1.
  set (L1 := KInv.set_groups ((a, needed) :: ld_groups L) L) in *.
  assert (Hr1 : s_regions st1 !! rid = Some (mkRegion RKGroup a needed)) by (rewrite Est1, ng_lookup, Erid, N.eqb_refl; reflexivity).
  assert (NS1 : s_shadow st1 !! rid = None).
  { rewrite Est1, Erid. change (s_shadow (fst (new_region RKGroup a needed st))) with (s_shadow st). exact (shadow_next_rid_none _ _ _ _ _ INV). }
  assert (TF1 : TF0 (step_seq st1)).
  { cps_destruct (step_seq_fields st1) as (A & B & _). apply (TF0_ctrl st1); [exact A| exact B|]. apply (TF0_ctrl st); [rewrite Est1; reflexivity| rewrite Est1; reflexivity| exact TF]. }
  pose proof (INVL_step_seq _ _ _ _ _ INV1) as INV2.
  cps_destruct (step_seq_fields st1) as (SS1 & SS2 & SS3 & SS4 & SS5 & _).
  assert (HC2 : 0 < c_avail_meta_count (s_ctx (step_seq st1))).
  { rewrite c_avail_meta_count_step_seq. rewrite Est1. change (s_ctx (fst (new_region RKGroup a needed st))) with (s_ctx st). lia. }
  cps_destruct (alloc_meta_okC (xorph x0 (Some rid)) (step_seq st1) L1 BL LS INV2 HC2) as (st3 & g & LS3 & E3 & P3 & INV3 & NIg & AF).
  rewrite E3. cbn beta iota zeta.
  change (lh_hdr full_lay) with (fun s b => hdr_havoc b s). cbn beta.
  assert (Hr3 : s_regions st3 !! rid = Some (mkRegion RKGroup a needed)) by (apply (amf_regions _ _ AF); [rewrite SS4; exact Hr1| reflexivity]).
  assert (NS3 : s_shadow st3 !! rid = None) by (rewrite (amf_shadow _ _ AF), SS1; exact NS1).
  assert (TF3 : TF0 st3) by (apply (TF0_ctrl (step_seq st1)); [exact (amf_shadow _ _ AF)| exact (amf_tick _ _ AF)| exact TF1]).
  cbn [xidle xorph x_idle x_zomb x_pend x_orph x_fresh x0] in INV3.
  cps_destruct (create63_ok st3 L1 BL LS3 g rid (mkRegion RKGroup a needed) needed INV3 Hr3 eq_refl eq_refl NS3 ltac:(lia) TF3)
    as (INV6 & TF6 & MR6 & GR6 & CTX6 & TK6 & RG6 & STR6 & RU6).
  match goal with |- context [ret (upd_ctx ?f ?s6, _)] => set (st6 := s6) in * end.
  pose proof (INVL_mmap_counter _ _ _ _ _ INV6) as INV7.
  set (st7 := upd_ctx _ st6) in *.
  assert (MR7 : MR st7 g = MR st6 g) by reflexivity.
  exists st7, g. split; [reflexivity|].
  assert (SS0 : sstart (mkMeta None None (Some (rid, 0)) 0 0 0 1 63 ((needed + 4095) / 4096)) 0 = 16).
  { unfold sstart, gbase. cbn -[Z.mul Z.add get_stride]. unfold UNIT. lia. }
  split.
  { unfold CORE_POST. cbn [fst snd]. split; [reflexivity|].
    split.
    { split.
      - intros q rq Hq Kq. rewrite s_regions_upd_ctx, RG6. apply (amf_regions _ _ AF); [| exact Kq]. rewrite SS4, Est1. apply (ng_keep _ _ _ _ _ _ _ INV). exact Hq.
      - rewrite s_secret_upd_ctx. transitivity (s_secret st3); [reflexivity|]. rewrite (amf_ssec _ _ AF). unfold step_seq. destruct (c_seq _ =? 255); rewrite Est1; reflexivity. }
    exists LS3, (rid, 0). rewrite MR7, MR6. cbn [m_last_idx].
    rewrite SS0. change (fst (rid, 0)) with rid.
    split; [exists 0; exact GR6|]. split; [lia|]. split; [exact INV7|].
    rewrite STR6. pose proof (round_up_pg_spec needed) as [RU _]. unfold needed, IB, UNIT in *.
    split; [lia|]. split; [apply TF0_TF2; apply (TF0_ctrl st6); [reflexivity| reflexivity| exact TF6]| lia]. }
  (* [comment removed for export] *)
  assert (GM6 : forall b, gm st7 b = if aptr_eqb b (rid, 0) then Some g else gm st3 b).
  { intros b. unfold st7, st6, gm. rewrite s_groups_upd_ctx, s_groups_add_slots, s_groups_put_group.
    destruct (aptr_eqb_spec b (rid, 0)) as [->|NE]; [rewrite lookup_insert_eq; reflexivity|].
    rewrite lookup_insert_ne by congruence. rewrite s_groups_hdr_havoc, s_groups_upd_meta. reflexivity. }
  assert (MRo : forall x, x <> g -> MR st7 x = MR st3 x).
  { intros x NE. unfold st7, st6, MR, get_meta_rec. rewrite s_metas_upd_ctx, s_metas_add_slots, s_metas_put_group, s_metas_hdr_havoc, s_metas_upd_meta.
    rewrite lookup_insert_ne by congruence. reflexivity. }
  assert (GM3 : forall b, gm st3 b = gm st b).
  { intros b. unfold gm. rewrite (amf_groups _ _ AF), s_groups_step_seq, Est1. reflexivity. }
  assert (MR3 : forall x, geo_of (MR st3 x) = geo_of (MR st x)).
  { intros x. rewrite (pf1_geo _ _ P3). unfold MR, get_meta_rec. rewrite s_metas_step_seq, Est1. reflexivity. }
  pose proof (ng_fresh _ st L BL LS INV) as FR. rewrite <- Erid in FR.
  assert (NB : forall b x, hosts st b x -> aptr_eqb b (rid, 0) = false).
  { intros b x Hh. apply aptr_eqb_neq. intros ->. apply (hosts_region _ _ _ _ _ _ _ INV Hh). exact FR. }
  assert (NHg : forall b, ~ hosts st b g).
  { intros b Hh. apply (idle_nohost _ _ _ _ _ g b INV3 ltac:(left; reflexivity)). apply hosts_gm. rewrite GM3. apply hosts_gm. exact Hh. }
  assert (RG7 : forall q rq, s_regions st !! q = Some rq -> s_regions st7 !! q = Some rq).
  { intros q rq Hq. unfold st7, st6. rewrite s_regions_upd_ctx, RG6.
    rewrite (pf1_regions _ _ P3), s_regions_step_seq, Est1. apply (ng_keep _ _ _ _ _ _ _ INV). exact Hq. }
  split.
  { constructor.
    - unfold st7, st6. rewrite s_ctx_upd_ctx, c_avail_meta_count_set_mmap_counter, s_ctx_add_slots, s_ctx_put_group, s_ctx_hdr_havoc, s_ctx_upd_meta.
      pose proof (pf1_cnt _ _ P3) as C3. rewrite c_avail_meta_count_step_seq in C3. rewrite Est1 in C3.
      change (s_ctx (fst (new_region RKGroup a needed st))) with (s_ctx st) in C3. lia.
    - intros sc _. unfold st7, st6. unfold usage, ctx. rewrite s_ctx_upd_ctx, c_usage_set_mmap_counter, s_ctx_add_slots, s_ctx_put_group, s_ctx_hdr_havoc, s_ctx_upd_meta.
      fold (ctx st3). fold (usage st3 sc). rewrite (pf1_usage _ _ P3). unfold usage, ctx. rewrite c_usage_step_seq, Est1. reflexivity.
    - intros b x Hh. split.
      + apply hosts_gm. rewrite GM6, (NB b x Hh), GM3. apply hosts_gm. exact Hh.
      + rewrite MRo by (intros ->; exact (NHg b Hh)). apply MR3.
    - intros b x Hh. apply hosts_gm in Hh. rewrite GM6 in Hh. destruct (aptr_eqb_spec b (rid, 0)) as [->|NE].
      + inversion Hh; subst x. right. rewrite MR7, MR6. cbn [m_sizeclass fst snd]. split; [reflexivity|]. split; [right; reflexivity| left; split; [exact FR| reflexivity]].
      + left. apply hosts_gm. rewrite <- GM3. exact Hh.
    - exact RG7. }
  rewrite <- Erid. split; [apply hosts_gm; rewrite GM6, aptr_eqb_refl; reflexivity|].
  rewrite MR7, MR6. split; reflexivity.
Qed.
End CORE.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma strel_ret_inv {R1 R2} (RR : R1 -> R2 -> Prop) r1 (t2 : M R2) :
  strel RR (SRet r1) t2 -> exists r2, t2 = SRet r2 /\ RR r1 r2.
Proof. intros H. inversion H; subst. eexists. split; [reflexivity| assumption]. Qed.

Lemma strel_vis_inv {R1 R2} (RR : R1 -> R2 -> Prop) e K1 (t2 : M R2) :
  strel RR (SVis e K1) t2 -> exists K2, t2 = SVis e K2 /\ forall a, strel RR (K1 a) (K2 a).
Proof.
  intros H. inversion H; subst.
  match goal with H1 : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep_dec.inj_pair2_eq_dec in H1; [subst| apply ev_eq_dec] end || idtac.
  all: eexists; split; [reflexivity| assumption].
Qed.

Lemma AFR_strip C d e st st1 : AFR C d e st st1 -> AFR C d e (strip st) (strip st1).
Proof. intros [A1 A2 A3 A4 A5]. constructor; [exact A1| exact A2| exact A3| exact A4| exact A5]. Qed.

(* [comment removed for export] *)
Definition KSUCC (C : Z -> Prop) (d sc : Z) (O : mstate -> aptr -> Z -> Prop) (cs cs' : mstate) (c : cptr) : Prop :=
  exists g bg idx, AFR C d (Some g) cs cs' /\ hosts cs' bg g /\ m_sizeclass (MR cs' g) = sc /\ 0 <= idx <= m_last_idx (MR cs' g) /\ c = (fst bg, sstart (MR cs' g) idx)
    /\ O cs' g (m_last_idx (MR cs' g)).

Lemma prun_ret {R} (r : R) : prun pans0 pupd0 tt (SRet r) = SRet (tt, r).
Proof. unfold prun. apply eruns_ret. Qed.

Lemma prun_mmap {R} a len p fl (K : Z -> M R) : prun pans0 pupd0 tt (SVis (EMmap a len p fl) K) = SVis (EMmap a len p fl) (fun z => prun pans0 pupd0 tt (K z)).
Proof. unfold prun. rewrite eruns_vis_keep by reflexivity. reflexivity. Qed.

Theorem cmalloc_shape cs L n :
  SIMREL cs L -> 0 <= n < MMAP_THRESHOLD -> (ZC (eff_class cs n) cs -> cost (eff_class cs n) <= c_avail_meta_count (s_ctx cs)) ->
  let sc := eff_class cs n in
  (exists cs' c, cmalloc cs n = SRet (cs', Some c) /\ KSUCC (chain sc) (cost sc) sc (OPURE sc cs) cs cs' c)
  \/ exists len K, cmalloc cs n = SVis (EMmap 0 len PROT_RW MAPF0) K /\ 0 < len <= 2^20 /\ ZC sc cs /\
       forall r, mmap_answer_ok (live_ranges cs) len r = true ->
         (is_err r = true -> exists cs', K r = SRet (cs', @None cptr) /\ AFR (chain sc) (cost sc) None cs cs')
         /\ (is_err r = false -> exists cs' c, K r = SRet (cs', Some c) /\ KSUCC (chain sc) (cost sc) sc (OMMAP sc n cs) cs cs' c).
Proof.
  (cps_intros (st0 & BL & LS & Ecs & INV0 & LIVE); intros Hn HCNT). cbn zeta.
  set (st := set_tick (N.succ (s_tick st0)) st0).
  assert (INV : INVL x0 st L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV0]).
  assert (TF : TF0 st) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV0)| cbn; lia]).
  assert (Ecs' : cs = strip st) by (unfold st; rewrite strip_set_tick; symmetry; exact Ecs).
  assert (ESC : eff_class cs n = eff_class st n) by (rewrite Ecs'; apply eff_class_strip).
  assert (HC : ZC (eff_class st n) st -> cost (eff_class st n) <= c_avail_meta_count (s_ctx st)) by (rewrite Ecs', eff_class_strip in HCNT; exact HCNT).
  rewrite ESC. set (sc := eff_class st n).
  assert (CORE : malloc_core full_lay st n = malloc_small_ctrl full_lay st n (fun st1 r => ret (st1, r)) (ret (st, @None (aptr * Z)))).
  { unfold malloc_core. replace (size_overflows n) with false by (symmetry; unfold size_overflows, MMAP_THRESHOLD in *; apply Z.leb_gt; lia).
    replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  pose proof (malloc_core_ctrl pans0 pupd0 n tt st cs Ecs') as REL. rewrite CORE in REL.
  assert (SUCC : forall (O O' : mstate -> aptr -> Z -> Prop) st1 g idx bg L1 (u2 : M (mstate * option (aptr * Z))),
    strel (CREL (O:=unit)) (prun pans0 pupd0 tt (SRet (st1, Some (g, idx)))) u2 ->
    CORE_POST st n L BL L1 (st1, Some (g, idx)) -> AFR (chain sc) (cost sc) (Some g) st st1 ->
    hosts st1 bg g -> m_sizeclass (MR st1 g) = sc -> 0 <= idx <= m_last_idx (MR st1 g) ->
    O st1 g (m_last_idx (MR st1 g)) -> (forall x li, O st1 x li -> O' (strip st1) x li) ->
    exists cs' c, sbind u2 (fun '(s1, r) => ret (strip s1, match r with Some (g0, i0) => Some (slot_of s1 g0 i0) | None => None end)) = SRet (cs', Some c)
      /\ KSUCC (chain sc) (cost sc) sc O' cs cs' c).
  { intros O O' st1 g idx bg L1 u2 R CP AF Hh SCg Hidx HGN HOO. rewrite prun_ret in R.
    cps_destruct (strel_ret_inv _ _ _ R) as ([s2 r2] & -> & [E1 E2]). cbn in E1, E2. subst s2 r2.
    rewrite sbind_ret_l. cbn. eexists _, _. split; [rewrite strip_strip, slot_of_strip; reflexivity|].
    cps_destruct CP as (_ & _ & LS1 & bg' & Hh' & _ & INV1 & _).
    exists g, bg, idx. split; [rewrite Ecs'; apply AFR_strip; exact AF|]. split; [exact Hh|]. split; [exact SCg|]. split; [exact Hidx|].
    split; [unfold slot_of; fold (MR st1 g); exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ idx Hh)|].
    exact (HOO _ _ HGN). }
  unfold cmalloc.
  destruct (malloc_small_shape st L BL LS n INV TF Hn HC) as [(st1 & g & idx & bg & E & CP & AF & Hh & SCg & Hidx & HGN)|(len & K & E & (LEN & PRE & MMK) & ZC0)].
  - left. rewrite E in REL. fold sc in AF, SCg, HGN.
    cps_destruct (SUCC (OPURE sc st) (OPURE sc cs) st1 g idx bg L _ REL CP AF Hh SCg Hidx HGN ltac:(intros x li Ho; rewrite Ecs'; exact Ho)) as (cs' & c & E2 & KS). exists cs', c. split; [exact E2| exact KS].
  - right. rewrite E in REL. rewrite prun_mmap in REL.
    cps_destruct (strel_vis_inv _ _ _ _ REL) as (K2 & E2 & RK). rewrite E2, sbind_vis.
    exists len. eexists. split; [reflexivity|]. split; [exact LEN|]. split; [rewrite Ecs'; exact ZC0|].
    intros r Hr. rewrite Ecs', live_ranges_strip, <- (mmap_answer_ok_eq x0 st L (proj1 INV)), <- answer_ok_mmap in Hr. destruct (MMK r Hr) as [QF QS]. split.
    + intros ER. cps_destruct (QF ER) as (st1 & EK & CP & AF). specialize (RK r). rewrite EK, prun_ret in RK.
      cps_destruct (strel_ret_inv _ _ _ RK) as ([s2 r2] & -> & [E1 E3]). cbn in E1, E3. subst s2 r2.
      rewrite sbind_ret_l. cbn. eexists. split; [rewrite strip_strip; reflexivity|]. rewrite Ecs'. apply AFR_strip. exact AF.
    + intros OK. cps_destruct (QS OK) as (st1 & g & idx & bg & EK & CP & AF & Hh & SCg & Hidx & HGN). specialize (RK r). rewrite EK in RK.
      exact (SUCC (OMMAP sc n st) (OMMAP sc n cs) st1 g idx bg _ _ RK CP AF Hh SCg Hidx HGN ltac:(intros x li Ho; rewrite Ecs'; exact Ho)).
Qed.

Theorem cmalloc_big_shape cs L n :
  SIMREL cs L -> MMAP_THRESHOLD <= n -> size_overflows n = false -> 1 <= c_avail_meta_count (s_ctx cs) ->
  exists K, cmalloc cs n = SVis (EMmap 0 (n + IB + UNIT) PROT_RW MAPF0) K /\
    forall r, mmap_answer_ok (live_ranges cs) (n + IB + UNIT) r = true ->
      (is_err r = true -> K r = SRet (cs, @None cptr))
      /\ (is_err r = false -> exists cs' c g bg, K r = SRet (cs', Some c) /\ AFR (fun c => c = 63) 1 (Some g) cs cs'
             /\ hosts cs' bg g /\ m_sizeclass (MR cs' g) = 63 /\ m_last_idx (MR cs' g) = 0 /\ c = (fst bg, sstart (MR cs' g) 0)).
Proof.
  (cps_intros (st0 & BL & LS & Ecs & INV0 & LIVE); intros Hn Hov HCNT).
  set (st := set_tick (N.succ (s_tick st0)) st0).
  assert (INV : INVL x0 st L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV0]).
  assert (TF : TF0 st) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV0)| cbn; lia]).
  assert (Ecs' : cs = strip st) by (unfold st; rewrite strip_set_tick; symmetry; exact Ecs).
  assert (HC : 1 <= c_avail_meta_count (s_ctx st)) by (rewrite Ecs' in HCNT; exact HCNT).
  pose proof (malloc_core_ctrl pans0 pupd0 n tt st cs Ecs') as REL.
  cps_destruct (malloc_big_shape st L BL LS n INV TF Hn Hov HC) as (K & E & (LEN & PRE & MMK)).
  rewrite E, prun_mmap in REL. cps_destruct (strel_vis_inv _ _ _ _ REL) as (K2 & E2 & RK).
  unfold cmalloc. rewrite E2, sbind_vis. eexists. split; [reflexivity|].
  intros r Hr. rewrite Ecs', live_ranges_strip, <- (mmap_answer_ok_eq x0 st L (proj1 INV)), <- answer_ok_mmap in Hr. destruct (MMK r Hr) as [QF QS]. split.
  - intros ER. pose proof (QF ER) as EK. specialize (RK r). rewrite EK, prun_ret in RK.
    cps_destruct (strel_ret_inv _ _ _ RK) as ([s2 r2] & -> & [E1 E3]). cbn in E1, E3. subst s2 r2.
    rewrite sbind_ret_l. cbn. rewrite strip_strip, <- Ecs'. reflexivity.
  - intros OK. cps_destruct (QS OK) as (st1 & g & EK & CP & AF & Hh & SCg & LIg). specialize (RK r). rewrite EK, prun_ret in RK.
    cps_destruct (strel_ret_inv _ _ _ RK) as ([s2 r2] & -> & [E1 E3]). cbn in E1, E3. subst s2 r2.
    rewrite sbind_ret_l. cbn. eexists _, _, g, (s_next_rid st, 0). split; [rewrite strip_strip, slot_of_strip; reflexivity|].
    split; [rewrite Ecs'; apply AFR_strip; exact AF|].
    cps_destruct CP as (_ & _ & LS1 & bg' & Hh' & _ & INV1 & _).
    split; [exact Hh|]. split; [exact SCg|]. split; [exact LIg|].
    unfold slot_of. fold (MR st1 g). exact (slot_start'_eq _ _ _ (proj1 (proj2 (proj2 INV1))) _ _ 0 Hh).
Qed.

End ACeilS1.
