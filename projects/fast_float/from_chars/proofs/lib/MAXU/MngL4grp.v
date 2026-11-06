(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv CatExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require CatSim AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface U_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngMeta MngOwn AXG_ffstep AXF_ff3 AXG_ffpost MngL4 MngL4free MngRel AXG_fgrp AXG_fgrpU MngUnm.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngRz2 MngWk MngRz MngU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma stk_ok_of_stk8 : forall m (sp : word), 8192 <= bv_unsigned sp ->
  stk SEGS m (bv_unsigned sp - 8192) (bv_unsigned sp) -> stk_ok SEGS m sp 8192.
Proof.
  intros m sp Hsp (H1 & H2 & H) a n Ha1 Ha2. rewrite <- (wa_u a).
  replace (bv_unsigned a) with (bv_unsigned sp - 8192 + (bv_unsigned a - (bv_unsigned sp - 8192))) by ring.
  apply (store_ok_of_bytes SEGS m (bv_unsigned sp - 8192) 8192); [|lia | lia].
  intros j Hj. pose proof (H (bv_unsigned sp - 8192 + j) ltac:(lia)) as (Hw & _). change (Mem.wa (bv_unsigned sp - 8192 + j)) with (wa (bv_unsigned sp - 8192 + j)) in Hw.
  exact Hw.
Qed.

Ltac entry_facts8 FE regs m hs g am i fr :=
  destruct FE as (HP & MD & Ha0 & Hra & Hret & AL & Hsp47 & HT & ST & HF & Hk & Ep & Ek);
  pose proof HP as [H0 Hctx Henv Hkro Hled Hpcg HAP HHT Hb1 HT20 Hpg Hini Hrap];
  pose proof Henv as (E1 & E2 & Edb & E3 & E4 & E5 & E6 & Eer & Eew);
  assert (Rsp8 : 2^20 + 8192 <= bv_unsigned (getr regs 2) <= 2^47) by (unfold sp_of, FNEED in *; lia);
  assert (HSTK8 : stk_ok SEGS m (getr regs 2) 8192) by (apply stk_ok_of_stk8; [unfold sp_of, FNEED in *; lia | exact ST]);
  assert (HFP8 : forall rg, In rg (footprint (hs_s hs)) -> loc_addr (hs_L hs) (fst rg) + snd rg <= bv_unsigned (getr regs 2) - 8192)
    by (intros rg Hrg; pose proof (HHT rg Hrg); unfold sp_of, FNEED in *; lia);
  assert (AL' : bv_unsigned (getr regs 2) mod 16 = 0) by (unfold sp_of in AL; exact AL);
  assert (HP10 : getr regs 10 = wa (loc_addr (hs_L hs) (LMem (frame_ptr am i fr)))) by (rewrite Ha0, Ep; reflexivity).

(* [comment removed for export] *)
Lemma stk_grow_pt : forall m m' lo hi, stk SEGS m lo hi ->
  (forall x, lo <= x < hi -> m (wa x) <> None -> m' (wa x) <> None) -> stk SEGS m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) Hg. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). change (Mem.wa a) with (wa a) in *.
  destruct (m' (wa a)) as [b'|] eqn:E'.
  - split; [unfold wview; rewrite E'; discriminate | exists b'; unfold Mem.mrd; rewrite E'; reflexivity].
  - assert (E0 : m (wa a) = None) by (destruct (m (wa a)) as [b0|] eqn:E0; [exfalso; exact (Hg a Ha ltac:(rewrite E0; discriminate) E') | reflexivity]).
    split.
    + unfold wview in *. rewrite E'. rewrite E0 in Hw. exact Hw.
    + exists b. unfold Mem.mrd in *. rewrite E'. rewrite E0 in Hb. exact Hb.
Qed.

Lemma layout_kf : forall L s s', MallocWfKf.kf_of s' = MallocWfKf.kf_of s -> layout_ok L s -> layout_ok L s'.
Proof.
  intros L s s' E (H1 & H2 & H3 & H4). pose proof (footprint_kf_eq s s' E) as EF.
  unfold MallocWfKf.kf_of in E. injection E as Er _ _.
  split; [exact H1|]. split; [intros k0 rg Hk0; unfold region_of in *; rewrite Er in Hk0; exact (H2 k0 rg Hk0)|].
  rewrite EF. split; [exact H3 | exact H4].
Qed.

Section FG.
Variable cfg : SpuriousCfg.
Variable HTOP : Z.
Context {fx : FPState}.

(* [comment removed for export] *)
#[using="Type"] Theorem free_contract_grp0 : forall hs regs m md p k ret K g am i fr s',
  free_entry HTOP hs regs m md p k ret g am i fr -> getr regs 4 = wa 0x77990 ->
  (am_freed am = 0 \/ Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am)) ->
  free (Some (frame_ptr am i fr)) (hs_s hs) = IRet (tt, s') ->
  free_cont cfg HTOP hs regs m md p k ret K ->
  realizes_cfg SEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x52f88) m (seg_rom SEGS)) md) K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs regs m md p k ret K g am i fr s' FE HR4 Hnt Hit CONT. entry_facts8 FE regs m hs g am i fr.
  destruct (free_grp0_step (hs_L hs) (hs_s hs) regs m (seg_rom SEGS) g am i fr s' H0 HF Hk Hnt Hctx HP10 HR4 E1 E2 E4
              (ex_intro _ (hs_can hs) (conj E3 E5)) E6 Eer Rsp8 AL' HSTK8 HFP8 HAP Hit) as (R & m' & Hms & Hcs & H0' & Hkf & Hfr & Hgr).
  exact (free_contract_step cfg HTOP fx regs m md hs p k ret K g am i fr s' R m' HP MD Hra Hret AL Hsp47 HT ST HF Hk Ep Ek Hms Hcs Hit Hkf H0' Hgr Hfr CONT).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ob_munmap_U : forall md0 L x md1 (B : Z) r len rg,
  MngRz2.LINK HTOP MngL4.FORB_P L x md1 -> U md1 <= U md0 -> (fun _ : kreq => 0) (KMunmap r len) <= B ->
  nth_error (MngRz2.kf_regions x) r = Some rg -> rg_kind rg = RkMap -> rg_live rg = true -> rg_len rg = page_round len ->
  U (AllocNodesCfg.munmap_next (MngWk.w64 (ly_reg L r)) (MngWk.w64 (page_round len)) md1) <= U md0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros md0 L x md1 B r len rg HL HU _ Hr Hk Hl Hlen.
  pose proof (MngRz2.lk_maps _ _ _ _ _ HL r rg (conj Hr (conj Hk Hl))) as Hhas. rewrite Hlen in Hhas.
  apply OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.map_has_In in Hhas.
  assert (TOP : alloc_top (m_vmmaps md1) < 2^64) by (pose proof (alloc_top_room (m_vmmaps md1)); unfold two_pow_64 in *; unfold stack_max_size in *; lia).
  assert (RG : MngU.inrange (vm_maps (m_vmmaps md1))).
  { intros e He. pose proof (MngRz2.lk_mtop _ _ _ _ _ HL e He). lia. }
  pose proof (MngRz2.lk_mtop _ _ _ _ _ HL _ Hhas) as T2. cbn [fst snd] in T2.
  pose proof (MngU.U_munmap_next md1 (MngWk.w64 (ly_reg L r)) (MngWk.w64 (page_round len)) (MngRz2.lk_lazy _ _ _ _ _ HL)
                (MngRz2.lk_mdisj _ _ _ _ _ HL) RG Hhas ltac:(lia)) as UM.
  unfold MngU.Um in UM. unfold U in *. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem free_contract_grpU : forall hs regs m md p k ret K g am i fr s2 r len kk,
  free_entry HTOP hs regs m md p k ret g am i fr -> getr regs 4 = wa 0x77990 ->
  (am_freed am = 0 \/ Z.lor (am_freed am) (am_avail am) + bit i = ones (am_last am)) ->
  free (Some (frame_ptr am i fr)) (hs_s hs) = IAsk (KMunmap r len) s2 kk ->
  free_cont cfg HTOP hs regs m md p k ret K ->
  realizes_cfg SEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x52f88) m (seg_rom SEGS)) md) K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs regs m md p k ret K g am i fr s2 r len kk FE HR4 Hnt Hit CONT. entry_facts8 FE regs m hs g am i fr.
  pose proof (LINK_of_v HTOP (hs_L hs) (hs_s hs) md Hled MD) as HLK.
  assert (HRP : forall q rg, region_of (hs_s hs) q = Some rg -> rg_kind rg = RkMap -> rg_live rg = true -> 0 < rg_len rg).
  { intros q rg Hq _ Hl. destruct (MngRz2.lk_rgeo _ _ _ _ _ HLK q rg Hq Hl) as (_ & _ & P & _). exact P. }
  destruct (free_grpU_step (hs_L hs) (hs_s hs) regs m (seg_rom SEGS) g am i fr s2 r len kk H0 HF Hk Hnt Hctx HP10 HR4 E1 E2 E4
              (ex_intro _ (hs_can hs) (conj E3 E5)) E6 Eer Eew Rsp8 AL' HSTK8 HFP8 HAP HRP Hit)
    as (R & m3 & Hms & AT & (rg & Hrg & Hkd & Hlv & Hlen) & HKF & Hrq & Hkk & R5 & m5 & Hms5 & Hcs & H0' & Hfr & Hgr).
  pose proof MD as [Hh Hl].
  assert (HTOPB : HTOP <= 2^47) by (unfold sp_of, FNEED in *; lia).
  eapply rzc_isteps; [exact Hh | exact Hl | apply catsim_isteps; exact Hms|].
  apply (MngRz2.case_munmap SEGS cfg MngL4.FORB_P HTOP HTOPB (seg_rom SEGS) (fun _ => 0) (fun _ md1 _ => U md1 <= U md) (ob_munmap_U md) r len
           (hs_L hs) (MallocWfKf.kf_of s2) md 0 s2 R (wa 0x55310) m3 K AT eq_refl Hrq ltac:(rewrite HKF; exact HLK) ltac:(lia) ltac:(cbn; lia)).
  intros eff ans L' md' Ho Hvm HL' HB'. inversion Ho; subst eff ans L'. cbn [eff_ret] in *.
  change (MngWk.mem_after m3 (mkEffectU (MngWk.w64 0) [] [] [(MngWk.w64 (ly_reg (hs_L hs) r), MngWk.w64 (page_round len))] [] []))
    with (MngWk.mem_after m3 (MngRz.eff_munmap (ly_reg (hs_L hs) r) (page_round len))).
  pose proof (MngRz2.lk_halt _ _ _ _ _ HL') as Hh'. pose proof (MngRz2.lk_lazy _ _ _ _ _ HL') as Hl'.
  eapply rzc_isteps; [exact Hh' | exact Hl' | apply catsim_isteps; exact Hms5|].
  (* [comment removed for export] *)
  pose proof H0 as (HW & HR & HM). pose proof HR as (HL & HC & HFM).
  assert (Hb : In (frame_ptr am i fr, fr_n fr) (user_blocks (hs_s hs))).
  { destruct (in_frames_inv _ _ _ _ _ HF) as (Hu & Hi & Hfri). unfold user_blocks. apply in_flat_map. exists (g, am). split; [exact Hu|].
    cbn [snd]. apply in_flat_map. exists i. split; [apply In_zseq; lia|]. rewrite Hfri, Hk. left. reflexivity. }
  destruct (free_blocks (hs_s hs) (frame_ptr am i fr) (fr_n fr) [(KMunmap r len, 1)] (s_unm s2 r) HW Hb
              ltac:(rewrite Hit; cbn [yields]; split; [reflexivity|]; split; [exact I|]; rewrite (Hkk 1); reflexivity)) as (l1 & l2 & El & El').
  assert (EFP : footprint s2 = footprint (hs_s hs)) by exact (footprint_kf_eq _ _ HKF).
  pose proof (footprint_region_In (hs_s hs) r rg Hrg Hkd Hlv) as HE.
  pose proof (HAP _ HE ltac:(discriminate)) as HEimg. unfold ranges_disjoint, crange in HEimg. cbn [fst snd loc_addr] in HEimg.
  pose proof (HHT _ HE) as HEtop. cbn [fst snd loc_addr] in HEtop. rewrite Hlen in HEimg, HEtop. rewrite Z.add_0_r in HEimg, HEtop.
  assert (FX5 : forall x, 0x10000 <= x < 0x99000 -> ~ (0x97c98 <= x < 0x98038) -> ~ (0x778ec <= x < 0x778f0) -> m5 (wa x) = m (wa x)).
  { intros x Hx Hnc Hne. apply Hfr; [lia | unfold sp_of, FNEED in *; clear - Hx HT HT20; lia | | lia | exact Hne].
    intros c Hc. apply (static_out_image (hs_L hs) (hs_s hs) c x HW HL Hctx HAP Hc); lia. }
  set (hs' := hs_set hs (s_unm s2 r)).
  apply (free_finish cfg HTOP fx regs m md hs p k ret K R5 m5 md' hs' (conj Hh' Hl') Hra Hret Hcs).
  - (* [comment removed for export] *)
    assert (Hsub : forall b, In b (user_blocks (s_unm s2 r)) -> In b (user_blocks (hs_s hs))).
    { intros b Hb'. rewrite El' in Hb'. rewrite El. apply in_app_iff in Hb' as [Hb'|Hb']; apply in_app_iff; [left|right; right]; exact Hb'. }
    assert (FR : forall a n, 0x10000 <= a -> a + Z.of_nat n <= 0x99000 -> a + Z.of_nat n <= 0x97c98 \/ 0x98038 <= a ->
                   a + Z.of_nat n <= 0x778ec \/ 0x778f0 <= a -> rdn SEGS m5 (wa a) n = rdn SEGS m (wa a) n).
    { intros a n Ha Hn Hnc Hne. apply rdn_frame; [lia | lia |]. intros x Hx. apply FX5; lia. }
    assert (NR : forall x, 0x778ec <= x < 0x778f0 -> ~ (ly_reg (hs_L hs) r <= x < ly_reg (hs_L hs) r + page_round len)) by (intros x Hx Hr; lia).
    destruct Henv as (E1' & E2' & Edb' & E3' & E4' & E5' & E6' & E8' & E9').
    apply Heap_intro. split; [exact H0'|]. split; [exact Hctx|]. split.
    { split; [rewrite FR by (cbn; lia); exact E1'|]. split; [intros sc Hsc; rewrite FR by (cbn; lia); exact (E2' sc Hsc)|].
      split; [intros j Hj; rewrite FR by (cbn; lia); exact (Edb' j Hj)|].
      split; [exact E3'|]. split; [rewrite FR by (cbn; lia); exact E4'|]. split; [rewrite FR by (cbn; lia); exact E5'|].
      split; [rewrite FR by (cbn; lia); exact E6'|].
      split.
      { intros j Hj. destruct (E8' j Hj) as (b0 & Hb0). unfold mrd in *. destruct (m5 (wa (ERRNO + j))) as [b'|] eqn:Em5; [exists b'; reflexivity|].
        destruct (m (wa (ERRNO + j))) as [b1|] eqn:Em.
        - exfalso. apply (Hgr (ERRNO + j) ltac:(unfold ERRNO; lia) ltac:(apply NR; unfold ERRNO; lia) ltac:(rewrite Em; discriminate) Em5).
        - exists b0. exact Hb0. }
      intros d k0 Hd Hk0. apply (store_ok_pt k0 m m5); [rewrite u_wa_small by (unfold ERRNO; lia); unfold ERRNO; lia | | exact (E9' d k0 Hd Hk0)].
      intros x Hx Hne. rewrite u_wa_small in Hx by (unfold ERRNO; lia). rewrite <- (wa_u x).
      pose proof (bv_unsigned_in_range _ x) as Bx. unfold bv_modulus in Bx.
      apply (Hgr (bv_unsigned x) ltac:(lia) ltac:(apply NR; unfold ERRNO in *; lia)). rewrite wa_u. exact Hne. }
    split.
    { destruct Hkro as ((K1 & K2 & K3) & (K4 & K5 & K6)).
      split; (split; [assumption | split; [assumption|]]); intros j Hj; change (Mem.wa j) with (wa j);
        rewrite (FX5 j ltac:(lia) ltac:(lia) ltac:(lia)); first [ exact (K3 j Hj) | exact (K6 j Hj) ]. }
    split; [apply LINKv_of; cbn [hs_L hs_s hs']; rewrite (kf_unm s2 r len); exact HL'|].
    split; [exact (pcg_free (hs_s hs) (frame_ptr am i fr) (fr_n fr) [(KMunmap r len, 1)] (s_unm s2 r) HW Hb
                     ltac:(rewrite Hit; cbn [yields]; split; [reflexivity|]; split; [exact I|]; rewrite (Hkk 1); reflexivity) Hpcg)|].
    split; [intros rg' Hrg' Hnc; apply HAP; [rewrite <- EFP; exact (footprint_unm_In s2 r rg' Hrg') | exact Hnc]|].
    split; [intros rg' Hrg'; apply HHT; rewrite <- EFP; exact (footprint_unm_In s2 r rg' Hrg')|].
    split; [intros b Hb'; apply Hb1; apply Hsub; exact Hb'|]. split; [exact HT20|].
    split; [unfold page_env in *; rewrite FR by (cbn; lia); exact Hpg|].
    split; [apply inited_of_areas; [exact (proj1 H0') | cbn [hs_s hs']; change (st_areas (s_unm s2 r)) with (st_areas s2); rewrite (areas_kf _ _ HKF); exact (areas_of_frame _ _ _ _ _ HW HF)]|].
    cbn [hs_s hs_L hs']. intros rq rgq E0 L0 K0. destruct (region_unm_live s2 r rq rgq E0 L0) as (Hne0 & E0').
    unfold region_of in E0'. rewrite (regions_kf _ _ HKF) in E0'.
    destruct (Hrap rq rgq E0' L0 K0) as (Aq1 & Aq2 & Aq3 & A4). split; [exact Aq1|]. split; [exact Aq2|]. split; [exact Aq3|].
    intros rq1 rgq1 Hnq1 Eq1 Lq1. destruct (region_unm_live s2 r rq1 rgq1 Eq1 Lq1) as (_ & Eq1'). unfold region_of in Eq1'. rewrite (regions_kf _ _ HKF) in Eq1'.
    exact (A4 rq1 rgq1 Hnq1 Eq1' Lq1).
  - exact Hvm.
  - exact HB'.
  - intros a Ha. destruct (keep_static a Ha) as (A1 & A2). apply FX5; [exact A1 | exact A2 |]. unfold U_KEEP in Ha. cbn [outside] in Ha. lia.
  - (* [comment removed for export] *)
    unfold blocks. cbn [hs_s hs_L hs']. rewrite El, El'. intros y. rewrite Ep, Ek.
    change (loc_addr (hs_L hs) (LMem (frame_ptr am i fr)), fr_n fr) with ((fun b : sptr * Z => (loc_addr (hs_L hs) (LMem (fst b)), snd b)) (frame_ptr am i fr, fr_n fr)).
    apply blocks_del_split. intros b Hbb E. injection E as E1' E2'.
    pose proof (user_blocks_disjoint (hs_s hs) (hs_L hs) HW HL) as PW. rewrite El, map_app_cons in PW.
    assert (Hb' : In (block_range (hs_L hs) b) (map (block_range (hs_L hs)) (l1 ++ l2))) by (apply in_map; exact Hbb).
    rewrite map_app in Hb'.
    destruct (pairwise_app_cons _ _ _ _ PW (block_range (hs_L hs) b) Hb') as [D|D];
      unfold ranges_disjoint, block_range in D; cbn [fst snd loc_addr] in D, E1'; cbn [loc_addr fst snd] in E1';
      pose proof (Hb1 b ltac:(rewrite El; apply in_app_iff in Hbb as [Hbb|Hbb]; apply in_app_iff; [left|right; right]; exact Hbb)) as Hn1;
      pose proof (Hb1 _ Hb) as Hn2; cbn [snd] in Hn1, Hn2; lia.
  - (* [comment removed for export] *)
    intros x Hx. apply outside_app' in Hx as (Ho1 & Ho2). apply outside_app' in Ho2 as (Ho2 & Ho3).
    cbn [outside] in Ho3. destruct Ho3 as (Hop & Ho3 & _).
    pose proof (u64_range x) as Rx.
    assert (Herr : ~ (0x778ec <= bv_unsigned x < 0x778f0)).
    { intros He. apply (owned_static hs (bv_unsigned x)); [unfold STATIC_P, ERRNO; cbn [outside]; lia | exact Ho1]. }
    assert (Hreg : ~ (ly_reg (hs_L hs) r <= bv_unsigned x < ly_reg (hs_L hs) r + page_round len)).
    { intros Hin. unfold owned in Ho1. apply outside_app' in Ho1 as (Ho1 & _). rewrite outside_filter, outside_flat_map in Ho1.
      pose proof (Ho1 _ HE) as Hc. rewrite outside_carve in Hc by (intros b Hbk; pose proof (blocks_pos HTOP hs m md HP b Hbk); lia).
      unfold fivl in Hc. cbn [fst snd loc_addr] in Hc. rewrite Hlen, Z.add_0_r in Hc.
      destruct Hc as [Hc|(b & Hbk & Hbx)]; [exact (Hc Hin)|].
      destruct (Z.eq_dec (fst b) p) as [Eb|Eb].
      - (* [comment removed for export] *)
        destruct (block_of hs b Hbk) as (b0 & Hb0 & Eb0). unfold block_range in Eb0.
        destruct (in_user_blocks_inv (hs_s hs) b0 Hb0) as (g' & am' & i' & fr' & _ & _ & _ & _ & Eb0').
        assert (Esb : snd b = k).
        { pose proof (user_blocks_disjoint (hs_s hs) (hs_L hs) HW HL) as PW.
          assert (CONTRA : b0 <> (frame_ptr am i fr, fr_n fr) -> False).
          { intros Hne. destruct (pairwise_map_In _ (block_range (hs_L hs)) _ _ _ PW Hb0 Hb Hne) as [D|D];
              unfold ranges_disjoint, block_range in D; cbn [fst snd] in D; rewrite Eb0 in Eb; cbn [fst] in Eb; rewrite Ep in Eb;
              pose proof (Hb1 _ Hb0) as N0; pose proof (Hb1 _ Hb) as N1; cbn [snd] in *; lia. }
          destruct (sptr_eq_dec (fst b0) (frame_ptr am i fr)) as [Ep1|Np1].
          - destruct (Z.eq_dec (snd b0) (fr_n fr)) as [Ep2|Np2].
            + rewrite Eb0. cbn [snd]. rewrite Ep2, Ek. reflexivity.
            + exfalso. apply CONTRA. intros Eq. apply Np2. rewrite Eq. reflexivity.
          - exfalso. apply CONTRA. intros Eq. apply Np1. rewrite Eq. reflexivity. }
        apply Hop. rewrite <- Eb, <- Esb. exact Hbx.
      - (* [comment removed for export] *)
        assert (Hbk' : In b (blocks hs')).
        { assert (Hbd : blocks_del (blocks hs) (blocks hs') (p, k)).
          { unfold blocks. cbn [hs_s hs_L hs']. rewrite El, El'. intros y. rewrite Ep, Ek.
            change (loc_addr (hs_L hs) (LMem (frame_ptr am i fr)), fr_n fr) with ((fun b : sptr * Z => (loc_addr (hs_L hs) (LMem (fst b)), snd b)) (frame_ptr am i fr, fr_n fr)).
            apply blocks_del_split. intros b' Hbb E. injection E as E1' E2'.
            pose proof (user_blocks_disjoint (hs_s hs) (hs_L hs) HW HL) as PW. rewrite El, map_app_cons in PW.
            assert (Hb' : In (block_range (hs_L hs) b') (map (block_range (hs_L hs)) (l1 ++ l2))) by (apply in_map; exact Hbb).
            rewrite map_app in Hb'.
            destruct (pairwise_app_cons _ _ _ _ PW (block_range (hs_L hs) b') Hb') as [D|D];
              unfold ranges_disjoint, block_range in D; cbn [fst snd loc_addr] in D, E1'; cbn [loc_addr fst snd] in E1';
              pose proof (Hb1 b' ltac:(rewrite El; apply in_app_iff in Hbb as [Hbb|Hbb]; apply in_app_iff; [left|right; right]; exact Hbb)) as Hn1;
              pose proof (Hb1 _ Hb) as Hn2; cbn [snd] in Hn1, Hn2; lia. }
          apply (proj2 (Hbd b)). split; [exact Hbk | intros Eq; apply Eb; rewrite Eq; reflexivity]. }
        destruct (block_of hs' b Hbk') as (b0 & Hb0 & Eb0). cbn [hs_s hs_L hs'] in Hb0, Eb0.
        destruct (blocks_in_footprint (s_unm s2 r) (hs_L hs) b0 (proj1 H0') (proj1 (proj1 (proj2 H0'))) Hb0) as (rg' & Hrg' & Hincl).
        assert (Hrg2 : region_of s2 r = Some rg) by (unfold MallocWfKf.kf_of in HKF; injection HKF as Er _ _; unfold region_of in *; rewrite Er; exact Hrg).
        pose proof (unm_disjoint (hs_L hs) s2 r rg rg' (layout_kf (hs_L hs) (hs_s hs) s2 HKF HL) Hrg2 Hkd Hlv Hrg') as D.
        unfold block_range in Eb0. rewrite Eb0 in Hbx. cbn [fst snd] in Hbx.
        unfold range_incl, block_range, crange, ranges_disjoint in Hincl, D. cbn [fst snd] in Hincl, D. rewrite Hlen in D. lia. }
    rewrite <- (wa_u x). apply Hfr; [lia | unfold sp_of, FNEED in Ho3; lia | | exact Hreg | exact Herr].
    intros c Hc Hin. exact (owned_image HTOP hs m md c (bv_unsigned x) HP Hc Hin Ho1).
  - apply (stk_grow_pt m m5 _ _ ST). intros x Hx Hne. apply (Hgr x); [unfold sp_of, FNEED in *; pose proof (u64_range (getr regs 2)); lia | | exact Hne].
    unfold sp_of, FNEED in *. lia.
  - exact CONT.
Qed.

End FG.
