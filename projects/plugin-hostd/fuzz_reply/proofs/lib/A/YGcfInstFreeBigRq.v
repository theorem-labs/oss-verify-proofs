(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch; owner a Theorem Labs lane): the recycle field of Deallocate's
   big-block arm, DGbigIF.dbg_rq_t (DGbigIF.v:116-124: the cut relation and the recycle invariant for the one chunk at
   QuarantineCallback::Recycle's call, from the memory at Put's size test), at the layer's instance
     ARX := YGcfInstBase.ARX_cf B IOK Hp, rpre := YGcfInstFreeModel.rpreD_big_cf B, fpre := fpre_hp_cf im_segs B Hp,
     dpost := CLdepot.dpost_x im_segs B, ARXr := YGcfInstDrainR.ARXr_cf B IOK Hp, AOX := aowned B, U := U_cf B,
     DRq := YGcfInstDrainR.DRq_cf B YGcfInstDrainR.NMAXD_big_cf (the contract's size bound at the unit's malloc limit),
   under the field's premises (the state qx S k z tr after the depot answer z and the chunk's change to CQuarantined,
   the memory dmem_b at Put's size test).
   rule 24: no function proved (kind: model / cut-relation entry of the big arm's Recycle call).

   [bext_rq_cf] is that field (DIfaceBig.dbg_rq).  YGcfInstFreeBig.DIfaceBigExt (YGcfInstFreeBig.v:90-100) still
   states the earlier text, with an st_cache_inited conjunct that DGbigIF no longer has (the flag is DRq_cf's guarded
   conjunct, YGcfInstDrainR.v:234); its consumer takes this lemma at DGbigIF's text.

   - [bigrq_arxr_cf]: the cut relation ARXr_cf at qx S k z tr and dmem_b's memory.  The route is YGcfInstFreeMid's
    (section m's lemmas for every field but the shadow; YGcfInstFreeMidE.enq_bridge_holds_cf for the frame of the call
     memory), without dmem_m's shadow poison: dmem_b keeps the whole shadow region as at the entry memory (okb_sh),
     so the cut relation's weak shadow (YGcfInstDrainR.shadow_ok_weak_cf) holds by the entry value off the chunk's
     user granules and by PRESENCE on them (the chunk is pending: CQuarantined and in no batch).
   - [bigrq_drq5_cf]: the first five conjuncts of YGcfInstDrainR.DRq_cf at (qx S k z tr) [qk k] [] (RIx_cf, the
     class deficit, the unqueued bytes, the two cache byte bounds), stated as their own Prop.
   - [bigrq_owned_cf]: the owned set of qx S k z tr is the entry state's plus the block (YGcfInstFreeModel.di_owned_x_cf).
   - [bext_rq_cf]: the field: the three above, DRq_cf's size conjunct (the chunk's request is below the unit's
     malloc limit, YG01cf.chunk_ok_cf) and its guarded cache conjunct (vacuous: the chunk is over kQuarantineMax by
     rpreD_big_cf, so it is not a primary chunk).
   The image premises are YGcfInstFreeMid section p's names; this file adds none.  Generic over CfImg / CfParams /
   AImg / DImg; no numeral of any image; no event term. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0dcf YG0scf YG0qcf YG03cf YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YG03dcf YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG DGif0 DGbigIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfRmodel YGcfMallocCompose YGcfInstBase YGcfInstFreeView.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstFreePost YGcfInstFreeModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfBatch.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstFreeMid.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CLdepot AFfl YGcfDIface YGcfInstDrainR.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac bceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.
Variable B : asyms.

(* The shadow region is off every window dmem_b writes (YGcfInstFreeMid.okm_sh's cases without the block's shadow,
   which only the enqueue side poisons). *)
Lemma okb_sh : forall ly S Hp rd k sp a, ARmcf B ly S Hp rd -> In k (st_chunks S) ->
  FP_IZONE B -> FP_DSTAT B -> FP_DZONE B ly -> ly_stk_lo ly + DGbaseC.DFSTACK <= sp <= ly_stk_hi ly ->
  kLowShadowBeg <= a < kHighMemBeg ->
  ~ DGgmC.WINT ly a /\ ~ DGgmC.WINB (sptr_addr B ly (ck_user k)) a /\ ~ (sp - DGbaseC.DFSTACK <= a < sp) /\
  ~ dg_izone a /\ ~ dg_dzone ly a.
Proof.
intros ly S Hp rd k sp a M Hk HIZ HDS HDZ Hsp Ha.
pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (ext_rounded_cf B ly S Hp rd M k Hk) as (ER & NN1 & NN2 & NN3).
assert (Q8 : 8 <= (ck_n k + 7) / 8 * 8).
{ pose proof (Z.div_le_mono 8 (ck_n k + 7) 8 ltac:(lia) ltac:(lia)) as D. change (8 / 8) with 1 in D. lia. }
pose proof (g_shx B ly S Hp rd M a Ha) as (NS & NIM & NT).
assert (NBP : forall a0, ly_NB ly <= a0 < ly_NB ly + kNodesBlockSize -> app_addr a0)
  by (intros a0 H0; apply (g_app_oext B ly S Hp rd M (ly_NB ly, kNodesBlockSize) a0 ltac:(unfold owned_extents; cbn; tauto));
      unfold in_zr; cbn [fst snd]; exact H0).
assert (SBP : forall a0, ly_SB ly <= a0 < ly_SB ly + kStoreBlockSize -> app_addr a0)
  by (intros a0 H0; apply (g_app_oext B ly S Hp rd M (ly_SB ly, kStoreBlockSize) a0 ltac:(unfold owned_extents; cbn; tauto));
      unfold in_zr; cbn [fst snd]; exact H0).
split; [|split; [|split; [|split]]].
- intros X. apply NT. unfold DGgmC.WINT, t_unwinding, t_stats, kThreadObjSize in *. lia.
- intros X. unfold DGgmC.WINB in X. unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia.
- intros X. apply NS. unfold DGbaseC.DFSTACK in *. lia.
- intros X. apply NIM. destruct (HIZ a X) as (X1 & _). exact (g_static_img B ly S Hp rd M a X1).
- intros X. destruct (proj2 (HDZ a) X) as (_ & [FP|OS]).
  + unfold CLdepot.depot_footprint in FP. destruct FP as [FP|[FP|[FP|FP]]].
    * apply NIM. exact (g_static_img B ly S Hp rd M a (HDS a (or_introl FP))).
    * pose proof (NBP a FP) as HA0. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
    * pose proof (SBP a FP) as HA0. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
    * apply NIM. exact (g_static_img B ly S Hp rd M a (HDS a (or_intror FP))).
  + apply NIM. exact (g_static_img B ly S Hp rd M a OS).
Qed.

Section i.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Local Notation ARX := (ARX_cf B IOK Hp).
Local Notation ARXr := (YGcfInstDrainR.ARXr_cf B IOK Hp).
Local Notation U := (U_cf B).
Local Notation rpre := (rpreD_big_cf B).
Local Notation fpre := (fpre_hp_cf im_segs B Hp).
Local Notation dpost := (CLdepot.dpost_x im_segs B).
Local Notation AOX := (aowned B).
Local Notation DRq := (YGcfInstDrainR.DRq_cf B YGcfInstDrainR.NMAXD_big_cf).
Hypothesis HIZO : YGcfDIface.IZONE_OWNED B.
Hypothesis HIZR : FP_IZONE_ROM B.
Hypothesis HDS : FP_DSTAT B.
Hypothesis HDZO : YGcfDIface.DZONE_OWNED B.
Hypothesis HDZF : FP_DZONE_FP B.
Hypothesis HCO : FP_CONST B.
Hypothesis HIAL : FV_IAL B.
Hypothesis HIMG : YGcfDIface.IMG_COVER.
(* the error-buffer object avoids the walk's image zones (the relation's machine cells are ARmcf's fields) *)
Hypothesis HERRB : ERRB_APART B.
(* Printf's two cells avoid the walk's image zones (ARmcf's amc_pf_cells, field round 3) *)
Hypothesis HPFA : PF_APART B.

(* (L1) the cut relation at Recycle's call state and memory *)
Lemma bigrq_arxr_cf : forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (mem : word -> option byte) mat,
  ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) -> U tr S ->
  find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
  ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
  0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
  dmem_b W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) mem ->
  ARXr inst ly (qx S k z tr) W mem (with_vm_backing (m_vm_lazy md0) mat md0).
Proof.
intros inst ly S W mem0 md0 p n tr k z hb1 sp0 mem mat (Ei & HAR & HXM) ((HU & HQ & HII & HBR & _) & HQS) HPN HBLK HUtr
  Hf Hst Hlo Hhi Hbot Hal Hhb HV0 DM.
destruct DM as ((memD & (AOKD & DEPD & CSTD) & PRD & EQD) & MEQ & IALP & PRS & PRW & V1 & V2 & V3).
pose proof HAR as (M0 & LED & BUD & MW & HSH).
pose proof (amc_exh_cell _ _ _ _ _ M0) as HEX. pose proof (amc_errb_cells _ _ _ _ _ M0) as HER.
pose proof (amc_layout _ _ _ _ _ M0) as LY. pose proof (amc_wf _ _ _ _ _ M0) as WF.
pose proof (LGUARD_of_ARmcf B ly S Hp _ md0 M0 HIMG LED) as HLG.
pose proof (FP_IZONE_of B HIZO HIZR (amc_syms _ _ _ _ _ M0)) as HIZ. pose proof (FP_DZONE_of B HDZO HDZF ly HLG) as HDZ.
pose proof (FP_CONST_of B HCO ly HLG) as HCOl.
destruct (find_user_block_cf _ 0 0 0 S p n (WfR_of_WfP_cf _ _ _ _ _ WF) HBLK) as (k0 & Hf0 & Hk & Hst0 & Hu & Hr).
rewrite Hf in Hf0. injection Hf0 as <-. subst p n.
(* the call state's invariant, from the entry state's and the depot's answer *)
pose proof (ms_wf B ly S Hp _ M0 k Hk Hst z tr AOKD HUtr) as WFX.
(* the chunk header's second byte (the chunk cell AVmask 127 17 at the entry memory) *)
assert (HB1M : Z.land hb1 127 = 17).
{ assert (C : cell_holds B ly (aview im_segs (w_H W) mem0)
    (ACell (aoff (aoff (sptr_exp (ck_beg k)) (ck_rz k - kChunkHeaderSize)) 1) 1 (AVmask 127 17))).
  { apply (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M0)). unfold acells_cf. rewrite !in_app_iff. do 2 right. left.
    apply in_flat_map. exists k. split; [exact Hk|]. unfold chunk_cells. apply in_app_iff. left. cbn. tauto. }
  cbn [cell_holds c_at c_val c_w] in C. rewrite (EA2_cf B ly S Hp _ M0 k _ _ Hk) in C. destruct C as (b & Hb & Hm).
  pose proof (chunk_facts_cf B ly S Hp _ k M0 Hk) as (_ & _ & _ & G4' & _).
  replace (ck_base B ly k + (ck_rz k - kChunkHeaderSize) + 1) with (sptr_addr B ly (ck_user k) - 16 + Z.of_nat 1) in Hb
    by (rewrite G4'; unfold kChunkHeaderSize; lia).
  rewrite (val_mem_aview_cf _ _ _ _ _ 1 HV0 ltac:(lia)) in Hb. injection Hb as <-. rewrite le_byte_hb1_cf in Hm by exact Hhb.
  exact Hm. }
assert (HHB : 0 <= hb1 < 256 /\ Z.land hb1 127 = 17) by exact (conj Hhb HB1M).
assert (Hsp : ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 <= ly_stk_hi ly) by (split; assumption).
pose proof (al_img_env_cf im_segs ly S md0 LY LED) as SEGS.
pose proof (chunk_facts_cf B ly S Hp _ k M0 Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (ext_rounded_cf B ly S Hp _ M0 k Hk) as (ER & NN1 & NN2 & NN3).
set (rd := aview im_segs (w_H W) mem0) in *. set (rd' := aview im_segs (w_H W) mem) in *.
set (rdD := aview im_segs (w_H W) memD) in *.
(* the frame: dmem_b keeps every byte off the walk's windows, the depot zone and the internal allocator's zone *)
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ Dm B ly k sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same_cf.
  assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha).
  apply MEQ; rewrite Ux.
  - unfold dwin_m. intros [X|[X|X]].
    + apply ND. do 2 right; left. unfold DSm. exact X.
    + apply ND. left. exact X.
    + apply ND. right; left. unfold DKm. exact X.
  - intros X. apply ND. do 4 right; left. exact X.
  - intros X. apply ND. do 3 right; left. exact X. }
(* the whole shadow region is kept (no poison on this side) *)
assert (AGb : forall a, kLowShadowBeg <= a < kHighMemBeg -> rd' a = rd a).
{ intros a Ha. destruct (okb_sh ly S Hp rd k sp0 a M0 Hk HIZ HDS HDZ Hsp Ha) as (N1 & N2 & N3 & N4 & N5).
  assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold kLowShadowBeg, kHighMemBeg in *; lia).
  subst rd rd'. apply aview_same_cf.
  assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha64).
  apply MEQ; rewrite Ux.
  - unfold dwin_m. intros [X|[X|X]]; [exact (N3 X) | exact (N1 X) | exact (N2 X)].
  - exact N5.
  - exact N4. }
assert (KEEP : forall g, 4096 <= g -> g + 8 <= kHighMemEnd -> rd' (shadow_addr g) = rd (shadow_addr g))
  by (intros g H1 H2; apply AGb; apply g_hs_bounds; assumption).
(* visibility: what the entry memory shows, the call memory shows *)
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv. subst rd rd'. unfold aview, mbyte, mrestrict in Hv |- *. set (x := Z_to_bv 64 a) in *.
  destruct (w_H W x) eqn:Hx; [exact Hv|].
  destruct (seg_rom im_segs x) eqn:ROM; [destruct (mem x); discriminate|].
  destruct (mem x) as [b|] eqn:E'; [discriminate|]. exfalso.
  assert (Hv0 : mem0 x <> None) by (intros E0; rewrite E0 in Hv; exact (Hv eq_refl)).
  set (a' := bv_unsigned x) in *. assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  assert (PRX : forall m, apresent (w_H W) m a' -> m x = None -> False)
    by (intros m [_ [bb Hb]] Hm; rewrite Ex in Hb; congruence).
  assert (EM : forall lo hi (c : Z), (lo <= c < hi) \/ ~ (lo <= c < hi)) by (intros; lia).
  destruct (EM (sp0 - DGbaseC.DFSTACK) sp0 a') as [Y2|Y2]. { exact (PRX mem (PRS a' Y2) E'). }
  assert (WD : (DGgmC.WINT ly a' \/ DGgmC.WINB (sptr_addr B ly (ck_user k)) a') \/
    ~ (DGgmC.WINT ly a' \/ DGgmC.WINB (sptr_addr B ly (ck_user k)) a')) by (unfold DGgmC.WINT, DGgmC.WINB; lia).
  destruct WD as [Y3|Y3]. { exact (PRX mem (PRW a' Y3) E'). }
  assert (NDZ : ~ dg_dzone ly a').
  { intros Y5. assert (P0 : apresent (w_H W) mem0 a').
    { split; [rewrite Ex; exact Hx|]. destruct (mem0 x) as [b0|] eqn:E0; [exists b0; rewrite Ex; exact E0 | exfalso; exact (Hv0 eq_refl)]. }
    destruct (PRD a' Y5 P0) as [_ [bd Hbd]]. rewrite Ex in Hbd. rewrite (EQD x Y5) in E'. congruence. }
  assert (NIZ : ~ dg_izone a') by (intros X; destruct (HIZ a' X) as (_ & R & _); rewrite Ex in R; exact (R ROM)).
  rewrite (MEQ x) in E'; [exact (Hv0 E') | | exact NDZ | exact NIZ].
  unfold dwin_m. intros [X|X]; [exact (Y2 X) | exact (Y3 X)]. }
(* the values the walk wrote *)
assert (NEW_hdr : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 16 + Z.of_nat i) = Some (YG0f.le_byte (3 + 256 * hb1) 4 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V1 Hi)).
assert (NEW_n : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 12 + Z.of_nat i) = Some (YG0f.le_byte (ck_n k) 4 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V2 Hi)).
assert (NEW_unw : rd' (ly_T ly + t_unwinding) = Some 0).
{ subst rd'. pose proof (val_mem_aview_cf (w_H W) mem (ly_T ly + t_unwinding) 1 0 0%nat V3 ltac:(lia)) as H0.
  rewrite Z.add_0_r in H0. exact H0. }
(* the internal allocator's cells, the depot's memory facts and the constant cells at the call memory *)
assert (IAL : Forall (cell_holds B ly rd') (ialloc_cells B (qx S k z tr)) /\ Forall (range_zero B ly rd') (ialloc_zero B))
  by (subst rd'; exact (ial_cells_of_post_cf B ly (qx S k z tr) W mem (ms_inited S k z tr HII) (proj1 (HIAL W mem) IALP))).
assert (DEP : CLdepot.depot_mem_ok B ly (YFl0C.depot_after z tr (dtick S)) rd').
{ assert (EDP : st_depot (CLdepot.depot_after z tr S) = st_depot (YFl0C.depot_after z tr (dtick S)))
    by (unfold CLdepot.depot_after, YFl0C.depot_after, dtick; destruct (z =? 0); reflexivity).
  pose proof (depot_mem_ok_same_cf B ly _ _ rdD EDP DEPD) as DEP1.
  apply (depot_mem_ok_fp_cf B ly _ rdD rd'); [| | exact DEP1].
  - pose proof (depot_len_bound _ _ (amc_universe _ _ _ _ _ M0) (wfc_depot _ _ _ _ _ WFX)) as LL.
    unfold depot_ids, DEPOT_MAX in *.
    change (st_depot (YFl0C.depot_after z tr (dtick S))) with (st_depot (qx S k z tr)). lia.
  - intros a Hfp.
    assert (Ha : 0 <= a < 2 ^ 64).
    { unfold CLdepot.depot_footprint in Hfp. destruct Hfp as [X|[X|[X|X]]].
      - pose proof (g_static_img B ly S Hp rd M0 a (HDS a (or_introl X))) as HI. pose proof (g_img B ly S Hp rd M0) as (I0 & I1 & I2).
        unfold in_zr in HI. unfold kImgLo, kImgEnd in *. lia.
      - pose proof (g_app_oext B ly S Hp rd M0 (ly_NB ly, kNodesBlockSize) a ltac:(unfold owned_extents; cbn; tauto)
          ltac:(unfold in_zr; cbn [fst snd]; exact X)) as AA. pose proof (app_addr_below_ceil a AA). bceil. unfold ASAN_CEIL in *. lia.
      - pose proof (g_app_oext B ly S Hp rd M0 (ly_SB ly, kStoreBlockSize) a ltac:(unfold owned_extents; cbn; tauto)
          ltac:(unfold in_zr; cbn [fst snd]; exact X)) as AA. pose proof (app_addr_below_ceil a AA). bceil. unfold ASAN_CEIL in *. lia.
      - pose proof (g_static_img B ly S Hp rd M0 a (HDS a (or_intror X))) as HI. pose proof (g_img B ly S Hp rd M0) as (I0 & I1 & I2).
        unfold in_zr in HI. unfold kImgLo, kImgEnd in *. lia. }
    subst rd' rdD. apply aview_same_cf. apply EQD. rewrite unsigned_lit_small by exact Ha. exact (proj1 (HDZ a) Hfp). }
assert (ODEC : forall o1 o2 : option Z, {o1 = o2} + {o1 <> o2}) by (decide equality; apply Z.eq_dec).
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc.
  apply (cell_holds_mix_cf B ly rdD rd rd' c (proj1 (Forall_forall _ _) CSTD c Hc) (proj1 (Forall_forall _ _) (amc_const _ _ _ _ _ M0) c Hc)).
  intros j Hj. destruct (g_const_loc B ly S Hp rd M0 c j Hc Hj) as [R64 _].
  destruct (ODEC (rd' (aeval B ly (c_at c) + j)) (rdD (aeval B ly (c_at c) + j))) as [E|NE]; [left; exact E | right].
  assert (ND : ~ dg_dzone ly (aeval B ly (c_at c) + j)).
  { intros Hd. apply NE. subst rd' rdD. apply aview_same_cf. apply EQD. rewrite unsigned_lit_small by exact R64. exact Hd. }
  destruct (m_const_ok B ly S Hp rd M0 k Hk z tr rd' hb1 HHB sp0 Hsp IAL HCOl c j Hc Hj ND) as [R64' NDc].
  exact (AG _ R64' NDc). }
(* the hidden bytes of the shadow band do not change *)
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem (w64 a) = mem0 (w64 a)).
{ intros a Hb Hh.
  assert (Ha64 : 0 <= a < 2 ^ 64)
    by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia).
  unfold w64 in *. assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha64).
  assert (PRX : forall m, apresent (w_H W) m a -> False) by (intros m [Hh' _]; rewrite Hh in Hh'; discriminate).
  apply MEQ; rewrite Ux.
  - unfold dwin_m. intros [X|[X|X]]; [exact (PRX mem (PRS a X)) | exact (PRX mem (PRW a (or_introl X)))
      | exact (PRX mem (PRW a (or_intror X)))].
  - intros X. destruct (proj2 (HDZ a) X) as (_ & [FP'|OS]).
    + unfold CLdepot.depot_footprint in FP'. destruct FP' as [Y|[Y|[Y|Y]]].
      * pose proof (g_static_img B ly S Hp rd M0 a (HDS a (or_introl Y))) as HI. pose proof (g_img B ly S Hp rd M0) as (I0 & I1 & I2).
        unfold in_zr in HI. clear - Hb HI I0 I2. unfold in_band_rw, kImgLo, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
      * pose proof (g_app_oext B ly S Hp rd M0 (ly_NB ly, kNodesBlockSize) a ltac:(unfold owned_extents; cbn; tauto)
          ltac:(unfold in_zr; cbn [fst snd]; exact Y)) as AA.
        clear - Hb AA. unfold app_addr, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *.
        bceil. unfold ASAN_CEIL in *. lia.
      * pose proof (g_app_oext B ly S Hp rd M0 (ly_SB ly, kStoreBlockSize) a ltac:(unfold owned_extents; cbn; tauto)
          ltac:(unfold in_zr; cbn [fst snd]; exact Y)) as AA.
        clear - Hb AA. unfold app_addr, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *.
        bceil. unfold ASAN_CEIL in *. lia.
      * pose proof (g_static_img B ly S Hp rd M0 a (HDS a (or_intror Y))) as HI. pose proof (g_img B ly S Hp rd M0) as (I0 & I1 & I2).
        unfold in_zr in HI. clear - Hb HI I0 I2. unfold in_band_rw, kImgLo, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
    + pose proof (owned_static_bound B a (amc_syms _ _ _ _ _ M0) OS) as [X1 X2].
      clear - Hb X1 X2. unfold in_band_rw, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
  - intros C. destruct (HIZ a C) as (OS & _).
    pose proof (owned_static_bound B a (amc_syms _ _ _ _ _ M0) OS) as [X1 X2].
    clear - Hb X1 X2. unfold in_band_rw, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia. }
(* the cut relation's weak shadow: the entry value where the model's value is unchanged, presence on the pending
   chunk's user granules (the model says shHeapFreed, the machine keeps the allocated shadow until Recycle) *)
assert (SHW : YGcfInstDrainR.shadow_ok_weak_cf B ly Hp rd' (qx S k z tr)).
{ destruct (ms_split B ly S Hp rd M0 k Hk z tr) as (l1 & l2 & E & E' & N1 & N2).
  pose proof (u_al8_cf B ly S Hp rd M0 k Hk) as (U8 & B8 & R8).
  intros g v Hg8 HS'. pose proof (amc_shadow _ _ _ _ _ M0 g) as SH.
  unfold ashadow in HS', SH. rewrite E', (ms_fa_poison B ly S Hp rd M0 k Hk z tr) in HS'. rewrite E in SH.
  rewrite AFfl.find_chunk_at_app in HS', SH. cbn [find_chunk_at] in HS', SH.
  change (ck_base B ly (qk k)) with (ck_base B ly k) in HS'. change (ck_extent (qk k)) with (ck_extent k) in HS'.
  assert (OTHER : forall x, In x (st_chunks S) -> ck_base B ly x <= g < ck_base B ly x + ck_extent x ->
    rd' (shadow_addr g) = rd (shadow_addr g)).
  { intros x Hx Hgx. pose proof (chunk_facts_cf B ly S Hp rd x M0 Hx) as (X1 & X2 & _).
    apply KEEP; [unfold in_app in X1; lia | bceil; unfold ASAN_CEIL, kHighMemEnd in *; lia]. }
  destruct (find_chunk_at B ly l1 g) as [x|] eqn:F1.
  - apply find_chunk_at_In in F1 as [Hx Hgx]. left.
    rewrite (OTHER x ltac:(rewrite E; apply in_app_iff; left; exact Hx) Hgx). exact (SH v Hg8 HS').
  - destruct ((ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k)) eqn:TK.
    + apply andb_prop in TK as [T1 T2]. apply Z.leb_le in T1. apply Z.ltb_lt in T2.
      change (ck_base B ly (qk k)) with (ck_base B ly k) in HS'.
      rewrite (KEEP g ltac:(unfold in_app in G1; lia) ltac:(bceil; unfold ASAN_CEIL, kHighMemEnd in *; lia)).
      apply Z.mod_divide in Hg8 as [c Hc]; [|lia]. apply Z.mod_divide in B8 as [b0 Hb0]; [|lia].
      apply Z.mod_divide in R8 as [r0 Hr0]; [|lia].
      assert (G8' : g mod 8 = 0) by (rewrite Hc; apply Z_mod_mult).
      assert (J : (g - ck_base B ly k) / 8 = c - b0)
        by (rewrite Hc, Hb0; replace (c * 8 - b0 * 8) with ((c - b0) * 8) by lia; apply Z_div_mult; lia).
      assert (RU : ck_rz k / 8 = r0) by (rewrite Hr0; apply Z_div_mult; lia).
      rewrite J in HS', SH. unfold chunk_granule in HS', SH.
      change (ck_rz (qk k)) with (ck_rz k) in HS'. change (ck_n (qk k)) with (ck_n k) in HS'.
      change (ck_state (qk k)) with CQuarantined in HS'. rewrite RU in HS', SH. rewrite Hst in SH.
      destruct (c - b0 <? r0) eqn:C1.
      * left. injection HS' as <-. exact (SH _ G8' eq_refl).
      * apply Z.ltb_ge in C1. destruct (c - b0 <? r0 + (ck_n k + 7) / 8) eqn:C2.
        -- apply Z.ltb_lt in C2. right. split.
           ++ unfold YGcfInstDrainR.pending_user_cf, YGcfInstDrainR.pending_cf. exists (qk k).
              split; [split; [rewrite E'; apply in_elt | split; [reflexivity | exact (ms_fresh B ly S Hp rd M0 k Hk Hst z tr)]]|].
              change (ck_base B ly (qk k)) with (ck_base B ly k). change (ck_rz (qk k)) with (ck_rz k).
              change (ck_n (qk k)) with (ck_n k). lia.
           ++ rewrite (SH (if c - b0 <? r0 + ck_n k / 8 then shAddressable
                     else if (c - b0 =? r0 + ck_n k / 8) && negb (ck_n k mod 8 =? 0) then ck_n k mod 8 else shHeapLeftRz));
                [discriminate | exact G8' | reflexivity].
        -- apply Z.ltb_ge in C2. injection HS' as <-. left. apply SH; [exact G8'|].
           assert (F1' : (c - b0 <? r0 + ck_n k / 8) = false).
           { apply Z.ltb_ge. pose proof (Z.div_le_mono (ck_n k) (ck_n k + 7) 8 ltac:(lia) ltac:(lia)). lia. }
           rewrite F1'. destruct (Z.eqb_spec (ck_n k mod 8) 0) as [Z0|NZ]; cbn [negb andb];
             [rewrite Bool.andb_false_r; reflexivity|].
           replace (c - b0 =? r0 + ck_n k / 8) with false; [reflexivity|]. symmetry. apply Z.eqb_neq.
           pose proof (Z.div_mod (ck_n k) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (ck_n k) 8 ltac:(lia)) as MB.
           pose proof (Z.div_mod (ck_n k + 7) 8 ltac:(lia)) as DM'. pose proof (Z.mod_pos_bound (ck_n k + 7) 8 ltac:(lia)) as MB'. nia.
    + destruct (find_chunk_at B ly l2 g) as [x|] eqn:F2.
      * apply find_chunk_at_In in F2 as [Hx Hgx]. left.
        rewrite (OTHER x ltac:(rewrite E; apply in_app_iff; right; right; exact Hx) Hgx). exact (SH v Hg8 HS').
      * destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
        pose proof (in_rangesb_true _ _ R) as (lo & len & Hin & Hg).
        pose proof (g_fa_poison_high B ly S Hp rd M0 lo len g Hin Hg) as [Y1 Y2]. left.
        rewrite (KEEP g ltac:(lia) ltac:(bceil; unfold ASAN_CEIL, kHighMemEnd in *; lia)). exact (SH v Hg8 HS'). }
(* the machine cells (ARmcf's fields): off the walk's writes *)
assert (XN : forall a, XC B ly a -> rd' a = rd a).
{ intros a X. pose proof (x_owned B ly S Hp rd M0 a X) as [R64 _]. apply AG; [exact R64|].
  unfold Dm, DKm, DSm, DHm. intros [D|[D|[D|[D|[D|D]]]]].
  - apply (x_T B ly S Hp rd M0 a X). unfold DGgmC.WINT in D.
    unfold t_unwinding, t_stats, kThreadObjSize in *. lia.
  - exact (x_kwords B ly S Hp rd M0 k a Hk X D).
  - exact (x_S B ly S Hp rd M0 a sp0 X Hsp D).
  - exact (xw_iz B ly S Hp rd M0 HERRB HIZ a X D).
  - exact (xw_dz B ly S Hp rd M0 HERRB HDS HDZ HLG a X D).
  - exact (x_kshadow B ly S Hp rd M0 k a Hk X D). }
assert (EXH' : exh_cell_cf B ly (qx S k z tr) rd').
{ apply (exh_cell_cf_frame B ly ly S (qx S k z tr) rd rd' HEX).
  - intros c. unfold qx, YFl0C.depot_after, dtick. destruct (z =? 0); reflexivity.
  - intros c Hc. apply XN. left. exists c. split; [exact Hc | reflexivity]. }
assert (ERR' : errb_cells_cf B ly (qx S k z tr) rd').
{ apply (errb_cells_cf_frame B ly ly S (qx S k z tr) rd rd' HER);
    try (unfold qx, YFl0C.depot_after, dtick; destruct (z =? 0); reflexivity); [|exact VIS].
  intros a Ha. apply XN. right. exact Ha. }
(* the cut relation at the call state *)
split; [exact Ei|]. split.
- split; [|split; [|split; [|split]]].
  + constructor.
    * exact (WfR_of_WfP_cf _ _ _ _ _ WFX).
    * exact (amc_universe _ _ _ _ _ M0).
    * exact (amc_syms _ _ _ _ _ M0).
    * exact LY.
    * unfold sec_placed. rewrite (ms_sec_extents B ly S Hp rd M0 k Hk z tr). exact (amc_placed _ _ _ _ _ M0).
    * exact CONST'.
    * exact (amc_const_owned _ _ _ _ _ M0).
    * exact (m_cells_all B ly S Hp rd M0 k Hk z tr rd' HIZ HDS HDZ hb1 HHB sp0 Hsp AG NEW_hdr NEW_n NEW_unw IAL DEP).
    * exact (m_fa B ly S Hp rd M0 k Hk z tr rd' HIZ HDS HDZ hb1 HHB sp0 Hsp AG IAL).
    * exact (m_flags B ly S Hp rd M0 k Hk z tr rd' HIZ HDS HDZ sp0 Hsp AG).
    * exact (m_depot B ly S k z tr rd' DEP).
    * exact SHW.
    * exact (m_zshadow B ly S Hp rd M0 k Hk z tr rd' HIZ HDS HDZ hb1 HHB sp0 Hsp AG IAL).
    * exact (m_junk B ly S Hp rd M0 k Hk Hst z tr rd' VIS).
    * exact (m_areas B ly S Hp rd M0 k Hk z tr rd' VIS).
    * exact (m_client B ly S Hp rd M0 k Hk z tr rd' VIS).
    * exact (proj2 IAL).
    * exact (amc_tsd _ _ _ _ _ M0).
    * exact (amc_static_img _ _ _ _ _ M0).
    * exact (m_hp_live B ly S Hp rd M0 k Hk z tr HPN).
    * exact (m_xs B ly S Hp rd M0 k Hk z tr).
    * exact EXH'.
    * exact ERR'.
    * exact (amc_cells_owned _ _ _ _ _ M0).
    * assert (HPFb : forall a, pf_byte a -> ~ dg_izone a /\ ~ dg_dzone ly a)
        by (intros a Ha; exact (conj (proj1 (HPFA a Ha)) (proj2 (HPFA a Ha) ly HLG))).
      eapply YGcfInstFreeMid.m_pf; eassumption.
    * exact (amc_pf_owned _ _ _ _ _ M0).
  + eapply ALedger_same_cf; [exact (ms_ledger B ly S Hp rd M0 k Hk z tr md0 LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb
      | apply eager_used_wvb].
  + destruct BUD as (BU1 & BU2 & BU3). split; [|split; [|exact BU3]].
    * rewrite (ms_budget B ly S Hp rd M0 k Hk z tr). exact BU1.
    * intros e He. rewrite (ms_sec_extents B ly S Hp rd M0 k Hk z tr) in He. exact (BU2 e He).
  + eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
  + eapply (ahs_transfer_cf im_segs B ly S Hp (qx S k z tr) (w_H W) mem0 mem SEGS M0 HSH VIS HSK).
    * intros a _ C. exact (ms_client B ly S Hp rd M0 k Hk z tr a C).
    * exact (ms_sec_extents B ly S Hp rd M0 k Hk z tr).
    * intros g Hg Hga _ _. apply KEEP;
        [exact (proj1 Hga) | bceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *; lia].
- exact (xs_mapped_keep_cf ly S _ md0 _ (ms_secs S k z tr) (m_vmmaps_wvb _ _ _) HXM).
Qed.

(* (L2) DRq_cf's first five conjuncts (YGcfInstDrainR.v:222-226) at the call state, the chunk pending, no batch object *)
Lemma bigrq_drq5_cf : forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (mem : word -> option byte),
  ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) -> U tr S ->
  find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
  ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
  0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
  dmem_b W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) mem ->
  RIx_cf (as_universe B) 0 0 0 (qx S k z tr) [qk k] [] [] /\
  (forall c, 1 <= c <= 31 ->
     cdef (qx S k z tr) c = (if c =? kBatchClass then class_size kBatchClass * Z.of_nat (length (@nil Z)) else 0)) /\
  unq_cf (qx S k z tr) <= items_n [qk k] /\
  qc_bytes (st_qthread (qx S k z tr)) <= kQuarantineCacheMax /\ qc_bytes (st_qglobal (qx S k z tr)) <= kQuarantineMax.
Proof.
intros inst ly S W mem0 md0 p n tr k z hb1 sp0 mem HA ((HU & HQ & HII & HBR & _) & HQS) _ HBLK HUtr Hf Hst _ _ _ _ _ _ DM.
destruct DM as ((memD & (AOKD & _ & _) & _ & _) & _).
pose proof (proj1 (proj2 HA)) as (M0 & _).
pose proof (amc_wf _ _ _ _ _ M0) as WF.
destruct (find_user_block_cf _ 0 0 0 S p n (WfR_of_WfP_cf _ _ _ _ _ WF) HBLK) as (k0 & Hf0 & Hk & Hst0 & Hu & Hr).
rewrite Hf in Hf0. injection Hf0 as <-.
pose proof (ms_wf B ly S Hp _ M0 k Hk Hst z tr AOKD HUtr) as WFX.
pose proof (qmeter_cf_tight S HQ) as (T1 & T2 & T3).
destruct (ms_split B ly S Hp _ M0 k Hk z tr) as (l1 & l2 & E & E' & N1 & N2).
pose proof (ms_quar B ly S Hp _ M0 k Hk Hst z tr) as QX.
split; [|split; [|split; [|split]]].
- unfold RIx_cf. cbn [app flat_map map].
  split; [exact (WfR_of_WfP_cf _ _ _ _ _ WFX)|].
  split; [constructor; [split; [rewrite E'; apply in_elt | reflexivity] | constructor]|].
  split; [constructor; [exact (ms_fresh B ly S Hp _ M0 k Hk Hst z tr) | exact (wq_nodup _ (wfc_quarantine _ _ _ _ _ WFX))]|].
  split; [constructor|]. split; constructor.
- intros c Hc. rewrite (wfc_compl0 _ _ _ _ _ WFX c Hc). cbn [length Z.of_nat]. destruct (c =? kBatchClass); lia.
- unfold unq_cf. rewrite QX, (ms_queued S k z tr). cbn [items_n fold_right]. change (ck_n (qk k)) with (ck_n k). lia.
- rewrite (ms_qthread S k z tr). exact T1.
- rewrite (ms_qglobal S k z tr). exact T2.
Qed.

(* (L3) the owned set of the call state is the entry state's plus the block *)
Lemma bigrq_owned_cf : forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (mem : word -> option byte),
  ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) -> U tr S ->
  find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
  ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
  0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
  dmem_b W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) mem ->
  forall a, AOX ly (qx S k z tr) a -> AOX ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n).
Proof.
intros inst ly S W mem0 md0 p n tr k z hb1 sp0 mem HA (HR & _) _ HBLK _ Hf _ _ _ _ _ _ _ _ a Ha.
exact (di_owned_x_cf B IOK Hp inst ly S W mem0 md0 p n k z tr a HA HR HBLK Hf Ha).
Qed.

(* The field: DGbigIF.dbg_rq_t (DIfaceBig.dbg_rq) at the layer's instance. *)
Lemma bext_rq_cf : dbg_rq_t B U ARX ARXr AOX rpre fpre dpost DRq.
Proof.
unfold dbg_rq_t.
intros inst ly S W mem0 md0 p n tr k z hb1 sp0 mem mat HA HR HF HB HU Hf Hst H1 H2 H3 H4 Hh HV DM.
pose proof (bigrq_arxr_cf inst ly S W mem0 md0 p n tr k z hb1 sp0 mem mat HA HR HF HB HU Hf Hst H1 H2 H3 H4 Hh HV DM) as L1.
pose proof (bigrq_drq5_cf inst ly S W mem0 md0 p n tr k z hb1 sp0 mem HA HR HF HB HU Hf Hst H1 H2 H3 H4 Hh HV DM)
  as (RX & CD & UQ & Q1 & Q2).
pose proof (bigrq_owned_cf inst ly S W mem0 md0 p n tr k z hb1 sp0 mem HA HR HF HB HU Hf Hst H1 H2 H3 H4 Hh HV DM) as L3.
split; [exact L1|]. split; [|exact L3].
destruct HR as ((_ & _ & _ & _ & HHO) & HQS).
pose proof (proj1 (proj2 HA)) as (M0 & _). pose proof (amc_wf _ _ _ _ _ M0) as WF.
destruct (find_user_block_cf _ 0 0 0 S p n (WfR_of_WfP_cf _ _ _ _ _ WF) HB) as (k0 & Hf0 & Hk & _ & _ & Hr).
rewrite Hf in Hf0. injection Hf0 as <-.
destruct (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ WF) k Hk) as [[R0 R1] _].
pose proof cf_malloc_max_pos as CMP.
unfold YGcfInstDrainR.DRq_cf.
split; [exact RX|]. split; [exact CD|]. split; [exact UQ|]. split; [exact Q1|]. split; [exact Q2|]. split.
- (* the size conjunct: the chunk's request is below the unit's malloc limit *)
  constructor; [|constructor]. change (ck_n (qk k)) with (ck_n k).
  unfold YGcfInstDrainR.NMAXD_big_cf, ck_n, req_size. destruct (Z.eqb_spec (ck_req k) 0); lia.
- (* the pending items' bytes (CfF2b 033ceb5fdb1c): the one chunk's request is below the unit's malloc limit *)
  split.
  { cbn [items_n fold_right]. change (ck_n (qk k)) with (ck_n k). pose proof YG08cf.cf_malloc_max_bound as CMB.
    unfold ck_n, req_size in *. assert (2 ^ 31 = 2147483648) by reflexivity. destruct (Z.eqb_spec (ck_req k) 0); unfold items_n; cbn; lia. }
  split.
  { (* the guarded cache conjunct: the chunk is over kQuarantineMax, so it is not a primary chunk; zs = [] *)
    intros [(k' & [<-|[]] & FP)|ZN]; [|exfalso; exact (ZN eq_refl)]. exfalso. change (ck_req (qk k)) with (ck_req k) in FP.
    unfold from_primary in FP. apply Z.leb_le in FP.
    pose proof (needed_primary_bounds (ck_req k) R0) as (NB1 & _ & _). pose proof (rz_size_bounds (ck_req k)) as [RZ _].
    rewrite <- Hr in HQS. unfold kMaxSize, kQuarantineMax in *. lia. }
  (* the unit's secondary admission at Recycle's call state (field round 3): Put changes neither st_secs nor the
     secondary chunks, so cf_hull_counts carries it from the entry's rpreD_free_cf *)
  apply (cf_hull_counts (qx S k z tr) S); [unfold nsec_cf; rewrite (ms_secs S k z tr); reflexivity
    | unfold sec_T_cf; rewrite (ms_secs S k z tr); reflexivity | exact HHO].
Qed.
End i.
End a.
