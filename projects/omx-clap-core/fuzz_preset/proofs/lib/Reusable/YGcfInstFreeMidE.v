(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch): the generic cf layer's Deallocate interface, the call-site
   bridge of Put's QuarantineCache::Enqueue (YGcfInstEnq.enq_bridge_cf) at the layer's walk relation, over
   YGcfInstFreeMid's model and memory sides (its sections 0 / m).  rule 24: no function proved (kind:
   interface-instance discharge: the allocator relation re-established at Enqueue's call).

   Split from YGcfInstFreeMid.v (field round 3): lane F1's enq_pre_cf ends with the call memory's overlay normal form
   and read-only bytes (YGcfInstEnq.v:152), which reach Put's call through round 3 part 3's MP: F1's enq_bridge_cf
   takes them as premises right after dmem_m (YGcfInstEnq.v:292 at a working branch bfaddc527576), and this bridge
   returns them (the walk's sections, which YGcfInstFreeBigRq reads, stay in YGcfInstFreeMid).
   The image premises are YGcfInstFreePost's (FP_IZONE_ROM, FP_DSTAT, FP_DZONE_FP, FP_CONST, ERRB_APART, PF_APART),
   YGcfDIface's (IZONE_OWNED, DZONE_OWNED, IMG_COVER) and YGcfInstFreeView's FV_IAL.  Generic over CfImg / CfParams /
   AImg / DImg; no numeral of any image; no event term. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0dcf YG0scf YG0qcf YG03cf YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfTok YG03dcf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRmodel YGcfMallocCompose YGcfInstBase YGcfInstFreeView.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstFreePost YGcfInstFreeModel YGcfBatch.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstFreeMid.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot CLenq YFfl YGcfDIface YGcfInstEnq YGcfInstDrainR YAkMemnorm DMspec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstFree.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac mceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.
Ltac msp := repeat match goal with |- _ /\ _ => split end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.
Variable B : asyms.
(* YGcfInstFreeMid's section-m names at this file's B (the bridge's text is the one it had in YGcfInstFreeMid) *)
Local Notation ms_wf := (YGcfInstFreeMid.ms_wf B).
Local Notation mDH_sh := (YGcfInstFreeMid.mDH_sh B).
Local Notation m_const_ok := (YGcfInstFreeMid.m_const_ok B).
Local Notation m_post_parts := (YGcfInstFreeMid.m_post_parts B).
Local Notation ms_ledger := (YGcfInstFreeMid.ms_ledger B).
Local Notation ms_budget := (YGcfInstFreeMid.ms_budget B).
Local Notation ms_sec_extents := (YGcfInstFreeMid.ms_sec_extents B).
Local Notation ms_client := (YGcfInstFreeMid.ms_client B).
Local Notation ms_quar := (YGcfInstFreeMid.ms_quar B).
Local Notation ms_split := (YGcfInstFreeMid.ms_split B).
Local Notation ms_fresh := (YGcfInstFreeMid.ms_fresh B).
Local Notation Dm := (YGcfInstFreeMid.Dm B).
Local Notation DHm := (YGcfInstFreeMid.DHm B).
Local Notation DKm := (YGcfInstFreeMid.DKm B).

(* ================================================================================================================ *)
(* 2. The bridge, at the image premises and the instance predicate IOK.                                             *)
Section p.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Hypothesis HIZO : YGcfDIface.IZONE_OWNED B.
Hypothesis HIZR : FP_IZONE_ROM B.
Hypothesis HDS : FP_DSTAT B.
Hypothesis HDZO : YGcfDIface.DZONE_OWNED B.
Hypothesis HDZF : FP_DZONE_FP B.
Hypothesis HCO : FP_CONST B.
Hypothesis HIAL : FV_IAL B.
Hypothesis HIMG : YGcfDIface.IMG_COVER.
(* the error-buffer object avoids the walk's image zones (the relation's machine cells: ARmcf's fields) *)
Hypothesis HERRB : ERRB_APART B.
(* Printf's two cells avoid the walk's image zones (ARmcf's amc_pf_cells, field round 3) *)
Hypothesis HPFA : PF_APART B.

Lemma enq_bridge_holds_cf : YGcfInstEnq.enq_bridge_cf B (ARX_cf B IOK Hp) (rpreD_small_cf B) (fpre_hp_cf im_segs B Hp)
  (CLdepot.dpost_x im_segs B) L24MAX_cf.
Proof.
unfold YGcfInstEnq.enq_bridge_cf.
intros inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat (Ei & HAR & HXM) ((HU & HQ & HII & HBR & HHO) & HQS) HPN HBLK HUtr
  Hf Hst Hlo Hhi Hbot Hal Hhb HV0 DM HRO HRA HRA4 HSP0 HGP HTP HA0 HA1 HA3 HA4.
destruct DM as ((memD & (AOKD & DEPD & CSTD) & PRD & EQD) & MEQ & IALP & SHV & PRS & PRW & V1 & V2 & V3).
pose proof HAR as (M0 & LED & BUD & MW & HSH).
pose proof (amc_exh_cell _ _ _ _ _ M0) as HEX. pose proof (amc_errb_cells _ _ _ _ _ M0) as HER.
pose proof (amc_layout _ _ _ _ _ M0) as LY. pose proof (amc_wf _ _ _ _ _ M0) as WF.
pose proof (LGUARD_of_ARmcf B ly S Hp _ md0 M0 HIMG LED) as HLG.
pose proof (FP_IZONE_of B HIZO HIZR (amc_syms _ _ _ _ _ M0)) as HIZ. pose proof (FP_DZONE_of B HDZO HDZF ly HLG) as HDZ.
pose proof (FP_CONST_of B HCO ly HLG) as HCOl.
destruct (find_user_block_cf _ 0 0 0 S p n (WfR_of_WfP_cf _ _ _ _ _ WF) HBLK) as (k0 & Hf0 & Hk & Hst0 & Hu & Hr).
rewrite Hf in Hf0. injection Hf0 as <-. subst p n.
(* the call state's invariant, from the entry state's and the depot's answer *)
pose proof (ms_wf ly S Hp _ M0 k Hk Hst z tr AOKD HUtr) as WFX.
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
assert (Hsp : ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 <= ly_stk_hi ly) by (split; assumption).
pose proof (al_img_env_cf im_segs ly S md0 LY LED) as SEGS.
pose proof (chunk_facts_cf B ly S Hp _ k M0 Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (ext_rounded_cf B ly S Hp _ M0 k Hk) as (ER & NN1 & NN2 & NN3).
set (rd := aview im_segs (w_H W) mem0) in *. set (rd' := aview im_segs (w_H W) mem) in *.
set (rdD := aview im_segs (w_H W) memD) in *.
(* the frame: outside the walk's windows, the depot zone, the internal allocator's zone and the block's shadow *)
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ Dm ly k sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same_cf.
  assert (Ux : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha).
  apply MEQ; rewrite Ux.
  - unfold dwin_m. intros [X|[X|X]].
    + apply ND. do 2 right; left. unfold DSm. exact X.
    + apply ND. left. exact X.
    + apply ND. right; left. unfold YGcfInstFreeMid.DKm. exact X.
  - intros X. apply ND. do 4 right; left. exact X.
  - intros X. apply ND. do 3 right; left. exact X.
  - intros X. apply ND. do 5 right. unfold dshadow, DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v in X.
    rewrite Z_div_mult in X by lia. unfold YGcfInstFreeMid.DHm, shadow_addr. exact X. }
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
  destruct (EM (DGgiC.SPv (sptr_addr B ly (ck_user k))) (DGgiC.SPv (sptr_addr B ly (ck_user k)) + DGgiC.CNT8v (req_size (ck_req k))) a')
    as [Y1|Y1].
  { rewrite (SHV x Y1) in E'. discriminate. }
  destruct (EM (sp0 - DGbaseC.DFSTACK) sp0 a') as [Y2|Y2]. { exact (PRX mem (PRS a' Y2) E'). }
  assert (WD : (DGgmC.WINT ly a' \/ DGgmC.WINB (sptr_addr B ly (ck_user k)) a') \/
    ~ (DGgmC.WINT ly a' \/ DGgmC.WINB (sptr_addr B ly (ck_user k)) a')) by (unfold DGgmC.WINT, DGgmC.WINB; lia).
  destruct WD as [Y3|Y3]. { exact (PRX mem (PRW a' Y3) E'). }
  assert (NDZ : ~ dg_dzone ly a').
  { intros Y5. assert (P0 : apresent (w_H W) mem0 a').
    { split; [rewrite Ex; exact Hx|]. destruct (mem0 x) as [b0|] eqn:E0; [exists b0; rewrite Ex; exact E0 | exfalso; exact (Hv0 eq_refl)]. }
    destruct (PRD a' Y5 P0) as [_ [bd Hbd]]. rewrite Ex in Hbd. rewrite (EQD x Y5) in E'. congruence. }
  assert (NIZ : ~ dg_izone a') by (intros X; destruct (HIZ a' X) as (_ & R & _); rewrite Ex in R; exact (R ROM)).
  rewrite (MEQ x) in E'; [exact (Hv0 E') | | exact NDZ | exact NIZ | exact Y1].
  unfold dwin_m. intros [X|X]; [exact (Y2 X) | exact (Y3 X)]. }
(* the values the walk wrote *)
assert (NEW_hdr : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 16 + Z.of_nat i) = Some (YG0f.le_byte (3 + 256 * hb1) 4 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V1 Hi)).
assert (NEW_n : forall i, (i < 4)%nat -> rd' (sptr_addr B ly (ck_user k) - 12 + Z.of_nat i) = Some (YG0f.le_byte (ck_n k) 4 i))
  by (intros i Hi; exact (val_mem_aview_cf _ _ _ _ _ i V2 Hi)).
assert (NEW_unw : rd' (ly_T ly + t_unwinding) = Some 0).
{ subst rd'. pose proof (val_mem_aview_cf (w_H W) mem (ly_T ly + t_unwinding) 1 0 0%nat V3 ltac:(lia)) as H0.
  rewrite Z.add_0_r in H0. exact H0. }
assert (NEW_sh : forall a, DHm ly k a -> rd a <> None -> rd' a = Some shHeapFreed).
{ intros a Hd Hv. pose proof (mDH_sh ly S Hp rd M0 k Hk a Hd) as [SH1 SH2].
  assert (Ha : kImgEnd <= a < 2 ^ 64) by (unfold kImgEnd, kLowShadowBeg, kHighMemBeg in *; lia).
  pose proof (seg_rom_none_above im_segs a SEGS Ha) as ROM. unfold w64 in ROM.
  subst rd rd'. unfold aview, mbyte, mrestrict in Hv |- *.
  destruct (w_H W (Z_to_bv 64 a)) eqn:Hx.
  - rewrite ROM in Hv. exfalso. exact (Hv eq_refl).
  - rewrite (SHV (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by (unfold kImgEnd in Ha; lia).
    unfold dshadow, DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v. rewrite Z_div_mult by lia. unfold YGcfInstFreeMid.DHm, shadow_addr in Hd. exact Hd. }
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
          ltac:(unfold in_zr; cbn [fst snd]; exact X)) as AA. pose proof (app_addr_below_ceil a AA). mceil. unfold ASAN_CEIL in *. lia.
      - pose proof (g_app_oext B ly S Hp rd M0 (ly_SB ly, kStoreBlockSize) a ltac:(unfold owned_extents; cbn; tauto)
          ltac:(unfold in_zr; cbn [fst snd]; exact X)) as AA. pose proof (app_addr_below_ceil a AA). mceil. unfold ASAN_CEIL in *. lia.
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
  destruct (m_const_ok ly S Hp rd M0 k Hk z tr rd' hb1 (conj Hhb HB1M) sp0 Hsp IAL HCOl c j Hc Hj ND) as [R64' NDc].
  exact (AG _ R64' NDc). }
(* the hidden bytes of the shadow band do not change *)
assert (SHP : forall a, DHm ly k a -> w_H W (Z_to_bv 64 a) = false).
{ intros a Hd. destruct (w_H W (Z_to_bv 64 a)) eqn:Hx; [|reflexivity]. exfalso.
  pose proof (mDH_sh ly S Hp rd M0 k Hk a Hd) as [SH1 SH2].
  assert (Ha : kImgEnd <= a < 2 ^ 64) by (unfold kImgEnd, kLowShadowBeg, kHighMemBeg in *; lia).
  pose proof (seg_rom_none_above im_segs a SEGS Ha) as ROM. unfold w64 in ROM.
  pose proof (u_al8_cf B ly S Hp rd M0 k Hk) as (U8 & B8 & R8).
  apply Z.mod_divide in U8 as [c Hc]; [|lia].
  unfold YGcfInstFreeMid.DHm, shadow_addr in Hd. rewrite Hc, Z_div_mult in Hd by lia.
  set (g := c * 8 + 8 * (a - (SHADOW_OFF + c))).
  assert (Eg : shadow_addr g = a) by (unfold shadow_addr, g; replace (c * 8 + 8 * (a - (SHADOW_OFF + c))) with ((a - SHADOW_OFF) * 8) by lia;
    rewrite Z_div_mult by lia; lia).
  assert (G8' : g mod 8 = 0) by (unfold g; replace (c * 8 + 8 * (a - (SHADOW_OFF + c))) with ((a - SHADOW_OFF) * 8) by lia; apply Z_mod_mult).
  assert (Gb : ck_base B ly k <= g < ck_base B ly k + ck_extent k) by (unfold g; lia).
  assert (FC : find_chunk_at B ly (st_chunks S) g = Some k)
    by (apply (find_chunk_at_hit_cf B ly S Hp rd (st_chunks S) k g M0 ltac:(intros y Hy; exact Hy) (wfc_chunks_nodup _ _ _ _ _ WF) Hk Gb)).
  pose proof (amc_shadow _ _ _ _ _ M0 g _ G8' ltac:(unfold ashadow; rewrite FC; reflexivity)) as R. rewrite Eg in R.
  subst rd. unfold aview, mbyte, mrestrict in R. rewrite Hx, ROM in R. discriminate R. }
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
        mceil. unfold ASAN_CEIL in *. lia.
      * pose proof (g_app_oext B ly S Hp rd M0 (ly_SB ly, kStoreBlockSize) a ltac:(unfold owned_extents; cbn; tauto)
          ltac:(unfold in_zr; cbn [fst snd]; exact Y)) as AA.
        clear - Hb AA. unfold app_addr, in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *.
        mceil. unfold ASAN_CEIL in *. lia.
      * pose proof (g_static_img B ly S Hp rd M0 a (HDS a (or_intror Y))) as HI. pose proof (g_img B ly S Hp rd M0) as (I0 & I1 & I2).
        unfold in_zr in HI. clear - Hb HI I0 I2. unfold in_band_rw, kImgLo, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
    + pose proof (owned_static_bound B a (amc_syms _ _ _ _ _ M0) OS) as [X1 X2].
      clear - Hb X1 X2. unfold in_band_rw, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
  - intros C. destruct (HIZ a C) as (OS & _).
    pose proof (owned_static_bound B a (amc_syms _ _ _ _ _ M0) OS) as [X1 X2].
    clear - Hb X1 X2. unfold in_band_rw, kImgEnd, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *. lia.
  - intros X. assert (XD : DHm ly k a).
    { unfold dshadow, DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v in X. rewrite Z_div_mult in X by lia. unfold YGcfInstFreeMid.DHm, shadow_addr. exact X. }
    pose proof (SHP a XD) as F. rewrite Hh in F. discriminate. }
(* the machine cells (ARmcf's fields): off the walk's writes *)
assert (XN : forall a, XC B ly a -> rd' a = rd a).
{ intros a X. pose proof (x_owned B ly S Hp rd M0 a X) as [R64 _]. apply AG; [exact R64|].
  unfold YGcfInstFreeMid.Dm, YGcfInstFreeMid.DKm, DSm, YGcfInstFreeMid.DHm. intros [D|[D|[D|[D|[D|D]]]]].
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
(* the relation of the call state *)
destruct (m_post_parts ly S Hp rd M0 k Hk Hst z tr rd' HIZ HDS HDZ hb1 (conj Hhb HB1M) WFX sp0 Hsp
  AG VIS NEW_hdr NEW_n NEW_unw NEW_sh IAL DEP CONST' HPN EXH' ERR'
  (fun a Ha => conj (proj1 (HPFA a Ha)) (proj2 (HPFA a Ha) ly HLG))) as [MF SHAG].
assert (ARXX : ARX_cf B IOK Hp inst ly (qx S k z tr) W mem (with_vm_backing (m_vm_lazy md0) mat md0)).
{ apply ARX_cf_start; [exact Ei| |exact (xs_mapped_keep_cf ly S _ md0 _ (ms_secs S k z tr) (m_vmmaps_wvb _ _ _) HXM)].
  split; [exact MF | split; [|split; [|split]]].
  + eapply ALedger_same_cf; [exact (ms_ledger ly S Hp rd M0 k Hk z tr md0 LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
  + destruct BUD as (BU1 & BU2 & BU3). split; [|split; [|exact BU3]].
    * rewrite (ms_budget ly S Hp rd M0 k Hk z tr). exact BU1.
    * intros e He. rewrite (ms_sec_extents ly S Hp rd M0 k Hk z tr) in He. exact (BU2 e He).
  + eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
  + eapply (ahs_transfer_cf im_segs B ly S Hp (qx S k z tr) (w_H W) mem0 mem SEGS M0 HSH VIS HSK).
    * intros a _ C. exact (ms_client ly S Hp rd M0 k Hk z tr a C).
    * exact (ms_sec_extents ly S Hp rd M0 k Hk z tr).
    * intros g Hg Hga HF _. exact (SHAG g Hg Hga HF). }
(* the byte facts: the thread cache and free_cf's quarantine guard (rpreD_small_cf) *)
pose proof (qmeter_cf_tight S HQ) as (T1 & T2 & T3).
pose proof cf_malloc_max_pos as CMP. pose proof cf_malloc_max_bound as CMB.
assert (NNq : ck_n k <= kQuarantineMax) by (unfold ck_n; exact HQS).
pose proof (ms_quar ly S Hp rd M0 k Hk Hst z tr) as QX.
split.
- (* Enqueue's pre at the call state *)
  unfold YGcfInstEnq.enq_pre_cf. msp.
  + exact ARXX.
  + unfold batch_room_cf. rewrite (ms_reg S k z tr). exact HBR.
  + exists S, k, z, tr. split; [reflexivity | exact WF].
  + destruct (ms_split ly S Hp rd M0 k Hk z tr) as (l1 & l2 & _ & E' & _). rewrite E'. apply in_elt.
  + reflexivity.
  + exact (ms_fresh ly S Hp rd M0 k Hk Hst z tr).
  + exact HRA.
  + exact HRA4.
  + rewrite HSP0. replace (sp0 - 80) with (sp0 + (-5) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
  + rewrite HSP0. unfold CLenq.QSTACK_G, DGbaseC.DFSTACK in *. lia.
  + rewrite HSP0. lia.
  + intros a Ha. rewrite HSP0 in Ha. apply PRS. unfold CLenq.QSTACK_G, DGbaseC.DFSTACK in *. lia.
  + exact HGP.
  + exact HTP.
  + exact HA0.
  + exact HA1.
  + exact HA3.
  + exact HA4.
  + unfold qloose. rewrite (ms_qthread S k z tr), (ms_qglobal S k z tr), QX, (ms_queued S k z tr).
    unfold kQuarantineCacheMax, kQuarantineMax in *. lia.
  + exact NNq.
  + (* the unit's secondary admission at Put's call state: Put changes neither st_secs nor the secondary chunks *)
    apply (cf_hull_counts (qx S k z tr) S); [unfold nsec_cf; rewrite (ms_secs S k z tr); reflexivity
      | unfold sec_T_cf; rewrite (ms_secs S k z tr); reflexivity | exact HHO].
  + (* the read-only bytes at Put's call memory: enq_bridge_cf's premise (part 3c) *)
    exact HRO.
- (* the caller's facts EP_cf *)
  unfold YGcfInstEnq.EP_cf. msp.
  + rewrite (ms_qglobal S k z tr). exact T2.
  + rewrite QX, (ms_queued S k z tr). change (ck_n (qk k)) with (ck_n k). lia.
  + rewrite (ms_qthread S k z tr). exact T1.
  + exact NNq.
  + rewrite (ms_batches S k z tr). exact (L24_room_cf _ S WF HBR).
Qed.

(* Lane F1's drain-entry byte premise enq_qb_t (YGcfInstEnq.v:272-279, the hull form of cf-f1 22b5f48d6248) at the
   layer's QB := lane F2b's QB_cf kQuarantineMax and L24 := L24MAX_cf: the split byte bounds from EP_cf and the push
   (YGcfInstDrainR.QB_cf_enq_post), the hull admission from the pre-state's and Enqueue's st_secs frame
   (YGcfInstEnq.enq_qb_hull_cf), the batch count from EP_cf's room for one more batch. *)
Lemma enq_qb_QB_cf : YGcfInstEnq.enq_qb_t (ARX_cf B IOK Hp) L24MAX_cf (YGcfInstDrainR.QB_cf kQuarantineMax).
Proof.
intros inst ly X W mem md k nb X' _ (EG & EQ & [ET EN] & EL) _ _ _ _ HH HNB Hqt Hch Hqg HSE _.
destruct (YGcfInstEnq.push_facts_cf (st_qthread X) k nb HNB) as (PB & PI & PL).
split.
- eapply (YGcfInstDrainR.QB_cf_enq_post X X' k nb ET EG EN Hqt Hqg).
  + unfold quar_n in *. rewrite Hch. rewrite queued_n_eq in EQ |- *.
    rewrite Hqt, Hqg, PI. lia.
  + exact (YGcfInstEnq.enq_qb_hull_cf X X' HH HSE).
- unfold all_batches in *. rewrite Hqt, Hqg. rewrite length_app in *.
  clear - PL EL. lia.
Qed.

(* DIfaceExtRh's enqueue field (YGcfInstFree.v, exr_enqueue: DIfaceExt's text) at the layer's choices, from the unit's
   three Enqueue arms (lane F1's seam YGcfInstEnq.EnqArmsCf), this file's call-site bridge and enq_qb_QB_cf, through
   lane F1's YGcfInstEnq.di_enqueue_cf. *)
Theorem exr_enqueue_cf : YGcfInstEnq.EnqArmsCf B (ARX_cf B IOK Hp) ->
  forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
    ARX_cf B IOK Hp inst ly S W mem0 md0 -> rpreD_small_cf B S n -> fpre_hp_cf im_segs B Hp ly S W mem0 p n ->
    In (p, n) (blocks S) -> U_cf B tr S ->
    find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
    0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
    dmem_m W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (CLdepot.dpost_x im_segs B inst ly S W tr z) mem ->
    (fun m => arodata_ok_cf im_segs B m) mem ->
    YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> spZ regs = sp0 - 80 ->
    getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
    getr regs 10 = w64 (ly_T ly + t_qc) -> getr regs 11 = w64 (ly_T ly + t_cache) ->
    getr regs 13 = w64 (sptr_addr B ly p - kChunkHeaderSize) -> getr regs 14 = w64 (req_size n) ->
    amreal im_segs (enqueue (qk k) (qx S k z tr)) W
      (cfg_at im_segs dg_enqueue regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
      (fun r W' c' => exists regs' mem' md' nb,
        c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
        DMspec.acall_post_x B (ARX_cf B IOK Hp) (aowned B) inst YFewC.QSTACK ly (qx S k z tr) W regs mem
          (with_vm_backing (m_vm_lazy md0) mat md0) (fun _ => False) ly (snd r) W' regs' mem' md' /\
        st_qthread (snd r) = qc_push (st_qthread (qx S k z tr)) (qk k) nb /\
        match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end /\
        st_chunks (snd r) = st_chunks (qx S k z tr) /\ st_qglobal (snd r) = st_qglobal (qx S k z tr) /\
        (forall a, aowned B ly (snd r) a -> aowned B ly (qx S k z tr) a) /\
        val_mem im_segs (mrestrict (w_H W') mem') (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread (snd r))) /\
        (qc_bytes (st_qthread (snd r)) <= kQuarantineCacheMax -> qtight (snd r)) /\
        (kQuarantineCacheMax < qc_bytes (st_qthread (snd r)) ->
          YGcfInstDrainR.QB_cf kQuarantineMax (snd r) /\ Z.of_nat (length (all_batches (snd r))) <= L24MAX_cf)).
Proof.
intros ARMS inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat HA HR HF HB HU Hf Hk Hs1 Hs2 Hs3 Hs4 Hh1 Hh2 HM HRO.
exact (YGcfInstEnq.di_enqueue_cf B Hp (ARX_cf B IOK Hp) (ARX_cf_ARcf B IOK Hp) (rpreD_small_cf B)
  (fpre_hp_cf im_segs B Hp) (CLdepot.dpost_x im_segs B) L24MAX_cf (YGcfInstDrainR.QB_cf kQuarantineMax)
  ARMS enq_bridge_holds_cf enq_qb_QB_cf inst ly S W mem0 md0 p n tr k z hb1 sp0 regs mem mat HA HR HF HB HU Hf Hk
  Hs1 Hs2 Hs3 Hs4 Hh1 Hh2 HM HRO).
Qed.

(* The primed callee record with its enqueue field from the unit's arms: YGcfInstFree.Build_DIfaceExtRh at the
   layer's choices (L24 := L24MAX_cf, QB := QB_cf kQuarantineMax) with exr_enqueue := exr_enqueue_cf; it takes the
   other ten fields in the record's order (exr_depot, exr_dpost_aok, then exr_drain .. exr_rview).  The type checker
   compares exr_enqueue_cf's statement with the field's text. *)
Definition diface_ext_rh_cf (ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
  (DRq : astate -> list chunk -> list Z -> Prop) (ARMS : YGcfInstEnq.EnqArmsCf B (ARX_cf B IOK Hp)) :=
  fun Ed Ea => YGcfInstFree.Build_DIfaceExtRh B IOK Hp ARXr L24MAX_cf (YGcfInstDrainR.QB_cf kQuarantineMax) DRq Ed Ea
    (exr_enqueue_cf ARMS).
End p.
End a.
