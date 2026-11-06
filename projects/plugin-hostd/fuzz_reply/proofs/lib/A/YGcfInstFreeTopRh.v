(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch, plan row (c)): the PRIMED twin of the generic cf layer's
   Deallocate top YGcfInstFreeTop.v, under the re-hide.  A secondary Recycle unmaps its map and re-hides the dead
   shadow interior, so the released post (plain wle, a frame with no exception) cannot hold at a real recycle; this
   file composes the PRIMED contract YGcfMallocComposeERh.adealloc_realizes_raw_cf_em_m_rh (amreal' over
   YGcfRehidePost.RZ_cf, leaf YGcfMallocComposeERhBase.dealloc_leaf_raw_em_rh).  rule 24: no function proved (kind:
   top-level composition of a unit's walk tops over the layer's interface instance).

   - [adealloc_realizes_raw_em_sig_rh]: YGcfInstFreeTop.adealloc_realizes_raw_em_sig's case split over
     YGcfInstFreeSig.WalkSigDrh: the null / common / mid arms recycle nothing, so their released walks lift
     (YG0dH.amreal_amreal' and ERhBase.dealloc_leaf_raw_em_rh_of); the drain arm is the unit's primed wsr_drn.  The
     common arm's batch room reads the interface's view field from R3's primed record DIfaceRh.DIface_rh.
   - [adealloc_join_cf_rh] / [adealloc_raw_em_rh_lift]: the twins of YGcfInstFreeTop.adealloc_join_cf /
     adealloc_raw_em_lift (free_cf's size test; the call-site relation ARX /\ qtight).
   - [adealloc_realizes_raw_cf_em_m_rh_walk] / [adealloc_realizes_raw_cf_em_m_rh_cf]: the primed Deallocate contract
     at the walk's relation YGcfInstBase.ARX_cf and at the call site's ARXq_cf, the form CfR's primed realloc compose
     takes.  Their callee premise is the PRIMED record YGcfInstFree.DIfaceExtRh (drain and Recycle at R3's twins),
     their walk premise the PRIMED YGcfInstFreeSig.WalkSigDrh (drain and big-block arms primed, wsr_rcs_rh).
   Generic over CfImg / CfParams / AImg / DImg and the instance predicate IOK; no numeral of any image; no event term. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG DMspec DMiface DGif0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require MemnormT MemnormDleaf ErrnoG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DIfaceRh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose YGcfMallocComposeE YGcfMallocComposeERh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstFreeSig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstFreeView YGcfInstFreeQ YGcfInstFreeModel YGcfInstFree.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstFreePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfDIface CLdepot YGcfInstDrainR.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The case split over WalkSigDrh (YGcfInstFreeTop.adealloc_realizes_raw_em_sig's proof, MemnormDtop.v:75-100,  *)
(*    at the primed contract).                                                                                       *)
Section s.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variables (ARX ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world im_segs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable atpD : Z.
Variable rpreB : astate -> Z -> Prop.
Variable ARXrB : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable DRqB : astate -> list chunk -> list Z -> Prop.
Variable MP : (word -> option byte) -> Prop.
Hypothesis IF : DIfaceRh.DIface_rh B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
Hypothesis WS : WalkSigDrh B U ft ARX AOX rpre lpost fpre atpD rpreB ARXrB DRqB MP.

(* a released walk that ends in the released (or errno-weak) leaf gives the primed run *)
Local Lemma lift_em : forall inst ly S W regs mem md p n tr,
  amreal im_segs (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
    (MemnormT.dealloc_leaf_raw_em im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr) ->
  YG0dH.amreal' im_segs YGcfRehidePost.RZ_cf (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
    (dealloc_leaf_raw_em_rh im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof.
intros inst ly S W regs mem md p n tr H.
eapply YG0dH.amreal'_mono; [| exact (YG0dH.amreal_amreal' im_segs YGcfRehidePost.RZ_cf _ _ _ _ H)].
intros r W' c' L. exact (dealloc_leaf_raw_em_rh_of im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c' L).
Qed.

Local Lemma lift_eem : forall inst ly S W regs mem md p n tr,
  amreal im_segs (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
    (MemnormDleaf.dealloc_leaf_raw_eem B ft ARX AOX lpost inst ly S W regs mem md p n tr) ->
  YG0dH.amreal' im_segs YGcfRehidePost.RZ_cf (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
    (dealloc_leaf_raw_em_rh im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof.
intros inst ly S W regs mem md p n tr H. apply lift_em.
eapply amreal_mono; [| exact H].
intros r W' c' L. exact (MemnormDleaf.leaf_raw_eem_raw_em B ft ARX AOX lpost inst ly S W regs mem md p n tr r W' c' L).
Qed.

Theorem adealloc_realizes_raw_em_sig_rh :
  adealloc_realizes_raw_em_rh im_segs B U ft ARX AOX rpre lpost fpre cf_pc_deallocate atpD MP.
Proof.
intros inst so bp ly S W regs mem md p n tr PRE0 HMP.
pose proof PRE0 as PRE1.
destruct PRE1 as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
destruct Hp0 as [HN|HBLK].
{ exact (lift_eem inst ly S W regs mem md p n tr
    (wsr_null B U ft ARX AOX rpre lpost fpre atpD rpreB ARXrB DRqB MP WS inst so bp ly S W regs mem md p n tr PRE0 HN)). }
destruct (Z_le_gt_dec (qc_bytes (st_qthread S) + req_size n + (if need_new_batch (st_qthread S) then kBatchBytes else 0)) kQuarantineCacheMax) as [ND|DR].
2:{ exact (wsr_drn B U ft ARX AOX rpre lpost fpre atpD rpreB ARXrB DRqB MP WS inst so bp ly S W regs mem md p n tr PRE0 HMP HBLK
      ltac:(lia)). }
destruct (need_new_batch (st_qthread S)) eqn:NB.
- exact (lift_em inst ly S W regs mem md p n tr
    (wsr_mid B U ft ARX AOX rpre lpost fpre atpD rpreB ARXrB DRqB MP WS inst so bp ly S W regs mem md p n tr PRE0 HMP HBLK NB
      ltac:(rewrite NB; exact ND))).
- pose proof (DIfaceRh.dih_view B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF inst ly S W mem md p n
    HARX HRP HFP HBLK) as DV.
  assert (ER : exists lastb initr, rev (qc_list (st_qthread S)) = lastb :: initr).
  { revert NB. unfold need_new_batch. destruct (rev (qc_list (st_qthread S))) as [|lastb initr] eqn:E; [discriminate|].
    intros _. exists lastb, initr. reflexivity. }
  destruct ER as (lastb & initr & ER).
  assert (BL : Z.of_nat (length (b_items lastb)) < kBatchSlots).
  { pose proof (db_slots W ly mem (st_qthread S) lastb (sptr_addr B ly p) (req_size n) (dv_batch B W ly inst mem S p n DV lastb initr ER)) as HS.
    unfold DGgiC.BCv in HS. revert NB. unfold need_new_batch. rewrite ER. intros NB'. apply Z.eqb_neq in NB'. lia. }
  rewrite Z.add_0_r in ND.
  exact (lift_eem inst ly S W regs mem md p n tr
    (wsr_common B U ft ARX AOX rpre lpost fpre atpD rpreB ARXrB DRqB MP WS inst so bp ly S W regs mem md p n tr
      lastb initr PRE0 HBLK ER BL ND)).
Qed.
End s.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The lift from a walk relation ARX to the call-site relation ARX /\ qtight (the twin of                        *)
(*    YGcfInstFreeTop.adealloc_raw_em_lift): the pre drops qtight; the post's qtight is the leaf's lpost.             *)
Lemma adealloc_raw_em_rh_lift : forall (segs : list Segment) B U ft
  (ARX : Z -> alayout -> astate -> world segs -> (word -> option byte) -> Model -> Prop) AOX rpre fpre pcD atp MP,
  adealloc_realizes_raw_em_rh segs B U ft ARX AOX rpre qtight fpre pcD atp MP ->
  adealloc_realizes_raw_em_rh segs B U ft (fun inst ly S W mem md => ARX inst ly S W mem md /\ qtight S) AOX rpre
    qtight fpre pcD atp MP.
Proof.
intros segs B U ft ARX AOX rpre fpre pcD atp MP H inst so bp ly S W regs mem md p n tr PRE HMP.
destruct PRE as ((HA & _) & REST).
eapply YG0dH.amreal'_mono; [| exact (H inst so bp ly S W regs mem md p n tr (conj HA REST) HMP)].
intros r W' c' (ly' & regs' & mem' & md' & Hc & ((PA & P2) & P8) & HE & HK & HL & HT).
exists ly', regs', mem', md'. split; [exact Hc|]. split; [exact (conj (conj (conj PA HL) P2) P8)|].
split; [exact HE|]. split; [exact HK|]. split; [exact HL | exact HT].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. free_cf's size test (the twin of YGcfInstFreeTop.adealloc_join_cf) at the primed contract.                     *)
Section j.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable Hp : list Z.
Variable atp : Z.
Variable MP : (word -> option byte) -> Prop.

Lemma adealloc_join_cf_rh :
  adealloc_realizes_raw_em_rh im_segs B U ft ARX AOX (rpreD_small_cf B) lpost (fpre_hp_cf im_segs B Hp)
    cf_pc_deallocate atp MP ->
  (forall inst so bp ly S W regs mem md p n tr,
    dealloc_pre im_segs B U ARX (rpreD_big_cf B) (fpre_hp_cf im_segs B Hp) atp inst so bp ly S W regs mem md p n tr ->
    In (p, n) (blocks S) ->
    YG0dH.amreal' im_segs YGcfRehidePost.RZ_cf (ft p tr S) W (cfg_at im_segs cf_pc_deallocate regs mem md)
      (dealloc_leaf_raw_em_rh im_segs B ft ARX AOX lpost inst ly S W regs mem md p n tr)) ->
  adealloc_realizes_raw_em_rh im_segs B U ft ARX AOX (rpreD_free_cf B) lpost (fpre_hp_cf im_segs B Hp)
    cf_pc_deallocate atp MP.
Proof.
intros SM BG inst so bp ly S W regs mem md p n tr PRE HMP.
pose proof PRE as (HA & HR & PR).
assert (Hd : p = PNull \/ p <> PNull) by (destruct p; [left; reflexivity | right; discriminate ..]).
destruct Hd as [HN|HN].
- subst p.
  destruct PR as (Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
    Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & _ & HFP).
  assert (Q0 : req_size 0 <= kQuarantineMax) by (change (req_size 0) with 1; unfold kQuarantineMax; lia).
  assert (PRE0 : dealloc_pre im_segs B U ARX (rpreD_small_cf B) (fpre_hp_cf im_segs B Hp) atp inst so bp ly S W regs mem md
    PNull 0 tr).
  { exact (conj HA (conj (conj HR Q0) (conj Hra (conj Hra4096 (conj Hal (conj Hlo (conj Hbot (conj Hhi (conj Hpres
      (conj Hgp (conj Htp (conj Hr10 (conj Hr11 (conj Hr12 (conj Hr13 (conj Hr14 (conj Hr15 (conj Hso1 (conj Hso2
      (conj Hso3 (conj Hbp1 (conj Hbp2 (conj Hbp3 (conj Htrlen (conj PSO (conj PLEN (conj PBUF (conj Htr
      (conj (or_introl eq_refl) HFP))))))))))))))))))))))))))))). }
  eapply YG0dH.amreal'_mono; [| exact (SM inst so bp ly S W regs mem md PNull 0 tr PRE0 HMP)].
  intros r W' c' (ly' & regs' & mem' & md' & Hc & HP & HE & HK & HL & HT).
  exists ly', regs', mem', md'. split; [exact Hc|]. split.
  + eapply dealloc_post_raw_rh_E_mono; [| exact HP]. intros a [Hne _]. exfalso. exact (Hne eq_refl).
  + exact (conj HE (conj HK (conj HL HT))).
- assert (HBLK : In (p, n) (blocks S)).
  { destruct PR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & [E|E] & _); [exfalso; exact (HN E) | exact E]. }
  destruct (Z_le_gt_dec (req_size n) kQuarantineMax) as [Hq|Hq].
  + exact (SM inst so bp ly S W regs mem md p n tr (conj HA (conj (conj HR Hq) PR)) HMP).
  + exact (BG inst so bp ly S W regs mem md p n tr (conj HA (conj (conj HR (Z.gt_lt _ _ Hq)) PR)) HBLK).
Qed.
End j.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The compose's primed Deallocate Prop at the layer's relations (the twins of YGcfInstFreeTop's section c).       *)
Section c.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable ARXr : list Z -> Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
(* The image premises of the layer's interface instance (YGcfInstFree.v), as YGcfInstFreeTop's section c. *)
Hypothesis HIOK : IOK_ok B IOK.
Hypothesis HIOKD : FM_INST_OK B.
Hypothesis HIMG : YGcfDIface.IMG_COVER.
Hypothesis HTSD : FV_TSD B.
Hypothesis HIAL : FV_IAL B.
Hypothesis HQC : FQ_CONST B.
Hypothesis HQB : QB_BYTES QB.
Hypothesis HDZ : YGcfDIface.DZONE_OWNED B.
Hypothesis HIZ : YGcfDIface.IZONE_OWNED B.
Hypothesis HZ3 : FV_ZONE3.
Hypothesis HIZR : FP_IZONE_ROM B.
Hypothesis HDS : FP_DSTAT B.
Hypothesis HDZF : FP_DZONE_FP B.
Hypothesis HCO : FP_CONST B.
Hypothesis HERRB : ERRB_APART B.
Hypothesis HPFA : PF_APART B.
(* the memory predicate at Deallocate's entry, as YGcfMallocComposeERh.adealloc_realizes_raw_cf_em_m_rh takes it *)
Local Notation MPcf := (fun m => arodata_ok_cf im_segs B m).

(* At the walk's relation ARX_cf: the small side from the primed interface instance and the unit's primed walk record,
   the recycle side from its primed big-block arm (wsr_big_rh), joined by free_cf's size test. *)
Theorem adealloc_realizes_raw_cf_em_m_rh_walk :
  (forall Hp, DIfaceExtRh B IOK Hp (ARXr Hp) L24 QB DRq) ->
  (forall Hp, WalkSigDrh B (U_cf B) free_cf (ARX_cf B IOK Hp) (aowned B) (rpreD_small_cf B) qtight
     (fpre_hp_cf im_segs B Hp) atp_cf (rpreD_big_cf B) (ARXr Hp) (YGcfInstDrainR.DRq_cf B YGcfInstDrainR.NMAXD_big_cf)
     MPcf) ->
  adealloc_realizes_raw_cf_em_m_rh im_segs B atp_cf (ARX_cf B IOK).
Proof.
intros E WS Hp.
apply adealloc_join_cf_rh.
- exact (adealloc_realizes_raw_em_sig_rh B (U_cf B) free_cf (ARX_cf B IOK Hp) (ARXr Hp) (aowned B) (rpreD_small_cf B) qtight
    (fpre_hp_cf im_segs B Hp) (CLdepot.dpost_x im_segs B) drain_body_cf L24 QB DRq atp_cf (rpreD_big_cf B)
    (ARXr Hp) (YGcfInstDrainR.DRq_cf B YGcfInstDrainR.NMAXD_big_cf) MPcf
    (diface_rh_cf B IOK Hp (ARXr Hp) L24 QB DRq HIOK HIOKD HIMG HTSD HIAL HQC HQB HDZ HIZ HZ3 HIZR HDS HDZF HCO HERRB HPFA
      (E Hp))
    (WS Hp)).
- exact (wsr_big_rh _ _ _ _ _ _ _ _ _ _ _ _ _ (WS Hp)).
Qed.

(* At the call site's relation ARXq_cf (ARX_cf and qtight, YGcfInstBase), the form the primed realloc compose takes. *)
Theorem adealloc_realizes_raw_cf_em_m_rh_cf :
  (forall Hp, DIfaceExtRh B IOK Hp (ARXr Hp) L24 QB DRq) ->
  (forall Hp, WalkSigDrh B (U_cf B) free_cf (ARX_cf B IOK Hp) (aowned B) (rpreD_small_cf B) qtight
     (fpre_hp_cf im_segs B Hp) atp_cf (rpreD_big_cf B) (ARXr Hp) (YGcfInstDrainR.DRq_cf B YGcfInstDrainR.NMAXD_big_cf)
     MPcf) ->
  adealloc_realizes_raw_cf_em_m_rh im_segs B atp_cf (ARXq_cf B IOK).
Proof.
intros E WS Hp.
exact (adealloc_raw_em_rh_lift im_segs B (U_cf B) free_cf (ARX_cf B IOK Hp) (aowned B) (rpreD_free_cf B)
  (fpre_hp_cf im_segs B Hp) cf_pc_deallocate atp_cf MPcf (adealloc_realizes_raw_cf_em_m_rh_walk E WS Hp)).
Qed.
End c.
End a.
