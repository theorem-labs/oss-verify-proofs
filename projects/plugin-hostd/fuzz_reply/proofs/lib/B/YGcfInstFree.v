(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch): the generic cf layer's Deallocate interface instances at the
   layer's walk relation YGcfInstBase.ARX_cf: DGif0.DIface, DIfaceR.DIfaceR, ErrnoG.DIfaceE / DIfaceRE and
   MnRecycle.DIfaceREm.  The cf twin of c5's DGif1.v (diface_cgif) and of DGif0cgif.v's role (the image's DImg is the
   unit's: a Context class here, never an instance).  rule 24: no function proved (kind: interface-instance
   discharge: the record assembled from the layer's field lemmas and the callee lanes' fields).

   The instance: U := U_cf B, ft := free_cf, ARX := ARX_cf B IOK Hp, AOX := aowned B, rpre := rpreD_small_cf B (the
   enqueue side of free_cf's size test: rpreD_free_cf and req_size n <= kQuarantineMax; YGcfInstFreeModel),
   lpost := qtight, fpre := fpre_hp_cf im_segs B Hp, dbody := drain_body_cf, dpost := CLdepot.dpost_x im_segs B
   (lane F1's dpost_cf); the drain's cut relation ARXr, the batch bound L24, the drain's byte premise QB and the
   recycle invariant DRq are section variables (lane F2b's ARXr_cf / QB_cf / DRq_cf with L24MAX_cf).
   - Proved here, over ARcf, by this lane: di_inst, di_view_n, di_view, di_shape_n, di_shape, di_lpost_d, di_qview,
     di_qowned, di_post_c, di_post_n, di_frame, di_stack, di_owned, di_owned_b, di_owned_i, di_owned_x
     (YGcfInstFreeView / Q / Post / Model); di_view at DGif0's dv_zone bound, which rpreD_small_cf's guard gives
     (a working branch 002b8cc32f7).
   - The record [DIfaceExt] holds the fields the layer takes from the callee lanes, each a named field at its DGif0
    text: di_depot, di_dpost_aok, di_enqueue (lane F1; its YGcfInstEnq.di_enqueue_cf takes the call-site bridge
    enq_bridge_cf, which this lane proves: YGcfInstFreeMidE.enq_bridge_holds_cf, over YGcfInstFreeMid's model and
    memory sides); di_drain, di_requar_x / r / e,
     di_rchunk, di_cdealloc, di_frame_r, di_rview (lane F2b).
   Image premises (named, over the classes' fields and the symbol table): IOK_ok, FM_INST_OK, YGcfDIface.IMG_COVER,
   FV_TSD, FV_IAL, FV_ZONE3, FQ_CONST, QB_BYTES, YGcfDIface.DZONE_OWNED, YGcfDIface.IZONE_OWNED, FP_IZONE_ROM,
   FP_DSTAT, FP_DZONE_FP, FP_CONST.
   Generic over CfImg / CfParams / AImg / DImg and IOK; no numeral of any image; the room comes from bytes, with no
   event-count term. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG DMspec DMiface DGif0 DIfaceR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG MnRecycle.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstFreeView YGcfInstFreeQ YGcfInstFreeModel YGcfInstFreePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CLdepot.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfDIface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DIfaceRh.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
(* the depot post: CLdepot's (lane F1's dpost_cf is that text) *)
Local Notation dpost := (CLdepot.dpost_x im_segs B).
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Local Notation ARX := (ARX_cf B IOK Hp).
Local Notation U := (U_cf B).
Local Notation rpre := (rpreD_small_cf B).
Local Notation fpre := (fpre_hp_cf im_segs B Hp).
Local Notation ft := free_cf.
Local Notation lpost := qtight.
Local Notation dbody := drain_body_cf.
Local Notation AOX := (aowned B).
(* DGif0.DIface's memory predicate at Put's call (field round 3 part 3c): arodata_ok_cf, as
   YGcfMallocComposeE.adealloc_realizes_raw_cf_em_m takes it at Deallocate's entry (lane F1's YGcfInstEnq.MP_enq_cf) *)
Local Notation MP := (fun m => arodata_ok_cf im_segs B m).

(* ================================================================================================================ *)
(* 1. The fields taken from elsewhere, at DGif0's text (DGif0.v:274-275, :282-329, :331, :344-352, :355-371).      *)
Record DIfaceExt : Prop := {
  ext_depot : forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
    ARX inst ly S W mem0 md0 -> U tr S ->
    (forall x : word, dg_dzone ly (bv_unsigned x) \/ (dg_czone ly (bv_unsigned x) /\ ~ dg_izone (bv_unsigned x)) -> mem x = mem0 x) ->
    getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
    getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
    (forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
    buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
    buf + 8 * 30 <= bv_unsigned (getr regs 2) - YFl0C.DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
    bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - YFl0C.DEP_STK ->
    bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
    (forall a, bv_unsigned (getr regs 2) - YFl0C.DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
    SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 dg_depot) mem (seg_rom im_segs)) md)
    (fun W' c' => W' = W /\ exists z regs' mem' mat,
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
      regs_preserved regs regs' /\
      (forall x : word, ~ (bv_unsigned (getr regs 2) - YFl0C.DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
         ~ dg_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
      (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
      dpost inst ly S W tr z mem');
  ext_dpost_aok : forall inst ly S W tr z m, dpost inst ly S W tr z m -> aok S (KDepot tr) z;
  ext_enqueue : forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) -> U tr S ->
    find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
    0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
    dmem_m W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) mem -> MP mem ->
    YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> spZ regs = sp0 - 80 ->
    getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
    getr regs 10 = w64 (ly_T ly + t_qc) -> getr regs 11 = w64 (ly_T ly + t_cache) ->
    getr regs 13 = w64 (sptr_addr B ly p - kChunkHeaderSize) -> getr regs 14 = w64 (req_size n) ->
    amreal im_segs (enqueue (qk k) (qx S k z tr)) W
      (cfg_at im_segs dg_enqueue regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
      (fun r W' c' => exists regs' mem' md' nb,
        c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
        acall_post_x B ARX AOX inst YFewC.QSTACK ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (fun _ => False)
          ly (snd r) W' regs' mem' md' /\
        st_qthread (snd r) = qc_push (st_qthread (qx S k z tr)) (qk k) nb /\
        match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end /\
        st_chunks (snd r) = st_chunks (qx S k z tr) /\ st_qglobal (snd r) = st_qglobal (qx S k z tr) /\
        (forall a, AOX ly (snd r) a -> AOX ly (qx S k z tr) a) /\
        val_mem im_segs (mrestrict (w_H W') mem') (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread (snd r))) /\
        (qc_bytes (st_qthread (snd r)) <= kQuarantineCacheMax -> lpost (snd r)) /\
        (kQuarantineCacheMax < qc_bytes (st_qthread (snd r)) -> QB (snd r) /\ Z.of_nat (length (all_batches (snd r))) <= L24));
  ext_drain : drain_spec_cf B ARX AOX dbody L24 QB;
  ext_requar_x : di_requar_x_t B ARX AOX L24 QB;
  ext_requar_r : di_requar_r_t B ARX ARXr AOX L24 QB DRq;
  ext_requar_e : di_requar_e_t ARX ARXr DRq;
  ext_rchunk : di_rchunk_t B ARXr AOX DRq;
  ext_cdealloc : di_cdealloc_t B ARXr AOX DRq;
  ext_frame_r : di_frame_t ARXr AOX;
  ext_rview : di_rview_t B ARXr DRq
}.

(* The PRIMED callee-field record (plan row (c), Main's decision (i)): the callee fields at the re-hide.  A secondary
   Recycle unmaps its map and re-hides the dead shadow interior (YA0nR.SRr'_rehide_ret), so two of DIfaceExt's fields
   are FALSE at a real recycle: the drain (DMspec.drain_spec_cf, a walk whose run recycles) and Recycle
   (DMiface.di_rchunk_t).  They become R3's twins (DIfaceRh.drain_spec_cf_rh, DIfaceRh.di_rchunk_rh_t: amreal' at
   YGcfRehidePost.RZ_cf, acall_post_x_rh).  The other nine are DIfaceExt's text: depot, dpost_aok, enqueue, frame_r,
   rview, and cdealloc (it frees a primary batch object, unmaps nothing, re-hides nothing; DMiface.v:245-254) and
   requar_x / r / e (one-world relation facts, no walk, no wle; DMiface.v:208-228). *)
Record DIfaceExtRh : Prop := {
  exr_depot : forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
    ARX inst ly S W mem0 md0 -> U tr S ->
    (forall x : word, dg_dzone ly (bv_unsigned x) \/ (dg_czone ly (bv_unsigned x) /\ ~ dg_izone (bv_unsigned x)) -> mem x = mem0 x) ->
    getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
    getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
    (forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
    buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
    buf + 8 * 30 <= bv_unsigned (getr regs 2) - YFl0C.DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
    bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - YFl0C.DEP_STK ->
    bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
    (forall a, bv_unsigned (getr regs 2) - YFl0C.DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
    SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 dg_depot) mem (seg_rom im_segs)) md)
    (fun W' c' => W' = W /\ exists z regs' mem' mat,
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
      regs_preserved regs regs' /\
      (forall x : word, ~ (bv_unsigned (getr regs 2) - YFl0C.DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
         ~ dg_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
      (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
      dpost inst ly S W tr z mem');
  exr_dpost_aok : forall inst ly S W tr z m, dpost inst ly S W tr z m -> aok S (KDepot tr) z;
  exr_enqueue : forall inst ly S W mem0 md0 p n tr k z hb1 sp0 (regs : bvmap 5 word) (mem : word -> option byte) mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> fpre ly S W mem0 p n -> In (p, n) (blocks S) -> U tr S ->
    find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
    ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
    0 <= hb1 < 256 -> val_mem im_segs (mrestrict (w_H W) mem0) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
    dmem_m W ly sp0 mem0 (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) mem -> MP mem ->
    YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs -> spZ regs = sp0 - 80 ->
    getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
    getr regs 10 = w64 (ly_T ly + t_qc) -> getr regs 11 = w64 (ly_T ly + t_cache) ->
    getr regs 13 = w64 (sptr_addr B ly p - kChunkHeaderSize) -> getr regs 14 = w64 (req_size n) ->
    amreal im_segs (enqueue (qk k) (qx S k z tr)) W
      (cfg_at im_segs dg_enqueue regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
      (fun r W' c' => exists regs' mem' md' nb,
        c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
        acall_post_x B ARX AOX inst YFewC.QSTACK ly (qx S k z tr) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0) (fun _ => False)
          ly (snd r) W' regs' mem' md' /\
        st_qthread (snd r) = qc_push (st_qthread (qx S k z tr)) (qk k) nb /\
        match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end /\
        st_chunks (snd r) = st_chunks (qx S k z tr) /\ st_qglobal (snd r) = st_qglobal (qx S k z tr) /\
        (forall a, AOX ly (snd r) a -> AOX ly (qx S k z tr) a) /\
        val_mem im_segs (mrestrict (w_H W') mem') (ly_T ly + t_qc + 24) 8 (qc_bytes (st_qthread (snd r))) /\
        (qc_bytes (st_qthread (snd r)) <= kQuarantineCacheMax -> lpost (snd r)) /\
        (kQuarantineCacheMax < qc_bytes (st_qthread (snd r)) -> QB (snd r) /\ Z.of_nat (length (all_batches (snd r))) <= L24));
  (* PRIMED: the drain under the re-hide (R3's twin of DMspec.drain_spec_cf) *)
  exr_drain : DIfaceRh.drain_spec_cf_rh B ARX AOX dbody L24 QB;
  exr_requar_x : di_requar_x_t B ARX AOX L24 QB;
  exr_requar_r : di_requar_r_t B ARX ARXr AOX L24 QB DRq;
  exr_requar_e : di_requar_e_t ARX ARXr DRq;
  (* PRIMED: QuarantineCallback::Recycle under the re-hide (R3's twin of DMiface.di_rchunk_t) *)
  exr_rchunk : DIfaceRh.di_rchunk_rh_t B ARXr AOX DRq;
  exr_cdealloc : di_cdealloc_t B ARXr AOX DRq;
  exr_frame_r : di_frame_t ARXr AOX;
  exr_rview : di_rview_t B ARXr DRq
}.

(* A callee set that re-hides nothing gives the primed record (R3's drain_spec_cf_rh_of / di_rchunk_rh_of). *)
Lemma DIfaceExtRh_of : DIfaceExt -> DIfaceExtRh.
Proof.
intros [Ed Ea Ee Edr Erx Err Ere Erc Ecd Efr Erv]. constructor.
- exact Ed.
- exact Ea.
- exact Ee.
- exact (DIfaceRh.drain_spec_cf_rh_of B ARX AOX dbody L24 QB Edr).
- exact Erx.
- exact Err.
- exact Ere.
- exact (DIfaceRh.di_rchunk_rh_of B ARXr AOX DRq Erc).
- exact Ecd.
- exact Efr.
- exact Erv.
Qed.

(* The primed drain at any extra post conjunct (R3's drain_spec_g_rh; lane F2b's ds_drain_rh_cf proves its memnorm form
   DIfaceRh.de_drain_m_rh_t = drain_spec_g_rh .. (acall_raw_em_x ..)) gives exr_drain's view form: drop the conjunct. *)
Lemma exr_drain_of_g : forall XR, DIfaceRh.drain_spec_g_rh B ARX AOX dbody L24 QB XR ->
  DIfaceRh.drain_spec_cf_rh B ARX AOX dbody L24 QB.
Proof.
intros XR H inst ly X W regs mem md PRE.
eapply YG0dH.amreal'_mono; [| exact (H inst ly X W regs mem md PRE)].
intros r W' c' (regs' & mem' & md' & Hc & HP & _). exists regs', mem', md'. exact (conj Hc HP).
Qed.

(* ================================================================================================================ *)
(* 2. DIface at the cf instance.                                                                                    *)
Section i.
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
(* the post fields' image premises (YGcfInstFreePost section 0) *)
Hypothesis HIZR : FP_IZONE_ROM B.
Hypothesis HDS : FP_DSTAT B.
Hypothesis HDZF : FP_DZONE_FP B.
Hypothesis HCO : FP_CONST B.
(* the error-buffer object avoids the walk's image zones (the relation's machine cells are ARmcf's fields) *)
Hypothesis HERRB : ERRB_APART B.
(* Printf's two cells avoid the walk's image zones (ARmcf's amc_pf_cells, field round 3) *)
Hypothesis HPFA : PF_APART B.

Lemma di_view_n_cf : forall inst ly S W mem md n, ARX inst ly S W mem md -> rpre S n -> dview_n B W ly inst mem.
Proof.
intros inst ly S W mem md n HA ((_ & _ & HI & _) & _).
pose proof (HIOK inst (ARX_cf_iok B IOK Hp inst ly S W mem md HA)) as ->.
exact (view_n_cf B HIMG HTSD HQC HIAL ly S Hp W mem md (ARX_cf_ARcf B IOK Hp _ ly S W mem md HA) HI).
Qed.

Lemma di_view_cf : forall inst ly S W mem md p n, ARX inst ly S W mem md -> rpre S n -> fpre ly S W mem p n ->
In (p, n) (blocks S) -> dview B W ly inst mem S p n.
Proof.
intros inst ly S W mem md p n HA ((_ & HQM & HI & _) & Hq) _ HBLK.
pose proof (HIOK inst (ARX_cf_iok B IOK Hp inst ly S W mem md HA)) as ->.
exact (view_cf B HIMG HTSD HQC HIAL HZ3 ly S Hp W mem md p n (ARX_cf_ARcf B IOK Hp _ ly S W mem md HA) HI
  (qmeter_cf_tight S HQM) HBLK Hq).
Qed.

Theorem diface_cf : DIfaceExt -> DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
Proof.
intros E. destruct E as [Ed Ea Ee Edr Erx Err Ere Erc Ecd Efr Erv].
constructor.
- exact (di_inst_cf B IOK Hp HIOK HIOKD).
- exact di_view_n_cf.
- exact di_view_cf.
- intros n tr S HR. exact (di_shape_n_cf B n tr S (proj1 HR)).
- intros p n tr S k Hp0 (HR & Hq). exact (di_shape_cf B p n tr S k Hp0 HR Hq).
- exact Ed.
- exact Ea.
- exact Ee.
- exact Edr.
- intros inst ly S W mem md p n tr k z nb X' W' mem' md' trc r HA HR.
  exact (di_lpost_d_cf B IOK Hp inst ly S W mem md p n tr k z nb X' W' mem' md' trc r HA (proj1 HR)).
- exact (di_qview_cf B IOK Hp L24 QB HIOK HIMG HTSD HQC HQB).
- exact (di_qowned_cf B IOK Hp L24 QB HIOK).
- exact Erx.
- exact Err.
- exact Ere.
- exact Erc.
- exact Ecd.
- exact Efr.
- exact Erv.
- intros inst ly S W mem0 md0 p n tr k lastb initr hb1 z sp0 mem' mat HA (HR & _) HF HB HU Hf Hk Hrev Hsl Hby
    Hs1 Hs2 Hs3 Hs4 Hh1 Hh2 HM Hpa.
  eapply post_c_cf; eassumption.
- intros inst ly S W mem0 md0 n tr sp0 mem' mat HA (HR & _) HF HU Hs1 Hs2 Hs3 Hs4 HM Hpa.
  eapply post_n_cf; eassumption.
- exact (di_frame_cf B IOK Hp).
- exact (di_stack_cf B IOK Hp).
- intros inst ly S W mem md p n k a HA HR. exact (di_owned_cf B IOK Hp HDZ inst ly S W mem md p n k a HA (proj1 HR)).
- exact (di_owned_b_cf B IOK Hp).
- exact (di_owned_i_cf B IOK Hp HIZ).
- intros inst ly S W mem md p n k z tr a HA HR. exact (di_owned_x_cf B IOK Hp inst ly S W mem md p n k z tr a HA (proj1 HR)).
Qed.

(* R3's primed interface record DIfaceRh.DIface_rh at the cf instance: DIface's fields in DIface's order (each named
   dih_ for di_), the layer-proved ones as in diface_cf, the eleven callee fields from DIfaceExtRh. *)
Theorem diface_rh_cf : DIfaceExtRh ->
  DIfaceRh.DIface_rh B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
Proof.
intros E. destruct E as [Ed Ea Ee Edr Erx Err Ere Erc Ecd Efr Erv].
constructor.
- exact (di_inst_cf B IOK Hp HIOK HIOKD).
- exact di_view_n_cf.
- exact di_view_cf.
- intros n tr S HR. exact (di_shape_n_cf B n tr S (proj1 HR)).
- intros p n tr S k Hp0 (HR & Hq). exact (di_shape_cf B p n tr S k Hp0 HR Hq).
- exact Ed.
- exact Ea.
- exact Ee.
- exact Edr.
- intros inst ly S W mem md p n tr k z nb X' W' mem' md' trc r HA HR.
  exact (di_lpost_d_cf B IOK Hp inst ly S W mem md p n tr k z nb X' W' mem' md' trc r HA (proj1 HR)).
- exact (di_qview_cf B IOK Hp L24 QB HIOK HIMG HTSD HQC HQB).
- exact (di_qowned_cf B IOK Hp L24 QB HIOK).
- exact Erx.
- exact Err.
- exact Ere.
- exact Erc.
- exact Ecd.
- exact Efr.
- exact Erv.
- intros inst ly S W mem0 md0 p n tr k lastb initr hb1 z sp0 mem' mat HA (HR & _) HF HB HU Hf Hk Hrev Hsl Hby
    Hs1 Hs2 Hs3 Hs4 Hh1 Hh2 HM Hpa.
  eapply post_c_cf; eassumption.
- intros inst ly S W mem0 md0 n tr sp0 mem' mat HA (HR & _) HF HU Hs1 Hs2 Hs3 Hs4 HM Hpa.
  eapply post_n_cf; eassumption.
- exact (di_frame_cf B IOK Hp).
- exact (di_stack_cf B IOK Hp).
- intros inst ly S W mem md p n k a HA HR. exact (di_owned_cf B IOK Hp HDZ inst ly S W mem md p n k a HA (proj1 HR)).
- exact (di_owned_b_cf B IOK Hp).
- exact (di_owned_i_cf B IOK Hp HIZ).
- intros inst ly S W mem md p n k z tr a HA HR. exact (di_owned_x_cf B IOK Hp inst ly S W mem md p n k z tr a HA (proj1 HR)).
Qed.
End i.

(* ================================================================================================================ *)
(* 3. The raw, errno and memnorm interfaces at the cf instance: each is the record of the callee lanes' contracts   *)
(*    (DIfaceR.v:169-178, ErrnoG.v:365-378, MnRecycle.v:106-113), formed at this instance.                         *)
Definition diface_r_cf := Build_DIfaceR B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
Definition diface_e_cf := ErrnoG.Build_DIfaceE B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
Definition diface_re_cf := ErrnoG.Build_DIfaceRE B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
Definition diface_rem_cf := MnRecycle.Build_DIfaceREm B U ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
End a.
