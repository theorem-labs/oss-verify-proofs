(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, AFREE_CF premise #11 at plugin-hostd/fuzz_reply image A, asan): the cf
   layer's primed callee record YGcfInstFree.DIfaceExtRh (lane F2a's text, cf-f2a 4b146f4de82c, carried to reply A on
   fu2-mp 8db00dd2a209) at reply A, [diface_ext_rh_reply_A_n] (section 3), for EVERY recycle-invariant size bound
   NMAXD with kQuarantineMax <= NMAXD < 2 ^ 30, EVERY instance predicate IOK with IOK_ok TfibB IOK and every ghost set
   Hp, from its eleven fields; and its two instances (section 4): [diface_ext_rh_reply_A] at NMAXD := kQuarantineMax
   (the small arm's) and [diface_ext_rh_reply_A_big] at NMAXD := NMAXD_big_cf (the big arm's, a Theorem Labs lane's EXTB in
   ReplyWalkSigDrh).  Sections 1-2 state eight of the fields as standalone lemmas at the field's exact type (VERBATIM
   DIfaceExt text, so each fits DIfaceExt and DIfaceExtRh alike).
   rule 24, one line per function the record's fields walk (the reuse search and the checker's CONFIRM are in
   diface-ext-brief.md (sha256 c32797d0d4cf; internal record), R24CheckDIface2 18:22Z):
   - proves function __sanitizer::StackDepotPut (reuse search: main / ossv/recipes / ossv/candidates /
     release/pau-projects-recipes by name and address / proof-index, FOUND: cgif_file asan-ubsan 0x724e0, reply A
     0x7430c) - PORTED, not re-proved: reply A's released contract A/AFem.v:1511 tfib_depot_ok (over A/AFl0.v:68
     tfib_depot_spec), through lane F1's YGcfInstDepot.di_depot_cf (carried by path, byte-identical, with
     YGcfInstDepotWreply.v, from a working branch 5174ba1afc97);
   - proves function __sanitizer::QuarantineCache<__asan::QuarantineCallback>::Enqueue (reuse search: same, FOUND: cgif
     asan-ubsan 0x35800, reply A 0x36094) - PORTED: lane F1's YGcfInstEnq.di_enqueue_cf (cf-f1 22b5f48d6248's text,
     carried by path to reply A by ReplyEnqReloc, fu2-mp cc0b03bd5ad4) through lane F2a's
     YGcfInstFreeMidE.exr_enqueue_cf, its three arms ReplyEnqReloc's YGcfInstEnqMissreply.enq_arms_cf_reply
     (a working branch 37eb0120d284), their Refill contract B3LeafCf's
     YGcfRefillTopreply.refill_spec_cf_reply_inst (a working branch c4c4a9802594);
   - proves function __sanitizer::Quarantine<__asan::QuarantineCallback, __asan::AsanChunk>::Drain (reuse search: same,
     FOUND: cgif asan-ubsan 0x32f58, reply A 0x337ec) - PORTED by citation: CfF2b's primed drain field
     YGcfInstDrainTopRh.ds_drain_rh_cf (route P, a working branch 67deba317dfb);
   - proves function __asan::QuarantineCallback::Recycle (reuse search: same, FOUND: cgif asan-ubsan 0x3359c, reply A
     0x33e30) - PORTED: H4's Recycle twin DMrcCf.rchunk_ok_rh_cf_closed (a Theorem Labs lane's RCH,
     a working branch 2c35faeeaec5);
   - proves function __sanitizer::SizeClassAllocator64LocalCache<__sanitizer::SizeClassAllocator64<__asan::AP64<
     __sanitizer::LocalAddressSpaceView> > >::Deallocate (reuse search: same, FOUND: cgif asan-ubsan 0x339a0, reply A
     0x34234) - PORTED by citation: a Theorem Labs lane's reply A CDH YGcfInstCdealloc.di_cdealloc_cf (a working branch
     9ee489aa7d76), and H3's DMcdF.cdealloc_g_of_reads at YGcfInstCdReads.cd_reads_cf inside the Recycle twin;
   - proves function __sanitizer::Quarantine<__asan::QuarantineCallback, __asan::AsanChunk>::DoRecycle (reuse search:
     same, FOUND: cgif asan-ubsan 0x33464, reply A 0x33cf8; it holds the inlined __asan::QuarantineCallback::Deallocate)
     - PORTED by citation, inside the drain field (a Theorem Labs lane's DMrecFRh.dorecycle_ok_rh, through ds_drain_rh_cf).
   The other fields walk no function (kind: interface-instance discharge from lanes F1 / F2b's proved field lemmas).
   The instance's choices (agreed with a Theorem Labs lane and a Theorem Labs lane, 2026-10-30 18:33Z; DRq's size bound generalised at
   a Theorem Labs lane's request, 22:40Z):
     B := TfibB, ARX := ARX_cf TfibB IOK Hp, ARXr := YGcfInstDrainR.ARXr_cf TfibB IOK Hp, L24 := L24MAX_cf,
     QB := YGcfInstDrainR.QB_cf kQuarantineMax, DRq := YGcfInstDrainR.DRq_cf TfibB NMAXD, AOX := aowned TfibB;
   the image classes are reply A's (AGif2reply.AImg_reply, DGif0reply.DImg_reply).  The CfImg is generic in Section r
   and reply A's CfImg_A from Section ra on (ERRB_QAPART_A is a fact of CfImg_A's errbuf object); the CfParams is
   generic in Sections r and ra and reply's CfParams_reply in Section e (the Recycle twin's drop bound REC_LE is a
   CfParams fact; ReplyDeallocInst.v states AFREE_CF at CfImg_A / CfParams_reply).
   - [exr_depot_reply_A]     YGcfInstDepot.di_depot_cf at ARX, with YGcfInstF1Wreply.IMG_COVER_reply, the image rows
     ReplyImg_depkeep.dep_keep_d_A (stated with NoDup / incl; given here from depot_fits by [depot_fits_incl_TfibB]:
     TfibB's universe has no wild prefixes, AD2l.v:39) and ReplyImg_depfp.dep_fp_d_A, and the depot contract
     YGcfInstDepotWreply.depot_spec_d_reply at the dhash row ReplyImg_dhash.dhash_img_A;
   - [exr_dpost_aok_reply_A] YGcfInstDepot.dpost_aok_cf;
   - [exr_frame_r_reply_A]   lane F2b's YGcfInstDrainQ.di_frame_r_cf;
   - [exr_rview_reply_A]     YGcfInstDrainQ.di_rview_cf's proof at NMAXD (it reads only DRq_cf's RIx_cf conjunct), over
     YGcfInstDrainQ's item_facts_cf / slot_carved_cf / slot_vs_chunk_cf and the rows ReplyImg_sbconst.SB_CONST_A and
     AD2l.TfibB_syms;
   - [exr_requar_e_reply_A]  YGcfInstDrainR.ARX_cf_of_ARXr_end at NMAXD (as YGcfInstDrainQ.di_requar_e_cf at
     kQuarantineMax);
   - [exr_cdealloc_reply_A]  a Theorem Labs lane's reply A CDH composition (YGcfInstCdealloc.v:46-69: H3's
     DMcdF.cdealloc_m_of_reads, then MnRecycle.de_cdealloc_em_e, the raw frame and errno conjuncts dropped) at NMAXD,
     over [cd_reads_n] (YGcfInstCdReads.cd_reads_cf's fields; its one DRq field rd_budget_x by cr_budget_x's proof,
     which skips the size conjunct) and [drq_cd_n] (YGcfInstDrainDq.drq_cd_cf's proof, which carries the size conjunct
     through CacheDealloc unchanged);
   - [exr_requar_x_reply_A] / [exr_requar_r_reply_A]  YGcfInstDrainX.di_requar_x_cf / di_requar_r_cf, with the rows
     ReplyImg_qapart.IMG_QAPART_A, ReplyImg_errbqapart.ERRB_QAPART_A, ReplyImg_constapart.CONST_APART_A;
     di_requar_r_cf gives DRq_cf at kQuarantineMax (the popped items were queued: YGcfInstDrainR.drain_recyc_DRq_cf),
     taken to NMAXD by [DRq_cf_mono] under kQuarantineMax <= NMAXD;
   - exr_enqueue (section 3)  YGcfInstFreeMidE.exr_enqueue_cf at its ten image rows: reply A's
     ReplyImg_fvzones.izone_owned_img / dzone_owned_img / fv_ial_img, a Theorem Labs lane's YGcfInstFreeImgreply.FP_*_TfibB
     (a working branch 6381f3da313e), YGcfInstF1Wreply.IMG_COVER_reply, ReplyImg_errbapart.ERRB_APART_A
     and a Theorem Labs lane's ReplyPfApartA.pf_apart_reply_A (a working branch 1f97204e0d5e);
   - [exr_rchunk_reply_A] (section 3)  DMrcCf.v:107-220 at NMAXD (rc_prim_step_reply, rc_prim_mach_rh_cf, rc_reads_cf
     and rchunk_ok_rh_cf_closed, whose pieces YGcfInstRcPrim states at every NMAXD) in memnorm form
     DIfaceRh.de_rchunk_m_rh_t, its conjuncts past the view form dropped; the walk constants NMAXD + 1 and
     sec_map_size NMAXD (DMrcCf's NMAXD_cf / LMAXD_cf at kQuarantineMax, YGcfInstFreeSecRhreply.SEC_rh_reply's at
     NMAXD_big_cf), whose nmaxd_ok / lmaxd_ok / drq_sizes need kQuarantineMax <= NMAXD < 2 ^ 30; its drop bound by
     CfF2b's YGcfInstDrainTopRh.rec_le_reply;
   - [exr_drain_m_reply_A] (section 3)  CfF2b's YGcfInstDrainTopRh.ds_drain_rh_cf (memnorm form
     DIfaceRh.de_drain_m_rh_t) at lane F2a's four layer fields at ARX (YGcfInstFreeQ.di_qview_cf / di_qowned_cf,
     YGcfInstFreeModel.di_stack_cf / di_frame_cf, as YGcfInstFree.diface_cf takes them; their rows FV_TSD by
     AF0m.ts_tsd, FQ_CONST by ReplyImg_fqconst.FQ_CONST_A, QB_BYTES as QB_cf's first conjunct) and rec_le_reply, taken
     to the view form by YGcfInstFree.exr_drain_of_g.
   Named premises of diface_ext_rh_reply_A_n: kQuarantineMax <= NMAXD < 2 ^ 30 and IOK_ok TfibB IOK; of its two
   instances, IOK_ok TfibB IOK only.
   Files of the 513-file deletion set this file Requires (a Theorem Labs lane's reply F1 lane cites them the same way):
   A/AFem.v and A/AFl0.v, through YGcfInstDepotWreply. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply ImgBaseAG ImgBaseDG DGif0reply AGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YF0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfBatch YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstDrainR YGcfInstDrainX YGcfInstDrainQ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CLdepot YGcfInstDepot YGcfInstDepotWreply YGcfInstF1Wreply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstCdealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyImg_depkeep ReplyImg_depfp ReplyImg_dhash ReplyImg_sbconst.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyImg_qapart ReplyImg_errbqapart ReplyImg_constapart.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0dH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CfParamsReply DIfaceRh YGcfInstFree YGcfInstFreeMidE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstEnqMissreply YGcfRefillTopreply RepArmTcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstFreeImgreply ReplyImg_fvzones ReplyImg_errbapart.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyPfApartA ReplyRelroGeoA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMrcCf DMrcSecCf DMcdF YGcfInstCdReads YGcfRehideAR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AF0m ReplyImg_fqconst YGcfInstFreeQ YGcfInstFreeModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstDrainTopRh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMwalkIF DMwalkIFRh DMrcReads DMrcFhCf DMrcPrim DMrcRhOk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstRcPrim YGcfRehidePost MnRecycle YGcfInstDrainDq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG03cf YG06bcf YGcfRoomCf YGcfCker.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* TfibB's universe has no wild prefixes (AD2l.v:39, univ_of Tfib_universe []), so a depot that fits it (YG01.v:153)
   lists only fixed traces: the NoDup / incl form the reply rows ReplyImg_depkeep.dep_keep_*_A take. *)
Lemma depot_fits_incl_TfibB : forall d : list (list Z), depot_fits (as_universe TfibB) d ->
  List.NoDup d /\ incl d (as_universe TfibB).
Proof.
intros d (ND & IN & _). split; [exact ND|].
intros t Ht. destruct (proj1 (Forall_forall _ _) IN t Ht) as [_ [H | (p & sfx & Hp & _)]]; [exact H|].
cbn [as_universe TfibB univ_of u_wild] in Hp. destruct Hp.
Qed.

(* ================================================================================================================ *)
(* 1. The fields at every CfImg.                                                                                    *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.
(* DRq_cf's size bound (YGcfInstDrainR.v:242, its conjunct Forall (fun k => ck_n k <= NMAXD)) *)
Variable NMAXD : Z.
Variable IOK : Z -> Prop.
Hypothesis HIOK : IOK_ok TfibB IOK.
Variable Hp : list Z.
Local Notation B := TfibB.
Local Notation ARX := (ARX_cf TfibB IOK Hp).
Local Notation ARXr := (ARXr_cf TfibB IOK Hp).
Local Notation U := (U_cf TfibB).
Local Notation AOX := (aowned TfibB).
Local Notation dpost := (CLdepot.dpost_x im_segs TfibB).
Local Notation DRq := (DRq_cf TfibB NMAXD).

(* DRq_cf reads its bound only in the size conjunct, so a larger bound keeps it. *)
Lemma DRq_cf_mono : forall N1 N2, N1 <= N2 -> forall S its zs, DRq_cf TfibB N1 S its zs -> DRq_cf TfibB N2 S its zs.
Proof.
intros N1 N2 HN S its zs (RX & CD & UQ & Q1 & Q2 & SZ & PB & CI & HHO).
refine (conj RX (conj CD (conj UQ (conj Q1 (conj Q2 (conj _ (conj PB (conj CI HHO)))))))).
eapply Forall_impl; [| exact SZ]. intros k Hk. cbv beta in Hk |- *. lia.
Qed.

(* YGcfInstDepot's image premise ds_keep at Deallocate's zone pair, at reply A (dep_keep_d_A over depot_fits). *)
Lemma dep_keep_d_reply_A :
  YGcfInstDepot.dep_keep_img TfibB (fun ly a => dg_dzone ly a \/ (dg_czone ly a /\ ~ dg_izone a)).
Proof.
intros ly S W mem0 mem LY IMG TSD HDF CST DEP MEQ.
destruct (depot_fits_incl_TfibB (st_depot S) HDF) as [ND INC].
exact (ReplyImg_depkeep.dep_keep_d_A TfibB TfibB_syms ly S W mem0 mem LY IMG TSD ND INC CST DEP MEQ).
Qed.

(* exr_depot (DIfaceExt's ext_depot, YGcfInstFree.v:77-95). *)
Lemma exr_depot_reply_A :
  forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
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
      dpost inst ly S W tr z mem').
Proof.
exact (YGcfInstDepot.di_depot_cf TfibB Hp ARX (ARX_cf_ARcf TfibB IOK Hp)
  YGcfInstF1Wreply.IMG_COVER_reply dep_keep_d_reply_A (ReplyImg_depfp.dep_fp_d_A TfibB TfibB_syms)
  (YGcfInstDepotWreply.depot_spec_d_reply TfibB TfibB_syms ReplyImg_dhash.dhash_img_A)).
Qed.

(* exr_dpost_aok (YGcfInstFree.v:96). *)
Lemma exr_dpost_aok_reply_A : forall inst ly S W tr z m, dpost inst ly S W tr z m -> aok S (KDepot tr) z.
Proof. exact (YGcfInstDepot.dpost_aok_cf TfibB). Qed.

(* exr_requar_e (YGcfInstFree.v:123): YGcfInstDrainR.ARX_cf_of_ARXr_end, which holds at every bound (YGcfInstDrainQ's
   di_requar_e_cf applies it at kQuarantineMax). *)
Lemma exr_requar_e_reply_A : di_requar_e_t ARX ARXr DRq.
Proof.
intros inst ly S W mem md HR HD. exact (proj1 (ARX_cf_of_ARXr_end TfibB IOK Hp inst ly S W mem md NMAXD HR HD)).
Qed.

(* H3's DMcdR.cd_reads at DRq: YGcfInstCdReads.cd_reads_cf's fields; its one field that reads DRq, rd_budget_x, by
   YGcfInstCdReads.cr_budget_x's proof (YGcfInstCdReads.v:425-437), which reads DRq_cf's deficit, byte, pending-bytes
   and admission conjuncts and not the size one. *)
Lemma cr_budget_x_n : DMcdR.rd_budget_x TfibB ARXr DRq.
Proof.
intros inst ly X z W regs mem md (H & _) its zs D _.
destruct H as (_ & (M & L & (HA & _) & _) & _).
destruct D as (_ & _ & HU & HT & HG & _ & HN & _ & HHO).
pose proof (YGcfRoomCf.qloose_cut_of_pending X its HU HT HG HN) as QL.
pose proof (amr_wfr _ _ _ _ _ M) as WF.
pose proof (YGcfRoomCf.room_rec_cf_of_cut _ ly X md WF QL HHO) as R.
replace (eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768)
  with (eager_used md + A_bytes (w_A W) + (2 * kUserMapSize + 32768)) by lia.
apply (YGcfCker.room_wA_parts_R _ _ ly X md W _ WF L HA R).
apply Z.leb_le. reflexivity.
Qed.

Lemma cd_reads_n : DMcdR.cd_reads TfibB ARXr AOX DRq RMAXD_cf.
Proof.
destruct (YGcfInstCdReads.cd_reads_cf TfibB IOK Hp TfibB_syms HIOK).
constructor; try assumption. exact cr_budget_x_n.
Qed.

(* H3's DMwalkIF.drq_cd at DRq: YGcfInstDrainDq.drq_cd_cf's proof (YGcfInstDrainDq.v:71-144), which carries DRq_cf's
   size conjunct SZ through CacheDealloc unchanged (CacheDealloc keeps the pending list), so it holds at every bound. *)
Lemma drq_cd_n : DMwalkIF.drq_cd DRq RMAXD_cf.
Proof.
intros S its z zs HD. pose proof HD as (RX & CD & UQ & Q1 & Q2 & SZ & PB & CI & HHO).
pose proof (proj1 RX) as W.
pose proof (YG03cf.wfr_classes _ _ _ _ _ W kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
unfold wf_class_cf in CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as A2.
pose proof (wrc_fa _ _ _ _ _ _ CL) as [F0 FM]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL.
pose proof (YG04.fa_len_nonneg (rg_free (reg S kBatchClass)) (wrc_runs _ _ _ _ _ _ CL)) as FN.
pose proof (YG03cf.mapped_bound_r_cf (as_universe TfibB) 0 0 0 S kBatchClass W ltac:(unfold kBatchClass; lia)) as MB.
pose proof (YGcfInstDrainDq.fa_len_room_cf TfibB _ S its (z :: zs) HD) as FA27.
(* the flag: the list of batch objects is not empty, so DRq_cf's guarded conjunct fires *)
assert (HCI : st_cache_inited S = true) by (apply CI; right; intros E; discriminate E).
(* the batch object's slot, from the recycle invariant *)
destruct RX as (_ & _ & _ & _ & SF & _).
pose proof (proj1 (Forall_forall _ _) SF z ltac:(apply in_app_iff; left; left; reflexivity)) as (Z1 & Z2 & Z3).
pose proof (wrc_cache _ _ _ _ _ _ CL) as PC. rewrite HCI in PC. destruct PC as [PM PL].
split.
- (* cd_model at the batch class *)
  unfold DMwalkIF.cd_model. unfold RMAXD_cf, kFreeArrayOffset in *.
  split; [unfold kBatchClass; lia|]. split; [exact HCI|]. split; [exact PL|]. split; [exact PM|].
  split; [lia|]. split; [lia|]. split; [exact Z2|]. split; [exact Z3|].
  split; [lia|]. split; [exact A2|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact FM|].
  split; [exact FA27|].
  (* the growth clause: the free array's length is tiny next to its cap, so a growth still fits *)
  intros HG. pose proof (YG06bcf.fa_len_bound_cf _ _ _ _ _ _ CL ltac:(reflexivity)) as FBB.
  change (class_size kBatchClass) with 8192 in FBB. change (max_cached kBatchClass / 2) with 1 in HG.
  unfold kFreeArrayMapSize, kFreeArrayMax in *. lia.
- (* the invariant at either result *)
  intros S' HRet.
  assert (OK : atok true (cache_dealloc kBatchClass z S)
    (YG03cf.cache_dealloc_post_cf (as_universe TfibB) 0 0 0 S kBatchClass (z - region_off kBatchClass)))
    by (apply (YG03cf.cache_dealloc_ok_cf (as_universe TfibB) 0 0 0 S kBatchClass z true W ltac:(unfold kBatchClass; lia));
        [lia | exact Z2 | exact Z3]).
  destruct (YGcfInstDrainDq.atok_cd_returns_cf _ _ _ _ _ _ OK HRet) as (ns' & POST).
  unfold YG03cf.cache_dealloc_post_cf in POST. cbv zeta in POST. cbn [snd] in POST.
  destruct POST as (W' & RO & CI' & AU & CE & MF & LEN).
  pose proof RO as (EC & ES & ESA & ESR & EQT & EQG & EFS & EDP & EII & ENV).
  (* the chunk list and the queues are the entry's, so every clause over them carries over *)
  assert (EQI : q_items S' = q_items S)
    by (unfold q_items, all_batches; rewrite EQT, EQG; reflexivity).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  + (* the recycle invariant: WfR_cf is the post's, and the lists are the entry's *)
    destruct HD as ((_ & IT & ND & BL & SF' & NDS) & _).
    split; [exact W'|]. split.
    * rewrite EC. exact IT.
    * split; [rewrite EQI; exact ND|]. split; [exact BL|].
      rewrite app_nil_r in SF', NDS. cbn [map] in *. rewrite app_nil_r. apply NoDup_cons_iff in NDS as [HZ NDS'].
      split; [|exact NDS'].
      apply Forall_forall. intros y Hy.
      pose proof (proj1 (Forall_forall _ _) SF' y ltac:(right; exact Hy)) as (Y1 & Y2 & Y3).
      rewrite (AU kBatchClass ltac:(unfold kBatchClass; lia)). split; [exact Y1|]. split; [exact Y2|].
      intros Hin. destruct (CE kBatchClass _ ltac:(unfold kBatchClass; lia) Hin) as [[EY _]|Hold]; [|exact (Y3 Hold)].
      (* the pushed object is z itself, which NoDup keeps apart from the rest *)
      apply HZ. replace z with y by lia. exact Hy.
  + (* the class deficit: the dealloc adds exactly one element of the batch class *)
    intros c' Hc'. pose proof (CD c' Hc') as CD'. unfold cdef in *.
    rewrite (AU c' ltac:(lia)), (LEN c' ltac:(lia)), Nat2Z.inj_add.
    destruct (Z.eqb_spec c' kBatchClass) as [->|NE].
    * replace (kBatchClass =? kBatchClass) with true in * by (symmetry; apply Z.eqb_refl).
      cbn [length] in CD'. rewrite Nat2Z.inj_succ in CD'. cbn [Z.of_nat]. lia.
    * replace (c' =? kBatchClass) with false in * by (symmetry; apply Z.eqb_neq; exact NE). cbn [Z.of_nat]. lia.
  + (* the deficit and the byte bounds read the chunks and the queues only *)
    unfold YG03cf.unq_cf, quar_n, queued_n in *. rewrite EC, EQI. exact UQ.
  + rewrite EQT. exact Q1.
  + rewrite EQG. exact Q2.
  + exact SZ.
  + exact PB.
  + intros _. exact CI'.
  + (* the admission: CacheDealloc keeps st_secs (regs_only), so both meters are the entry's *)
    apply (cf_hull_counts _ S); [unfold nsec_cf; rewrite ES; reflexivity | unfold sec_T_cf; rewrite ES; reflexivity | exact HHO].
Qed.

(* exr_cdealloc (YGcfInstFree.v:125): a Theorem Labs lane's reply A CDH composition (YGcfInstCdealloc.v:46-69) at DRq: H3's
   walk DMcdF.cdealloc_m_of_reads over [cd_reads_n] and [drq_cd_n], then MnRecycle.de_cdealloc_em_e, the raw frame
   and errno conjuncts dropped. *)
Lemma exr_cdealloc_reply_A : di_cdealloc_t B ARXr AOX DRq.
Proof.
pose proof (MnRecycle.de_cdealloc_em_e TfibB ARXr AOX DRq
  (DMcdF.cdealloc_m_of_reads TfibB ARXr AOX DRq RMAXD_cf TfibB_syms YGcfInstDrainR.rmaxd_ok_cf cd_reads_n drq_cd_n)) as CDE.
intros inst ly X its z zs W regs mem md PREX RX.
eapply amreal_mono; [| exact (CDE inst ly X its z zs W regs mem md PREX RX)].
intros r W' c' (regs' & mem' & md' & Hc & HP & _ & _ & REST).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP | exact REST].
Qed.

(* exr_frame_r (YGcfInstFree.v:126). *)
Lemma exr_frame_r_reply_A : di_frame_t ARXr AOX.
Proof. exact (di_frame_r_cf TfibB IOK Hp). Qed.

(* exr_rview (YGcfInstFree.v:127): YGcfInstDrainQ.di_rview_cf's proof (YGcfInstDrainQ.v:165-183), which reads only
   DRq_cf's first conjunct (RIx_cf), so it holds at every bound; the image rows ReplyImg_sbconst.SB_CONST_A and
   AD2l.TfibB_syms. *)
Lemma exr_rview_reply_A : di_rview_t B ARXr DRq.
Proof.
intros inst ly X W mem md its zs (HI & HA & _) (RX & _). pose proof (HIOK _ HI) as ->.
destruct HA as (M & _).
assert (IT : forall k, In k its -> In k (st_chunks X)).
{ intros k Hk. destruct RX as (_ & IT & _). exact (proj1 (proj1 (Forall_forall _ _) IT k ltac:(apply in_app_iff; left; exact Hk))). }
split; [|split].
- pose proof (amr_const _ _ _ _ _ M) as C. rewrite (im_const_eq TfibB ly TfibB_syms) in C.
  pose proof (proj1 (Forall_forall _ _) C _ (ReplyImg_sbconst.SB_CONST_A ly)) as Hc.
  pose proof (cell_holds_val_mem im_segs TfibB ly (w_H W) mem (AInst o_space) 8 (ASp 0) Hc) as V. cbn [aeval] in V.
  rewrite Z.add_0_r in V. exact V.
- intros k Hk. exact (item_facts_cf TfibB Hp ly X _ k M (IT k Hk)).
- intros z Hz.
  assert (SZ : slot_ok_cf X z)
    by (apply (RIx_cf_slots (as_universe TfibB) 0 0 0 X its [] zs z RX); cbn [map]; rewrite app_nil_r; exact Hz).
  pose proof (slot_carved_cf TfibB Hp ly X _ z M SZ) as (C1 & C2 & C3).
  pose proof SZ as (_ & Z2 & _). rewrite class_size_24_cf in Z2.
  split; [exact C1|]. split; [exact C2|]. split; [unfold kBatchBytes; exact Z2|].
  intros k a Hk Ha. exact (slot_vs_chunk_cf TfibB Hp ly X _ z k M SZ (IT k Hk) a Ha).
Qed.

(* The batch class's allocated bound of the view x-form (DMwalkIF.di_rview_x_t's second half):
   YGcfInstDrainQ.di_rview_alloc_cf's proof (YGcfInstDrainQ.v:189-198), which does not read DRq. *)
Lemma rview_alloc_n : forall inst ly X W mem md its zs, ARXr inst ly X W mem md -> DRq X its zs ->
  rg_alloc_user (reg X kBatchClass) <= RMAXD_cf.
Proof.
intros inst ly X W mem md its zs (_ & HA & _) _.
pose proof (amr_wfr _ _ _ _ _ (proj1 HA)) as W0.
pose proof (YG03cf.wfr_classes _ _ _ _ _ W0 kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1.
pose proof (YG03cf.mapped_bound_r_cf (as_universe TfibB) 0 0 0 X kBatchClass W0 ltac:(unfold kBatchClass; lia)) as MB.
unfold RMAXD_cf. lia.
Qed.

End r.

(* ================================================================================================================ *)
(* 2. The two re-quarantine fields that read the errbuf object's place: at reply A's CfImg_A (A/CfImgA.v:12).       *)
#[local] Existing Instance CfImg_A.

Section ra. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Variable NMAXD : Z.
(* the popped items were queued, so DRq_cf holds at the quarantine's entry bound; NMAXD is at least that *)
Hypothesis HNQ : kQuarantineMax <= NMAXD.
Variable IOK : Z -> Prop.
Hypothesis HIOK : IOK_ok TfibB IOK.
Variable Hp : list Z.
Local Notation B := TfibB.
Local Notation ARX := (ARX_cf TfibB IOK Hp).
Local Notation ARXr := (ARXr_cf TfibB IOK Hp).
Local Notation AOX := (aowned TfibB).
Local Notation L24 := L24MAX_cf.
Local Notation QB := (QB_cf kQuarantineMax).
Local Notation DRq := (DRq_cf TfibB NMAXD).

(* exr_requar_x (YGcfInstFree.v:121). *)
Lemma exr_requar_x_reply_A : di_requar_x_t B ARX AOX L24 QB.
Proof.
exact (di_requar_x_cf TfibB IOK Hp HIOK TfibB_syms ReplyImg_qapart.IMG_QAPART_A ReplyImg_errbqapart.ERRB_QAPART_A
  ReplyImg_constapart.CONST_APART_A L24MAX_cf kQuarantineMax).
Qed.

(* exr_requar_r (YGcfInstFree.v:122): YGcfInstDrainX.di_requar_r_cf, whose invariant at kQuarantineMax
   (YGcfInstDrainR.drain_recyc_DRq_cf) [DRq_cf_mono] raises to NMAXD. *)
Lemma exr_requar_r_reply_A : di_requar_r_t B ARX ARXr AOX L24 QB DRq.
Proof.
pose proof (di_requar_r_cf TfibB IOK Hp HIOK TfibB_syms ReplyImg_qapart.IMG_QAPART_A ReplyImg_errbqapart.ERRB_QAPART_A
  ReplyImg_constapart.CONST_APART_A kQuarantineMax L24MAX_cf) as RQ.
intros inst ly X W mem md sp0 tmp S' P mem' md' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
destruct (RQ inst ly X W mem md sp0 tmp S' P mem' md' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12) as (AR & D & OW).
exact (conj AR (conj (DRq_cf_mono kQuarantineMax NMAXD HNQ _ _ _ D) OW)).
Qed.

End ra.

(* ================================================================================================================ *)
(* 3. The record DIfaceExtRh (YGcfInstFree.v:137) at reply A, at reply's CfParams_reply (A/CfParamsReply.v:120).     *)
#[local] Existing Instance CfParamsReply.CfParams_reply.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable NMAXD : Z.
(* kQuarantineMax <= NMAXD for exr_requar_r ([DRq_cf_mono]) and, with NMAXD < 2 ^ 30, for the RChunk walk's size
   premises at the walk constants NMAXD + 1 / sec_map_size NMAXD *)
Hypothesis HNM : kQuarantineMax <= NMAXD < 2 ^ 30.
Variable IOK : Z -> Prop.
Hypothesis HIOK : IOK_ok TfibB IOK.
Local Notation AOX := (aowned TfibB).
Local Notation DRq := (DRq_cf TfibB NMAXD).

(* exr_drain (YGcfInstFree.v:182, PRIMED) in its memnorm form: CfF2b's YGcfInstDrainTopRh.ds_drain_rh_cf at the image
   rows of reply A (TfibB_syms, ERRB_QAPART_A), lane F2a's four layer fields at ARX (as YGcfInstFree.diface_cf takes
   them) and the drop bound YGcfInstDrainTopRh.rec_le_reply at CfParams_reply. *)
Lemma exr_drain_m_reply_A : forall Hp,
  DIfaceRh.de_drain_m_rh_t TfibB (ARX_cf TfibB IOK Hp) AOX drain_body_cf L24MAX_cf (QB_cf kQuarantineMax).
Proof.
intros Hp.
exact (YGcfInstDrainTopRh.ds_drain_rh_cf TfibB IOK Hp HIOK TfibB_syms TfibB_syms ReplyImg_errbqapart.ERRB_QAPART_A
  (YGcfInstFreeQ.di_qview_cf TfibB IOK Hp L24MAX_cf (QB_cf kQuarantineMax) HIOK YGcfInstF1Wreply.IMG_COVER_reply
    (AF0m.ts_tsd TfibB TfibB_syms) (ReplyImg_fqconst.FQ_CONST_A TfibB TfibB_syms) (fun X H => proj1 H))
  (YGcfInstFreeQ.di_qowned_cf TfibB IOK Hp L24MAX_cf (QB_cf kQuarantineMax) HIOK)
  (YGcfInstFreeModel.di_stack_cf TfibB IOK Hp) (YGcfInstFreeModel.di_frame_cf TfibB IOK Hp)
  YGcfInstDrainTopRh.rec_le_reply).
Qed.

(* The size premises of H4's RChunk top DMwalkIFRh.rchunk_ok_rh_t at DRq, at the walk constants NMAXD + 1 and
   sec_map_size NMAXD: DMrcCf's NMAXD_cf / LMAXD_cf (YGcfInstDrainR.v:507-508) at kQuarantineMax, and
   YGcfInstFreeSecRhreply.SEC_rh_reply's NOK / LOK / RDS at NMAXD_big_cf. *)
Lemma nmaxd_ok_n : DMwalkIF.nmaxd_ok (NMAXD + 1).
Proof. pose proof HNM as [N1 N2]. unfold DMwalkIF.nmaxd_ok. unfold kQuarantineMax in N1. lia. Qed.

(* NMAXD is a secondary request (past kMaxSize), so its map is above it (YGcfInstFreeSecRhreply.big_map_above's proof),
   and below the map of 2 ^ 30 (YGcfInstDrainR.lmaxd_ok_big_cf's proof). *)
Lemma lmaxd_ok_n : DMwalkIF.lmaxd_ok (NMAXD + 1) (sec_map_size NMAXD).
Proof.
pose proof HNM as [N1 N2]. unfold kQuarantineMax in N1. unfold DMwalkIF.lmaxd_ok.
assert (N0 : 0 <= NMAXD) by lia.
split.
- pose proof (rounded_size_bounds NMAXD N0) as [R1 _].
  pose proof (rz_size_bounds NMAXD) as [Z1 _].
  pose proof (req_size_bounds NMAXD N0) as (_ & _ & Q3).
  assert (FP : from_primary NMAXD = false).
  { unfold from_primary, needed_primary. apply Z.leb_gt. unfold kMaxSize. lia. }
  pose proof (secondary_geometry NMAXD N0 FP) as (_ & _ & S3 & _).
  unfold kPage, kSecRz in S3. lia.
- pose proof (YGcfInstDrainR.sec_map_size_mono_cf NMAXD (2 ^ 30) ltac:(lia)) as MO.
  assert (SM : sec_map_size (2 ^ 30) <= 2 ^ 31 - 8192) by (vm_compute; discriminate). lia.
Qed.

Lemma drq_sizes_n : DMwalkIF.drq_sizes DRq (NMAXD + 1) (sec_map_size NMAXD).
Proof.
intros S its zs k D Hin.
assert (H2 : 2 * kMaxSize + 96 <= NMAXD) by (pose proof HNM as [N1 _]; unfold kMaxSize, kQuarantineMax in *; lia).
exact (YGcfInstDrainR.drq_sizes_cf TfibB NMAXD H2 S its zs k D Hin).
Qed.

(* DMrcCf.rc_prim_step_reply (DMrcCf.v:107-117) at DRq: YGcfInstRcPrim.rc_prim_step_cf at NMAXD. *)
Lemma rc_prim_step_n : forall Hp,
  DMrcReads.rc_prim_step_t TfibB (ARXr_cf TfibB IOK Hp) AOX DRq RMAXD_cf.
Proof.
intros Hp inst ly X k ks zs cbp W regs mem md off mem' md' PRE DR Hb AG VIS NEW HK CONST Ev El Ee.
assert (HR : kFreeArrayOffset <= RMAXD_cf) by (unfold RMAXD_cf; lia).
destruct (YGcfInstRcPrim.rc_prim_step_cf TfibB IOK Hp NMAXD RMAXD_cf HR inst ly X k ks zs cbp W regs mem md off mem' md'
  PRE DR Hb AG VIS NEW HK CONST Ev El Ee) as (A1 & A2 & A3 & A4 & A5).
split; [exact A1|]. split; [exact (DMrcCf.cd_model_of_cf _ _ _ _ A2)|].
split; [exact A3|]. split; [exact A4 | exact A5].
Qed.

(* DMrcCf.rc_prim_mach_rh_cf (DMrcCf.v:122-132) at DRq: DMrcPrim.rchunk_prim_m, which is generic in DRq. *)
Lemma rc_prim_mach_rh_n : forall Hp,
  DMrcRhOk.rc_prim_mach_rh_t TfibB (ARXr_cf TfibB IOK Hp) AOX DRq RMAXD_cf.
Proof.
intros Hp TB RP CDG inst ly X k ks zs cbp W regs mem md off PRE RX Hb.
eapply YG0dH.amreal'_mono; [| exact (YG0dH.amreal_amreal' im_segs YGcfRehidePost.RZ_cf _ _ _ _
  (DMrcPrim.rchunk_prim_m TfibB TB _ AOX _ RMAXD_cf RP CDG inst ly X k ks zs cbp W regs mem md off PRE RX Hb))].
intros r0 W' c' (regs' & mem' & md' & Hc & HP & HT).
exists regs', mem', md'. split; [exact Hc|].
split; [exact (YGcfRehidePost.acall_post_x_rh_of TfibB _ AOX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) | exact HT].
Qed.

(* DMrcCf.rc_reads_cf (DMrcCf.v:168-189) at DRq: H4's read record under the re-hide, its DRq fields by
   YGcfInstRcPrim's head / model / fh / room / split fields at NMAXD. *)
Lemma rc_reads_n : forall Hp,
  DMrcRhOk.rc_reads_rh TfibB (ARXr_cf TfibB IOK Hp) (DMrcSecCf.ARXsl_cf TfibB IOK Hp) AOX DRq RMAXD_cf.
Proof.
intros Hp.
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- split; [|split; [|split; [|split]]].
  + exact (YGcfInstRcPrim.rc_head_cf TfibB NMAXD).
  + exact (YGcfInstRcPrim.rc_model_cf TfibB NMAXD).
  + exact (DMrcFhCf.rc_prim_fh_of_cut TfibB TfibB_syms _ _
      (YGcfInstRcPrim.rc_fh_cut_facts_cf TfibB IOK Hp NMAXD HIOK DMrcCf.img_cover_reply)).
  + exact (rc_prim_step_n Hp).
  + intros inst ly X k ks zs cbp W regs mem md off PRE RX Hb G.
    exact (YGcfInstRcPrim.rc_prim_room_cf TfibB IOK Hp NMAXD inst ly X k ks zs cbp W regs mem md off PRE RX Hb G).
- exact (rc_prim_mach_rh_n Hp).
- exact (DMrcCf.SC_cf TfibB TfibB_syms IOK Hp HIOK).
- exact (DMrcCf.SM_cf TfibB TfibB_syms IOK Hp).
- exact (DMrcSecCf.rc_sec_step_sl_of_cf TfibB TfibB_syms IOK Hp ReplyImg_errbqapart.ERRB_QAPART_A
    YGcfInstDrainTopRh.rec_le_reply).
- exact (YGcfInstRcPrim.rc_split_cf TfibB NMAXD).
- exact (DMrcCf.rc_sec_pre_rh_cf TfibB IOK Hp).
- exact (DMrcCf.rc_sec_rehide_all_cf TfibB IOK Hp).
Qed.

(* exr_rchunk (YGcfInstFree.v:187, PRIMED): H4's Recycle twin, DMrcRhOk.rchunk_ok_rh on [rc_reads_n] (DMrcCf's
   rchunk_ok_rh_cf / rchunk_ok_rh_cf_closed at DRq), in its memnorm form DIfaceRh.de_rchunk_m_rh_t, at the size premises
   above, the frame law di_frame_r_cf, the view x-form ([exr_rview_reply_A] and [rview_alloc_n], as
   YGcfInstDrainTop.drain_reads_cf states it) and H3's CacheDealloc contract DMcdF.cdealloc_g_of_reads at [cd_reads_n]
   (as CfF2b's ds_drain_rh_cf takes it); the raw, errno and memnorm conjuncts are dropped to give the view form
   DIfaceRh.di_rchunk_rh_t. *)
Lemma exr_rchunk_reply_A : forall Hp, DIfaceRh.di_rchunk_rh_t TfibB (ARXr_cf TfibB IOK Hp) AOX DRq.
Proof.
intros Hp.
pose proof (DMrcRhOk.rchunk_ok_rh TfibB _ (DMrcSecCf.ARXsl_cf TfibB IOK Hp) _ _ (NMAXD + 1) (sec_map_size NMAXD) RMAXD_cf
  (rc_reads_n Hp) TfibB_syms nmaxd_ok_n lmaxd_ok_n YGcfInstDrainR.rmaxd_ok_cf drq_sizes_n
  (di_frame_r_cf TfibB IOK Hp)
  (conj (exr_rview_reply_A NMAXD IOK HIOK Hp) (rview_alloc_n NMAXD IOK Hp))
  (DMcdF.cdealloc_g_of_reads TfibB (ARXr_cf TfibB IOK Hp) AOX DRq RMAXD_cf TfibB_syms YGcfInstDrainR.rmaxd_ok_cf
    (cd_reads_n NMAXD IOK HIOK Hp))) as RM.
intros inst ly X k ks zs cbp W regs mem md P D.
eapply YG0dH.amreal'_mono; [| exact (RM inst ly X k ks zs cbp W regs mem md P D)].
intros r W' c' (regs' & mem' & md' & Hc & HP & _ & _ & _ & HT).
exists regs', mem', md'. exact (conj Hc (conj HP HT)).
Qed.

(* The record at reply A, every bound NMAXD in [kQuarantineMax, 2 ^ 30) and every ghost set Hp:
   YGcfInstFree.Build_DIfaceExtRh over the eleven fields, in its order. *)
Theorem diface_ext_rh_reply_A_n : forall Hp,
  YGcfInstFree.DIfaceExtRh TfibB IOK Hp (ARXr_cf TfibB IOK Hp) L24MAX_cf (QB_cf kQuarantineMax) (DRq_cf TfibB NMAXD).
Proof.
intros Hp. constructor.
- exact (exr_depot_reply_A IOK Hp).
- exact exr_dpost_aok_reply_A.
- exact (YGcfInstFreeMidE.exr_enqueue_cf TfibB IOK Hp
    (ReplyImg_fvzones.izone_owned_img TfibB TfibB_syms) YGcfInstFreeImgreply.FP_IZONE_ROM_TfibB
    YGcfInstFreeImgreply.FP_DSTAT_TfibB (ReplyImg_fvzones.dzone_owned_img TfibB TfibB_syms)
    YGcfInstFreeImgreply.FP_DZONE_FP_TfibB YGcfInstFreeImgreply.FP_CONST_TfibB
    (ReplyImg_fvzones.fv_ial_img TfibB TfibB_syms) YGcfInstF1Wreply.IMG_COVER_reply
    ReplyImg_errbapart.ERRB_APART_A ReplyPfApartA.pf_apart_reply_A
    (YGcfInstEnqMissreply.enq_arms_cf_reply TfibB TfibB_syms IOK Hp HIOK ReplyRelroGeoA.relro_seg_reply_A
      (YGcfRefillTopreply.refill_spec_cf_reply_inst TfibB IOK TfibB_syms HIOK
        (@RepArmTcf.classfull_cf_of_hyps fx rc CfParamsReply.CfParams_reply)))).
- eapply YGcfInstFree.exr_drain_of_g. exact (exr_drain_m_reply_A Hp).
- exact (exr_requar_x_reply_A IOK HIOK Hp).
- exact (exr_requar_r_reply_A NMAXD (proj1 HNM) IOK HIOK Hp).
- exact (exr_requar_e_reply_A NMAXD IOK Hp).
- exact (exr_rchunk_reply_A Hp).
- exact (exr_cdealloc_reply_A NMAXD IOK HIOK Hp).
- exact (exr_frame_r_reply_A IOK Hp).
- exact (exr_rview_reply_A NMAXD IOK HIOK Hp).
Qed.

End e.

(* ================================================================================================================ *)
(* 4. The two instances: the small arm's bound kQuarantineMax (the statement a Theorem Labs lane's ReplyDeallocInst cites) and  *)
(*    the big arm's NMAXD_big_cf = cf_malloc_max, 2 ^ 30 - 2 ^ 20 at CfParams_reply (A/CfParamsReply.v:121).           *)
Lemma nmaxd_small_ok : kQuarantineMax <= kQuarantineMax < 2 ^ 30.
Proof. unfold kQuarantineMax. lia. Qed.

Lemma nmaxd_big_ok_reply : kQuarantineMax <= NMAXD_big_cf < 2 ^ 30.
Proof. unfold NMAXD_big_cf. split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity. Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable IOK : Z -> Prop.
Hypothesis HIOK : IOK_ok TfibB IOK.

Theorem diface_ext_rh_reply_A : forall Hp,
  YGcfInstFree.DIfaceExtRh TfibB IOK Hp (ARXr_cf TfibB IOK Hp) L24MAX_cf (QB_cf kQuarantineMax) (DRq_cf TfibB kQuarantineMax).
Proof. exact (diface_ext_rh_reply_A_n kQuarantineMax nmaxd_small_ok IOK HIOK). Qed.

Theorem diface_ext_rh_reply_A_big : forall Hp,
  YGcfInstFree.DIfaceExtRh TfibB IOK Hp (ARXr_cf TfibB IOK Hp) L24MAX_cf (QB_cf kQuarantineMax) (DRq_cf TfibB NMAXD_big_cf).
Proof. exact (diface_ext_rh_reply_A_n NMAXD_big_cf nmaxd_big_ok_reply IOK HIOK). Qed.
End i.
