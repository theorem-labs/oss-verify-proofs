(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch): the generic cf layer's interface for Deallocate's big-block
   arm, DGbigIF.DIfaceBig (PRIMED in place, a working branch 3711d297cf5a, DeallocNmaxA, ruling (A): dbg_rcs_t
   is Recycle under the re-hide), at the layer's walk relation
   YGcfInstBase.ARX_cf and the recycle side of free_cf's size test (rpre := YGcfInstFreeModel.rpreD_big_cf, i.e.
   rpreD_free_cf and kQuarantineMax < req_size n).  rule 24: no function proved (kind: interface-instance discharge).

   - Proved here or taken from this lane's DIface instance: dbg_inst, dbg_view (YGcfInstFreeView.view_big_cf),
     dbg_shape (free_cf's recycle side, [di_shape_big_cf]), dbg_post (qtight at the end of every granted free path:
     YGcfRoom.free_cf_room_inv), dbg_frame, dbg_stack, dbg_owned, dbg_owned_i.
   - From YGcfInstFree.DIfaceExtRh (verbatim DGif0 texts, which do not read rpre): dbg_depot, dbg_dpost_aok (lane F1),
     dbg_requar_e, dbg_frame_r (lane F2b).
   - The record [DIfaceBigExt] holds the two recycle fields: dbg_rq (the drain's cut relation and the recycle
     invariant for the one chunk at Recycle's call) and dbg_rcs (Recycle on the big chunk, primed), at their DGbigIF
     texts; [diface_big_rh_cf_at] fills them from a Theorem Labs lane's bext_rq_cf and from the unit's primed walk SEC_rh_t.
   Generic over CfImg / CfParams / AImg / DImg and IOK; no numeral of any image; no event term. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YG0qcf YG03cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG DMspec DMiface DGif0 DGbigIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoom.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstFreeView YGcfInstFreeModel YGcfInstFree.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfDIface CLdepot YGcfInstDrainR YGcfInstFreeBigRq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstFreeSig YGcfInstFreePost.
Import ListNotations.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.
Variable B : asyms.

(* The chunk of the recycle side is a SECONDARY chunk with its bookkeeping: the premise triple of H4's flag-free
   secondary Recycle walk (DMrc.v:59-62, `ck_beg k = PSec r o /\ nth_error (st_secs X) r = Some sm /\
   nth_error (st_sec_arr X) i = Some r`), from the model's Wf alone.  A primary chunk's request fits its class
   (primary_geometry: req_size <= class_size <= kMaxSize < kQuarantineMax), so the PPrim arm of chunk_ok_cf is excluded
   by the size test; the PSec arm gives the live map sm, and wf_sec_cf's wsc_arr_chunks puts r in the pointer array.
   This bridges DGbigIF.dbg_rcs_t's size premise to H4's PSec form at the cf instance (DGbig itself has no Wf). *)
Lemma big_sec_triple_cf : forall U pp cc bb X k,
  WfR_cf U pp cc bb X -> In k (st_chunks X) -> kQuarantineMax < ck_n k ->
  exists r o sm i, ck_beg k = PSec r o /\ nth_error (st_secs X) r = Some sm /\ nth_error (st_sec_arr X) i = Some r.
Proof.
intros U pp cc bb X k W Hk Hbig.
pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ W) k Hk) as [Hreq CK].
destruct (ck_beg k) as [|off|r off|c q] eqn:Eb; try (destruct CK; fail).
- exfalso. destruct CK as (Fp & _ & _).
  pose proof (primary_geometry (ck_req k) ltac:(lia) Fp) as (_ & [G1 G2] & G3 & _).
  pose proof (rz_size_bounds (ck_req k)) as [Z1 _].
  unfold ck_n in Hbig. unfold kMaxSize, kQuarantineMax in *. lia.
- destruct CK as (_ & Hoff & sm & Hsm & _).
  assert (Hin : In r (st_sec_arr X)).
  { apply (proj2 (wsc_arr_chunks _ (wfr_secondary _ _ _ _ _ W) r)). exists k. split; [exact Hk|]. rewrite Eb, Hoff. reflexivity. }
  destruct (In_nth_error _ _ Hin) as [i Hi].
  exists r, off, sm, i. split; [reflexivity|]. split; [exact Hsm | exact Hi].
Qed.

(* The recycle side of free_cf's size test. *)
Lemma di_shape_big_cf : forall p n tr S k, p <> PNull -> rpreD_free_cf B S n -> kQuarantineMax < req_size n ->
In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
free_cf p tr S = (depot_put tr ;; modify (fun s => set_chunks (upd_chunk (st_chunks s) (qk k)) s) ;; recycle_chunk (qk k) ;;
  dmd drain_body_cf) (dtick S).
Proof.
intros p n tr S k _ ((_ & HW) & _ & HI & _) Hq Hbl Hf Hk.
destruct (find_user_spec _ _ _ Hf) as [Hin Hu].
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ HW) k Hin) as [_ CK].
destruct (find_user_block_cf _ _ _ _ S p n (WfR_of_WfP_cf _ _ _ _ _ HW) Hbl) as (k2 & Hf2 & _ & _ & _ & Hr2).
rewrite Hf in Hf2. injection Hf2 as <-.
assert (QS : ck_n (mkChunk (ck_beg k) (ck_req k) CQuarantined) <=? kQuarantineMax = false)
  by (apply Z.leb_gt; unfold ck_n; cbn [ck_req]; rewrite Hr2; exact Hq).
rewrite <- dmd_cf. unfold dtick.
destruct p as [|o|r o|c q].
- exfalso. unfold ck_user in Hu. revert Hu CK. destruct (ck_beg k); cbn; intros Hu CK; try discriminate Hu; exact CK.
- unfold free_cf. cbn -[depot_put enqueue recycle_chunk maybe_drain_cf upd_chunk find_user ck_n kQuarantineMax Z.leb]. rewrite HI.
  cbn -[depot_put enqueue recycle_chunk maybe_drain_cf upd_chunk find_user ck_n kQuarantineMax Z.leb]. rewrite Hf.
  cbn -[depot_put enqueue recycle_chunk maybe_drain_cf upd_chunk find_user ck_n kQuarantineMax Z.leb]. rewrite Hk, QS. reflexivity.
- unfold free_cf. cbn -[depot_put enqueue recycle_chunk maybe_drain_cf upd_chunk find_user ck_n kQuarantineMax Z.leb]. rewrite HI.
  cbn -[depot_put enqueue recycle_chunk maybe_drain_cf upd_chunk find_user ck_n kQuarantineMax Z.leb]. rewrite Hf.
  cbn -[depot_put enqueue recycle_chunk maybe_drain_cf upd_chunk find_user ck_n kQuarantineMax Z.leb]. rewrite Hk, QS. reflexivity.
- unfold free_cf. cbn -[depot_put enqueue recycle_chunk maybe_drain_cf upd_chunk find_user ck_n kQuarantineMax Z.leb]. rewrite HI.
  cbn -[depot_put enqueue recycle_chunk maybe_drain_cf upd_chunk find_user ck_n kQuarantineMax Z.leb]. rewrite Hf.
  cbn -[depot_put enqueue recycle_chunk maybe_drain_cf upd_chunk find_user ck_n kQuarantineMax Z.leb]. rewrite Hk, QS. reflexivity.
Qed.

(* qtight at the end of every granted path of free_cf, from Wf_cf and qtight at the entry (YGcfRoom.free_cf_room_inv). *)
Lemma free_cf_post_tight : forall p n tr S X' trc, rpreD_free_cf B S n -> apath (free_cf p tr S) trc (tt, X') -> qtight X'.
Proof.
intros p n tr S X' trc ((_ & HW) & HQM & _ & _) Hpa.
destruct (rpost_apath _ true _ _ _ (free_cf_room_inv _ S p tr true HW (qmeter_cf_tight S HQM)) Hpa) as [_ HQ].
exact HQ.
Qed.

Section i.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Local Notation dpost := (CLdepot.dpost_x im_segs B).
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Local Notation ARX := (ARX_cf B IOK Hp).
Local Notation U := (U_cf B).
Local Notation rpre := (rpreD_big_cf B).
Local Notation fpre := (fpre_hp_cf im_segs B Hp).
Local Notation AOX := (aowned B).

(* The two recycle fields of DGbigIF.DIfaceBig (the PRIMED text, a working branch 3711d297cf5a, ruling (A)),
   by reference to their texts: dbg_rq_t (the cut relation and the recycle invariant for the one chunk at Recycle's
   call; a Theorem Labs lane's YGcfInstFreeBigRq.bext_rq_cf at the cf choice) and dbg_rcs_t (Recycle on the big chunk under the
   re-hide; dbg_rcs_of_sec_rh_cf below from the unit's primed walk SEC_rh_t). *)
Record DIfaceBigExt : Prop := {
  bext_rq : dbg_rq_t B U ARX ARXr AOX rpre fpre dpost DRq;
  bext_rcs : dbg_rcs_t B ARXr AOX DRq
}.

Hypothesis HIOK : IOK_ok B IOK.
Hypothesis HIOKD : FM_INST_OK B.
Hypothesis HIMG : YGcfDIface.IMG_COVER.
Hypothesis HTSD : FV_TSD B.
Hypothesis HIAL : FV_IAL B.
Hypothesis HQC : FQ_CONST B.
Hypothesis HDZ : YGcfDIface.DZONE_OWNED B.
Hypothesis HIZ : YGcfDIface.IZONE_OWNED B.
Hypothesis HZ3 : FV_ZONE3.

(* The callee fields read here (depot, dpost_aok, requar_e, frame_r) are DIfaceExtRh's verbatim ones. *)
Theorem diface_big_cf : DIfaceExtRh B IOK Hp ARXr L24 QB DRq -> DIfaceBigExt ->
  DIfaceBig B U free_cf ARX ARXr AOX rpre qtight fpre dpost drain_body_cf DRq.
Proof.
intros E [Erq Ercs].
destruct E as [Ed Ea _ _ _ _ Ere _ _ Efr _].
constructor.
- exact (di_inst_cf B IOK Hp HIOK HIOKD).
- intros inst ly S W mem md p n HA ((_ & HQM & HI & _) & Hbg) _ HBLK.
  pose proof (HIOK inst (ARX_cf_iok B IOK Hp inst ly S W mem md HA)) as ->.
  exact (view_big_cf B HIMG HTSD HQC HIAL HZ3 ly S Hp W mem md p n (ARX_cf_ARcf B IOK Hp _ ly S W mem md HA) HI
    (qmeter_cf_tight S HQM) HBLK Hbg).
- intros inst ly W mem md p n tr S k _ Hp0 (HR & Hbg) Hbl Hf Hk. exact (di_shape_big_cf p n tr S k Hp0 HR Hbg Hbl Hf Hk).
- exact Ed.
- exact Ea.
- exact Erq.
- exact Ercs.
- exact Ere.
- intros inst ly S W mem0 md0 p n tr X' W' mem' md' _ (HR & _) _ _ _ (trc & Hpa & _).
  exact (free_cf_post_tight p n tr S X' trc HR Hpa).
- (* the thread cache's size word: a quarantine cell of ARcf *)
  intros inst ly S W mem0 md0 p n X' W' mem' md' _ _ _ HA'.
  pose proof (proj1 (ARX_cf_ARcf B IOK Hp inst ly X' W' mem' md' HA')) as M'.
  replace (ly_T ly + t_qc + 24) with (aeval B ly (aoff (AT t_qc) 24)) by (cbn; lia).
  eapply (cell_stateZ_cf B ly X' Hp W' mem' M'); [|reflexivity].
  unfold acells_cf. rewrite !in_app_iff. do 4 right. left. unfold quar_cells. right. right. apply in_app_iff. left.
  unfold qc_cells. do 3 right. left. reflexivity.
- exact (di_frame_cf B IOK Hp).
- exact Efr.
- exact (di_stack_cf B IOK Hp).
- (* dwrites_b is dwrites without the block's shadow disjunct *)
  intros inst ly S W mem md p n k a HA HR Hb Hf Ra Hw.
  apply (di_owned_cf B IOK Hp HDZ inst ly S W mem md p n k a HA (proj1 HR) Hb Hf Ra).
  unfold dwrites_b in Hw. unfold dwrites. destruct Hw as [X|[X|[X|X]]]; tauto.
- exact (di_owned_i_cf B IOK Hp HIZ).
Qed.
End i.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The big chunk's Recycle under the re-hide (DGbigIF.dbg_rcs_t, primed) from the unit's primed secondary Recycle walk *)
(* (YGcfInstFreeSig.SEC_rh_t): the size premise gives the walk's PSec triple through the model's Wf (big_sec_triple_cf *)
(* on DRq_cf's RIx_cf).                                                                                              *)
Section r.
Variable ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable NMAXD : Z.
Theorem dbg_rcs_of_sec_rh_cf :
  SEC_rh_t B AOX ARXr (YGcfInstDrainR.DRq_cf B NMAXD) -> dbg_rcs_t B ARXr AOX (YGcfInstDrainR.DRq_cf B NMAXD).
Proof.
intros SEC inst ly X k ks zs cbp W regs mem md PRE Hbig RX.
pose proof RX as ((WF & IT & _) & _).
apply Forall_app in IT as [IT _]. apply Forall_cons_iff in IT as [[Hk _] _].
destruct (big_sec_triple_cf _ 0 0 0 X k WF Hk Hbig) as (r & o & sm & i & Hb & Hsm & Hi).
exact (SEC inst ly X k ks zs cbp W regs mem md r o sm i PRE RX Hb Hsm Hi).
Qed.
End r.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* DGbigIF.DIfaceBig (primed) at the cf choice (ARXr := YGcfInstDrainR.ARXr_cf, DRq := DRq_cf at NMAXD_big_cf): the   *)
(* recycle fields from a Theorem Labs lane's YGcfInstFreeBigRq.bext_rq_cf and from the unit's walk SEC_rh_t.                     *)
Section k.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Variable L24 : Z.
Variable QB : astate -> Prop.
Local Notation ARXr := (YGcfInstDrainR.ARXr_cf B IOK Hp).
Local Notation DRqB := (YGcfInstDrainR.DRq_cf B YGcfInstDrainR.NMAXD_big_cf).
Hypothesis HIOK : IOK_ok B IOK.
Hypothesis HIOKD : FM_INST_OK B.
Hypothesis HIMG : YGcfDIface.IMG_COVER.
Hypothesis HTSD : FV_TSD B.
Hypothesis HIAL : FV_IAL B.
Hypothesis HQC : FQ_CONST B.
Hypothesis HDZ : YGcfDIface.DZONE_OWNED B.
Hypothesis HIZ : YGcfDIface.IZONE_OWNED B.
Hypothesis HZ3 : FV_ZONE3.
Hypothesis HIZR : FP_IZONE_ROM B.
Hypothesis HDS : FP_DSTAT B.
Hypothesis HDZF : FP_DZONE_FP B.
Hypothesis HCO : FP_CONST B.
Hypothesis HERRB : ERRB_APART B.
Hypothesis HPFA : PF_APART B.
Theorem diface_big_rh_cf_at :
  DIfaceExtRh B IOK Hp ARXr L24 QB DRqB -> SEC_rh_t B (aowned B) ARXr DRqB ->
  DIfaceBig B (U_cf B) free_cf (ARX_cf B IOK Hp) ARXr (aowned B) (rpreD_big_cf B) qtight (fpre_hp_cf im_segs B Hp)
    (CLdepot.dpost_x im_segs B) drain_body_cf DRqB.
Proof.
intros E SEC.
apply (diface_big_cf IOK Hp ARXr L24 QB DRqB HIOK HIOKD HIMG HTSD HIAL HQC HDZ HIZ HZ3 E).
constructor.
- exact (YGcfInstFreeBigRq.bext_rq_cf B IOK Hp HIZ HIZR HDS HDZ HDZF HCO HIAL HIMG HERRB HPFA).
- exact (dbg_rcs_of_sec_rh_cf ARXr (aowned B) YGcfInstDrainR.NMAXD_big_cf SEC).
Qed.
End k.
End a.
