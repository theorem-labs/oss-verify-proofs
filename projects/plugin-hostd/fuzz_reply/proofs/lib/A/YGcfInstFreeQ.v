(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch): the generic cf layer's Deallocate interface, the drain's
   quarantine reads DGif0.di_qview / di_qowned (DMiface.di_qview_t / di_qowned_t) at the layer's walk relation
   YGcfInstBase.ARX_cf.  rule 24: no function proved (kind: interface-instance discharge).

   The cf twin of c5's DGif1.v:1693-1858 and :2213-2218 (qowned_cgif, qv_*_cgif, qview_cgif_narrow, qview_cgif), over
   YG0ncf.ARmcf / ARcf.  The instance object is the symbol table's (premise YGcfInstBase.IOK_ok over the unit's instance
   predicate IOK, the field DMiface.qv_inst asks for it); the Quarantine object's constants are constant cells
   (premise YGcfInstFreeView.FQ_CONST); the drain's byte premise QB gives DMiface.qv_bytes (premise QB_BYTES:
   lane F2b's QB_cf is defined as that bound).  The instance's quarantine header is owned through the instance
   object's owned range (YG0qcf.inst_owned_range_cf); the class bound is YG01cf.mapped_bound_cf, never an event bound.
   Generic over CfImg / CfParams / AImg / DImg; no numeral of any image; no event term. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose YGcfInstBase YGcfInstFreeView.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfDIface.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.
Ltac dsplits := repeat match goal with |- _ /\ _ => split end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Variable B : asyms.

(* ================================================================================================================ *)
(* 0. Premises.                                                                                                     *)
(* (The unit's instance predicate names the symbol table's instance object: YGcfInstBase.IOK_ok, qview's qv_inst.) *)
(* (The Quarantine object's constant cells are YGcfInstFreeView.FQ_CONST.) *)
(* The drain's byte premise bounds both caches (DMiface.qv_bytes; cgif: qloose). *)
Definition QB_BYTES (QB : astate -> Prop) : Prop :=
  forall X, QB X -> qc_bytes (st_qthread X) + qc_bytes (st_qglobal X) <= 2 ^ 31.

(* ================================================================================================================ *)
(* 1. The parts of DMiface.qview over ARmcf.                                                                        *)
Lemma qv_cells_cf : forall ly X Hp (W : world im_segs) (mem : word -> option byte),
ARmcf B ly X Hp (aview im_segs (w_H W) mem) -> Forall (cell_holds B ly (aview im_segs (w_H W) mem)) (quar_cells X).
Proof.
intros ly X Hp W mem M. apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M)).
unfold acells_cf. rewrite !in_app_iff. do 4 right; left. exact Hc.
Qed.

Lemma qv_const_cf : FQ_CONST B -> forall ly X Hp (W : world im_segs) (mem : word -> option byte),
ARmcf B ly X Hp (aview im_segs (w_H W) mem) ->
val_mem im_segs (mrestrict (w_H W) mem) (as_inst B + o_q_max) 8 kQuarantineMax /\
val_mem im_segs (mrestrict (w_H W) mem) (as_inst B + o_q_min) 8 kQuarantineMin /\
val_mem im_segs (mrestrict (w_H W) mem) (as_inst B + o_q_cmutex + 2) 2 0.
Proof.
intros HC ly X Hp W mem M. destruct (HC ly) as (C1 & _ & C2 & C3).
split; [|split]; eapply const_at_val; eassumption.
Qed.

(* The thread object is visible (aareas' (AT 0, kThreadObjSize)) and an owned extent, off the image window. *)
Lemma qv_tpres_cf : forall ly X Hp (W : world im_segs) (mem : word -> option byte) md a,
ARmcf B ly X Hp (aview im_segs (w_H W) mem) -> ALedger_cf im_segs ly X md ->
ly_T ly + t_qc <= a < ly_T ly + t_qc + 32 -> apresent (w_H W) mem a.
Proof.
intros ly X Hp W mem md a M L Ha. pose proof (amc_layout _ _ _ _ _ M) as LO.
assert (IN : In (AT 0, kThreadObjSize) (aareas X)).
{ unfold aareas. rewrite !in_app_iff. do 6 right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) (amc_areas _ _ _ _ _ M) _ IN (a - ly_T ly)
  ltac:(cbn [snd]; unfold t_qc, kThreadObjSize in *; lia)) as V.
cbn [fst] in V. replace (aeval B ly (AT 0) + (a - ly_T ly)) with a in V by (cbn [aeval]; lia).
destruct (owned_extents_bound ly a LO ltac:(apply Exists_exists; exists (ly_T ly, kThreadObjSize); split;
  [unfold owned_extents; cbn; tauto | unfold in_zr, t_qc, kThreadObjSize in *; cbn [fst snd]; lia])) as (APP & _ & NIMG).
pose proof (app_addr_below_ceil a APP) as CE.
exact (aview_present_cf im_segs ly X md (w_H W) mem a L ltac:(ceil; unfold ASAN_CEIL in *; lia) NIMG V).
Qed.

(* Every batch object is a class-kBatchClass object of the region's allocated part. *)
Lemma qv_geom_cf : forall ly X Hp rd, ARmcf B ly X Hp rd ->
rg_alloc_user (reg X kBatchClass) <= kFreeArrayOffset /\
forall b, In b (all_batches X) ->
0 <= b_self b - region_off kBatchClass /\ b_self b - region_off kBatchClass + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\
(b_self b - region_off kBatchClass) mod kBatchBytes = 0.
Proof.
intros ly X Hp rd M. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL.
pose proof (mapped_bound_cf (as_universe B) 0 0 0 X kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
split; [lia|].
intros b Hb. destruct (batch_geom_cf B ly X Hp rd M b Hb) as (x & Eb & Px & Ax & Ux & _).
assert (Ex : b_self b - region_off kBatchClass = x) by (unfold region_base in Eb; lia).
rewrite Ex. dsplits; assumption.
Qed.

(* A batch object is in the class-kBatchClass region's mapped part (aareas), in high memory. *)
Lemma qv_bpres_cf : forall ly X Hp (W : world im_segs) (mem : word -> option byte) md b a,
ARmcf B ly X Hp (aview im_segs (w_H W) mem) -> ALedger_cf im_segs ly X md -> In b (all_batches X) ->
bobj ly b a -> apresent (w_H W) mem a.
Proof.
intros ly X Hp W mem md b a M L Hb Ha. pose proof (amc_layout _ _ _ _ _ M) as LO. unfold bobj in Ha.
destruct (batch_geom_cf B ly X Hp _ M b Hb) as (x & Eb & Px & Ax & Ux & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (IN : In (ASp (region_off kBatchClass), rg_mapped_user (reg X kBatchClass)) (aareas X)).
{ unfold aareas. rewrite !in_app_iff. left. apply in_flat_map. exists kBatchClass.
  split; [apply In_zseq; unfold kBatchClass; lia | left; reflexivity]. }
pose proof (proj1 (Forall_forall _ _) (amc_areas _ _ _ _ _ M) _ IN (x + (a - (ly_space ly + b_self b)))
  ltac:(cbn [snd]; unfold kBatchBytes in *; lia)) as V.
cbn [fst] in V. replace (aeval B ly (ASp (region_off kBatchClass)) + (x + (a - (ly_space ly + b_self b)))) with a in V
  by (cbn [aeval]; unfold region_base in Eb; lia).
apply (vis_present_cf ly X md (w_H W) mem a L LO);
  [ceil; unfold kHighMemBeg, ASAN_CEIL, kBatchBytes, kFreeArrayOffset, region_base in *; lia
  | unfold kHighMemBeg, kImgEnd, region_base in *; lia | exact V].
Qed.

Lemma qv_nodup_cf : forall ly X Hp rd, ARmcf B ly X Hp rd -> List.NoDup (map b_self (all_batches X)).
Proof.
intros ly X Hp rd M. pose proof (amc_wf _ _ _ _ _ M) as WF.
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wrc_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND.
apply YG04.NoDup_app_iff in ND as (_ & ND & _). apply YG04.NoDup_app_iff in ND as (_ & ND & _).
rewrite batch_offs_24 in ND.
clear - ND. induction (all_batches X) as [|x t IH]; cbn in *; [constructor|].
inversion ND as [|y l N1 N2]; subst. constructor; [|exact (IH N2)].
intros Hin. apply N1. apply in_map_iff in Hin as (x' & E & Hx'). apply in_map_iff. exists x'. split; [lia | exact Hx'].
Qed.

Lemma qv_wf_cf : forall ly X Hp rd, ARmcf B ly X Hp rd ->
qc_bytes (st_qthread X) = sum_bytes (qc_list (st_qthread X)) /\
qc_bytes (st_qglobal X) = sum_bytes (qc_list (st_qglobal X)) /\
Forall (fun b => (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) (all_batches X) /\
Forall (fun k => 0 <= ck_n k) (q_items X).
Proof.
intros ly X Hp rd M. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (wfc_quarantine _ _ _ _ _ WF) as WQ.
dsplits; [exact (wq_bytes_t _ WQ) | exact (wq_bytes_g _ WQ) | exact (wq_batches _ WQ) |].
apply Forall_forall. intros k Hk.
pose proof (proj1 (Forall_forall _ _) (wq_items _ WQ) k Hk) as [Hin _].
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ WF) k Hin) as [Hn _].
unfold ck_n. pose proof (req_size_bounds (ck_req k) ltac:(lia)). lia.
Qed.

Lemma qv_inited_cf : forall ly X Hp rd, ARmcf B ly X Hp rd -> kQuarantineCacheMax < qc_bytes (st_qthread X) ->
st_cache_inited X = true.
Proof.
intros ly X Hp rd M HTB. pose proof (amc_wf _ _ _ _ _ M) as WF.
apply (wfc_qinited _ _ _ _ _ WF). intros E. unfold all_batches in E. apply app_eq_nil in E as [E _].
pose proof (wq_bytes_t _ (wfc_quarantine _ _ _ _ _ WF)) as QB. rewrite E in QB. cbn in QB.
unfold kQuarantineCacheMax in HTB. lia.
Qed.

(* ================================================================================================================ *)
(* 2. The two fields at the walk relation.                                                                          *)
Section f.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Variable L24 : Z.
Variable QB : astate -> Prop.
Hypothesis HIOK : IOK_ok B IOK.
Hypothesis HIMG : YGcfDIface.IMG_COVER.
Hypothesis HTSD : FV_TSD B.
Hypothesis HQC : FQ_CONST B.
Hypothesis HQB : QB_BYTES QB.

(* (di_qowned) the quarantine's header words are in the instance object's owned range and the thread object
   (own_core_cf); the batch objects are owned (own_batch_cf). *)
Lemma di_qowned_cf : di_qowned_t (ARX_cf B IOK Hp) (aowned B) L24 QB.
Proof.
intros inst ly X W mem md a HA _ Ra Hq.
pose proof (HIOK inst (ARX_cf_iok B IOK Hp inst ly X W mem md HA)) as Ei. subst inst.
pose proof (proj1 (ARX_cf_ARcf B IOK Hp (as_inst B) ly X W mem md HA)) as M.
destruct Hq as [Hq|(b & Hb & Hob)].
- unfold qhdr in Hq. destruct Hq as [Hq|[Hq|Hq]].
  1,2: apply (inst_owned_range_cf B ly X Hp _ M); unfold o_quar in *; lia.
  eapply (own_core_cf B ly X Hp _ (ly_T ly, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|].
  cbn [fst snd]. unfold t_qc, kThreadObjSize in *. lia.
- unfold bobj in Hob. exact (own_batch_cf B ly X Hp _ b a M Hb Hob).
Qed.

(* (di_qview) DMiface.qview, field by field. *)
Lemma di_qview_cf : di_qview_t B (ARX_cf B IOK Hp) L24 QB.
Proof.
intros inst ly X W mem md HA (HTB & HQ & _).
pose proof (HIOK inst (ARX_cf_iok B IOK Hp inst ly X W mem md HA)) as Ei. subst inst.
pose proof (ARX_cf_ARcf B IOK Hp (as_inst B) ly X W mem md HA) as HAR.
pose proof (proj1 HAR) as M. pose proof (proj1 (proj2 HAR)) as L. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (qv_const_cf HQC ly X Hp W mem M) as (C1 & C2 & C3).
pose proof (qv_geom_cf ly X Hp _ M) as [G1 G2].
pose proof (qv_wf_cf ly X Hp _ M) as (F1 & F2 & F3 & F4).
constructor.
- reflexivity.
- exact LO.
- exact (HIMG ly X md L).
- rewrite (amc_tsd _ _ _ _ _ M). exact HTSD.
- exact (qv_cells_cf ly X Hp W mem M).
- exact (conj C1 (conj C2 C3)).
- intros a Ha. exact (qv_tpres_cf ly X Hp W mem md a M L Ha).
- intros b a Hb Ha. exact (qv_bpres_cf ly X Hp W mem md b a M L Hb Ha).
- exact (conj G1 G2).
- apply NoDup_ListNoDup. exact (qv_nodup_cf ly X Hp _ M).
- exact (conj F1 (conj F2 (conj F3 F4))).
- exact (HQB X HQ).
- exact (qv_inited_cf ly X Hp _ M HTB).
Qed.
End f.
End a.
