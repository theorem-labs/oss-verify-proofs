(* CARRIED from commit feb36b594af6a0c0013ffa13916ea68f15baf41c,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainQ.v, sha256 3863436edef07c81f55ec26235552b1d1034940c64b0dd83d47de9de9259cb4d (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix cgif_file_fuzzer.lib -> fuzz_reply.lib.Reusable, except ImgBaseDG / DMiface / DMspec / YGcfInstBase /
   YGcfMallocCompose (and the YGcfInstDrain* files), which name reply's lib/B files; a sentence is split at a directory
   change, the module order kept. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the generic cf instance layer, lane F2b: the read fields of DMiface over
   the drain's cut relation, at the cf instance (ARXr := YGcfInstDrainR.ARXr_cf B IOK Hp, AOX := aowned B,
   DRq := YGcfInstDrainR.DRq_cf B).
   rule 24: no function proved (kind: interface-instance discharge of DMiface read fields; relation-level facts).

   - [di_frame_r_cf] (DGif0.DIface's di_frame_r : DMiface.di_frame_t ARXr AOX): RL.AR_frame_law_ok_cf, the ARcfR twin of
     YG0qcf.AR_frame_law_ok_cf (YGcfInstDrainRL.v);
   - [di_stack_r_cf]: DMiface.di_stack_t ARXr AOX, from RL.AR_stack_law_ok_cf;
   - [di_requar_e_cf] (di_requar_e : DMiface.di_requar_e_t ARX ARXr DRq at ARX := YGcfInstBase.ARX_cf B IOK Hp):
     YGcfInstDrainR.ARcf_of_ARXr_end;
   - [di_rview_cf] (di_rview : DMiface.di_rview_t B ARXr DRq): the space-base word, the pending chunks' headers and the
     pending batch objects at every cut; the cf twin of cgif's DGif1.rview_cgif (DGif1.v:2222-2247) with YFhl.item_facts /
     sb_cell and YFhf.slot_carved / slot_vs_chunk restated over ARmcfR (YFhf.v:70-129, YFhl.v:94-122).
   Image premises (named, over ImgBase.AImg's fields only): [SB_CONST], the space-base word is a constant cell of the
   image (cgif: in Tfib_const, YFhl.sb_cell); [IOK_inst], the unit's instance predicate names the symbol table's instance
   object (preset's IOK is that equation).  Image-free otherwise and event-free (no event-count term, no event regime,
   no event-keyed budget appears). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf YG03dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase YGcfInstDrainX YGcfInstDrainR YGcfInstDrainRL.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The image premises.                                                                                              *)
(* The space-base word of the allocator instance (AInst o_space) is a constant cell of the image (YFhl.sb_cell at
   cgif). *)
Definition SB_CONST : Prop := forall ly, In (ACell (AInst o_space) 8 (AV (ASp 0))) (im_const ly).

Section B.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Local Notation ARXr := (ARXr_cf B IOK Hp).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The laws of the cut relation.                                                                                    *)
Lemma di_frame_r_cf : di_frame_t ARXr (aowned B).
Proof.
intros inst ly S W mem md mem' md' (HI & HA & HX) AGR VIS Hvm Hlz He HK.
split; [exact HI|]. split; [exact (RL.AR_frame_law_ok_cf im_segs B ly S Hp W mem md mem' md' HA AGR VIS Hvm Hlz He HK)|].
(* the two machine cells are fields of the relation since field round 2, kept by the frame law itself *)
intros e He'. rewrite Hvm. exact (HX e He').
Qed.

Lemma di_stack_r_cf : di_stack_t ARXr (aowned B).
Proof.
intros inst ly S W mem md a (_ & HA & _) Ha. exact (RL.AR_stack_law_ok_cf im_segs B ly S Hp W mem md a HA Ha).
Qed.

(* di_requar_e: when nothing is pending, the cut relation is the walk's relation again (Compl0 from DRq_cf's
   deficit at zs = []). *)
Lemma di_requar_e_cf : di_requar_e_t (ARX_cf B IOK Hp) ARXr (DRq_cf B kQuarantineMax).
Proof.
intros inst ly S W mem md HR HD. exact (proj1 (ARX_cf_of_ARXr_end B IOK Hp inst ly S W mem md kQuarantineMax HR HD)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The pending batch objects at a cut (YFhf.slot_ok / slot_carved / slot_vs_chunk over ARmcfR).                     *)
Definition slot_ok_cf (X : astate) (z : Z) : Prop :=
0 <= z - region_off kBatchClass < rg_alloc_user (reg X kBatchClass) /\
(z - region_off kBatchClass) mod class_size kBatchClass = 0 /\ ~ In (z - region_off kBatchClass) (class_elems X kBatchClass).

Lemma RIx_cf_slots : forall U pp cc bb X its P selfs z, RIx_cf U pp cc bb X its P selfs -> In z (selfs ++ map b_self P) ->
slot_ok_cf X z.
Proof. intros U pp cc bb X its P selfs z (_ & _ & _ & _ & SF & _) Hz. exact (proj1 (Forall_forall _ _) SF z Hz). Qed.

Lemma class_size_24_cf : class_size kBatchClass = 8192. Proof. reflexivity. Qed.
Lemma region_off_24_cf : region_off kBatchClass = 24 * 2 ^ 32. Proof. reflexivity. Qed.

Lemma slot_carved_cf : forall ly X rd z, ARmcfR B ly X Hp rd -> slot_ok_cf X z ->
0 <= z - region_off kBatchClass /\ z - region_off kBatchClass + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\
rg_alloc_user (reg X kBatchClass) <= rg_mapped_user (reg X kBatchClass) <= kFreeArrayOffset.
Proof.
intros ly X rd z M (Z1 & Z2 & _). pose proof (amr_wfr _ _ _ _ _ M) as W.
pose proof (wfr_classes _ _ _ _ _ W kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as A2.
pose proof (mapped_bound_r_cf (as_universe B) 0 0 0 X kBatchClass W ltac:(unfold kBatchClass; lia)) as MB.
rewrite class_size_24_cf in Z2, A2. unfold kBatchBytes. split; [lia|]. split; [|lia]. clear - Z1 Z2 A2.
apply Z.mod_divide in Z2 as [q1 Hq1]; [|lia]. apply Z.mod_divide in A2 as [q2 Hq2]; [|lia]. nia.
Qed.

Lemma slot_vs_chunk_cf : forall ly X rd z k, ARmcfR B ly X Hp rd -> slot_ok_cf X z -> In k (st_chunks X) ->
forall a, ly_space ly + z <= a < ly_space ly + z + kBatchBytes -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k).
Proof.
intros ly X rd z k M SZ Hk a Ha Hin. pose proof (slot_carved_cf ly X rd z M SZ) as (C1 & C2 & C3). pose proof SZ as (Z1 & Z2 & Z3).
pose proof (RL.chunk_facts_cf B ly X Hp rd k M Hk) as CF. unfold RL.cfacts_cf in CF.
destruct CF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & CK).
pose proof (region_in_prim ly kBatchClass (amr_layout _ _ _ _ _ M) ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
rewrite class_size_24_cf in Z2. unfold region_base in *. rewrite region_off_24_cf in *.
destruct (ck_beg k) as [|off|r o|c p] eqn:Eb; try solve [destruct CK].
- cbv zeta in CK. destruct CK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
  set (c := prim_class off) in *. set (x := off - region_off c) in *.
  rewrite (region_off_eq c) in K5 by lia.
  destruct (Z.eq_dec c kBatchClass) as [Ec|Nc].
  + assert (INx : In x (class_elems X kBatchClass)).
    { rewrite <- Ec. unfold class_elems. rewrite !in_app_iff. right; right; left. subst x c. exact (In_chunk_offs X k off Hk Eb). }
    assert (NE : x <> z - 24 * 2 ^ 32) by (intros E; apply Z3; rewrite <- E; exact INx).
    rewrite Ec in K4, K7. rewrite class_size_24_cf in K4, K7. rewrite K4 in Hin. rewrite Ec in K5. unfold kBatchClass in K5.
    unfold kBatchBytes in *. clear - Ha Hin K5 K7 Z2 NE.
    apply Z.mod_divide in K7 as [q1 Hq1]; [|lia]. apply Z.mod_divide in Z2 as [q2 Hq2]; [|lia]. nia.
  + rewrite K4 in Hin. unfold kBatchClass in Nc. unfold kBatchBytes, kFreeArrayOffset in *.
    pose proof (class_ok c ltac:(lia)) as (Q1 & _).
    assert (c <= 23 \/ 25 <= c) as [Lc|Lc] by lia; clear - Ha Hin K5 K6 K8 K9 C1 C2 C3 Lc Q1; nia.
- destruct CK as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
  pose proof (amr_placed _ _ _ _ _ M) as [_ PD].
  pose proof (pairwise_app_inv zdisjoint (sec_extents ly X) (static_extents ly) PD) as (_ & _ & CR).
  assert (INP : In (ly_prim ly, kPrimResvSize) (static_extents ly)) by (unfold static_extents, owned_extents; cbn; tauto).
  pose proof (CR _ _ K5 INP) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ.
  rewrite K3, K4 in Hin. unfold kPage, kBatchBytes, kFreeArrayOffset in *. lia.
Qed.

(* A pending chunk's header (YFhl.item_facts over ARmcfR). *)
Lemma item_facts_cf : forall ly X rd k, ARmcfR B ly X Hp rd -> In k (st_chunks X) ->
aeval B ly (sptr_exp (ck_hdr k)) = ck_base B ly k + ck_rz k - kChunkHeaderSize /\
4096 <= ck_base B ly k + ck_rz k - kChunkHeaderSize /\ ck_base B ly k + ck_rz k - kChunkHeaderSize + 16 <= ASAN_CEIL /\
(ck_base B ly k + ck_rz k - kChunkHeaderSize) mod 16 = 0.
Proof.
intros ly X rd k M Hk. pose proof (RL.chunk_facts_cf B ly X Hp rd k M Hk) as CF. unfold RL.cfacts_cf in CF.
destruct CF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & CK).
assert (HP : match ck_beg k with PPrim _ | PSec _ _ => True | _ => False end)
  by (destruct (ck_beg k); first [exact I | destruct CK]).
assert (EH : aeval B ly (sptr_exp (ck_hdr k)) = ck_base B ly k + ck_rz k - kChunkHeaderSize).
{ unfold ck_hdr. change (aeval B ly (sptr_exp (padd (ck_beg k) (ck_rz k - kChunkHeaderSize))))
    with (sptr_addr B ly (padd (ck_beg k) (ck_rz k - kChunkHeaderSize))).
  rewrite (YG0s.sptr_addr_padd B ly _ _ HP). unfold ck_base. lia. }
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & Q1 & _).
split; [exact EH|]. ceil. unfold in_app, kLowShadowBeg, kChunkHeaderSize, kHighMemBeg, ASAN_CEIL in *.
split; [lia|]. split; [lia|].
apply Z.mod_divide in F3 as [q3 Hq3]; [|lia]. apply Z.mod_divide in F6 as [q6 Hq6]; [|lia].
apply Z.mod_divide; [lia|]. exists (q3 + q6 - 1). lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* di_rview.                                                                                                        *)
Hypothesis IOK_inst : IOK_ok B IOK.
Hypothesis SBC : SB_CONST.
Hypothesis TS : im_syms B.

Lemma di_rview_cf : di_rview_t B ARXr (DRq_cf B kQuarantineMax).
Proof.
intros inst ly X W mem md its zs (HI & HA & _) (RX & _). pose proof (IOK_inst _ HI) as ->.
destruct HA as (M & _).
assert (IT : forall k, In k its -> In k (st_chunks X)).
{ intros k Hk. destruct RX as (_ & IT & _). exact (proj1 (proj1 (Forall_forall _ _) IT k ltac:(apply in_app_iff; left; exact Hk))). }
split; [|split].
- pose proof (amr_const _ _ _ _ _ M) as C. rewrite (im_const_eq B ly TS) in C.
  pose proof (proj1 (Forall_forall _ _) C _ (SBC ly)) as Hc.
  pose proof (cell_holds_val_mem im_segs B ly (w_H W) mem (AInst o_space) 8 (ASp 0) Hc) as V. cbn [aeval] in V.
  rewrite Z.add_0_r in V. exact V.
- intros k Hk. exact (item_facts_cf ly X _ k M (IT k Hk)).
- intros z Hz.
  assert (SZ : slot_ok_cf X z) by (apply (RIx_cf_slots (as_universe B) 0 0 0 X its [] zs z RX); cbn [map]; rewrite app_nil_r; exact Hz).
  pose proof (slot_carved_cf ly X _ z M SZ) as (C1 & C2 & C3).
  pose proof SZ as (_ & Z2 & _). rewrite class_size_24_cf in Z2.
  split; [exact C1|]. split; [exact C2|]. split; [unfold kBatchBytes; exact Z2|].
  intros k a Hk Ha. exact (slot_vs_chunk_cf ly X _ z k M SZ (IT k Hk) a Ha).
Qed.

(* The requar view field as WalkB1 states it (DMwalkIF.di_rview_x_t @ 215f6356933): di_rview_t and the batch class's
   allocated bound.  RMAXD_cf is kFreeArrayOffset: the class's free array begins there, so nothing above it is user
   memory (DMwalkIF.v:304-308), and the invariant keeps every class's mapped user part inside it.  RMAXD_cf and its
   bound are YGcfInstDrainR's, one text for the three walk constants. *)
Lemma di_rview_alloc_cf : forall inst ly X W mem md its zs, ARXr inst ly X W mem md -> DRq_cf B kQuarantineMax X its zs ->
rg_alloc_user (reg X kBatchClass) <= RMAXD_cf.
Proof.
intros inst ly X W mem md its zs (_ & HA & _) _.
pose proof (amr_wfr _ _ _ _ _ (proj1 HA)) as W0.
pose proof (wfr_classes _ _ _ _ _ W0 kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1.
pose proof (mapped_bound_r_cf (as_universe B) 0 0 0 X kBatchClass W0 ltac:(unfold kBatchClass; lia)) as MB.
unfold RMAXD_cf. lia.
Qed.

End B.
End U.
