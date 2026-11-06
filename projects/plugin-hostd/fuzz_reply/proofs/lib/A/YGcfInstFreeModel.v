(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch): the generic cf layer's Deallocate interface, the fields that
   read the model and the owned set (DGif0.di_inst, di_shape_n, di_shape, di_frame, di_stack, di_owned, di_owned_b,
   di_owned_i, di_owned_x) at the layer's walk relation YGcfInstBase.ARX_cf.  rule 24: no function proved (kind:
   interface-instance discharge).

   The cf twins of c5's DGif1.v:1610-1691 (owned_cgif, owned_b_cgif, owned_i_cgif, owned_x_cgif), :744-819 (their
   helpers) and :2158-2205 (inst, shape, frame, stack), over YG0ncf.ARmcf / ARcf with YG0qcf / YG0scf / YG03cf's
   _cf lemmas.  The shape proofs follow preset's YGcfDIface.v:107-131 (a Theorem Labs lane, a0fed4266a1b); the owned-set image
   premises are the layer's YGcfDIface.DZONE_OWNED / IZONE_OWNED (one name per fact).  The instance tag: premise
   FM_INST_OK (the unit's IOK names an instance its DImg accepts).
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG DMspec DMiface DGif0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstFreeView.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfDIface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfRoom.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac dsplits := repeat match goal with |- _ /\ _ => split end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.
Variable B : asyms.

(* ================================================================================================================ *)
(* 0. Premises over the classes' fields and the symbol table.                                                       *)
(* DImg accepts the symbol table's instance object (cgif: DGif1.inst_cgif). *)
Definition FM_INST_OK : Prop := dg_inst_ok (as_inst B).
(* (The depot and internal-allocator zones' owned-set premises are YGcfDIface.DZONE_OWNED / IZONE_OWNED.) *)

(* free_cf's size test (YG00cf.free_cf, Quarantine::Put's `size <= max_size`) splits Deallocate in two: the enqueue
   side (DIface, this lane's instance) for req_size n <= kQuarantineMax, the recycle side (the big arm,
   DGbigIF.DIfaceBig) above it.  The guard sits in rpre, since di_shape's premises hold rpre but not fpre.  At PNull
   neither guard is needed: YGcfInstFreeTop's join sends PNull to the enqueue side at n := 0. *)
Definition rpreD_small_cf (S : astate) (n : Z) : Prop := rpreD_free_cf B S n /\ req_size n <= kQuarantineMax.
Definition rpreD_big_cf (S : astate) (n : Z) : Prop := rpreD_free_cf B S n /\ kQuarantineMax < req_size n.

(* ================================================================================================================ *)
(* 1. Helpers over ARmcf (DGif1.v:763-819).                                                                         *)
Lemma own_ext_nonuser_cf : forall ly S Hp rd x a, ARmcf B ly S Hp rd -> In x (st_chunks S) ->
ck_base B ly x <= a < ck_base B ly x + ck_extent x ->
~ (ck_base B ly x + ck_rz x <= a < ck_base B ly x + ck_rz x + req_size (ck_req x)) -> aowned B ly S a.
Proof.
intros ly S Hp rd x a M Hx Ha Hnu. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (NB : forall y, In y (st_chunks S) -> ck_state y = CAllocated ->
  ~ (ck_base B ly y + ck_rz y <= a < ck_base B ly y + ck_rz y + req_size (ck_req y))).
{ intros y Hy Hsy Hr. destruct (sptr_eqb (ck_beg y) (ck_beg x)) eqn:Eq.
  - apply sptr_eqb_spec in Eq. destruct (In_split_beg _ _ Hx (wfc_chunks_nodup _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as (l1 & l2 & E & N1 & N2).
    assert (y = x).
    { rewrite E in Hy. apply in_app_iff in Hy as [X|[<-|X]]; [exfalso; apply N1 | reflexivity | exfalso; apply N2];
      rewrite <- Eq; apply in_map_iff; exists y; auto. }
    subst y. exact (Hnu Hr).
  - assert (Hne : ck_beg y <> ck_beg x) by (intros E'; apply sptr_eqb_spec in E'; congruence).
    pose proof (user_in_extent_cf B ly S Hp rd y a M Hy Hr) as HE.
    pose proof (chunks_disjoint_cf B ly S Hp rd y x M Hy Hx Hne) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia. }
pose proof (amc_layout _ _ _ _ _ M) as LO0.
destruct (ck_beg x) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
  pose proof (region_in_prim ly (prim_class o) LO0 ltac:(lia)) as (R1 & R2 & _).
  eapply own_prim_nonuser_cf; [exact M | lia | exact NB].
- destruct GG as (-> & _ & Gbase & Gext & Gin & Gal & _).
  pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req x)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl
    (proj2 (amc_placed _ _ _ _ _ M)) Gin ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
  eapply own_ext_cf; [exact M | right; apply Exists_exists; exists (ly_sec ly r, sec_map_size (ck_req x));
    split; [exact Gin | unfold in_zr, kPage in *; cbn; lia] | exact NB |].
  unfold zdisjoint, kFakeFramesOff, kPage in *. cbn [fst snd] in DJ. lia.
Qed.

(* The word just past a batch object (a full batch's slot) is owned. *)
Lemma own_past_batch_cf : forall ly S Hp rd b a, ARmcf B ly S Hp rd -> In b (all_batches S) ->
ly_space ly + b_self b + kBatchBytes <= a < ly_space ly + b_self b + kBatchBytes + 8 -> aowned B ly S a.
Proof.
intros ly S Hp rd b a M Hb Ha. pose proof (amc_layout _ _ _ _ _ M) as LO.
destruct (batch_geom_cf B ly S Hp rd M b Hb) as (x & Eb & Px & Ax & Ux & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
eapply own_prim_nonuser_cf; [exact M | unfold kBatchBytes, kFreeArrayOffset in *; lia |].
intros y Hy Hsy Hr. pose proof (user_in_extent_cf B ly S Hp rd y a M Hy Hr) as HE.
pose proof (chunk_facts_cf B ly S Hp rd y M Hy) as (_ & _ & _ & _ & G5 & _).
pose proof (batch_vs_chunk_cf B ly S Hp rd M b y Hb Hy) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ.
unfold kBatchBytes in *. lia.
Qed.

(* The state after the tick and the chunk's change (DGif0.qx), field by field. *)
Lemma qx_fields_cf : forall S k z tr,
st_qthread (qx S k z tr) = st_qthread S /\ st_qglobal (qx S k z tr) = st_qglobal S /\
st_chunks (qx S k z tr) = upd_chunk (st_chunks S) (qk k) /\ st_secs (qx S k z tr) = st_secs S /\
frames (qx S k z tr) = frames S.
Proof. intros S k z tr. unfold qx, dtick, YFl0C.depot_after. destruct (z =? 0); repeat split; reflexivity. Qed.

Lemma sec_extents_qx_cf : forall ly S k z tr l1 l2, st_chunks S = l1 ++ k :: l2 ->
st_chunks (qx S k z tr) = l1 ++ qk k :: l2 -> sec_extents ly (qx S k z tr) = sec_extents ly S.
Proof.
intros ly S k z tr l1 l2 E E'. unfold sec_extents. rewrite E, E', !flat_map_app. cbn [flat_map].
unfold qk. cbn [ck_beg ck_req]. reflexivity.
Qed.

(* ARX_cf at a new world / memory / model with the same maps: the instance tag and the errbuf's mapping
   (xs_mapped_cf reads only the state and m_vmmaps) carry; ARcf (which carries the machine cells) is given. *)
Lemma ARX_cf_swap : forall IOK Hp inst ly S W mem md (W' : world im_segs) mem' md',
ARX_cf B IOK Hp inst ly S W mem md -> ARcf im_segs B ly S Hp W' mem' md' -> m_vmmaps md' = m_vmmaps md ->
ARX_cf B IOK Hp inst ly S W' mem' md'.
Proof.
intros IOK Hp inst ly S W mem md W' mem' md' HA AR' Hvm.
apply ARX_cf_start; [exact (ARX_cf_iok B IOK Hp inst ly S W mem md HA) | exact AR' |].
intros e He. rewrite Hvm. exact (ARX_cf_xsm B IOK Hp inst ly S W mem md HA e He).
Qed.

(* ================================================================================================================ *)
(* 2. The fields at the walk relation.                                                                              *)
Section f.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Local Notation ARX := (ARX_cf B IOK Hp).
Local Notation rpre := (rpreD_free_cf B).

Lemma di_inst_cf : IOK_ok B IOK -> FM_INST_OK -> forall inst ly S W mem md, ARX inst ly S W mem md -> dg_inst_ok inst.
Proof.
intros HO HI inst ly S W mem md HA. rewrite (HO inst (ARX_cf_iok B IOK Hp inst ly S W mem md HA)). exact HI.
Qed.

Lemma di_shape_n_cf : forall n tr S, rpre S n -> free_cf PNull tr S = ret tt (dtick S).
Proof.
intros n tr S (_ & _ & HI & _). unfold free_cf, tick, bind, get, modify, ret, dtick. cbn. rewrite HI. reflexivity.
Qed.

(* The enqueue side of free_cf's size test (as YGcfDIface.di_shape_cf). *)
Lemma di_shape_cf : forall p n tr S k, p <> PNull -> rpre S n -> req_size n <= kQuarantineMax -> In (p, n) (blocks S) ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
free_cf p tr S = (depot_put tr ;; modify (fun s => set_chunks (upd_chunk (st_chunks s) (qk k)) s) ;; enqueue (qk k) ;;
  dmd drain_body_cf) (dtick S).
Proof.
intros p n tr S k _ ((_ & HW) & _ & HI & _) Hq Hbl Hf Hk.
destruct (find_user_spec _ _ _ Hf) as [Hin Hu].
pose proof (proj1 (Forall_forall _ _) (wfc_chunks _ _ _ _ _ HW) k Hin) as [_ CK].
destruct (find_user_block_cf _ _ _ _ S p n (WfR_of_WfP_cf _ _ _ _ _ HW) Hbl) as (k2 & Hf2 & _ & _ & _ & Hr2).
rewrite Hf in Hf2. injection Hf2 as <-.
assert (QS : ck_n (mkChunk (ck_beg k) (ck_req k) CQuarantined) <=? kQuarantineMax = true)
  by (apply Z.leb_le; unfold ck_n; cbn [ck_req]; rewrite Hr2; exact Hq).
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

(* The frame law keeps the owned bytes; the layer's AR_frame_law_ok_cf moves the machine cells with them (their
   ownership from ARmcf's amc_cells_owned). *)
Lemma di_frame_cf : di_frame_t ARX (aowned B).
Proof.
intros inst ly S W mem md mem' md' HA AGR VIS Hvm Hlz He HK.
apply (ARX_cf_swap IOK Hp inst ly S W mem md W mem' md' HA); [| exact Hvm].
apply (AR_frame_law_ok_cf im_segs B ly S Hp W mem md mem' md' (ARX_cf_ARcf B IOK Hp inst ly S W mem md HA)); try assumption.
all: intros a Ha Ho; exact (AGR a Ha Ho).
Qed.

Lemma di_stack_cf : di_stack_t ARX (aowned B).
Proof.
intros inst ly S W mem md a HA Ha.
exact (AR_stack_law_ok_cf im_segs B ly S Hp W mem md a (ARX_cf_ARcf B IOK Hp inst ly S W mem md HA) Ha).
Qed.

(* (di_owned) the walk's writes outside its stack windows: the thread's cells (own_core_cf), the chunk header
   (own_meta_cf), the block's first word (its user bytes, or its extent past them), the depot zone (DZONE_OWNED) and the
   block's shadow (own_shadow_prim_cf / own_shadow_sec_cf). *)
Lemma di_owned_cf : YGcfDIface.DZONE_OWNED B ->
forall inst ly S W mem md p n k a, ARX inst ly S W mem md -> rpre S n -> In (p, n) (blocks S) ->
find_user (st_chunks S) p = Some k -> 0 <= a < 2 ^ 64 -> dwrites ly (sptr_addr B ly p) (req_size n) a ->
aowned B ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n).
Proof.
intros DZ inst ly S W mem md p n k a HA _ Hblk _ Ra Hw.
pose proof (proj1 (ARX_cf_ARcf B IOK Hp inst ly S W mem md HA)) as M.
apply In_blocks in Hblk as (k0 & Hk0 & Hst0 & Hu0 & Hr0).
pose proof (chunk_facts_cf B ly S Hp _ k0 M Hk0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (ext_rounded_cf B ly S Hp _ M k0 Hk0) as (ER & NN1 & NN2 & NN3). unfold ck_n in ER, NN1, NN2, NN3.
rewrite <- Hu0, <- Hr0 in Hw |- *. rewrite G4 in Hw |- *.
unfold dwrites in Hw. destruct Hw as [X|[X|[X|[X|X]]]].
- left. unfold DGgiC.WINT in X.
  eapply (own_core_cf B ly S Hp _ (ly_T ly, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|].
  cbn [fst snd]. unfold t_qc, t_unwinding, t_stats, kThreadObjSize in *. lia.
- left. apply (own_meta_cf B ly S Hp _ k0 a M Hk0).
  assert (0 <= match ck_beg k0 with PSec _ _ => kPage | _ => 0 end) by (destruct (ck_beg k0); unfold kPage; lia). lia.
- destruct (Z_lt_le_dec a (ck_base B ly k0 + ck_rz k0 + req_size (ck_req k0))) as [L|L]; [right; lia | left].
  apply (own_ext_nonuser_cf ly S Hp _ k0 a M Hk0); lia.
- left. destruct (DZ ly a X) as [Z|[Z|Z]].
  + exact (own_static_cf B ly S Hp _ a M Z).
  + eapply (own_core_cf B ly S Hp _ (ly_NB ly, kNodesBlockSize) a M); [unfold core_extents; cbn; tauto | cbn [fst snd]; exact Z].
  + eapply (own_core_cf B ly S Hp _ (ly_SB ly, kStoreBlockSize) a M); [unfold core_extents; cbn; tauto | cbn [fst snd]; exact Z].
- left. unfold dshadow, DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v in X.
  assert (U8 : exists a0, ck_base B ly k0 + ck_rz k0 = a0 * 8).
  { apply Z.mod_divide in G3 as [q Hq]; [|lia]. apply Z.mod_divide in G6 as [q' Hq']; [|lia]. exists (2 * q + 2 * q'). lia. }
  destruct U8 as [a0 Hua]. rewrite Hua in X. rewrite !Z_div_mult in X by lia.
  replace a with (shadow_addr ((a0 + (a - (SHADOW_OFF + a0))) * 8)).
  2:{ unfold shadow_addr. rewrite Z_div_mult by lia. lia. }
  destruct (extent_zone_cf B ly S Hp _ k0 M Hk0) as [[Z1 Z2]|(m & len & Zin & Z1 & Z2)].
  + eapply own_shadow_prim_cf; [exact M|]. lia.
  + eapply own_shadow_sec_cf; [exact M | exact Zin |]. unfold kPage in *. lia.
Qed.

(* (di_owned_b) the last batch's byte count, item count and slot are owned (own_batch_cf), or, for a full last
   batch, the word just past the batch object (own_past_batch_cf). *)
Lemma di_owned_b_cf : forall inst ly S W mem md lastb initr a, ARX inst ly S W mem md ->
rev (qc_list (st_qthread S)) = lastb :: initr -> 0 <= a < 2 ^ 64 -> bwrites ly lastb a -> aowned B ly S a.
Proof.
intros inst ly S W mem md lastb initr a HA Hrev Ra Hw.
pose proof (proj1 (ARX_cf_ARcf B IOK Hp inst ly S W mem md HA)) as M.
assert (Hin : In lastb (all_batches S)).
{ assert (E : qc_list (st_qthread S) = rev (lastb :: initr)) by (rewrite <- Hrev; rewrite rev_involutive; reflexivity).
  unfold all_batches. apply in_app_iff. left. rewrite E. cbn [rev]. apply in_app_iff. right. apply in_eq. }
pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ (amc_wf _ _ _ _ _ M))) lastb Hin) as [L1 L2].
apply Nat2Z.inj_le in L2. rewrite Z2Nat.id in L2 by (unfold kBatchSlots; lia).
unfold bwrites, DGgiC.SLOTv, DGgiC.Bv, DGgiC.BCv in Hw.
destruct (Z_lt_le_dec a (ly_space ly + b_self lastb + kBatchBytes)) as [Lt|Ge].
- apply (own_batch_cf B ly S Hp _ lastb a M Hin). unfold kBatchSlots, kBatchBytes in *. lia.
- apply (own_past_batch_cf ly S Hp _ lastb a M Hin). unfold kBatchSlots, kBatchBytes in *. lia.
Qed.

(* (di_owned_i) the internal allocator's zone is its area or owned static bytes. *)
Lemma di_owned_i_cf : YGcfDIface.IZONE_OWNED B ->
forall inst ly S W mem md a, ARX inst ly S W mem md -> dg_izone a -> aowned B ly S a.
Proof.
intros IZ inst ly S W mem md a HA Ha.
pose proof (proj1 (ARX_cf_ARcf B IOK Hp inst ly S W mem md HA)) as M.
destruct (IZ a Ha) as [Z|Z].
- apply (own_area_cf B ly S Hp _ (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B) a M);
    [unfold asyms_areas; cbn; tauto | cbn [fst snd]; lia].
- exact (own_static_cf B ly S Hp _ a M Z).
Qed.

(* (di_owned_x) the owned set of the quarantined state is the entry state's plus the block. *)
Lemma di_owned_x_cf : forall inst ly S W mem md p n k z tr a, ARX inst ly S W mem md -> rpre S n ->
In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k ->
aowned B ly (qx S k z tr) a -> aowned B ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n).
Proof.
intros inst ly S W mem md p n k z tr a HA _ Hb Hf O.
pose proof (proj1 (ARX_cf_ARcf B IOK Hp inst ly S W mem md HA)) as M. pose proof (amc_wf _ _ _ _ _ M) as W0.
destruct (find_user_block_cf _ _ _ _ _ p n (WfR_of_WfP_cf _ _ _ _ _ W0) Hb) as (k0 & Hf0 & Hk0 & Hst0 & Hu0 & Hr0).
rewrite Hf in Hf0. injection Hf0 as <-.
destruct (In_split_beg _ _ Hk0 (wfc_chunks_nodup _ _ _ _ _ W0)) as (l1 & l2 & E & N1 & N2).
destruct (qx_fields_cf S k z tr) as (_ & _ & Qc & _ & Qf).
assert (E' : st_chunks (qx S k z tr) = l1 ++ qk k :: l2).
{ rewrite Qc, E. apply upd_chunk_present; [reflexivity | exact N1]. }
pose proof (sec_extents_qx_cf ly S k z tr l1 l2 E E') as SE.
assert (Dec : (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n) \/ ~ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n)) by lia.
destruct Dec as [Din|Dout]; [right; exact Din|]. left.
unfold aowned in O |- *. rewrite SE in O. destruct O as [OW NC]. split; [exact OW|].
intros [(k' & Hk' & Hst' & Ha') | (cp' & Hcp & Hcpa)].
- rewrite E in Hk'. apply in_app_iff in Hk' as [H1|[<-|H2]].
  + apply NC. left. exists k'. split; [rewrite E'; apply in_app_iff; left; exact H1|]. split; assumption.
  + apply Dout. rewrite <- Hu0. unfold ck_n in Ha'. rewrite Hr0 in Ha'. exact Ha'.
  + apply NC. left. exists k'. split; [rewrite E'; apply in_app_iff; right; right; exact H2|]. split; assumption.
- apply NC. right. exists cp'. rewrite Qf. split; assumption.
Qed.

(* (di_lpost_d) qtight at the end of every granted path of the drain tree from the enqueued state X', from Wf_cf and
   qtight at the entry state S (ARX_cf's Wf_cf; rpre's meter).  The proof is YGcfDIface.v:146-175's (a Theorem Labs lane,
   a0fed4266a1b), which reads only the entry state's facts; X''s relation is not used. *)
Lemma di_lpost_d_cf : forall inst ly S W mem md p n tr k z nb X' (W' : world im_segs) (mem' : word -> option byte)
  (md' : Model) trc r,
ARX inst ly S W mem md -> rpre S n -> In (p, n) (blocks S) -> U_cf B tr S ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
st_qthread X' = qc_push (st_qthread (qx S k z tr)) (qk k) nb ->
match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end ->
st_chunks X' = st_chunks (qx S k z tr) -> st_qglobal X' = st_qglobal (qx S k z tr) ->
ARX inst ly X' W' mem' md' ->
kQuarantineCacheMax < qc_bytes (st_qthread X') ->
apath (drain_body_cf X' X') trc r -> gflag trc = true -> qtight (snd r).
Proof.
intros inst ly S W mem md p n tr k z nb X' W' mem' md' trc r HA HR _ _ Hf _ E3 Hnb E1 E2 _ Hbig Hpa _.
pose proof (ARX_cf_wf B IOK Hp inst ly S W mem md HA) as W0.
destruct HR as (_ & HQM & _ & _). pose proof (qmeter_cf_tight S HQM) as T. pose proof T as (T1 & T2 & T3).
destruct (qx_fields_cf S k z tr) as (Qt & Qg & Qc & _).
rewrite Qt in E3, Hnb. rewrite Qg in E2. rewrite Qc in E1.
assert (E4 : nb = None -> need_new_batch (st_qthread S) = false) by (intros ->; exact Hnb).
pose proof (wfc_quarantine _ _ _ _ _ W0) as Q. pose proof (wfc_chunks _ _ _ _ _ W0) as HC.
pose proof (wfc_chunks_nodup _ _ _ _ _ W0) as HND.
assert (Hpos : Forall (fun x => 0 <= ck_n x) (st_chunks S)).
{ eapply Forall_impl; [|exact HC]. cbv beta. intros x Hx. pose proof (chunk_ok_cf_n S x Hx). lia. }
destruct (find_user_spec _ _ _ Hf) as [Hk _].
unfold qk in *.
assert (HD : DRAIN_PRE X').
{ unfold DRAIN_PRE. rewrite E1, E2, E3.
  split; [exact T2|]. split; [apply qc_push_bytes; [exact E4 | exact (wq_bytes_t _ Q)]|].
  split; [exact (wq_bytes_g _ Q)|].
  split.
  { unfold q_items, all_batches. rewrite E3, E2, flat_map_app, qc_push_items by exact E4.
    pose proof (wq_items _ Q) as HQ. unfold q_items, all_batches in HQ. rewrite flat_map_app in HQ.
    apply Forall_app in HQ as [HQt HQg].
    apply Forall_app. split; [apply Forall_app; split; [|constructor; [reflexivity | constructor]]|].
    - eapply Forall_impl; [|exact HQt]. cbv beta. intros x [_ Hx]. exact Hx.
    - eapply Forall_impl; [|exact HQg]. cbv beta. intros x [_ Hx]. exact Hx. }
  split.
  { rewrite map_beg_upd; [exact HND|]. exact (in_map ck_beg _ _ Hk). }
  unfold quar_n, queued_n, q_items, all_batches in *. rewrite E1, E2, E3, flat_map_app, qc_push_items by exact E4.
  rewrite flat_map_app, items_n_app in T3. rewrite !items_n_app, items_n_cons, items_n_nil.
  pose proof (quar_nl_upd (st_chunks S) (mkChunk (ck_beg k) (ck_req k) CQuarantined) Hpos) as Hu.
  cbn [is_alloc ck_state] in Hu. unfold ck_n in *. cbn [ck_req] in *. lia. }
rewrite <- (maybe_drain_cf_drain X' Hbig) in Hpa.
destruct (rpost_apath _ true _ _ _ (maybe_drain_tight X' true HD) Hpa) as [_ HQ]. exact HQ.
Qed.
End f.
End a.
