(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: di_shape_cf takes the premise req_size n <= kQuarantineMax (free_cf's enqueue side); the larger blocks take the big arm. *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: di_shape_cf takes the premise req_size n <= kQuarantineMax (free_cf's enqueue side); the larger blocks take the big arm. A change request to a Theorem Labs lane. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfDIface.v at commit d0377850faab (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* Theorem Labs, 2026-10: fuzz_preset's event-free allocator instance (suffix cf), the MODEL-LEVEL fields of c-asan's
   Deallocate interface DIface (lib/Reusable/DGif0.v:271-387; cgif lib/DGif0.v:266-381 at aa322d8bb0b) at the instance
     ft := free_cf, ARX := ARXs_cf B im_segs Hp, AOX := aowned B, rpre := rpre_dealloc_cf B, fpre := fpre_cf Hp,
     lpost := qtight, dbody := drain_body_cf (DMspec), U := admits (as_universe B) (P'', YG01.v:158; a Theorem Labs lane 22:05Z),
   for EVERY ghost set Hp: a malloc / free call keeps the caller's Hp (YG0dcf.v:13), so the instance fixes it per call
   and the post's ARcf is at that same Hp (Main, 2026-10-29: no `exists Hp`). AOX is cgif's aowned, as DGtop.v's cgif
   corollaries take it, and not aowned-or-xs_cf: free_leaf_cf's exception set has no errbuf extent (YG0dcf.v:431-445).
   fpre is the freed base not hidden, afree_realizes_cf's own premise (YG0dcf.v:451).
   Each lemma di_<field>_cf below states the field's type at that instance.
   THE FILE NAMES NO IMAGE. The field types are c-asan's image-free ones: DGif0 / DMspec / DMiface state them over
   ImgBase.AImg (the segments im_segs, the image window im_img_cover) and ImgBaseDG.DImg (the zones dg_dzone /
   dg_izone and the internal allocator's cells dg_ial_post), taken here as [Context {IM : AImg} {DI : DImg}]. Those
   five files are byte copies of aa322d8bb0b in lib/Reusable (each says so on its first line). A unit instantiates the
   two classes at its image: image A (preset's ASan binary) is A/ADIfaceA.v (AImg_A, DImg_A), which also discharges the
   image premises below with A's named facts.
   Premises a field needs from the image are named, over the class fields only: IMG_COVER (di_view_n part (a)),
   DZONE_OWNED (di_owned), IZONE_OWNED (di_owned_i). di_post_n's machine half is the premise POST_N_MEM; at image A
   the field is proved without it (A/ADIfacePostNA.v, di_post_n_A, restated at the instance in A/ADIfaceA.v).
   ARXs_cf takes the segment list explicitly, so a walk at a unit's segments names it without the class; it takes
   the ghost set Hp next, so ARXs_cf B segs is the Hp-indexed relation YGcfMallocCompose.v's bridge takes.
   Nothing here is a function's proof (rule 24). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0dcf YG0qcf YG0scf YG03cf YGcfRoomPre YGcfRmodel YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG DMspec DMiface DGif0.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================================================================ *)
(* The image window from the ledger, at any segment list and bounds: some segment starts at or below [lo] and some  *)
(* segment ends at or above [hi]. A unit proves the two segment premises at its image (A/ADIfaceA.v) and so its     *)
(* im_img_cover (IMG_COVER below).                                                                                  *)
Section IMG.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition IMG_LO_SEG (segs : list Segment) (lo : Z) : Prop := exists sg, In sg segs /\ Z.of_N (seg_base sg) <= lo.
Definition IMG_HI_SEG (segs : list Segment) (hi : Z) : Prop :=
exists sg, In sg segs /\ hi <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Lemma img_cover_of_ledger_cf : forall segs lo hi ly S md, IMG_LO_SEG segs lo -> IMG_HI_SEG segs hi -> ALedger_cf segs ly S md ->
fst (ly_img ly) <= lo /\ hi <= fst (ly_img ly) + snd (ly_img ly).
Proof.
intros segs lo hi ly S md (sg1 & H1 & E1) (sg2 & H2 & E2) L. split.
- destruct (alc_img _ _ _ _ L sg1 H1) as [A _]. lia.
- destruct (alc_img _ _ _ _ L sg2 H2) as [_ A]. lia.
Qed.
End IMG.

(* ================================================================================================================ *)
(* The instance.                                                                                                    *)
Section INST.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.
Context (B : asyms).

(* ARX at a segment list and a ghost set Hp: ARcf at Hp and acall_pre_cf's state conjuncts (YG0dcf.v:229-245; not its
   hull admission cf_hull_ok, :247). The errbuf slot's placement is ARcf's own (ARmcf's field amc_xs_placed, YG0ncf.v:239; YG0ncf.xs_placed_of_ARcf), not a conjunct here. The
   instance object is the symbol table's (as_inst B). DIface's ARX is ARXs_cf B im_segs Hp. *)
Definition ARXs_cf (segs : list Segment) (Hp : list Z) (inst : Z) (ly : alayout) (S : astate) (W : world segs)
(mem : word -> option byte) (md : Model) : Prop :=
inst = as_inst B /\ ARcf segs B ly S Hp W mem md /\
qmeter_cf S /\ Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max /\ ERRB_ROOM S /\
abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8 <= CF_MAX /\ batch_room_cf S.
(* rpre: cgif's rpre_dealloc_cgif (DeallocGcgif.v:23 at 3f2fdc5b787: aregime S /\ qmeter S /\ st_internal_inited S
   = true) restated at the instance: the realloc composition's Deallocate premise rpreD_cfr (universe_ok and Wf_cf,
   YGcfRmodel.v:71, in place of the event regime, which the event-free model drops as acall_pre_cf does), qmeter_cf
   for qmeter, and the internal allocator initialized. *)
Definition rpre_dealloc_cf (S : astate) (n : Z) : Prop := rpreD_cfr B S n /\ qmeter_cf S /\ st_internal_inited S = true.
(* fpre: the freed base is not a hidden head (afree_realizes_cf's premise, YG0dcf.v:451); without it ARcf at Hp
   after the free fails amc_hp_live (YG0ncf.v:234-235). cgif's fpre_cgif is True (projects/omx-clap-core/fuzz_state/proofs/lib/A/DeallocGcgif.v:26-27; cgif lib/DeallocGcgif.v:24-25 at 3f2fdc5b787). *)
Definition fpre_cf (Hp : list Z) (ly : alayout) (S : astate) (W : world im_segs) (mem : word -> option byte) (p : sptr)
(n : Z) : Prop :=
~ In (sptr_addr B ly p) Hp.

Lemma ARXs_cf_ARm : forall segs Hp inst ly S (W : world segs) mem md, ARXs_cf segs Hp inst ly S W mem md ->
ARmcf B ly S Hp (aview segs (w_H W) mem).
Proof. intros segs Hp inst ly S W mem md (_ & (M & _) & _). exact M. Qed.
Lemma ARXs_cf_wf : forall segs Hp inst ly S (W : world segs) mem md, ARXs_cf segs Hp inst ly S W mem md ->
Wf_cf (as_universe B) S.
Proof. intros segs Hp inst ly S W mem md H. exact (amc_wf _ _ _ _ _ (ARXs_cf_ARm _ _ _ _ _ _ _ _ H)). Qed.
Lemma ARXs_cf_qtight : forall segs Hp inst ly S (W : world segs) mem md, ARXs_cf segs Hp inst ly S W mem md -> qtight S.
Proof. intros segs Hp inst ly S W mem md (_ & _ & Q & _). exact (qmeter_cf_tight S Q). Qed.

(* The state after the tick and after the chunk's change (DGif0's qx). *)
Lemma qx_fields : forall S k z tr,
st_qthread (qx S k z tr) = st_qthread S /\ st_qglobal (qx S k z tr) = st_qglobal S /\
st_chunks (qx S k z tr) = upd_chunk (st_chunks S) (qk k) /\ st_secs (qx S k z tr) = st_secs S /\
frames (qx S k z tr) = frames S.
Proof. intros S k z tr. unfold qx, dtick, YFl0C.depot_after. destruct (z =? 0); repeat split; reflexivity. Qed.

(* ================================================================================================================ *)
(* (shape) di_shape_n, di_shape.                                                                                    *)
Lemma di_shape_n_cf : forall n tr S, rpre_dealloc_cf S n -> free_cf PNull tr S = ret tt (dtick S).
Proof.
intros n tr S (_ & _ & HI). unfold free_cf, tick, bind, get, modify, ret, dtick. cbn. rewrite HI. reflexivity.
Qed.

(* The enqueue side of free_cf's size test (YG00cf.free_cf): DIface's di_shape holds for the blocks up to
   kQuarantineMax; the larger blocks take the big arm (the internal file BIG-ARM.md section 7). *)
Lemma di_shape_cf : forall p n tr S k, p <> PNull -> rpre_dealloc_cf S n -> req_size n <= kQuarantineMax -> In (p, n) (blocks S) ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
free_cf p tr S = (depot_put tr ;; modify (fun s => set_chunks (upd_chunk (st_chunks s) (qk k)) s) ;; enqueue (qk k) ;; dmd drain_body_cf) (dtick S).
Proof.
intros p n tr S k _ ((_ & HW) & _ & HI) Hq Hbl Hf Hk.
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

(* ================================================================================================================ *)
(* (drain) di_lpost_d: qtight at the end of every path of the drain tree from the enqueued state X'.                *)
Lemma di_lpost_d_cf : forall Hp inst ly S W mem md p n tr k z nb X' (W' : world im_segs) (mem' : word -> option byte) (md' : Model) trc r,
ARXs_cf im_segs Hp inst ly S W mem md -> rpre_dealloc_cf S n -> In (p, n) (blocks S) -> admits (as_universe B) tr S ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
st_qthread X' = qc_push (st_qthread (qx S k z tr)) (qk k) nb ->
match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end ->
st_chunks X' = st_chunks (qx S k z tr) -> st_qglobal X' = st_qglobal (qx S k z tr) ->
ARXs_cf im_segs Hp inst ly X' W' mem' md' ->
kQuarantineCacheMax < qc_bytes (st_qthread X') ->
apath (drain_body_cf X' X') trc r -> gflag trc = true -> qtight (snd r).
Proof.
intros G inst ly S W mem md p n tr k z nb X' W' mem' md' trc r HA _ _ _ Hf _ E3 Hnb E1 E2 _ Hbig Hp _.
pose proof (ARXs_cf_wf _ _ _ _ _ _ _ _ HA) as W0. pose proof (ARXs_cf_qtight _ _ _ _ _ _ _ _ HA) as T. pose proof T as (T1 & T2 & T3).
destruct (qx_fields S k z tr) as (Qt & Qg & Qc & _).
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
rewrite <- (maybe_drain_cf_drain X' Hbig) in Hp.
destruct (rpost_apath _ true _ _ _ (maybe_drain_tight X' true HD) Hp) as [_ HQ]. exact HQ.
Qed.

(* ================================================================================================================ *)
(* (post) di_post_n, parts (a) and (c): ARX and qtight are kept by the tick. Part (b), the machine half (the cells *)
(* dmem_n rewrites: t_unwinding := 0 and the internal allocator's zone := dg_ial_post), is the premise POST_N_MEM. *)
Lemma ARXs_cf_dtick : forall segs Hp inst ly S (W : world segs) mem md,
ARXs_cf segs Hp inst ly S W mem md -> ARXs_cf segs Hp inst ly (dtick S) W mem md.
Proof.
intros segs Hp inst ly S W mem md (Hi & (M & L & BUD & MW & HS) & (QM & R1 & R2 & R3 & R4)).
assert (E : abudget_cf (dtick S) = abudget_cf S) by exact (abudget_cf_frame S (dtick S) eq_refl eq_refl eq_refl eq_refl).
split; [exact Hi|]. split.
2: { split; [exact (conj (proj1 QM) (mroom_cf_frame S (dtick S) eq_refl eq_refl eq_refl eq_refl (proj2 QM)))|].
     split; [exact R1|]. split; [exact R2|]. split; [rewrite E; exact R3 | exact R4]. }
unfold dtick. split; [|split; [|split; [exact (abudget_ok_cf_frame segs ly S (set_nev (st_nev S + 1) S) W eq_refl
  eq_refl eq_refl eq_refl BUD) | split; [exact MW | exact HS]]]].
- pose proof (amc_wf _ _ _ _ _ M) as WM. destruct M. constructor; try assumption. exact (WfP_cf_tick _ _ _ _ _ WM).
- destruct L. constructor; assumption.
Qed.

Lemma qtight_dtick : forall S, qtight S -> qtight (dtick S).
Proof. intros S H. exact H. Qed.

(* The machine premise of di_post_n (part (b)): the memory dmem_n leaves keeps ARX at the entry state. *)
Definition POST_N_MEM : Prop :=
forall Hp inst ly S W mem0 md0 n tr sp0 mem' mat,
ARXs_cf im_segs Hp inst ly S W mem0 md0 -> rpre_dealloc_cf S n -> fpre_cf Hp ly S W mem0 PNull n -> admits (as_universe B) tr S ->
ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
dmem_n W ly sp0 mem0 mem' ->
ARXs_cf im_segs Hp inst ly S W mem' (with_vm_backing (m_vm_lazy md0) mat md0).

Lemma di_post_n_cf : POST_N_MEM ->
forall Hp inst ly S W mem0 md0 n tr sp0 mem' mat,
ARXs_cf im_segs Hp inst ly S W mem0 md0 -> rpre_dealloc_cf S n -> fpre_cf Hp ly S W mem0 PNull n -> admits (as_universe B) tr S ->
ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
dmem_n W ly sp0 mem0 mem' ->
(exists trc, apath (free_cf PNull tr S) trc (tt, dtick S) /\ gflag trc = true) ->
ARXs_cf im_segs Hp inst ly (dtick S) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\ qtight (dtick S).
Proof.
intros HB Hp inst ly S W mem0 md0 n tr sp0 mem' mat HA HR HF HU H1 H2 H3 H4 HM _.
split.
- apply ARXs_cf_dtick. exact (HB Hp inst ly S W mem0 md0 n tr sp0 mem' mat HA HR HF HU H1 H2 H3 H4 HM).
- apply qtight_dtick. exact (ARXs_cf_qtight _ _ _ _ _ _ _ _ HA).
Qed.

(* ================================================================================================================ *)
(* (laws) di_frame, di_stack.                                                                                       *)
Lemma di_frame_cf : forall Hp, di_frame_t (ARXs_cf im_segs Hp) (aowned B).
Proof.
intros Hp inst ly S W mem md mem' md' (Hi & AR & R) AGR VIS Hvm Hlz He HK.
split; [exact Hi|]. split; [|exact R].
apply (AR_frame_law_ok_cf im_segs B ly S Hp W mem md mem' md' AR); try assumption.
all: intros a Ha Ho; exact (AGR a Ha Ho).
Qed.

Lemma di_stack_cf : forall Hp, di_stack_t (ARXs_cf im_segs Hp) (aowned B).
Proof.
intros Hp inst ly S W mem md a (_ & AR & _) Ha O.
exact (AR_stack_law_ok_cf im_segs B ly S Hp W mem md a AR Ha O).
Qed.

(* ================================================================================================================ *)
(* (owned) di_owned_x: the owned set of the quarantined, depot-updated state is the entry state's plus the block.   *)
Lemma sec_extents_qx : forall ly S k z tr l1 l2, st_chunks S = l1 ++ k :: l2 ->
st_chunks (qx S k z tr) = l1 ++ qk k :: l2 -> sec_extents ly (qx S k z tr) = sec_extents ly S.
Proof.
intros ly S k z tr l1 l2 E E'. unfold sec_extents. rewrite E, E', !flat_map_app. cbn [flat_map].
unfold qk. cbn [ck_beg ck_req]. reflexivity.
Qed.

Lemma di_owned_x_cf : forall Hp inst ly S W mem md p n k z tr a,
ARXs_cf im_segs Hp inst ly S W mem md -> rpre_dealloc_cf S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k ->
aowned B ly (qx S k z tr) a -> aowned B ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n).
Proof.
intros Hp inst ly S W mem md p n k z tr a HA _ Hb Hf O.
pose proof (ARXs_cf_wf _ _ _ _ _ _ _ _ HA) as W0.
destruct (find_user_block_cf _ _ _ _ _ p n (WfR_of_WfP_cf _ _ _ _ _ W0) Hb) as (k0 & Hf0 & Hk0 & Hst0 & Hu0 & Hr0).
rewrite Hf in Hf0. injection Hf0 as <-.
destruct (In_split_beg _ _ Hk0 (wfc_chunks_nodup _ _ _ _ _ W0)) as (l1 & l2 & E & N1 & N2).
destruct (qx_fields S k z tr) as (_ & _ & Qc & _ & Qf).
assert (E' : st_chunks (qx S k z tr) = l1 ++ qk k :: l2).
{ rewrite Qc, E. apply upd_chunk_present; [reflexivity | exact N1]. }
pose proof (sec_extents_qx ly S k z tr l1 l2 E E') as SE.
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

(* ================================================================================================================ *)
(* (view) di_view_n part (a), dn_img: the image window from the ledger, under the image premise IMG_COVER.          *)
Definition IMG_COVER : Prop := forall ly S md, ALedger_cf im_segs ly S md -> im_img_cover ly.

Lemma di_view_n_img_cf : IMG_COVER ->
forall Hp inst ly S W mem md n, ARXs_cf im_segs Hp inst ly S W mem md -> rpre_dealloc_cf S n -> im_img_cover ly.
Proof.
intros HC Hp inst ly S W mem md n (_ & (_ & L & _) & _) _. exact (HC ly S md L).
Qed.

(* ================================================================================================================ *)
(* (owned) di_owned, di_owned_b, di_owned_i.                                                                        *)
(* Image premises: the depot zone is the symbol table's owned static areas plus the nodes and store blocks, and the *)
(* internal allocator's zone is its area or owned static bytes (cgif's DImg: DGgi.v:514-516; image A's: ADIfaceA). *)
Definition DZONE_OWNED : Prop := forall ly a, dg_dzone ly a ->
Exists (in_zr a) (as_owned_static B) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Definition IZONE_OWNED : Prop := forall a, dg_izone a ->
(as_ialloc_lo B <= a < as_ialloc_hi B) \/ Exists (in_zr a) (as_owned_static B).

(* A chunk's header room and slack: rz + 8 bytes fit in its extent. *)
Lemma rz8_extent : forall k, 0 <= ck_req k -> ck_rz k + 8 <= ck_extent k.
Proof.
intros k H. unfold ck_rz, ck_extent.
pose proof (rounded_size_bounds (ck_req k) H) as [[R1 _] _]. pose proof (rz_size_bounds (ck_req k)) as [Z1 _].
destruct (from_primary (ck_req k)) eqn:Hfp.
- pose proof (primary_geometry (ck_req k) H Hfp) as (_ & [_ P2] & _). unfold needed_size in P2. rewrite Hfp in P2.
  unfold needed_primary in P2. lia.
- pose proof (secondary_geometry (ck_req k) H Hfp) as (_ & E2 & _ & [S1 _] & _). rewrite E2 in S1.
  unfold needed_primary in S1. lia.
Qed.

(* The bytes of a chunk's extent past its user bytes are owned (own_meta_cf's argument, YG0qcf.v:204). *)
Lemma own_slack_cf : forall ly S Hp rd k a, ARmcf B ly S Hp rd -> In k (st_chunks S) ->
ck_base B ly k + ck_rz k + req_size (ck_req k) <= a < ck_base B ly k + ck_extent k -> aowned B ly S a.
Proof.
intros ly S Hp rd k a M Hk Ha. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
assert (NB : forall k', In k' (st_chunks S) -> ck_state k' = CAllocated ->
~ (ck_base B ly k' + ck_rz k' <= a < ck_base B ly k' + ck_rz k' + req_size (ck_req k'))).
{ intros k' Hk' Hst' Hr. pose proof (user_in_extent_cf B ly S Hp rd k' a M Hk' Hr) as HE.
  destruct (sptr_eqb (ck_beg k') (ck_beg k)) eqn:Eq.
  - apply sptr_eqb_spec in Eq. destruct (In_split_beg _ _ Hk (wfc_chunks_nodup _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as (l1 & l2 & E & N1 & N2).
    assert (k' = k).
    { rewrite E in Hk'. apply in_app_iff in Hk' as [X|[<-|X]]; [exfalso; apply N1 | reflexivity | exfalso; apply N2];
      rewrite <- Eq; apply in_map_iff; exists k'; auto. }
    subst k'. lia.
  - assert (Hne : ck_beg k' <> ck_beg k) by (intros E'; apply sptr_eqb_spec in E'; congruence).
    pose proof (chunks_disjoint_cf B ly S Hp rd k' k M Hk' Hk Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia. }
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
  pose proof (region_in_prim ly (prim_class o) (amc_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _).
  eapply own_prim_nonuser_cf; [exact M | lia | exact NB].
- destruct GG as (-> & _ & Gbase & Gext & Gin & Gal & _).
  pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_F ly, kFakeStackSize) _ (static_extents ly) eq_refl
    (proj2 (amc_placed _ _ _ _ _ M)) Gin ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
  eapply own_ext_cf; [exact M | right; apply Exists_exists; exists (ly_sec ly r, sec_map_size (ck_req k));
    split; [exact Gin | unfold in_zr, kPage in *; cbn; lia] | exact NB |].
  unfold zdisjoint, kFakeFramesOff, kPage in *. cbn [fst snd] in D. lia.
Qed.

(* The shadow of a chunk's user bytes is owned. *)
Lemma own_user_shadow_cf : forall ly S Hp rd k g, ARmcf B ly S Hp rd -> In k (st_chunks S) ->
ck_base B ly k <= g < ck_base B ly k + ck_extent k -> aowned B ly S (shadow_addr g).
Proof.
intros ly S Hp rd k g M Hk Hg. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal). unfold kFreeArrayOffset in Gal.
  pose proof (region_in_prim ly (prim_class o) (amc_layout _ _ _ _ _ M) ltac:(lia)) as (R1 & R2 & _).
  apply (own_shadow_prim_cf B ly S Hp rd g M). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  apply (own_shadow_sec_cf B ly S Hp rd _ _ g M Gin). unfold kPage in *. lia.
Qed.

Lemma di_owned_cf : DZONE_OWNED ->
forall Hp inst ly S W mem md p n k a,
ARXs_cf im_segs Hp inst ly S W mem md -> rpre_dealloc_cf S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k ->
0 <= a < 2 ^ 64 -> dwrites ly (sptr_addr B ly p) (req_size n) a ->
aowned B ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n).
Proof.
intros DZ Hp inst ly S W mem md p n k a HA _ Hb Hf _ Hw.
pose proof (ARXs_cf_ARm _ _ _ _ _ _ _ _ HA) as M. pose proof (amc_wf _ _ _ _ _ M) as W0.
destruct (find_user_block_cf _ _ _ _ _ p n (WfR_of_WfP_cf _ _ _ _ _ W0) Hb) as (k0 & Hf0 & Hk0 & Hst0 & Hu0 & Hr0).
rewrite Hf in Hf0. injection Hf0 as <-.
pose proof (chunk_facts_cf B ly S Hp _ k M Hk0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (rz8_extent k ltac:(lia)) as RZ8.
rewrite <- Hu0, G4. rewrite <- Hu0, G4 in Hw. rewrite <- Hr0. rewrite <- Hr0 in Hw.
unfold dwrites in Hw. destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]].
- left. apply (own_core_cf B ly S Hp _ (ly_T ly, kThreadObjSize) a M); [unfold core_extents; cbn; tauto|].
  unfold DGgiC.WINT, t_qc, t_unwinding, t_stats, kThreadObjSize in *. cbn [fst snd]. lia.
- left. apply (own_meta_cf B ly S Hp _ k a M Hk0).
  assert (Hm : 0 <= match ck_beg k with PSec _ _ => kPage | _ => 0 end) by (destruct (ck_beg k); unfold kPage; cbn; lia). lia.
- destruct (Z_lt_le_dec a (ck_base B ly k + ck_rz k + req_size (ck_req k))) as [Hlt|Hge]; [right; lia|].
  left. apply (own_slack_cf ly S Hp _ k a M Hk0). lia.
- left. destruct (DZ ly a Hw) as [Hz|[Hz|Hz]].
  + exact (own_static_cf B ly S Hp _ a M Hz).
  + apply (own_core_cf B ly S Hp _ (ly_NB ly, kNodesBlockSize) a M); [unfold core_extents; cbn; tauto | cbn [fst snd]; lia].
  + apply (own_core_cf B ly S Hp _ (ly_SB ly, kStoreBlockSize) a M); [unfold core_extents; cbn; tauto | cbn [fst snd]; lia].
- left. unfold dshadow, DGgiC.SPv, DGgiC.CNT8v, DGgiC.N8v in Hw.
  pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
  set (pa := ck_base B ly k + ck_rz k) in *. set (nn := req_size (ck_req k)) in *.
  assert (P16 : pa mod 16 = 0) by (subst pa; apply Z.mod_divide in G3 as [q3 Hq3]; [|lia];
    apply Z.mod_divide in G6 as [q6 Hq6]; [|lia]; apply Z.mod_divide; [lia|]; exists (q3 + q6); lia).
  apply Z.mod_divide in P16 as [qp Hqp]; [|lia].
  assert (EP : pa / 8 = 2 * qp) by (rewrite Hqp; replace (qp * 16) with ((2 * qp) * 8) by lia; apply Z.div_mul; lia).
  rewrite EP in Hw. rewrite Z.div_mul in Hw by lia.
  pose proof (Z.mul_div_le (nn + 7) 8 ltac:(lia)) as T1. pose proof (Z.div_pos (nn + 7) 8 ltac:(lia) ltac:(lia)) as T2.
  set (t := (nn + 7) / 8) in *.
  replace a with (shadow_addr (8 * (a - SHADOW_OFF))).
  2: { unfold shadow_addr. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
  apply (own_user_shadow_cf ly S Hp _ k _ M Hk0). subst pa. lia.
Qed.

(* The 8 bytes after a batch object are owned: they are the next class-kBatchClass slot's header room, or no
   chunk's user bytes (own_batch_cf's argument, YG0qcf.v:238). *)
Lemma own_after_batch_cf : forall ly S Hp rd b a, ARmcf B ly S Hp rd -> In b (all_batches S) ->
ly_space ly + b_self b + kBatchBytes <= a < ly_space ly + b_self b + kBatchBytes + 8 -> aowned B ly S a.
Proof.
intros ly S Hp rd b a M Hb Ha. pose proof (amc_wf _ _ _ _ _ M) as WF. pose proof (amc_layout _ _ _ _ _ M) as LO.
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (mapped_bound_cf (as_universe B) 0 0 0 S kBatchClass WF ltac:(unfold kBatchClass; lia)) as MB.
pose proof (region_in_prim ly kBatchClass LO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2.
unfold kBatchBytes, kUserMapSize, kFreeArrayOffset in *.
assert (BX : ly_space ly + b_self b = region_base ly kBatchClass + x) by (unfold region_base; subst x; lia).
eapply own_prim_nonuser_cf; [exact M | lia |].
intros k Hk Hst Hr. pose proof (chunk_facts_cf B ly S Hp rd k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q1 & Q2 & Q3).
destruct (ck_beg k) as [|o|r o|c p] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal). unfold kFreeArrayOffset in Gal.
  destruct (Z.eq_dec (prim_class o) kBatchClass) as [Ec|Hc].
  + rewrite Ec in *. rewrite CS in *. set (xk := o - region_off kBatchClass) in *.
    apply Z.mod_divide in Gxm as [q1 Hq1]; [|lia]. apply Z.mod_divide in X2 as [q2 Hq2]; [|lia]. lia.
  + pose proof (region_in_prim ly (prim_class o) LO ltac:(lia)) as (R1' & R2' & _).
    unfold region_base in *. rewrite !region_off_eq in * by (unfold kBatchClass; lia). unfold kBatchClass in *.
    destruct (Z.lt_ge_cases (prim_class o) 24).
    * pose proof (Z.mul_le_mono_nonneg_r (prim_class o + 1) 24 (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
    * pose proof (Z.mul_le_mono_nonneg_r (24 + 1) (prim_class o) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  pose proof (pairwise_In zdisjoint _ (ly_sec ly r, sec_map_size (ck_req k)) (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl
    (proj2 (amc_placed _ _ _ _ _ M)) Gin ltac:(unfold static_extents, owned_extents; cbn; tauto)) as D.
  unfold zdisjoint, kPage in *. cbn [fst snd] in D. lia.
Qed.

Lemma di_owned_b_cf : forall Hp inst ly S W mem md lastb initr a,
ARXs_cf im_segs Hp inst ly S W mem md -> rev (qc_list (st_qthread S)) = lastb :: initr -> 0 <= a < 2 ^ 64 -> bwrites ly lastb a ->
aowned B ly S a.
Proof.
intros Hp inst ly S W mem md lastb initr a HA Hr _ Hw.
pose proof (ARXs_cf_ARm _ _ _ _ _ _ _ _ HA) as M.
assert (Hin : In lastb (all_batches S)).
{ assert (X : In lastb (rev (qc_list (st_qthread S)))) by (rewrite Hr; left; reflexivity).
  apply in_rev in X. unfold all_batches. apply in_or_app. left. exact X. }
pose proof (wq_batches _ (wfc_quarantine _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as BL.
pose proof (proj1 (Forall_forall _ _) BL lastb Hin) as [L1 L2].
apply Nat2Z.inj_le in L2. rewrite Z2Nat.id in L2 by (unfold kBatchSlots; lia).
unfold bwrites, DGgiC.SLOTv, DGgiC.Bv, DGgiC.BCv in Hw.
destruct Hw as [Hw|Hw].
- apply (own_batch_cf B ly S Hp _ lastb a M Hin). unfold kBatchBytes. lia.
- destruct (Z_lt_le_dec a (ly_space ly + b_self lastb + kBatchBytes)) as [Hlt|Hge].
  + apply (own_batch_cf B ly S Hp _ lastb a M Hin). unfold kBatchBytes in *. lia.
  + apply (own_after_batch_cf ly S Hp _ lastb a M Hin). unfold kBatchBytes, kBatchSlots in *. lia.
Qed.

Lemma di_owned_i_cf : IZONE_OWNED ->
forall Hp inst ly S W mem md a, ARXs_cf im_segs Hp inst ly S W mem md -> dg_izone a -> aowned B ly S a.
Proof.
intros IZ Hp inst ly S W mem md a HA Ha.
pose proof (ARXs_cf_ARm _ _ _ _ _ _ _ _ HA) as M.
destruct (IZ a Ha) as [Hz|Hz].
- apply (own_area_cf B ly S Hp _ (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B) a M); [unfold asyms_areas; cbn; tauto | cbn [fst snd]; lia].
- exact (own_static_cf B ly S Hp _ a M Hz).
Qed.

End INST.
