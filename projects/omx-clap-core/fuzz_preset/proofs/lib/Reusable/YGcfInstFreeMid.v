(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfInstFreeMid.v, with its module paths changed. *)
(* Theorem Labs, 2026-10 (lane F2a, a working branch): the generic cf layer's Deallocate interface, the model and
   memory sides of the call-site bridge of Put's QuarantineCache::Enqueue (YGcfInstEnq.enq_bridge_cf) at the layer's
   walk relation; the bridge itself is YGcfInstFreeMidE.enq_bridge_holds_cf (split off in field round 3, so that
   YGcfInstFreeBigRq, which reads section m, does not depend on lane F1's call-site premises).  rule 24: no function
   proved (kind:
   interface-instance discharge: the allocator relation re-established at Enqueue's call).

   The cf twin of c5's DGif1.v:1868-2155 (enq_bridge_cgif) with the released AR fact it calls (YFfl.free_mid_ARm,
   ARm at the quarantined state and the call memory dmem_m) re-proved over YG0ncf.ARmcf / ARcf, at the instance
     ARX := YGcfInstBase.ARX_cf B IOK Hp, rpre := YGcfInstFreeModel.rpreD_small_cf B, fpre := fpre_hp_cf im_segs B Hp,
     dpost := CLdepot.dpost_x im_segs B, L24 := YGcfBatch.L24MAX_cf.
   - section m, the model side: qx's fields (DGif0.qx: the tick, the depot answer z, the chunk's flip), Wf_cf of qx from
     Wf_cf S and the depot answer's aok alone (no granted path is a premise of the bridge, and no event term: the tick
     keeps WfP_cf with slack, depot_put's append keeps it at a fresh trace of the universe, the flip keeps Compl0);
   - section m, the memory side: the walk's write set Dm at Enqueue's call (dwin_m with the whole depot zone, the
     internal allocator's zone and the block's shadow), and ARmcf of qx at the call memory, as YGcfInstFreePost's
     section cs does for qfin_c (no gap patch: the depot's cells from the depot post, the constant cells from the depot
     post on the zone and from the entry memory off it);
   - the batch bound EP_cf asks for (length (all_batches X) + 1 <= L24MAX_cf) from batch_room_cf and Compl0 of class
     kBatchClass (L24_room_cf), the strict form of YGcfBatch.batches_bound_cf.
   The image premises are YGcfInstFreePost's (FP_IZONE_ROM, FP_DSTAT, FP_DZONE_FP, FP_CONST), YGcfDIface's
   (IZONE_OWNED, DZONE_OWNED) and YGcfInstFreeView's FV_IAL; this file adds none.  Generic over CfImg / CfParams /
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot CLenq YFfl YGcfDIface YGcfInstEnq.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac mceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.
Ltac msp := repeat match goal with |- _ /\ _ => split end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.
Variable B : asyms.

(* ================================================================================================================ *)
(* 0. The batch bound with room for one more batch (EP_cf's last conjunct; YGcfBatch.batches_bound_cf strict).      *)
Lemma L24_room_cf : forall U s, Wf_cf U s -> batch_room_cf s -> Z.of_nat (length (all_batches s)) + 1 <= L24MAX_cf.
Proof.
intros U s W HR. unfold batch_room_cf in HR.
assert (Hc : 1 <= kBatchClass <= 31) by (unfold kBatchClass; lia).
pose proof (wfc_compl0 _ _ _ _ _ W kBatchClass Hc) as HC. unfold cdef in HC.
pose proof (wrc_alloc _ _ _ _ _ _ (wfc_classes _ _ _ _ _ W kBatchClass Hc)) as [A1 A2].
assert (Hl : (length (all_batches s) <= length (class_elems s kBatchClass))%nat).
{ unfold class_elems, batch_offs. rewrite Z.eqb_refl. rewrite !length_app, length_map. lia. }
apply Nat2Z.inj_le in Hl.
assert (CS : class_size kBatchClass = 8192) by reflexivity.
rewrite CS in HC. unfold L24MAX_cf. rewrite CS. apply Z.div_le_lower_bound; [lia|].
unfold kUserMapSize, kFreeArrayOffset in *. lia.
Qed.

(* ================================================================================================================ *)
(* 1. Put's Enqueue call state qx S k z tr: the model side, then the memory side.                                   *)
Section m.
Variables (ly : alayout) (S : astate) (Hp : list Z) (rd : reader).
Hypothesis M : ARmcf B ly S Hp rd.
Variable k : chunk.
Hypothesis Hk : In k (st_chunks S).
Hypothesis Hst : ck_state k = CAllocated.
Variables (z : Z) (tr : list Z).
Local Notation S' := (qx S k z tr).
Ltac zc := unfold qx, YFl0C.depot_after, dtick; destruct (z =? 0); reflexivity.

Lemma ms_regions : st_regions S' = st_regions S.   Proof. zc. Qed.
Lemma ms_cache : st_cache S' = st_cache S.         Proof. zc. Qed.
Lemma ms_cinit : st_cache_inited S' = st_cache_inited S. Proof. zc. Qed.
Lemma ms_secs : st_secs S' = st_secs S.             Proof. zc. Qed.
Lemma ms_sec_arr : st_sec_arr S' = st_sec_arr S.    Proof. zc. Qed.
Lemma ms_sec_res : st_sec_reserved S' = st_sec_reserved S. Proof. zc. Qed.
Lemma ms_fs : st_fs S' = st_fs S.                   Proof. zc. Qed.
Lemma ms_qthread : st_qthread S' = st_qthread S.    Proof. zc. Qed.
Lemma ms_qglobal : st_qglobal S' = st_qglobal S.    Proof. zc. Qed.
Lemma ms_depot : st_depot S' = st_depot (YFl0C.depot_after z tr (dtick S)). Proof. reflexivity. Qed.
Lemma ms_quar_cells : quar_cells S' = quar_cells S. Proof. zc. Qed.
Lemma ms_chunks : st_chunks S' = upd_chunk (st_chunks S) (qk k).
Proof. unfold qx. cbn [st_chunks set_chunks]. f_equal. zc. Qed.
Lemma ms_inited : st_internal_inited S = true -> st_internal_inited S' = true.
Proof. intros HII. unfold qx, YFl0C.depot_after, dtick; destruct (z =? 0); cbn [st_internal_inited set_chunks set_depot set_nev]; exact HII. Qed.
Lemma ms_reg : forall c, reg S' c = reg S c.        Proof. intros c. unfold reg. rewrite ms_regions. reflexivity. Qed.
Lemma ms_cacheq : forall c, cache S' c = cache S c. Proof. intros c. unfold cache. rewrite ms_cache. reflexivity. Qed.
Lemma ms_frames : frames S' = frames S.             Proof. unfold frames. rewrite ms_fs. reflexivity. Qed.
Lemma ms_batches : all_batches S' = all_batches S.  Proof. unfold all_batches. rewrite ms_qthread, ms_qglobal. reflexivity. Qed.
Lemma ms_qitems : q_items S' = q_items S.           Proof. unfold q_items. rewrite ms_batches. reflexivity. Qed.
Lemma ms_queued : queued_n S' = queued_n S.         Proof. unfold queued_n. rewrite ms_qitems. reflexivity. Qed.

Lemma ms_split : exists l1 l2, st_chunks S = l1 ++ k :: l2 /\ st_chunks S' = l1 ++ qk k :: l2 /\
  ~ In (ck_beg k) (map ck_beg l1) /\ ~ In (ck_beg k) (map ck_beg l2).
Proof.
destruct (In_split_beg _ _ Hk (wfc_chunks_nodup _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as (l1 & l2 & E & N1 & N2).
exists l1, l2. split; [exact E|]. split; [|split; assumption].
rewrite ms_chunks, E. apply upd_chunk_present; [reflexivity | exact N1].
Qed.
Lemma ms_sec_extents : sec_extents ly S' = sec_extents ly S.
Proof.
destruct ms_split as (l1 & l2 & E & E' & _). unfold sec_extents. rewrite E', E.
apply (YFfl.flat_map_mid _ l1 (qk k) k l2). reflexivity.
Qed.
Lemma ms_fa_poison : fa_poison_ranges ly S' = fa_poison_ranges ly S.
Proof.
destruct ms_split as (l1 & l2 & E & E' & _). unfold fa_poison_ranges, reg. rewrite ms_regions, E', E.
rewrite (YFfl.flat_map_mid _ l1 (qk k) k l2) by reflexivity. reflexivity.
Qed.
Lemma ms_budget : abudget_cf S' = abudget_cf S.
Proof.
destruct ms_split as (l1 & l2 & E & E' & _).
(* the hull term (field round 3: CfParams' cf_hull) moves only with st_secs and the live hulls: cf_hull_frame *)
assert (LH : sec_live_hulls S' = sec_live_hulls S).
{ unfold sec_live_hulls. rewrite E', E. rewrite !(fold_chunk_mid _ l1 (qk k) k l2) by reflexivity. reflexivity. }
unfold abudget_cf. rewrite (cf_hull_frame S S' ms_secs LH).
unfold prim_committed, sec_live_bytes, sec_live_hulls, errb_cap_cf, errb_e.
rewrite ms_regions, ms_sec_res, ms_secs, E', E.
rewrite !(fold_chunk_mid _ l1 (qk k) k l2) by reflexivity.
reflexivity.
Qed.
Lemma ms_ledger : forall md, ALedger_cf im_segs ly S md -> ALedger_cf im_segs ly S' md.
Proof.
intros md L. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15 L16 L17]. constructor; try assumption.
- destruct L4 as (pieces & P1 & P2). exists pieces. split; [|exact P2].
  unfold prim_pieces_ok, cut_ok, prim_hole_at, reg in P1 |- *. rewrite ms_regions. exact P1.
- rewrite ms_sec_extents. exact L7.
- unfold errb_zone. rewrite ms_sec_extents.
  replace (xs_cf ly S') with (xs_cf ly S) by (unfold xs_cf, errb_cap_cf, errb_e; rewrite ms_secs; reflexivity). exact L8.
- unfold eager_cf, prim_committed, errb_zone. rewrite ms_regions, ms_sec_res, ms_sec_extents.
  replace (xs_cf ly S') with (xs_cf ly S) by (unfold xs_cf, errb_cap_cf, errb_e; rewrite ms_secs; reflexivity). exact L9.
- rewrite ms_sec_extents. exact L12.
- replace (xs_cf ly S') with (xs_cf ly S) by (unfold xs_cf, errb_cap_cf, errb_e; rewrite ms_secs; reflexivity). exact L17.
Qed.
(* the quarantined chunk is no longer a client byte *)
Lemma ms_client : forall a, aclient_byte B ly S' a -> aclient_byte B ly S a.
Proof.
intros a [(x & Hx & Hsx & Hr)|(fp & Hcp & Hr)].
- left. destruct ms_split as (l1 & l2 & E & E' & N1 & N2). rewrite E' in Hx.
  assert (Hne : x <> qk k) by (intros ->; cbn [ck_state qk] in Hsx; discriminate Hsx).
  exists x. split; [rewrite E; apply in_app_iff; apply in_app_iff in Hx as [Hx|[Hx|Hx]];
    [left; exact Hx | exfalso; exact (Hne (eq_sym Hx)) | right; right; exact Hx]|]. split; [exact Hsx | exact Hr].
- right. exists fp. rewrite ms_frames in Hcp. split; [exact Hcp | exact Hr].
Qed.
(* the flip moves the chunk's bytes from the live set to the quarantined set; the queues do not change *)
Lemma ms_quar : quar_n S' = quar_n S + ck_n k.
Proof.
destruct ms_split as (l1 & l2 & E & E' & _). unfold quar_n. rewrite E', E, !quar_nl_split_cf.
replace (is_alloc k) with true by (unfold is_alloc; rewrite Hst; reflexivity).
replace (is_alloc (qk k)) with false by reflexivity. change (ck_n (qk k)) with (ck_n k). lia.
Qed.
(* the chunk is in no batch (Wf_cf's queued items are quarantined chunks; k is allocated) *)
Lemma ms_fresh : ~ In (ck_beg (qk k)) (map ck_beg (q_items S')).
Proof.
destruct (In_split_beg _ _ Hk (wfc_chunks_nodup _ _ _ _ _ (amc_wf _ _ _ _ _ M))) as (l1 & l2 & E & N1 & N2).
rewrite ms_qitems. unfold qk. cbn [ck_beg]. intros Hin.
apply in_map_iff in Hin as (k'' & Hb'' & Hk'').
pose proof (proj1 (Forall_forall _ _) (wq_items _ (wfc_quarantine _ _ _ _ _ (amc_wf _ _ _ _ _ M))) k'' Hk'') as [H1 H2].
rewrite E in H1. apply in_app_iff in H1 as [H1|[<-|H1]]; [apply N1 | congruence | apply N2]; rewrite <- Hb''; apply in_map; exact H1.
Qed.
(* Wf_cf of the call state, from Wf_cf S and the depot's answer (YFfl.WS' without its event premise: the tick keeps
   WfP_cf with slack 1, the append keeps the depot fitting the universe (YG01.depot_put_fits, from the call's
   admission), the flip keeps Compl0) *)
Lemma ms_wf : aok S (KDepot tr) z -> admits (as_universe B) tr S -> Wf_cf (as_universe B) S'.
Proof.
intros HZ Htr. pose proof (amc_wf _ _ _ _ _ M) as W.
pose proof (WfP_cf_tick_y3 _ S W) as W1.
assert (W2 : WfP_cf (as_universe B) 1 1 1 (YFl0C.depot_after z tr (dtick S))).
{ unfold YFl0C.depot_after. destruct (Z.eqb_spec z 0) as [_|Hz]; [exact W1|].
  cbn [aok] in HZ. destruct HZ as [HZ|[_ HM]]; [lia|].
  apply (WfP_cf_set_depot_y3 _ 1 1 1 (dtick S)); [exact W1|].
  change (st_depot (dtick S)) with (st_depot S).
  exact (depot_put_fits _ S tr (wfc_depot _ _ _ _ _ W) Htr HM). }
destruct (In_split_beg _ _ Hk (wfc_chunks_nodup _ _ _ _ _ W)) as (l1 & l2 & E & N1 & N2).
assert (ED : st_chunks (YFl0C.depot_after z tr (dtick S)) = st_chunks S)
  by (unfold YFl0C.depot_after, dtick; destruct (z =? 0); reflexivity).
assert (EX : S' = set_chunks (l1 ++ quar_of_cf k :: l2) (YFl0C.depot_after z tr (dtick S))).
{ unfold qx. rewrite ED, E. rewrite upd_chunk_present by (reflexivity || exact N1). reflexivity. }
pose proof (WfR_flip_cf _ 1 1 1 (YFl0C.depot_after z tr (dtick S)) l1 k l2 (WfR_of_WfP_cf _ _ _ _ _ W2)
  ltac:(rewrite ED; exact E) Hst) as W4.
rewrite EX. unfold Wf_cf. apply (WfP_cf_weaken _ 1 1 1 0 0 0); [|lia|lia|lia].
apply WfP_of_WfR_cf; [exact W4|]. intros c Hc.
rewrite <- (wfc_compl0 _ _ _ _ _ W c Hc). apply cdef_ext.
- unfold YFl0C.depot_after, dtick. destruct (z =? 0); reflexivity.
- unfold class_elems.
  rewrite (chunk_offs_begs_cf S (set_chunks (l1 ++ quar_of_cf k :: l2) (YFl0C.depot_after z tr (dtick S))) c)
    by (cbn [st_chunks set_chunks]; rewrite E, !map_app; reflexivity).
  unfold YFl0C.depot_after, dtick. destruct (z =? 0); reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The memory side: the walk's write set at Enqueue's call and the relation at the call memory (YFfl.free_mid_ARm).  *)
Variable rd' : reader.
Hypothesis HIZ : FP_IZONE B.
Hypothesis HDS : FP_DSTAT B.
Hypothesis HDZ : FP_DZONE B ly.
Variable hb1 : Z.
Hypothesis Hhb1 : 0 <= hb1 < 256 /\ Z.land hb1 127 = 17.
Hypothesis WFX : Wf_cf (as_universe B) S'.
Variable sp : Z.
Hypothesis Hsp : ly_stk_lo ly + DGbaseC.DFSTACK <= sp <= ly_stk_hi ly.
Local Notation T := (ly_T ly).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).

Definition DKm (a : Z) : Prop := (u - 16 <= a < u - 8) \/ (u <= a < u + 8).
Definition DSm (a : Z) : Prop := sp - DGbaseC.DFSTACK <= a < sp.
Definition DHm (a : Z) : Prop := shadow_addr u <= a < shadow_addr u + (nn + 7) / 8.
Definition Dm (a : Z) : Prop := DGgmC.WINT ly a \/ DKm a \/ DSm a \/ dg_izone a \/ dg_dzone ly a \/ DHm a.

Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ Dm a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_hdr : forall i, (i < 4)%nat -> rd' (u - 16 + Z.of_nat i) = Some (YG0f.le_byte (3 + 256 * hb1) 4 i).
Hypothesis NEW_n : forall i, (i < 4)%nat -> rd' (u - 12 + Z.of_nat i) = Some (YG0f.le_byte nn 4 i).
Hypothesis NEW_unw : rd' (T + t_unwinding) = Some 0.
Hypothesis NEW_sh : forall a, DHm a -> rd a <> None -> rd' a = Some shHeapFreed.
Hypothesis IAL : Forall (cell_holds B ly rd') (ialloc_cells B S') /\ Forall (range_zero B ly rd') (ialloc_zero B).
Hypothesis DEP : CLdepot.depot_mem_ok B ly (YFl0C.depot_after z tr (dtick S)) rd'.
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
(* the freed block's base is not a hidden head (the free site's premise fpre_hp_cf) *)
Hypothesis HPu : ~ In u Hp.
(* the relation's machine cells at the call memory (ARmcf's amc_exh_cell / amc_errb_cells, field round 2) *)
Hypothesis EXHm : exh_cell_cf B ly S' rd'.
Hypothesis ERRm : errb_cells_cf B ly S' rd'.

Lemma mWF : Wf_cf (as_universe B) S. Proof. exact (amc_wf _ _ _ _ _ M). Qed.
Lemma mLO : layout_ok ly. Proof. exact (amc_layout _ _ _ _ _ M). Qed.
Lemma mKF : cfacts_cf B ly S k. Proof. exact (chunk_facts_cf B ly S Hp rd k M Hk). Qed.
Lemma mHu : u = ck_base B ly k + ck_rz k. Proof. pose proof mKF as (_ & _ & _ & G4 & _). exact G4. Qed.
Lemma mER : ck_rz k + (nn + 7) / 8 * 8 <= ck_extent k /\ 1 <= nn /\ 0 <= (nn + 7) / 8 /\ nn <= (nn + 7) / 8 * 8 < nn + 8.
Proof. exact (ext_rounded_cf B ly S Hp rd M k Hk). Qed.
Lemma mU8 : u mod 8 = 0 /\ ck_base B ly k mod 8 = 0 /\ ck_rz k mod 8 = 0.
Proof. exact (u_al8_cf B ly S Hp rd M k Hk). Qed.
Lemma mQ8 : 8 <= (nn + 7) / 8 * 8.
Proof. pose proof mER as (_ & NN1 & _). pose proof (Z.div_le_mono 8 (nn + 7) 8 ltac:(lia) ltac:(lia)) as D. change (8 / 8) with 1 in D. lia. Qed.

(* the block's shadow lies in the shadow region *)
Lemma mDH_sh : forall a, DHm a -> kLowShadowBeg <= a < kHighMemBeg.
Proof.
intros a Ha. pose proof mKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof mER as (ER & NN1 & NN2 & NN3). pose proof mU8 as (U8 & B8 & R8). pose proof mHu as EU.
assert (LO4 : 4096 <= ck_base B ly k) by (clear - G1; unfold in_app in G1; lia).
apply Z.mod_divide in U8 as [c Hc]; [|lia].
assert (H1 : kLowShadowBeg <= shadow_addr u < kHighMemBeg).
{ apply g_hs_bounds; mceil; unfold ASAN_CEIL, kHighMemEnd in *; lia. }
assert (H2 : kLowShadowBeg <= shadow_addr (u + 8 * ((nn + 7) / 8 - 1)) < kHighMemBeg).
{ apply g_hs_bounds; mceil; unfold ASAN_CEIL, kHighMemEnd in *; lia. }
assert (E2 : shadow_addr (u + 8 * ((nn + 7) / 8 - 1)) = shadow_addr u + ((nn + 7) / 8 - 1)).
{ unfold shadow_addr. rewrite Hc. replace (c * 8 + 8 * ((nn + 7) / 8 - 1)) with ((c + ((nn + 7) / 8 - 1)) * 8) by lia.
  rewrite !Z_div_mult by lia. lia. }
unfold DHm in Ha. rewrite E2 in H2. lia.
Qed.

Definition okm (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ Dm a.
Definition okrm (lo len : Z) : Prop := forall a, lo <= a < lo + len -> okm a.
Lemma AGm : forall a, okm a -> rd' a = rd a. Proof. intros a [H1 H2]. exact (AG a H1 H2). Qed.

(* An application byte off every window the walk writes. *)
Lemma okm_app : forall a, app_addr a -> ~ (ly_stk_lo ly <= a < ly_stk_hi ly) -> ~ in_zr a (ly_img ly) ->
  ~ (T <= a < T + kThreadObjSize) -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
  ~ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) -> ~ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> okm a.
Proof.
intros a AA NST NIM NT NK NNB NSB. pose proof mER as (ER & NN1 & NN2 & NN3). pose proof mHu as EU.
pose proof mKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof mQ8 as Q8.
pose proof (app_addr_below_ceil a AA) as BC.
split; [mceil; unfold ASAN_CEIL in *; lia|]. intros [X|[X|[X|[X|[X|X]]]]].
- apply NT. unfold DGgmC.WINT, t_unwinding, t_stats, kThreadObjSize in *. lia.
- apply NK. unfold DKm in X. lia.
- apply NST. unfold DSm, DGbaseC.DFSTACK in *. lia.
- apply NIM. destruct (HIZ a X) as (X1 & _). exact (g_static_img B ly S Hp rd M a X1).
- destruct (proj2 (HDZ a) X) as (_ & [FP|OS]).
  + unfold CLdepot.depot_footprint in FP. destruct FP as [FP|[FP|[FP|FP]]].
    * apply NIM. exact (g_static_img B ly S Hp rd M a (HDS a (or_introl FP))).
    * exact (NNB FP).
    * exact (NSB FP).
    * apply NIM. exact (g_static_img B ly S Hp rd M a (HDS a (or_intror FP))).
  + apply NIM. exact (g_static_img B ly S Hp rd M a OS).
- pose proof (mDH_sh a X) as [S1 S2]. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* A shadow byte off the block's shadow. *)
Lemma okm_sh : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ DHm a -> okm a.
Proof.
intros a Ha ND. pose proof mKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof mER as (ER & NN1 & NN2 & NN3). pose proof mHu as EU. pose proof mQ8 as Q8.
pose proof (g_shx B ly S Hp rd M a Ha) as (NS & NIM & NT).
assert (NBP : forall a0, ly_NB ly <= a0 < ly_NB ly + kNodesBlockSize -> app_addr a0)
  by (intros a0 H0; apply (g_app_oext B ly S Hp rd M (ly_NB ly, kNodesBlockSize) a0 ltac:(unfold owned_extents; cbn; tauto));
      unfold in_zr; cbn [fst snd]; exact H0).
assert (SBP : forall a0, ly_SB ly <= a0 < ly_SB ly + kStoreBlockSize -> app_addr a0)
  by (intros a0 H0; apply (g_app_oext B ly S Hp rd M (ly_SB ly, kStoreBlockSize) a0 ltac:(unfold owned_extents; cbn; tauto));
      unfold in_zr; cbn [fst snd]; exact H0).
split; [mceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia|]. intros [X|[X|[X|[X|[X|X]]]]].
- apply NT. unfold DGgmC.WINT, t_unwinding, t_stats, kThreadObjSize in *. lia.
- unfold DKm in X. unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia.
- apply NS. unfold DSm, DGbaseC.DFSTACK in *. lia.
- apply NIM. destruct (HIZ a X) as (X1 & _). exact (g_static_img B ly S Hp rd M a X1).
- destruct (proj2 (HDZ a) X) as (_ & [FP|OS]).
  + unfold CLdepot.depot_footprint in FP. destruct FP as [FP|[FP|[FP|FP]]].
    * apply NIM. exact (g_static_img B ly S Hp rd M a (HDS a (or_introl FP))).
    * pose proof (NBP a FP) as HA0. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
    * pose proof (SBP a FP) as HA0. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
    * apply NIM. exact (g_static_img B ly S Hp rd M a (HDS a (or_intror FP))).
  + apply NIM. exact (g_static_img B ly S Hp rd M a OS).
- exact (ND X).
Qed.

(* The regions the relation reads, each off the walk's windows. *)
Lemma okm_koff : (exists c, 1 <= c <= 30 /\ region_base ly c <= ck_base B ly k /\
    ck_base B ly k + ck_extent k <= region_base ly c + kFreeArrayOffset /\
    ly_prim ly <= region_base ly c /\ region_base ly c + 2 ^ 32 <= ly_prim ly + kPrimResvSize) \/
  (exists e, In e (sec_extents ly S) /\ fst e <= ck_base B ly k /\ ck_base B ly k + ck_extent k <= fst e + snd e).
Proof.
pose proof mKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c0 p0] eqn:Eb; try solve [destruct GG].
- left. cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal & Gm).
  pose proof (region_in_prim ly (prim_class o) mLO ltac:(lia)) as (R1 & R2 & _).
  exists (prim_class o). msp; lia.
- right. destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  exists (ly_sec ly r, sec_map_size (ck_req k)). cbn [fst snd]. msp; [exact Gin | unfold kPage in *; lia | unfold kPage in *; lia].
Qed.
Lemma okm_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize ->
  ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) -> okm a.
Proof.
intros a Ha NK. pose proof (g_app_oext B ly S Hp rd M (ly_prim ly, kPrimResvSize) a ltac:(unfold owned_extents; cbn; tauto)
  ltac:(unfold in_zr; cbn [fst snd]; lia)) as AA.
destruct (owned_extents_bound ly a mLO ltac:(apply Exists_exists; exists (ly_prim ly, kPrimResvSize);
  split; [unfold owned_extents; cbn; tauto | unfold in_zr; cbn; lia])) as (_ & NST & NIM).
pose proof (SX_cf B ly S Hp rd M 0 2 _ _ eq_refl eq_refl ltac:(lia)) as D2.
pose proof (SX_cf B ly S Hp rd M 0 4 _ _ eq_refl eq_refl ltac:(lia)) as D4.
pose proof (SX_cf B ly S Hp rd M 0 5 _ _ eq_refl eq_refl ltac:(lia)) as D5.
unfold zdisjoint in D2, D4, D5. cbn [fst snd] in D2, D4, D5.
apply (okm_app a AA NST NIM); [| exact NK | |]; unfold kThreadObjSize, kNodesBlockSize, kStoreBlockSize in *; lia.
Qed.
Lemma okm_oext : forall i x sz, nth_error (owned_extents ly) i = Some (x, sz) -> (i <> 0)%nat -> (i <> 2)%nat ->
  (i <> 4)%nat -> (i <> 5)%nat -> okrm x sz.
Proof.
intros i x sz He Hi0 Hi2 Hi4 Hi5 a Ha.
pose proof (g_app_oext B ly S Hp rd M (x, sz) a (nth_error_In _ _ He) ltac:(unfold in_zr; cbn [fst snd]; lia)) as AA.
destruct (g_oext B ly S Hp rd M i x sz a He Hi2 Ha) as (A1 & A2 & A3 & A4).
assert (Hi8 : (i < 8)%nat).
{ assert (HL : (i < length (owned_extents ly))%nat) by (apply nth_error_Some; rewrite He; discriminate).
  unfold owned_extents in HL. cbn [length] in HL. lia. }
assert (HS : nth_error (static_extents ly) i = Some (x, sz)) by (unfold static_extents; rewrite nth_error_app1 by (cbn; lia); exact He).
pose proof (SX_cf B ly S Hp rd M i 4 _ _ HS eq_refl Hi4) as D4.
pose proof (SX_cf B ly S Hp rd M i 5 _ _ HS eq_refl Hi5) as D5.
pose proof (anyX_cf B ly S Hp rd M k i _ Hk HS ltac:(lia)) as DK.
unfold zdisjoint in D4, D5, DK. cbn [fst snd] in D4, D5, DK.
apply (okm_app a AA A2 A3 A4); unfold kNodesBlockSize, kStoreBlockSize in *; lia.
Qed.
Lemma okm_Q : okrm (ly_Q ly) kPtrArrayResv. Proof. exact (okm_oext 1 _ _ eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). Qed.
Lemma okm_F : okrm (ly_F ly) kFakeStackSize. Proof. exact (okm_oext 3 _ _ eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). Qed.
Lemma okm_T : forall a, T <= a < T + kThreadObjSize -> ~ DGgmC.WINT ly a -> okm a.
Proof.
intros a Ha NW. pose proof mHu as EU. pose proof mER as (ER & NN1 & NN2 & NN3).
pose proof mKF as (G1 & G2 & G3 & G4 & G5 & _). pose proof mQ8 as Q8.
pose proof (g_app_oext B ly S Hp rd M (ly_T ly, kThreadObjSize) a ltac:(unfold owned_extents; cbn; tauto)
  ltac:(unfold in_zr; cbn [fst snd]; lia)) as AA.
destruct (g_T B ly S Hp rd M a Ha) as (A1 & A2 & A3).
pose proof (SX_cf B ly S Hp rd M 2 4 _ _ eq_refl eq_refl ltac:(lia)) as D4.
pose proof (SX_cf B ly S Hp rd M 2 5 _ _ eq_refl eq_refl ltac:(lia)) as D5.
pose proof (anyX_cf B ly S Hp rd M k 2 _ Hk eq_refl ltac:(lia)) as DK.
unfold zdisjoint in D4, D5, DK. cbn [fst snd] in D4, D5, DK.
split; [mceil; unfold ASAN_CEIL in *; lia|]. intros [X|[X|[X|[X|[X|X]]]]].
- exact (NW X).
- unfold DKm in X. unfold kThreadObjSize in *. lia.
- apply A2. unfold DSm, DGbaseC.DFSTACK in *. lia.
- apply A3. destruct (HIZ a X) as (X1 & _). exact (g_static_img B ly S Hp rd M a X1).
- destruct (proj2 (HDZ a) X) as (_ & [FP|OS]).
  + unfold CLdepot.depot_footprint in FP. destruct FP as [FP|[FP|[FP|FP]]].
    * apply A3. exact (g_static_img B ly S Hp rd M a (HDS a (or_introl FP))).
    * unfold kNodesBlockSize, kThreadObjSize in *. lia.
    * unfold kStoreBlockSize, kThreadObjSize in *. lia.
    * apply A3. exact (g_static_img B ly S Hp rd M a (HDS a (or_intror FP))).
  + apply A3. exact (g_static_img B ly S Hp rd M a OS).
- pose proof (mDH_sh a X) as [SH1 SH2]. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma okm_k : forall a, ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ DKm a -> okm a.
Proof.
intros a Ha ND. pose proof mKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof mER as (ER & NN1 & NN2 & NN3). pose proof mHu as EU.
assert (AA : app_addr a) by (exact (in_app_addr _ _ a G1 Ha)).
destruct (chunk_apart_cf B ly S Hp rd k a M Hk Ha) as (NIM & NST).
pose proof (anyX_cf B ly S Hp rd M k 2 _ Hk eq_refl ltac:(lia)) as D2.
pose proof (anyX_cf B ly S Hp rd M k 4 _ Hk eq_refl ltac:(lia)) as D4.
pose proof (anyX_cf B ly S Hp rd M k 5 _ Hk eq_refl ltac:(lia)) as D5.
unfold zdisjoint in D2, D4, D5. cbn [fst snd] in D2, D4, D5.
split; [pose proof (app_addr_below_ceil a AA); mceil; unfold ASAN_CEIL in *; lia|].
intros [X|[X|[X|[X|[X|X]]]]].
- unfold DGgmC.WINT, t_unwinding, t_stats, kThreadObjSize in *. lia.
- exact (ND X).
- apply NST. unfold DSm, DGbaseC.DFSTACK in *. lia.
- apply NIM. destruct (HIZ a X) as (X1 & _). exact (g_static_img B ly S Hp rd M a X1).
- destruct (proj2 (HDZ a) X) as (_ & [FP|OS]).
  + unfold CLdepot.depot_footprint in FP. destruct FP as [FP|[FP|[FP|FP]]].
    * apply NIM. exact (g_static_img B ly S Hp rd M a (HDS a (or_introl FP))).
    * unfold kNodesBlockSize in *. lia.
    * unfold kStoreBlockSize in *. lia.
    * apply NIM. exact (g_static_img B ly S Hp rd M a (HDS a (or_intror FP))).
  + apply NIM. exact (g_static_img B ly S Hp rd M a OS).
- pose proof (mDH_sh a X) as [SH1 SH2]. unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma okm_other : forall x a, In x (st_chunks S) -> ck_beg x <> ck_beg k ->
  ck_base B ly x <= a < ck_base B ly x + ck_extent x -> okm a.
Proof.
intros x a Hx Hne Ha. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
assert (AA : app_addr a) by (exact (in_app_addr _ _ a G1 Ha)).
destruct (chunk_apart_cf B ly S Hp rd x a M Hx Ha) as (NIM & NST).
pose proof (anyX_cf B ly S Hp rd M x 2 _ Hx eq_refl ltac:(lia)) as D2.
pose proof (anyX_cf B ly S Hp rd M x 4 _ Hx eq_refl ltac:(lia)) as D4.
pose proof (anyX_cf B ly S Hp rd M x 5 _ Hx eq_refl ltac:(lia)) as D5.
pose proof (chunks_disjoint_cf B ly S Hp rd x k M Hx Hk Hne) as DK.
unfold zdisjoint in D2, D4, D5, DK. cbn [fst snd] in D2, D4, D5, DK.
apply (okm_app a AA NST NIM); unfold kThreadObjSize, kNodesBlockSize, kStoreBlockSize in *; lia.
Qed.
Lemma okm_batch : forall b2 a, In b2 (all_batches S) ->
  ly_space ly + b_self b2 <= a < ly_space ly + b_self b2 + kBatchBytes -> okm a.
Proof.
intros b2 a Hb2 Ha. apply (okm_prim a (g_batch B ly S Hp rd M b2 a Hb2 Ha)).
pose proof (batch_vs_chunk_cf B ly S Hp rd M b2 k Hb2 Hk) as DB.
unfold zdisjoint in DB. cbn [fst snd] in DB. unfold kBatchBytes in *. lia.
Qed.
(* a secondary's page header is apart from the freed chunk (YFex.secmap_vs_chunk at the cf facts) *)
Lemma m_secmap_vs_k : forall x r o, In x (st_chunks S) -> ck_beg x = PSec r o -> ck_beg x <> ck_beg k ->
  zdisjoint (ly_sec ly r, sec_map_size (ck_req x)) (ck_base B ly k, ck_extent k).
Proof.
intros x r o Hx Ebx Hne.
pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
rewrite Ebx in GG. destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof mKF as (_ & _ & _ & _ & _ & _ & _ & _ & GK).
destruct (ck_beg k) as [|o'|r' o'|c' p'] eqn:Ebk; try solve [destruct GK].
- apply zdisjoint_sym.
  exact (prim_vs_secmap_cf B ly S Hp rd k o' (ly_sec ly r, sec_map_size (ck_req x)) M Hk Ebk Gin).
- destruct GK as (-> & _ & Kbase & Kext & Kin & _).
  pose proof (secmaps_disjoint_cf B ly S Hp rd x k r kPage r' kPage M Hx Hk Ebx Ebk ltac:(rewrite Ebk; exact Hne)) as DJ.
  unfold zdisjoint, kPage in *. cbn [fst snd] in DJ |- *. lia.
Qed.
Lemma okm_secpage : forall x r o a, In x (st_chunks S) -> ck_beg x = PSec r o ->
  ly_sec ly r <= a < ly_sec ly r + kPage -> okm a.
Proof.
intros x r o a Hx Ebx Ha. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (_ & _ & _ & _ & _ & _ & _ & _ & GG).
rewrite Ebx in GG. destruct GG as (-> & _ & Gbase & Gext & Gin & _).
pose proof (proj1 (Forall_forall _ _) (sec_extents_len_cf B ly S Hp rd M) _ Gin) as L. cbn [snd] in L.
destruct (g_sec B ly S Hp rd M (ly_sec ly r, sec_map_size (ck_req x)) a Gin ltac:(unfold in_zr, kPage in *; cbn [fst snd]; lia))
  as (A1 & NST & NIM & NT).
destruct (owned_sec_bound_cf B ly S Hp rd a M ltac:(apply Exists_exists; exists (ly_sec ly r, sec_map_size (ck_req x));
  split; [exact Gin | unfold in_zr, kPage in *; cbn [fst snd]; lia])) as (AA & _ & _).
pose proof (SECX_cf B ly S Hp rd M _ 0 _ Gin eq_refl) as D0.
pose proof (SECX_cf B ly S Hp rd M _ 4 _ Gin eq_refl) as D4.
pose proof (SECX_cf B ly S Hp rd M _ 5 _ Gin eq_refl) as D5.
assert (DK : ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k)).
{ intros HK. destruct okm_koff as [(c & Hc & X1 & X2 & X3 & X4)|(e & He & E1 & E2)].
  - unfold zdisjoint in D0. cbn [fst snd] in D0. unfold kPage, kFreeArrayOffset in *. lia.
  - destruct (sptr_eqb (ck_beg k) (PSec r kPage)) eqn:Eq.
    + apply sptr_eqb_spec in Eq. pose proof mKF as (_ & _ & _ & _ & _ & _ & _ & _ & GK). rewrite Eq in GK.
      destruct GK as (_ & _ & Kbase & _). unfold kPage in *. lia.
    + assert (Hne : ck_beg x <> ck_beg k) by (rewrite Ebx; intros E'; rewrite <- E', sptr_eqb_refl in Eq; discriminate).
      pose proof (m_secmap_vs_k x r kPage Hx Ebx Hne) as DD. unfold zdisjoint in DD. cbn [fst snd] in DD.
      unfold kPage in *. lia. }
unfold zdisjoint in D0, D4, D5. cbn [fst snd] in D0, D4, D5.
apply (okm_app a AA NST NIM NT DK); unfold kPage, kNodesBlockSize, kStoreBlockSize in *; lia.
Qed.
Lemma okm_rinfo : okrm (ly_rinfo ly) 4096.
Proof.
intros a Ha. pose proof (lo_space_in _ mLO) as [SP1 SP2].
apply (okm_prim a); [unfold ly_rinfo, kRegionInfoOff, kSpaceSize in *; lia|].
destruct okm_koff as [(c & Hc & X1 & X2 & X3 & X4)|(e & He & E1 & E2)].
- assert (RC : region_base ly c = ly_space ly + c * 2 ^ 32)
    by (unfold region_base; rewrite region_off_eq by lia; reflexivity).
  unfold ly_rinfo, kRegionInfoOff, kFreeArrayOffset in *. rewrite RC in X2.
  assert (c * 2 ^ 32 <= 30 * 2 ^ 32) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
- pose proof (pairwise_In zdisjoint _ e (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl
    (proj2 (amc_placed _ _ _ _ _ M)) He ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
  unfold zdisjoint in DJ. cbn [fst snd] in DJ. unfold ly_rinfo, kRegionInfoOff, kSpaceSize in *. lia.
Qed.
Lemma okm_fa : forall c, 1 <= c <= 31 -> okrm (fa_base ly c) kFreeArrayMax.
Proof.
intros c Hc a Ha. pose proof (region_in_prim ly c mLO Hc) as (R1 & R2 & R3 & R4 & R5).
assert (RC : region_base ly c = ly_space ly + c * 2 ^ 32)
  by (unfold region_base; rewrite region_off_eq by lia; reflexivity).
assert (EF : fa_base ly c = region_base ly c + kFreeArrayOffset) by (unfold fa_base, region_base; lia).
apply (okm_prim a); [unfold kFreeArrayOffset, kFreeArrayMax in *; lia|].
destruct okm_koff as [(c' & Hc' & X1 & X2 & X3 & X4)|(e & He & E1 & E2)].
- assert (RC' : region_base ly c' = ly_space ly + c' * 2 ^ 32)
    by (unfold region_base; rewrite region_off_eq by lia; reflexivity).
  destruct (Z.eq_dec c' c) as [->|Hne].
  + unfold kFreeArrayOffset, kFreeArrayMax in *. lia.
  + destruct (Z.lt_ge_cases c' c).
    * assert (HM : (c' + 1) * 2 ^ 32 <= c * 2 ^ 32) by (apply Z.mul_le_mono_nonneg_r; lia).
      unfold kFreeArrayOffset, kFreeArrayMax in *. lia.
    * assert (HM : (c + 1) * 2 ^ 32 <= c' * 2 ^ 32) by (apply Z.mul_le_mono_nonneg_r; lia).
      unfold kFreeArrayOffset, kFreeArrayMax in *. lia.
- pose proof (pairwise_In zdisjoint _ e (ly_prim ly, kPrimResvSize) (sec_extents ly S) (static_extents ly) eq_refl
    (proj2 (amc_placed _ _ _ _ _ M)) He ltac:(unfold static_extents, owned_extents; cbn; tauto)) as DJ.
  unfold zdisjoint in DJ. cbn [fst snd] in DJ. unfold kFreeArrayOffset, kFreeArrayMax in *. lia.
Qed.
Lemma okm_img : forall a, in_zr a (ly_img ly) -> ~ dg_izone a -> ~ dg_dzone ly a -> okm a.
Proof.
intros a Ha NI ND. destruct (g_imgx B ly S Hp rd M a Ha) as (A1 & A2 & A3).
pose proof (anyX_cf B ly S Hp rd M k 9 _ Hk eq_refl ltac:(lia)) as DK.
pose proof (g_img B ly S Hp rd M) as (I0 & I1 & I2).
unfold zdisjoint, in_zr in *. cbn [fst snd] in DK.
split; [unfold kImgEnd in *; lia|]. intros [X|[X|[X|[X|[X|X]]]]].
- apply A3. unfold DGgmC.WINT, t_unwinding, t_stats, kThreadObjSize in *. lia.
- unfold DKm in X. pose proof mHu as EU. pose proof mER as (ER & NN1 & NN2 & NN3).
  pose proof mKF as (G1 & G2 & G3 & G4 & G5 & _). pose proof mQ8 as Q8.
  unfold kImgLo in *. lia.
- apply A2. unfold DSm, DGbaseC.DFSTACK in *. lia.
- exact (NI X).
- exact (ND X).
- pose proof (mDH_sh a X) as [SH1 SH2]. unfold kImgEnd, kLowShadowBeg in *. lia.
Qed.
(* Printf's two cells (field round 3): owned static data (amc_pf_owned), so inside the image, and apart from the two
   zones the walk writes there (YGcfInstFreePost.PF_APART at this layout). *)
Hypothesis HPFm : forall a, pf_byte a -> ~ dg_izone a /\ ~ dg_dzone ly a.
Lemma okm_pf : forall a, pf_byte a -> okm a.
Proof.
intros a Ha. destruct (HPFm a Ha) as [NI ND].
exact (okm_img a (g_static_img B ly S Hp rd M a (proj1 (proj1 (amc_pf_owned _ _ _ _ _ M) a Ha))) NI ND).
Qed.
Lemma m_pf : pf_cells_cf B ly rd'.
Proof.
exact (pf_cells_move_cf B ly S Hp rd rd' okm M (amc_pf_owned _ _ _ _ _ M) (fun a _ Ha => AGm a Ha) okm_pf
  (amc_pf_cells _ _ _ _ _ M)).
Qed.
Lemma okm_inst : okrm (as_inst B) 3632.
Proof.
intros a Ha. apply okm_img.
- exact (g_inst_img B ly S Hp rd M a Ha).
- intros X. exact (proj1 (proj2 (proj2 (HIZ a X))) Ha).
- intros X. exact (proj1 (proj2 (HDZ a) X) Ha).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cells of the call state at the call memory.                                                                  *)
Lemma OLDm : forall c, In c (acells_cf B ly S) -> cell_holds B ly rd c.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) (amc_cells _ _ _ _ _ M) c Hc). Qed.
Ltac old_inm := apply Forall_forall; intros ? HIN; apply OLDm; unfold acells_cf; rewrite !in_app_iff.
Ltac fconsm := apply Forall_cons; [split; cbn; lia|].
Lemma cell_xfer_m : forall c, cell_holds B ly rd c ->
  (forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> okm (aeval B ly (c_at c) + j)) -> cell_holds B ly rd' c.
Proof. intros c Hc Hok. eapply (cell_holds_agree B ly rd rd' c Hc). intros j Hj. apply AGm, Hok, Hj. Qed.
Lemma cells_xfer_m : forall L lo len, okrm lo len -> Forall (cell_in B ly lo len) L ->
  Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd') L.
Proof.
intros L lo len OK IN OLD. apply Forall_forall. intros c Hc. apply cell_xfer_m; [exact (proj1 (Forall_forall _ _) OLD c Hc)|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN c Hc) as [H1 H2]. apply OK. lia.
Qed.
Lemma mEA : forall y d, In y (st_chunks S) -> aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d.
Proof. intros y d Hy. exact (EA_cf B ly S Hp rd M y d Hy). Qed.
Lemma mEA2 : forall y d d', In y (st_chunks S) -> aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d'.
Proof. intros y d d' Hy. exact (EA2_cf B ly S Hp rd M y d d' Hy). Qed.
Lemma mEA0 : forall y, aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y. Proof. reflexivity. Qed.
Lemma m_hdr_bytes : YG0f.le_byte (3 + 256 * hb1) 4 0 = 3 /\ YG0f.le_byte (3 + 256 * hb1) 4 1 = hb1 /\
  YG0f.le_byte (3 + 256 * hb1) 4 2 = 0 /\ YG0f.le_byte (3 + 256 * hb1) 4 3 = 0.
Proof.
destruct Hhb1 as [R _]. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
rewrite (Z.mod_small _ 4294967296) by lia.
change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 3) with 24.
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 0) with 1. change (2 ^ 8) with 256. change (2 ^ 16) with 65536.
change (2 ^ 24) with 16777216. rewrite Z.div_1_r. msp.
- rewrite (Z.mul_comm 256 hb1), Z_mod_plus_full. reflexivity.
- rewrite Z.add_comm, (Z.mul_comm 256 hb1), Z_div_plus_full_l by lia. change (3 / 256) with 0. rewrite Z.add_0_r.
  apply Z.mod_small. lia.
- rewrite Z.div_small by lia. reflexivity.
- rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma m_cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells_cf S') (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold region_cells_cf, region_cells.
rewrite ms_reg. cbn [removelast].
apply (cells_xfer_m _ _ _ okm_rinfo).
- unfold cell_in, ly_rinfo, kRegionInfoOff. repeat fconsm. apply Forall_nil.
- old_inm. left. apply in_flat_map. exists c. split; [apply In_zseq; lia|].
  unfold region_cells_cf, region_cells. cbn [removelast]. exact HIN.
Qed.
Lemma okrm_cache : okrm (T + t_cache + 80) (80 * 31).
Proof. intros a Ha. apply okm_T; unfold DGgmC.WINT, t_cache, t_unwinding, t_stats, kThreadObjSize in *; lia. Qed.
Lemma m_cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S') (zseq 1 31)).
Proof.
apply Forall_flat_map'. intros c Hc. apply zseq_In in Hc. unfold cache_cells. rewrite ms_cacheq, ms_cinit.
apply (cells_xfer_m _ _ _ okrm_cache).
- pose proof (wfc_classes _ _ _ _ _ mWF c ltac:(lia)) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC.
  pose proof (class_ok c ltac:(lia)) as (_ & _ & _ & K4 & _).
  unfold cell_in, t_cache. destruct (st_cache_inited S).
  + destruct WC as [PM PL]. repeat fconsm. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv).
    cbn [fst snd c_at c_w z4 c4 aeval aoff]. apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
  + repeat fconsm. apply Forall_nil.
- old_inm. right; left. apply in_flat_map. exists c. split; [apply In_zseq; lia|].
  unfold cache_cells. exact HIN.
Qed.
Lemma m_cells_chunk_other : forall x, In x (st_chunks S) -> ck_beg x <> ck_beg k -> Forall (cell_holds B ly rd') (chunk_cells x).
Proof.
intros x Hx Hne. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (req_size_bounds (ck_req x) ltac:(lia)) as (_ & Q2 & _).
apply (cells_xfer_m _ (ck_base B ly x) (ck_extent x)); [intros a Ha; exact (okm_other x a Hx Hne Ha) | |].
- unfold chunk_cells, kChunkHeaderSize, cell_in. apply Forall_app. split.
  + repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?(mEA2 x), ?(mEA x) by exact Hx;
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
  + destruct (Z.eqb_spec (ck_rz x) 16); [apply Forall_nil|].
    repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?(mEA2 x), ?(mEA x), ?(mEA0 x) by exact Hx;
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.max Pos.max Z.pos_sub]; lia|]). apply Forall_nil.
- old_inm. do 2 right; left. apply in_flat_map. exists x. split; [exact Hx | exact HIN].
Qed.
Lemma m_cells_chunk_k : Forall (cell_holds B ly rd') (chunk_cells (qk k)).
Proof.
pose proof mKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof mHu as EU.
pose proof mER as (ER & NN1 & NN2 & NN3). pose proof m_hdr_bytes as (HB0 & HB1 & HB2 & HB3). destruct Hhb1 as [_ HM].
assert (Hk1 : forall d, aeval B ly (aoff (sptr_exp (ck_beg (qk k))) d) = ck_base B ly k + d) by (intros d; exact (mEA k d Hk)).
assert (Hk2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg (qk k))) d) d') = ck_base B ly k + d + d')
  by (intros d d'; exact (mEA2 k d d' Hk)).
assert (EU16 : ck_base B ly k + (ck_rz k - 16) = u - 16) by lia.
unfold chunk_cells. change (ck_rz (qk k)) with (ck_rz k). change (ck_n (qk k)) with nn. unfold kChunkHeaderSize.
apply Forall_app. split.
- apply Forall_cons.
  { cbn [cell_holds c_at c_val c_w z1 c1]. rewrite Hk1, EU16. change (aeval B ly (ANum (hdr_state (qk k)))) with 3.
    intros kk Hkk. rewrite NEW_hdr by lia. destruct kk; [|lia]. rewrite HB0. reflexivity. }
  apply Forall_cons.
  { cbn [cell_holds c_at c_val c_w]. rewrite Hk2, EU16. exists hb1. split; [|exact HM].
    change (u - 16 + 1) with (u - 16 + Z.of_nat 1). rewrite (NEW_hdr 1%nat) by lia. rewrite HB1. reflexivity. }
  apply Forall_cons.
  { cbn [cell_holds c_at c_val c_w z2 c2]. rewrite Hk2, EU16. change (aeval B ly (ANum 0)) with 0. intros kk Hkk.
    replace (u - 16 + 2 + Z.of_nat kk) with (u - 16 + Z.of_nat (2 + kk)) by lia. rewrite NEW_hdr by lia.
    destruct kk as [|[|]]; cbn [Nat.add]; [rewrite HB2; reflexivity | rewrite HB3; reflexivity | lia]. }
  apply Forall_cons; [|apply Forall_nil].
  { cbn [cell_holds c_at c_val c_w z4 c4]. rewrite Hk2, EU16. change (aeval B ly (ANum nn)) with nn. intros kk Hkk.
    replace (u - 16 + 4 + Z.of_nat kk) with (u - 12 + Z.of_nat kk) by lia. rewrite NEW_n by lia. reflexivity. }
- destruct (Z.eqb_spec (ck_rz k) 16) as [E16|N16]; [apply Forall_nil|].
  assert (R32 : 32 <= ck_rz k) by (apply Z.mod_divide in G6 as [q Hq]; [|lia]; lia).
  assert (OKM : okrm (ck_base B ly k) 16) by (intros a Ha; apply okm_k; [lia | unfold DKm; lia]).
  apply (cells_xfer_m _ _ _ OKM).
  + assert (Hk0 : aeval B ly (sptr_exp (ck_beg (qk k))) = ck_base B ly k) by reflexivity.
    unfold cell_in. apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite Hk0; cbn; lia|].
    apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite Hk1; cbn; lia|]. apply Forall_nil.
  + assert (OLDK : Forall (cell_holds B ly rd) (chunk_cells k))
      by (old_inm; do 2 right; left; apply in_flat_map; exists k; split; [exact Hk | exact HIN]).
    unfold chunk_cells, kChunkHeaderSize in OLDK. apply Forall_app in OLDK as [_ OLDK].
    destruct (Z.eqb_spec (ck_rz k) 16); [lia | exact OLDK].
Qed.
Lemma m_cells_chunks : forall l1 l2, st_chunks S = l1 ++ k :: l2 -> ~ In (ck_beg k) (map ck_beg l1) ->
  ~ In (ck_beg k) (map ck_beg l2) -> Forall (cell_holds B ly rd') (flat_map chunk_cells (l1 ++ qk k :: l2)).
Proof.
intros l1 l2 E N1 N2. rewrite flat_map_app. cbn [flat_map]. rewrite !Forall_app. msp.
- apply Forall_flat_map'. intros x Hx. apply m_cells_chunk_other;
    [rewrite E; apply in_app_iff; left; exact Hx | intros Ex; apply N1; rewrite <- Ex; apply in_map; exact Hx].
- exact m_cells_chunk_k.
- apply Forall_flat_map'. intros x Hx. apply m_cells_chunk_other;
    [rewrite E; apply in_app_iff; right; right; exact Hx | intros Ex; apply N2; rewrite <- Ex; apply in_map; exact Hx].
Qed.
Lemma m_cells_sec : Forall (cell_holds B ly rd') (sec_cells S').
Proof.
destruct ms_split as (l1 & l2 & E & E' & N1 & N2).
pose proof (wfc_secondary _ _ _ _ _ mWF) as X. destruct X as [Snd Sac Sal Sres Sral].
assert (OLDS : Forall (cell_holds B ly rd) (sec_cells S)) by (old_inm; do 3 right; left; exact HIN).
unfold sec_cells in OLDS |- *. rewrite ms_sec_res, ms_sec_arr, E'.
rewrite (YFfl.flat_map_mid _ l1 (qk k) k l2) by reflexivity. rewrite <- E.
apply Forall_cons_iff in OLDS as [O1 OLDS]. apply Forall_cons_iff in OLDS as [O2 OLDS].
apply Forall_cons_iff in OLDS as [O3 OLDS]. apply Forall_app in OLDS as [O4 O5].
pose proof okm_inst as OKI.
apply Forall_cons; [apply (cell_xfer_m _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_reserved; lia|].
apply Forall_cons; [apply (cell_xfer_m _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_n; lia|].
apply Forall_cons; [apply (cell_xfer_m _ O3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_sec_mutex; lia|].
apply Forall_app. split.
- apply (cells_xfer_m _ _ _ okm_Q); [|exact O4]. apply Forall_forall. intros c Hc.
  apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
  unfold cell_in. cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) O5 c Hc) as Oc.
  apply in_flat_map in Hc as (x & Hx & Hc).
  destruct (ck_beg x) as [|o|r o|c' p] eqn:Ebx; try solve [destruct Hc].
  assert (OKP : okrm (ly_sec ly r) 32) by (intros a Ha; eapply (okm_secpage x r o a Hx Ebx); unfold kPage; lia).
  apply (cell_xfer_m _ Oc). intros j Hj. apply OKP. destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hj |- *; lia.
Qed.
Lemma m_cells_quar : Forall (cell_holds B ly rd') (quar_cells S').
Proof.
rewrite ms_quar_cells.
assert (OLDQ : Forall (cell_holds B ly rd) (quar_cells S)) by (old_inm; do 4 right; left; exact HIN).
pose proof okm_inst as OKI.
unfold quar_cells, qc_cells in OLDQ |- *.
apply Forall_cons_iff in OLDQ as [O1 OLDQ]. apply Forall_cons_iff in OLDQ as [O2 OLDQ]. apply Forall_app in OLDQ as [OT OG].
apply Forall_cons_iff in OT as [O3 OT]. apply Forall_cons_iff in OT as [O4 OT]. apply Forall_cons_iff in OT as [O5 OT]. apply Forall_cons_iff in OT as [O6 OT].
apply Forall_cons_iff in OG as [G1 OG]. apply Forall_cons_iff in OG as [G2 OG]. apply Forall_cons_iff in OG as [G3 OG]. apply Forall_cons_iff in OG as [G4 OG].
assert (OKQ : okrm (T + t_qc) 32) by (intros a Ha; apply okm_T; unfold DGgmC.WINT, t_qc, t_unwinding, t_stats, kThreadObjSize in *; lia).
apply Forall_cons; [apply (cell_xfer_m _ O1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_cmutex; lia|].
apply Forall_cons; [apply (cell_xfer_m _ O2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_rmutex; lia|].
apply Forall_app. split.
- apply Forall_cons; [apply (cell_xfer_m _ O3); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
  apply Forall_cons; [apply (cell_xfer_m _ O4); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
  apply Forall_cons; [apply (cell_xfer_m _ O5); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
  apply Forall_cons; [apply (cell_xfer_m _ O6); intros j Hj; apply OKQ; cbn in Hj |- *; lia|].
  apply Forall_forall. intros c Hc. apply (cell_xfer_m _ (proj1 (Forall_forall _ _) OT c Hc)).
  destruct (batch_cells_within B ly (qc_list (st_qthread S)) c Hc) as (b2 & I2 & [R1 R2]). intros j Hj.
  pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ mWF)) b2 ltac:(unfold all_batches; apply in_app_iff; left; exact I2)) as [L1 L2].
  apply (okm_batch b2); [unfold all_batches; apply in_app_iff; left; exact I2 | unfold kBatchSlots, kBatchBytes in *; lia].
- apply Forall_cons; [apply (cell_xfer_m _ G1); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
  apply Forall_cons; [apply (cell_xfer_m _ G2); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
  apply Forall_cons; [apply (cell_xfer_m _ G3); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
  apply Forall_cons; [apply (cell_xfer_m _ G4); intros j Hj; apply OKI; cbn in Hj |- *; unfold o_q_size; lia|].
  apply Forall_forall. intros c Hc. apply (cell_xfer_m _ (proj1 (Forall_forall _ _) OG c Hc)).
  destruct (batch_cells_within B ly _ c Hc) as (b2 & I2 & [R1 R2]). intros j Hj.
  pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfc_quarantine _ _ _ _ _ mWF)) b2 ltac:(unfold all_batches; apply in_app_iff; right; exact I2)) as [L1 L2].
  apply (okm_batch b2); [unfold all_batches; apply in_app_iff; right; exact I2 | unfold kBatchSlots, kBatchBytes in *; lia].
Qed.
Lemma m_cells_fs : Forall (cell_holds B ly rd') (fs_cells S').
Proof.
assert (OLDF : Forall (cell_holds B ly rd) (fs_cells S)) by (old_inm; do 5 right; left; exact HIN).
unfold fs_cells in OLDF |- *. rewrite ms_fs. apply (cells_xfer_m _ _ _ okm_F); [|exact OLDF].
unfold cell_in, kFakeStackSize. fconsm. fconsm.
apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih.
apply in_seq in Hih. cbn. lia.
Qed.
Lemma m_cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S').
Proof. destruct DEP as (D1 & _ & _). unfold depot_cells, depot_ids, depot_frames in D1 |- *. rewrite ms_depot. exact D1. Qed.
Lemma m_cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
unfold thread_cells. apply Forall_cons; [|apply Forall_nil]. cbn [cell_holds c_at c_val c_w z1 c1 aeval].
intros kk Hkk. destruct kk; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, NEW_unw. reflexivity.
Qed.
Lemma m_cells_all : Forall (cell_holds B ly rd') (acells_cf B ly S').
Proof.
destruct ms_split as (l1 & l2 & E & E' & N1 & N2). unfold acells_cf. rewrite E'. rewrite !Forall_app. msp.
- exact m_cells_regions.
- exact m_cells_caches.
- exact (m_cells_chunks l1 l2 E N1 N2).
- exact m_cells_sec.
- exact m_cells_quar.
- exact m_cells_fs.
- exact m_cells_depot.
- exact (proj1 IAL).
- exact m_cells_thread.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The remaining fields.                                                                                             *)
Lemma m_fa : fa_entries_ok ly rd' S'.
Proof.
intros c i v Hc Hi Hv kk Hkk. rewrite ms_reg in Hi, Hv.
rewrite AGm; [exact (amc_fa _ _ _ _ _ M c i v Hc Hi Hv kk Hkk)|].
pose proof (wfc_classes _ _ _ _ _ mWF c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL.
pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB. apply (okm_fa c Hc). lia.
Qed.
Lemma m_flags : fs_flags_ok ly rd' S'.
Proof.
intros cid pos Hc Hpos. rewrite ms_frames. rewrite AGm; [exact (amc_flags _ _ _ _ _ M cid pos Hc Hpos)|].
pose proof (flag_off_bounds cid pos Hc Hpos) as FB. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff in *.
apply okm_F. unfold kFakeStackSize. lia.
Qed.
Lemma m_depot : depot_ok B ly rd' S'.
Proof. destruct DEP as (_ & D2 & _). unfold depot_ok, depot_ids, depot_traces in D2 |- *. rewrite ms_depot. exact D2. Qed.
(* the freed block's bytes are not a hidden head: a hidden head is the user base of another live block *)
Lemma m_head_off : forall g, ck_base B ly k <= g < ck_base B ly k + ck_extent k -> in_head Hp g = false.
Proof.
intros g Hg. destruct (in_head Hp g) eqn:E; [|reflexivity]. exfalso.
unfold in_head in E. apply existsb_exists in E as (p0 & Hp0 & Hb).
apply andb_prop in Hb as [HB1 HB2]. apply Z.leb_le in HB1. apply Z.ltb_lt in HB2.
pose proof (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ M) p0 Hp0) as (k0 & Hk0 & Hst0 & Ep0 & Hn0).
pose proof (chunk_facts_cf B ly S Hp rd k0 M Hk0) as (_ & _ & _ & G40 & G50 & _ & _ & G80 & _).
destruct (sptr_eqb (ck_beg k0) (ck_beg k)) eqn:Eb.
- apply sptr_eqb_spec in Eb.
  assert (k0 = k) by (apply (YFfl.NoDup_map_In ck_beg (st_chunks S) k0 k (wfc_chunks_nodup _ _ _ _ _ mWF) Hk0 Hk Eb)).
  subst k0. apply HPu. rewrite <- Ep0. exact Hp0.
- assert (Hne : ck_beg k0 <> ck_beg k) by (intros E'; rewrite E', sptr_eqb_refl in Eb; discriminate).
  pose proof (chunks_disjoint_cf B ly S Hp rd k0 k M Hk0 Hk Hne) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ.
  unfold ck_n in Hn0. rewrite Ep0, G40 in HB1, HB2. lia.
Qed.
Lemma m_DH_iff : forall g, g mod 8 = 0 -> (DHm (shadow_addr g) <-> u <= g < u + (nn + 7) / 8 * 8).
Proof.
intros g Hg. pose proof mU8 as (U8 & _ & _). pose proof mER as (_ & _ & NN2 & _).
unfold DHm, shadow_addr. apply Z.mod_divide in Hg as [c Hc]; [|lia]. apply Z.mod_divide in U8 as [a0 Ha0]; [|lia].
rewrite Hc, Ha0. rewrite !Z_div_mult by lia. nia.
Qed.
Lemma m_shadow : shadow_ok_cf B ly Hp rd' S'.
Proof.
destruct ms_split as (l1 & l2 & E & E' & N1 & N2).
pose proof mKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof mHu as EU.
pose proof mER as (ER & NN1 & NN2 & NN3). pose proof mU8 as (U8 & B8 & R8).
intros g v Hg8 HS'. pose proof (amc_shadow _ _ _ _ _ M g) as SH.
unfold ashadow in HS', SH. rewrite E', ms_fa_poison in HS'. rewrite E in SH.
rewrite YFfl.find_chunk_at_app in HS', SH. cbn [find_chunk_at] in HS', SH.
change (ck_base B ly (qk k)) with (ck_base B ly k) in HS'. change (ck_extent (qk k)) with (ck_extent k) in HS'.
assert (OTHER : forall x, In x (st_chunks S) -> ck_beg x <> ck_beg k ->
  ck_base B ly x <= g < ck_base B ly x + ck_extent x ->
  rd (shadow_addr g) = Some (if in_head Hp g then shUserPoison else v) ->
  rd' (shadow_addr g) = Some (if in_head Hp g then shUserPoison else v)).
{ intros x Hx Hne Hgx Hrd. pose proof (chunk_facts_cf B ly S Hp rd x M Hx) as (X1 & X2 & _).
  rewrite AGm; [exact Hrd|]. apply okm_sh.
  - apply g_hs_bounds; [unfold in_app in X1; lia | mceil; unfold ASAN_CEIL, kHighMemEnd in *; lia].
  - intros HD. apply (m_DH_iff g Hg8) in HD.
    pose proof (chunks_disjoint_cf B ly S Hp rd x k M Hx Hk Hne) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia. }
destruct (find_chunk_at B ly l1 g) as [x|] eqn:F1.
- apply find_chunk_at_In in F1 as [Hx Hgx].
  apply (OTHER x); [rewrite E; apply in_app_iff; left; exact Hx
    | intros Ex; apply N1; rewrite <- Ex; apply in_map; exact Hx | exact Hgx | exact (SH v Hg8 HS')].
- destruct ((ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k)) eqn:TK.
  + apply andb_prop in TK as [T1 T2]. apply Z.leb_le in T1. apply Z.ltb_lt in T2.
    change (ck_base B ly (qk k)) with (ck_base B ly k) in HS'.
    rewrite (m_head_off g ltac:(lia)) in SH |- *.
    apply Z.mod_divide in Hg8 as [c Hc]; [|lia]. apply Z.mod_divide in B8 as [b0 Hb0]; [|lia].
    apply Z.mod_divide in R8 as [r0 Hr0]; [|lia].
    assert (J : (g - ck_base B ly k) / 8 = c - b0)
      by (rewrite Hc, Hb0; replace (c * 8 - b0 * 8) with ((c - b0) * 8) by lia; apply Z_div_mult; lia).
    assert (RU : ck_rz k / 8 = r0) by (rewrite Hr0; apply Z_div_mult; lia).
    rewrite J in HS', SH. unfold chunk_granule in HS', SH.
    change (ck_rz (qk k)) with (ck_rz k) in HS'. change (ck_n (qk k)) with nn in HS'.
    change (ck_state (qk k)) with CQuarantined in HS'. rewrite RU in HS', SH. rewrite Hst in SH.
    destruct (c - b0 <? r0) eqn:C1.
    * apply Z.ltb_lt in C1. injection HS' as <-. rewrite AGm; [exact (SH _ ltac:(rewrite Hc; apply Z_mod_mult) eq_refl)|].
      apply okm_sh; [apply g_hs_bounds; [unfold in_app in G1; lia | mceil; unfold ASAN_CEIL, kHighMemEnd in *; lia]|].
      intros HD. apply (m_DH_iff g ltac:(rewrite Hc; apply Z_mod_mult)) in HD. nia.
    * apply Z.ltb_ge in C1. destruct (c - b0 <? r0 + (nn + 7) / 8) eqn:C2.
      -- apply Z.ltb_lt in C2. injection HS' as <-.
         apply NEW_sh; [apply (m_DH_iff g ltac:(rewrite Hc; apply Z_mod_mult)); nia|].
         rewrite (SH (if c - b0 <? r0 + nn / 8 then shAddressable
                      else if (c - b0 =? r0 + nn / 8) && negb (nn mod 8 =? 0) then nn mod 8 else shHeapLeftRz));
           [discriminate | rewrite Hc; apply Z_mod_mult | reflexivity].
      -- apply Z.ltb_ge in C2. injection HS' as <-.
         assert (OLDV : rd (shadow_addr g) = Some shHeapLeftRz).
         { apply SH; [rewrite Hc; apply Z_mod_mult|].
           assert (F1' : (c - b0 <? r0 + nn / 8) = false).
           { apply Z.ltb_ge. pose proof (Z.div_le_mono nn (nn + 7) 8 ltac:(lia) ltac:(lia)). lia. }
           rewrite F1'. destruct (Z.eqb_spec (nn mod 8) 0) as [Z0|NZ]; cbn [negb andb];
             [rewrite Bool.andb_false_r; reflexivity|].
           replace (c - b0 =? r0 + nn / 8) with false; [reflexivity|]. symmetry. apply Z.eqb_neq.
           pose proof (Z.div_mod nn 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound nn 8 ltac:(lia)) as MB.
           pose proof (Z.div_mod (nn + 7) 8 ltac:(lia)) as DM'. pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(lia)) as MB'. nia. }
         rewrite AGm; [exact OLDV|].
         apply okm_sh; [apply g_hs_bounds; [unfold in_app in G1; lia | mceil; unfold ASAN_CEIL, kHighMemEnd in *; lia]|].
         intros HD. apply (m_DH_iff g ltac:(rewrite Hc; apply Z_mod_mult)) in HD. nia.
  + assert (NK : ~ (ck_base B ly k <= g < ck_base B ly k + ck_extent k)).
    { intros X. assert (TT : (ck_base B ly k <=? g) && (g <? ck_base B ly k + ck_extent k) = true)
        by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). rewrite TT in TK. discriminate. }
    destruct (find_chunk_at B ly l2 g) as [x|] eqn:F2.
    * apply find_chunk_at_In in F2 as [Hx Hgx].
      apply (OTHER x); [rewrite E; apply in_app_iff; right; right; exact Hx
        | intros Ex; apply N2; rewrite <- Ex; apply in_map; exact Hx | exact Hgx | exact (SH v Hg8 HS')].
    * destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:R; [|discriminate].
      pose proof (in_rangesb_true _ _ R) as (lo & len & Hin & Hg).
      pose proof (g_fa_poison_high B ly S Hp rd M lo len g Hin Hg) as [Y1 Y2].
      rewrite AGm; [exact (SH v Hg8 HS')|].
      apply okm_sh; [apply g_hs_bounds; [lia | mceil; unfold ASAN_CEIL, kHighMemEnd in *; lia]|].
      intros HD. apply (m_DH_iff g Hg8) in HD. lia.
Qed.
Lemma m_zshadow : zshadow_ok B ly rd'.
Proof.
pose proof (amc_zshadow _ _ _ _ _ M) as ZS. unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *.
change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGm; [exact Z0|]. apply okm_sh; [exact (g_zsh_sh B ly S Hp rd M r i Hr Hi)|].
intros HD. pose proof mKF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). pose proof mHu as EU.
pose proof mER as (ER & NN1 & NN2 & NN3). pose proof mU8 as (U8 & B8 & R8).
pose proof (amc_layout _ _ _ _ _ M) as LO.
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd] in Hi, Z0, HD |- *.
- pose proof (lo_top _ LO) as (_ & _ & _ & T4 & T5 & _ & T7). unfold page_aligned in T5.
  apply Z.mod_divide in T5 as [s0 Hs0]; [|lia].
  assert (E8 : shadow_addr (ly_stk_lo ly) + i = shadow_addr (ly_stk_lo ly + 8 * i)).
  { unfold shadow_addr. rewrite Hs0. replace (s0 * 4096) with ((512 * s0) * 8) by lia.
    replace (512 * s0 * 8 + 8 * i) with ((512 * s0 + i) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
  rewrite E8 in HD. apply (m_DH_iff (ly_stk_lo ly + 8 * i)
    ltac:(rewrite Hs0; replace (s0 * 4096 + 8 * i) with ((512 * s0 + i) * 8) by lia; apply Z_mod_mult)) in HD.
  pose proof (Z.mul_div_le (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
  pose proof (anyX_cf B ly S Hp rd M k 8 _ Hk eq_refl ltac:(lia)) as D8.
  unfold zdisjoint in D8. cbn [fst snd] in D8. lia.
- pose proof (g_zsh_img B ly S Hp rd M r Hr) as [Z1 Z2]. pose proof (g_img B ly S Hp rd M) as (I0 & I1 & I2).
  pose proof (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ M)) r Hr) as (Q1 & Q2 & Q3 & Q4 & Q5).
  destruct r as [lo len]. cbn [fst snd] in *. apply Z.mod_divide in Q3 as [c Hc]; [|lia].
  assert (E8 : shadow_addr lo + i = shadow_addr (lo + 8 * i)).
  { unfold shadow_addr. rewrite Hc. replace (c * 8 + 8 * i) with ((c + i) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
  rewrite E8 in HD. apply (m_DH_iff (lo + 8 * i)
    ltac:(rewrite Hc; replace (c * 8 + 8 * i) with ((c + i) * 8) by lia; apply Z_mod_mult)) in HD.
  pose proof (Z.mul_div_le len 8 ltac:(lia)).
  pose proof (anyX_cf B ly S Hp rd M k 9 _ Hk eq_refl ltac:(lia)) as D9.
  unfold zdisjoint in D9. cbn [fst snd] in D9. unfold kImgLo in *. lia.
Qed.
Lemma m_vis_sub : forall r r', range_vis B ly rd r' -> aeval B ly (fst r') <= aeval B ly (fst r) ->
  aeval B ly (fst r) + snd r <= aeval B ly (fst r') + snd r' -> range_vis B ly rd' r.
Proof.
intros r r' V H1 H2 i Hi. apply VIS.
replace (aeval B ly (fst r) + i) with (aeval B ly (fst r') + (aeval B ly (fst r) + i - aeval B ly (fst r'))) by lia.
apply V. lia.
Qed.
Lemma m_junk : Forall (range_vis B ly rd') (ajunk_cf B ly S').
Proof.
destruct ms_split as (l1 & l2 & E & E' & N1 & N2). pose proof (amc_junk _ _ _ _ _ M) as J.
pose proof (amc_client _ _ _ _ _ M) as CL. pose proof mHu as EU.
assert (VK : forall L, Forall (range_vis B ly rd) L -> Forall (range_vis B ly rd') L)
  by (intros L HL; exact (Forall_range_vis_keep B ly rd rd' L VIS HL)).
unfold ajunk_cf in J |- *. unfold quar_junk in J |- *. rewrite ms_batches.
unfold cache_junk, cache, sec_junk in J |- *. rewrite ms_cinit, ms_cache, ms_sec_arr, ms_sec_res, E'. rewrite E in J.
rewrite (YFfl.flat_map_mid (fun k0 : chunk => match ck_beg k0 with PSec r _ => [(ASec r 32, kPage - 32)] | _ => [] end) l1 (qk k) k l2)
  by reflexivity.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J]. apply Forall_app in J as [J5 J].
apply Forall_cons; [intros i Hi; apply VIS; exact (J1 i Hi)|].
apply Forall_cons; [intros i Hi; apply VIS; exact (J2 i Hi)|].
apply Forall_app. split; [exact (VK _ J3)|]. apply Forall_app. split; [exact (VK _ J4)|].
apply Forall_app. split; [|exact (VK _ J)].
rewrite flat_map_app in J5 |- *. cbn [flat_map] in J5 |- *. apply Forall_app in J5 as [J5a J5].
apply Forall_app in J5 as [J5k J5b].
apply Forall_app. split; [exact (VK _ J5a)|]. apply Forall_app. split; [|exact (VK _ J5b)].
unfold chunk_junk in J5k |- *. change (ck_rz (qk k)) with (ck_rz k). change (ck_n (qk k)) with nn.
change (ck_extent (qk k)) with (ck_extent k). change (ck_state (qk k)) with CQuarantined. rewrite Hst in J5k.
apply Forall_app in J5k as [Ja J5k]. apply Forall_app in J5k as [Jb J5k]. apply Forall_app in J5k as [_ Jd].
apply Forall_app. split; [exact (VK _ Ja)|]. apply Forall_app. split; [exact (VK _ Jb)|].
apply Forall_app. split; [|exact (VK _ Jd)].
apply Forall_cons; [|apply Forall_nil].
apply (m_vis_sub _ (sptr_exp (ck_user k), ck_n k)).
- apply (proj1 (Forall_forall _ _) CL). unfold aclient. apply in_app_iff. left. apply in_flat_map.
  exists k. split; [exact Hk|]. unfold chunk_user. rewrite Hst. left. reflexivity.
- cbn [fst snd]. change (sptr_exp (ck_beg (qk k))) with (sptr_exp (ck_beg k)). rewrite (mEA k _ Hk).
  fold (sptr_addr B ly (ck_user k)). lia.
- cbn [fst snd]. change (sptr_exp (ck_beg (qk k))) with (sptr_exp (ck_beg k)). rewrite (mEA k _ Hk).
  fold (sptr_addr B ly (ck_user k)). lia.
Qed.
Lemma m_areas : Forall (range_vis B ly rd') (aareas S').
Proof.
destruct ms_split as (l1 & l2 & E & E' & N1 & N2). pose proof (amc_areas _ _ _ _ _ M) as A.
unfold aareas, reg in A |- *. rewrite ms_regions, ms_sec_res, E'. rewrite E in A.
rewrite (YFfl.flat_map_mid _ l1 (qk k) k l2) by reflexivity. exact (Forall_range_vis_keep B ly rd rd' _ VIS A).
Qed.
Lemma m_client : Forall (range_vis B ly rd') (aclient S').
Proof.
destruct ms_split as (l1 & l2 & E & E' & N1 & N2). pose proof (amc_client _ _ _ _ _ M) as A.
apply Forall_forall. intros r Hr i Hi. apply VIS.
assert (Hr0 : In r (aclient S)).
{ unfold aclient in Hr |- *. apply in_app_iff in Hr as [Hr|Hr]; apply in_app_iff; [left | right; rewrite ms_frames in Hr; exact Hr].
  apply in_flat_map in Hr as (x & Hx & Hrx). apply in_flat_map. exists x. split; [|exact Hrx].
  rewrite E' in Hx. rewrite E. apply in_app_iff in Hx as [Hx|[Hx|Hx]].
  - apply in_app_iff. left. exact Hx.
  - subst x. cbn [chunk_user qk ck_state In] in Hrx. destruct Hrx.
  - apply in_app_iff. right. right. exact Hx. }
exact (proj1 (Forall_forall _ _) A r Hr0 i Hi).
Qed.
Lemma m_hp_live : Forall (fun p => exists k0, In k0 (st_chunks S') /\ ck_state k0 = CAllocated /\
  p = sptr_addr B ly (ck_user k0) /\ cf_head <= ck_n k0) Hp.
Proof.
destruct ms_split as (l1 & l2 & E & E' & N1 & N2). apply Forall_forall. intros p0 Hp0.
destruct (proj1 (Forall_forall _ _) (amc_hp_live _ _ _ _ _ M) p0 Hp0) as (k0 & Hk0 & Hs0 & Ep0 & Hn0).
exists k0. split; [|exact (conj Hs0 (conj Ep0 Hn0))]. rewrite E'. rewrite E in Hk0.
apply in_app_iff in Hk0 as [X|[X|X]]; apply in_app_iff; [left; exact X | | right; right; exact X].
exfalso. subst k0. apply HPu. rewrite <- Ep0. exact Hp0.
Qed.
Lemma m_xs : xs_placed_cf ly S'.
Proof.
pose proof (amc_xs_placed _ _ _ _ _ M) as X. unfold xs_placed_cf in X |- *.
replace (xs_cf ly S') with (xs_cf ly S) by (unfold xs_cf, errb_cap_cf, errb_e; rewrite ms_secs; reflexivity).
rewrite ms_sec_extents. exact X.
Qed.
(* ARmcf of the call state at the call memory, and the agreement on the free granules' shadow (ahs_transfer_cf). *)
Theorem m_post_parts : ARmcf B ly S' Hp rd' /\
  (forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> rd' (shadow_addr g) = rd (shadow_addr g)).
Proof.
split.
- constructor.
  + exact WFX.
  + exact (amc_universe _ _ _ _ _ M).
  + exact (amc_syms _ _ _ _ _ M).
  + exact mLO.
  + unfold sec_placed. rewrite ms_sec_extents. exact (amc_placed _ _ _ _ _ M).
  + exact CONST'.
  + exact (amc_const_owned _ _ _ _ _ M).
  + exact m_cells_all.
  + exact m_fa.
  + exact m_flags.
  + exact m_depot.
  + exact m_shadow.
  + exact m_zshadow.
  + exact m_junk.
  + exact m_areas.
  + exact m_client.
  + exact (proj2 IAL).
  + exact (amc_tsd _ _ _ _ _ M).
  + exact (amc_static_img _ _ _ _ _ M).
  + exact m_hp_live.
  + exact m_xs.
  + exact EXHm.
  + exact ERRm.
  + exact (amc_cells_owned _ _ _ _ _ M).
  + exact m_pf.
  + exact (amc_pf_owned _ _ _ _ _ M).
- intros g Hg Hga HF. pose proof mKF as (G1 & G2 & G3 & G4 & G5 & _). pose proof mHu as EU.
  pose proof mER as (ER & NN1 & NN2 & NN3).
  apply AGm. apply okm_sh.
  + apply g_hs_bounds; [exact (proj1 Hga) | mceil; unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *; lia].
  + intros HD. apply (m_DH_iff g Hg) in HD.
    destruct (hfree_off_extent_cf B ly S Hp rd k g M Hk Hg HF) as [X|X]; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The constant cells off the depot zone are off the walk's windows (DGif1.v:2024-2045's CD over owned_core).       *)
Hypothesis HCO : FP_CONST_at B ly.
Lemma mDK_ext : forall a, DKm a -> ck_base B ly k <= a < ck_base B ly k + ck_extent k.
Proof.
intros a X. pose proof mKF as (G1 & G2 & G3 & G4 & G5 & _). pose proof mHu as EU. pose proof mER as (ER & NN1 & NN2 & NN3).
pose proof mQ8 as Q8. unfold DKm in X. lia.
Qed.
Lemma mDH_img : forall a r, In r (as_owned_static B) -> shadow_addr (fst r) <= a < shadow_addr (fst r) + (snd r + 7) / 8 ->
  ~ DHm a.
Proof.
intros a r Hr Ha HD. unfold DHm in HD.
pose proof (proj1 (Forall_forall _ _) (amc_static_img _ _ _ _ _ M) r ltac:(apply in_app_iff; left; exact Hr)) as [Z1 Z2].
pose proof (lo_img _ mLO) as (I0 & I1 & I2 & I3).
pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ M)) r Hr) as (Y1 & Y2 & Y3).
pose proof (anyX_cf B ly S Hp rd M k 9 _ Hk eq_refl ltac:(lia)) as DJI. unfold zdisjoint in DJI. cbn [fst snd] in DJI.
pose proof mKF as (G1 & G2 & G3 & G4 & G5 & _). pose proof mHu as EU. pose proof mER as (ER & NN1 & NN2 & NN3).
pose proof mU8 as (U8 & _ & _).
assert (EE : exists e, kImgLo + snd (ly_img ly) = 8 * e).
{ unfold page_aligned in I3. apply Z.mod_divide in I3 as [w Hw]; [|lia]. exists (8192 + 512 * w). unfold kImgLo. lia. }
destruct EE as [e He].
apply Z.mod_divide in U8 as [c Hc]; [|lia].
assert (SU : shadow_addr u = SHADOW_OFF + c) by (unfold shadow_addr; rewrite Hc, Z_div_mult by lia; reflexivity).
rewrite SU in HD. unfold zr_sub in Z1, Z2. cbn [fst snd] in Z1, Z2.
destruct DJI as [DJI|DJI].
- assert (F1 : kImgLo / 8 <= fst r / 8) by (apply Z.div_le_mono; lia).
  change (kImgLo / 8) with 8192 in F1. unfold shadow_addr in Ha. unfold kImgLo in *. lia.
- assert (F2 : fst r / 8 + (snd r + 7) / 8 <= (fst r + snd r + 7) / 8).
  { pose proof (Z.div_mod (fst r) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (fst r) 8 ltac:(lia)) as MB.
    replace (fst r + snd r + 7) with (fst r / 8 * 8 + (fst r mod 8 + snd r + 7)) by lia.
    rewrite Z.div_add_l by lia.
    pose proof (Z.div_le_mono (snd r + 7) (fst r mod 8 + snd r + 7) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (F3 : (fst r + snd r + 7) / 8 < e + 1) by (apply Z.div_lt_upper_bound; lia).
  unfold shadow_addr in Ha. lia.
Qed.
Lemma m_const_ok : forall c j, In c (as_const B ly) -> 0 <= j < Z.max 1 (Z.of_nat (c_w c)) ->
  ~ dg_dzone ly (aeval B ly (c_at c) + j) -> okm (aeval B ly (c_at c) + j).
Proof.
intros c j Hc Hj ND.
destruct (g_const_loc B ly S Hp rd M c j Hc Hj) as [R64 NST]. destruct (HCO c j Hc Hj) as [NIZ NWT].
pose proof (proj1 (Forall_forall _ _) (amc_const_owned _ _ _ _ _ M) c Hc j Hj) as OW. unfold owned_core in OW.
pose proof (g_img B ly S Hp rd M) as (I0 & I1 & I2).
set (a := aeval B ly (c_at c) + j) in *.
split; [exact R64|]. intros [X|[X|[X|[X|[X|X]]]]].
- apply NWT. unfold DGgiC.WINT. right. exact X.
- apply mDK_ext in X. destruct OW as [O|[O|O]].
  + pose proof (g_static_img B ly S Hp rd M a O) as HI.
    pose proof (anyX_cf B ly S Hp rd M k 9 _ Hk eq_refl ltac:(lia)) as DJI. unfold zdisjoint, in_zr in *. cbn [fst snd] in *. lia.
  + apply Exists_exists in O as (e & He & Hae). unfold core_extents in He. unfold in_zr in Hae.
    cbn [In] in He. destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd] in Hae;
    [ pose proof (anyX_cf B ly S Hp rd M k 1 _ Hk eq_refl ltac:(lia)) as DD
    | pose proof (anyX_cf B ly S Hp rd M k 2 _ Hk eq_refl ltac:(lia)) as DD
    | pose proof (anyX_cf B ly S Hp rd M k 4 _ Hk eq_refl ltac:(lia)) as DD
    | pose proof (anyX_cf B ly S Hp rd M k 5 _ Hk eq_refl ltac:(lia)) as DD
    | pose proof (anyX_cf B ly S Hp rd M k 6 _ Hk eq_refl ltac:(lia)) as DD
    | pose proof (anyX_cf B ly S Hp rd M k 7 _ Hk eq_refl ltac:(lia)) as DD ];
    unfold zdisjoint in DD; cbn [fst snd] in DD; lia.
  + apply Exists_exists in O as (r & Hr & Hra). unfold in_zr in Hra. cbn [fst snd] in Hra.
    pose proof (proj1 (Forall_forall _ _) (aso_static _ (amc_syms _ _ _ _ _ M)) r Hr) as (Y1 & Y2 & Y3).
    pose proof mKF as (G1 & G2 & _).
    assert (D1 : fst r / 8 <= fst r) by (apply Z.div_le_upper_bound; lia).
    assert (D2 : (snd r + 7) / 8 <= snd r + 7) by (apply Z.div_le_upper_bound; lia).
    assert (D0 : 512 <= fst r / 8) by (pose proof (Z.div_le_mono 4096 (fst r) 8 ltac:(lia) ltac:(lia)) as D; exact D).
    unfold in_app, shadow_addr, SHADOW_OFF, kImgEnd, kLowShadowBeg, kHighMemBeg in *. lia.
- apply NST. unfold DSm, DGbaseC.DFSTACK in *. lia.
- exact (NIZ X).
- exact (ND X).
- destruct OW as [O|[O|O]].
  + pose proof (g_static_img B ly S Hp rd M a O) as HI. pose proof (mDH_sh a X) as [S1 S2].
    unfold in_zr in HI. unfold kImgLo, kImgEnd, kLowShadowBeg in *. lia.
  + apply Exists_exists in O as (e & He & Hae).
    assert (HeO : In e (owned_extents ly)) by (unfold core_extents in He; unfold owned_extents; cbn in He |- *; tauto).
    pose proof (g_app_oext B ly S Hp rd M e a HeO Hae) as AA. pose proof (mDH_sh a X) as [S1 S2].
    unfold app_addr, kLowShadowBeg, kHighMemBeg in *. lia.
  + apply Exists_exists in O as (r & Hr & Hra). exact (mDH_img a r Hr Hra X).
Qed.
End m.
End a.
