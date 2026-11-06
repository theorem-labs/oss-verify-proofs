(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstDrainR.v, sha256 fcbd68ace16995977b466db6781f7370701d158acb2abb6c9b0951c923df759b (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
   Modules that are per image in this tree (lane W's AllocG / DeallocG / DMspec / DMiface / ImgBaseDG / DGif0, the F1 core's
   YGcfRehidePost / YGcfRecStep, and the per-image cf files of this carry) name lib/A; a sentence is split at a directory
   change, the module order kept.
*)
(* Theorem Labs, 2026-10: the generic cf instance layer, lane F2b: the drain's CUT relation, its
   recycle invariant and its byte premise at the cf instance, and the model half of the re-quarantine fields.
   rule 24: no function proved (kind: instance definitions and model-level facts of DMiface's drain cuts).

   cgif's drain fields take ARXr := ARX_cgif and DRq := RIx (DGif1dI.v, DGif1dr.DRq_cgif): cgif's Wf has no
   completeness clause, so AR survives the cuts.  The cf invariant Wf_cf adds wfc_compl0 (YG01cf.v:153), which a cut
   breaks: between Recycle's pop and the CacheDealloc that returns a batch object, that object is allocated in class
   kBatchClass but listed nowhere (DMiface.v:6-7).  So at the cf instance:
   - [ARmcfR] / [ARcfR]: YG0ncf.ARmcf / ARcf with YG03cf.WfR_cf (WfP_cf without wfc_compl0) for Wf_cf, every other field
     verbatim; [ARmcfR_of_ARmcf] / [ARmcf_of_ARmcfR] convert, the latter under Compl0;
   - [ARXr_cf B IOK Hp]: the cut relation, indexed as YGcfInstBase.ARX_cf: the instance predicate and ARcfR;
   - [DRq_cf B S its zs]: YG03cf.RIx_cf at the pending chunks [its] and batch objects [zs], the class-kBatchClass
     deficit those objects leave (cdef = class_size * |zs|, 0 elsewhere), the unqueued quarantine bytes bounded by the
     pending chunks' (unq_cf S <= items_n its), and qtight's two byte bounds;
   - [QB_cf NMAXD]: the drain entry's byte premise (DMspec / DMiface's QB): both caches together at most 2 ^ 31 bytes
     (DMiface.qview's qv_bytes), no unqueued quarantined bytes (qtight's third clause), and the split bounds: the
     thread cache at most kQuarantineCacheMax + kBatchBytes + NMAXD (it is over kQuarantineCacheMax at the drain) and
     the global cache at most kQuarantineMax.  NMAXD is the QUARANTINE-ENTRY bound: free_cf enqueues a block only when
     its size is at most kQuarantineMax (else it recycles at once), so every unit instantiates NMAXD := kQuarantineMax
     and meets [NMAXD <= 2 ^ 28]; it is NOT cf_malloc_max.  [QB_cf_intro] derives the joint bound from the split ones;
     [QB_cf_split_push] re-establishes the split ones after Enqueue's push from the two byte bounds at its pre-state and
     a pushed block within NMAXD; [QB_cf_enq_post] is the whole of QB_cf kQuarantineMax at Enqueue's post, from
     free_cf's guard (the pushed block's ck_n <= kQuarantineMax) and Enqueue's quar_n <= queued_n; [QB_cf_of_QB_w]
     takes lane F1's QB_w directly.
   Model facts: [drain_xfer_Wf_cf] (Wf_cf after the transfer, DMiface.drain_xfer), [drain_recyc_DRq_cf] (DRq_cf at
   Recycle's call of DoRecycle, DMiface.drain_recyc, over YG03cf / YG03dcf's merge and pop lemmas), [DRq_cf_end]
   (Wf_cf and qtight when nothing is pending), and the cut relation's ends [ARcfR_of_ARcf] / [ARcf_of_ARXr_end].
   Size bounds: only the Section variable NMAXD; batch counts are YGcfBatch.L24MAX_cf.  Image-free and event-free (no
   event-count term, no event regime and no event-keyed budget appears). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf YG03dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfBatch.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0l YGcfRoom YG08 YG08cf.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The cut record: YG0ncf.ARmcf (YG0ncf.v:130-214) with WfR_cf for Wf_cf.                                        *)
Section Y.
Variable B : asyms.
Variable ly : alayout.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The shadow at the cut (Main 06:3xZ, after a Theorem Labs lane measured bext_rq_cf FALSE as stated): a chunk that free marked
   CQuarantined but has not been enqueued (the big arm recycles it at once, PreQuarantine runs only on the enqueue
   side) carries its ALLOCATED shadow on the machine while the model already says shHeapFreed.  The cut relation
   therefore frees the VALUE of such a chunk's user granules and keeps only their PRESENCE (the machine's byte is
   there: a Theorem Labs lane's measurement reads 0).  Recycle writes the value, so no walk reads it (measured: the two readers
   under ARXr_cf, YGcfInstRcPrim.v:1138-1143 and :751-753, test presence only).  With nothing pending the two forms
   agree (shadow_ok_of_weak_cf below), so the relation's ends are unchanged. *)
Definition pending_cf (S : astate) (k : chunk) : Prop :=
In k (st_chunks S) /\ ck_state k = CQuarantined /\ ~ In (ck_beg k) (map ck_beg (q_items S)).

Definition pending_user_cf (S : astate) (g : Z) : Prop :=
exists k, pending_cf S k /\ ck_base B ly k + ck_rz k <= g < ck_base B ly k + ck_rz k + (ck_n k + 7) / 8 * 8.

Definition shadow_ok_weak_cf (Hp : list Z) (rd : reader) (S : astate) : Prop :=
forall g v, g mod 8 = 0 -> ashadow B ly S g = Some v ->
  rd (shadow_addr g) = Some (if in_head Hp g then shUserPoison else v) \/
  (pending_user_cf S g /\ rd (shadow_addr g) <> None).

Definition no_pending_cf (S : astate) : Prop :=
forall k, In k (st_chunks S) -> ck_state k = CQuarantined -> In (ck_beg k) (map ck_beg (q_items S)).

(* With the quarantine tight (quar_n <= queued_n) nothing is pending: a quarantined chunk off the queues would add
   its own bytes to the quarantined count, and every chunk's user size is at least one (req_size). *)
Lemma no_pending_of_tight_cf : forall U pp cc bb S, WfR_cf U pp cc bb S -> quar_n S <= queued_n S -> no_pending_cf S.
Proof.
intros U pp cc bb S W HT k Hk Hst.
destruct (In_dec YGcfRoom.sptr_eq_dec (ck_beg k) (map ck_beg (q_items S))) as [Hin|Hni]; [exact Hin|exfalso].
pose proof (wq_items _ (wfr_quarantine _ _ _ _ _ W)) as QI.
pose proof (wq_nodup _ (wfr_quarantine _ _ _ _ _ W)) as QN.
pose proof (wfr_chunks _ _ _ _ _ W) as CK.
assert (POS : forall x, In x (st_chunks S) -> 1 <= ck_n x).
{ intros x Hx. destruct (proj1 (Forall_forall _ _) CK x Hx) as [[R0 _] _].
  unfold ck_n, req_size. destruct (Z.eqb_spec (ck_req x) 0); lia. }
assert (SUB : incl (q_items S ++ [k]) (List.filter (fun x => negb (is_alloc x)) (st_chunks S))).
{ intros x Hx. apply List.filter_In. apply in_app_iff in Hx as [Hx|[<-|[]]].
  - destruct (proj1 (Forall_forall _ _) QI x Hx) as [Hin Hq]. split; [exact Hin|].
    unfold is_alloc. rewrite Hq. reflexivity.
  - split; [exact Hk|]. unfold is_alloc. rewrite Hst. reflexivity. }
assert (ND : List.NoDup (q_items S ++ [k])).
{ apply NoDup_app_iff. split; [exact (NoDup_map_inv _ _ QN)|]. split; [constructor; [intros []|constructor]|].
  intros x Hx [<-|[]]. apply Hni. apply in_map. exact Hx. }
assert (PF : Forall (fun x => 0 <= ck_n x) (List.filter (fun x => negb (is_alloc x)) (st_chunks S))).
{ apply Forall_forall. intros x Hx. apply List.filter_In in Hx as [Hx _]. pose proof (POS x Hx). lia. }
pose proof (YGcfRoom.items_n_incl (q_items S ++ [k]) _ ND SUB PF) as LE.
rewrite items_n_app in LE. cbn [items_n fold_right] in LE.
rewrite <- YGcfRoom.quar_nl_filter in LE.
pose proof (POS k Hk). unfold quar_n, queued_n in *. lia.
Qed.

Lemma shadow_weak_of_ok_cf : forall Hp rd S, shadow_ok_cf B ly Hp rd S -> shadow_ok_weak_cf Hp rd S.
Proof. intros Hp rd S H g v Hg Hv. left. exact (H g v Hg Hv). Qed.

Lemma shadow_ok_of_weak_cf : forall Hp rd S, no_pending_cf S -> shadow_ok_weak_cf Hp rd S ->
shadow_ok_cf B ly Hp rd S.
Proof.
intros Hp rd S NP H g v Hg Hv. destruct (H g v Hg Hv) as [HL|[(k & (Hk & Hst & Hni) & _) _]]; [exact HL|].
exfalso. exact (Hni (NP k Hk Hst)).
Qed.

(* The exemption set only shrinks when the queues lose items and the chunk list does not change, so the weak form
   transports along a step that moves the quarantine and keeps the governed shadow bytes. *)
Lemma shadow_weak_ext_cf : forall S S' Hp (rd rd' : reader),
st_chunks S' = st_chunks S ->
(forall b, In b (map ck_beg (q_items S')) -> In b (map ck_beg (q_items S))) ->
(forall g, ashadow B ly S' g = ashadow B ly S g) ->
(forall g v, g mod 8 = 0 -> ashadow B ly S g = Some v ->
   rd' (shadow_addr g) = rd (shadow_addr g)) ->
shadow_ok_weak_cf Hp rd S -> shadow_ok_weak_cf Hp rd' S'.
Proof.
intros S S' Hp rd rd' EC EQ EA AG H g v Hg Hv. rewrite EA in Hv.
rewrite (AG g v Hg Hv). destruct (H g v Hg Hv) as [HL|[(k & (Hk & Hst & Hni) & HR) HP]]; [left; exact HL|].
right. split; [|exact HP]. exists k. split; [|exact HR].
split; [rewrite EC; exact Hk|]. split; [exact Hst|]. intros Hin. exact (Hni (EQ _ Hin)).
Qed.

Lemma shadow_present_weak_cf : forall Hp rd S g v, shadow_ok_weak_cf Hp rd S -> g mod 8 = 0 ->
ashadow B ly S g = Some v -> rd (shadow_addr g) <> None.
Proof.
intros Hp rd S g v H Hg Hv. destruct (H g v Hg Hv) as [HL|[_ HP]]; [rewrite HL; discriminate | exact HP].
Qed.

Record ARmcfR (S : astate) (Hp : list Z) (rd : reader) : Prop := {
amr_wfr : WfR_cf (as_universe B) 0 0 0 S;
amr_universe : universe_ok (as_universe B);
amr_syms : asyms_ok B;
amr_layout : layout_ok ly;
amr_placed : sec_placed ly S;
amr_const : Forall (cell_holds B ly rd) (as_const B ly);
amr_const_owned : Forall (cell_owned B ly) (as_const B ly);
amr_cells : Forall (cell_holds B ly rd) (acells_cf B ly S);
amr_fa : fa_entries_ok ly rd S;
amr_flags : fs_flags_ok ly rd S;
amr_depot : depot_ok B ly rd S;
amr_shadow : shadow_ok_weak_cf Hp rd S;
amr_zshadow : zshadow_ok B ly rd;
amr_junk : Forall (range_vis B ly rd) (ajunk_cf B ly S);
amr_areas : Forall (range_vis B ly rd) (aareas S);
amr_client : Forall (range_vis B ly rd) (aclient S);
amr_zero : Forall (range_zero B ly rd) (ialloc_zero B);
amr_tsd : ly_tsd ly = as_tsd B;
amr_static_img : Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B);
amr_hp_live : Forall (fun p => exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\
  p = sptr_addr B ly (ck_user k) /\ cf_head <= ck_n k) Hp;
amr_xs_placed : xs_placed_cf ly S;
(* field round 2 (layer 91e2b229c0f): the two machine cells and the two unit rows their ownership needs live in the
   relation, so the walks' relations carry them instead of ARX_cf's conjuncts. *)
amr_exh_cell : exh_cell_cf B ly S rd;
amr_errb_cells : errb_cells_cf B ly S rd;
amr_cells_owned : EXH_OFF_t /\ errb_obj_owned_t B /\ errb_ial_apart_t B;
(* field round 3: Printf's two writable image cells and their ownership row (YG0ncf.v's amc_pf_cells / amc_pf_owned) *)
amr_pf_cells : pf_cells_cf B ly rd;
amr_pf_owned : pf_cells_owned_t B
}.

Lemma ARmcfR_of_ARmcf : forall S Hp rd, ARmcf B ly S Hp rd -> ARmcfR S Hp rd.
Proof.
intros S Hp rd M.
destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient
  Xzero Xtsd Ximg Xhp Xxs Xexh Xerrb Xown Xpf Xpfo].
constructor; try assumption; [exact (WfR_of_WfP_cf _ _ _ _ _ Xwf) | exact (shadow_weak_of_ok_cf Hp rd S Xshadow)].
Qed.

Lemma ARmcf_of_ARmcfR : forall S Hp rd, ARmcfR S Hp rd -> Compl0 S -> no_pending_cf S -> ARmcf B ly S Hp rd.
Proof.
intros S Hp rd M HC NP.
destruct M as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient
  Xzero Xtsd Ximg Xhp Xxs Xexh Xerrb Xown Xpf Xpfo].
constructor; try assumption; [exact (WfP_of_WfR_cf _ _ _ _ _ Xwf HC) | exact (shadow_ok_of_weak_cf Hp rd S NP Xshadow)].
Qed.
End Y.

Section A0.
Variable segs : list Segment.
Variable B : asyms.
Variable ly : alayout.
(* YG0ncf.ARcf (YG0ncf.v:520-522) over ARmcfR. *)
Definition ARcfR (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model) : Prop :=
ARmcfR B ly S Hp (aview segs (w_H W) mem) /\ ALedger_cf segs ly S md /\ abudget_ok_cf segs ly S W /\ amwf md
/\ ahs B ly S (w_H W) mem.

Lemma ARcfR_of_ARcf : forall S Hp W mem md, ARcf segs B ly S Hp W mem md -> ARcfR S Hp W mem md.
Proof.
intros S Hp W mem md (M & L & BU & MW & HS). split; [exact (ARmcfR_of_ARmcf B ly S Hp _ M)|].
exact (conj L (conj BU (conj MW HS))).
Qed.

Lemma ARcf_of_ARcfR : forall S Hp W mem md, ARcfR S Hp W mem md -> Compl0 S -> no_pending_cf S ->
ARcf segs B ly S Hp W mem md.
Proof.
intros S Hp W mem md (M & L & BU & MW & HS) HC NP. split; [exact (ARmcf_of_ARmcfR B ly S Hp _ M HC NP)|].
exact (conj L (conj BU (conj MW HS))).
Qed.
End A0.



(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The instance's cut relation, recycle invariant and drain byte premise.                                        *)
Section I. Context {IM : AImg}.
Variable B : asyms.
(* NMAXD is a PARAMETER of the contract, not kQuarantineMax (Main, 2026-10-30, after a Theorem Labs lane measured the big
   arm): the small arm instantiates it at the quarantine's entry bound, the big arm at the unit's malloc limit,
   since free_cf recycles an over-cap chunk at once instead of enqueuing it. *)
Definition DRq_cf (NMAXD : Z) (S : astate) (its : list chunk) (zs : list Z) : Prop :=
RIx_cf (as_universe B) 0 0 0 S its [] zs /\
(forall c, 1 <= c <= 31 -> cdef S c = (if c =? kBatchClass then class_size kBatchClass * Z.of_nat (length zs) else 0)) /\
unq_cf S <= items_n its /\
qc_bytes (st_qthread S) <= kQuarantineCacheMax /\ qc_bytes (st_qglobal S) <= kQuarantineMax /\
(* the pending items' sizes: on the small arm each was a queued item (YG01cf.wfc_qsize), and the pop and the
   recycles only drop them; on the big arm the one item is the unit's malloc limit *)
Forall (fun k => ck_n k <= NMAXD) its /\
(* the pending items' bytes: they left a quarantine whose two queues held at most 2 ^ 31 bytes together (QB_cf's
   first conjunct, :246), so the cut's quarantined count exceeds its queued count by at most that much - the
   allowance of AbudgetRestate's qloose_cut (YGcfRoomCf.room_rec_cf_of_cut) *)
items_n its <= 2 ^ 31 /\
(* the caches are inited, where that is read: CacheDealloc runs only for a PRIMARY chunk, and a primary chunk is
   only reached after a primary allocation, which runs init_cache_if_needed (YG00.v:339 / :465).  The small arm
   has the flag outright (the drain runs with a non-empty thread queue, wfr_qinited); the big arm's single item
   is secondary, so the guard is vacuous there (a Theorem Labs lane: st_cache_inited (qx ..) = st_cache_inited S). *)
(((exists k, In k its /\ from_primary (ck_req k) = true) \/ zs <> []) -> st_cache_inited S = true) /\
(* the unit's secondary admission (Main 2026-10-30): from QB_cf at the drain's entry; the cut, CacheDealloc and
   Recycle keep every entry's sm_len / sm_size, so the two meters nsec_cf / sec_T_cf are unchanged (cf_hull_counts) *)
cf_hull_ok S.

(* NMAXD: the quarantine-entry bound (free_cf enqueues a block only when its size is at most kQuarantineMax; else it
   recycles at once).  A Section variable so that a consumer may state its own premise on it; every unit instantiates
   it at kQuarantineMax, which meets NMAXD <= 2 ^ 28. *)
Section QBs.
Variable NMAXD : Z.

Definition QB_cf (X : astate) : Prop :=
qc_bytes (st_qthread X) + qc_bytes (st_qglobal X) <= 2 ^ 31 /\ quar_n X <= queued_n X /\
qc_bytes (st_qthread X) <= kQuarantineCacheMax + kBatchBytes + NMAXD /\ qc_bytes (st_qglobal X) <= kQuarantineMax /\
(* the unit's secondary admission at the drain's entry (Main 2026-10-30): the free's push carries it from the call's
   acall_pre_cf by cf_hull_counts, and the drain keeps it in DRq_cf *)
cf_hull_ok X.

(* The split bounds give the joint one when NMAXD <= 2 ^ 28 (kQuarantineMax meets it). *)
Lemma QB_cf_intro : forall X, NMAXD <= 2 ^ 28 -> quar_n X <= queued_n X ->
qc_bytes (st_qthread X) <= kQuarantineCacheMax + kBatchBytes + NMAXD -> qc_bytes (st_qglobal X) <= kQuarantineMax ->
cf_hull_ok X -> QB_cf X.
Proof.
intros X HN HQ H1 H2 HH. unfold QB_cf, kQuarantineCacheMax, kBatchBytes, kQuarantineMax in *.
split; [lia|]. split; [exact HQ|]. split; [lia|]. split; [lia | exact HH].
Qed.

(* Both split bounds hold after Enqueue's push, from the two byte bounds before it (qtight's first two clauses; NOT
   qtight itself, whose quar_n clause is false at Enqueue's pre-state, where the chunk is quarantined but not yet
   queued), when the pushed block is within the entry bound. *)
Lemma QB_cf_split_push : forall S0 X k nb,
qc_bytes (st_qthread S0) <= kQuarantineCacheMax -> qc_bytes (st_qglobal S0) <= kQuarantineMax -> ck_n k <= NMAXD ->
st_qthread X = qc_push (st_qthread S0) k nb -> st_qglobal X = st_qglobal S0 ->
qc_bytes (st_qthread X) <= kQuarantineCacheMax + kBatchBytes + NMAXD /\ qc_bytes (st_qglobal X) <= kQuarantineMax.
Proof.
intros S0 X k nb T1 T2 HK E1 E2. rewrite E1, E2. split; [|exact T2].
destruct nb as [b|]; cbn [qc_push qc_bytes]; unfold kBatchBytes in *; lia.
Qed.
End QBs.

Lemma kQuarantineMax_entry : kQuarantineMax <= 2 ^ 28. Proof. unfold kQuarantineMax. lia. Qed.

(* QB_cf at Enqueue's post (DGif0.v:329's QB), PROVED from free_cf's guard: the pushed block has
   ck_n k <= kQuarantineMax (free_cf's enqueue arm, Put's inclusive test), the two caches were within their bounds at
   Enqueue's pre-state (lane F1's EP_cf), Enqueue pushed exactly that block onto the thread cache and left the global
   cache alone (DGif0.v:322 / :324), and Enqueue's post keeps quar_n <= queued_n (lane F1's YGcfInstEnq.QB_w). *)
Lemma QB_cf_enq_post : forall S0 X k nb,
qc_bytes (st_qthread S0) <= kQuarantineCacheMax -> qc_bytes (st_qglobal S0) <= kQuarantineMax -> ck_n k <= kQuarantineMax ->
st_qthread X = qc_push (st_qthread S0) k nb -> st_qglobal X = st_qglobal S0 -> quar_n X <= queued_n X ->
cf_hull_ok X -> QB_cf kQuarantineMax X.
Proof.
intros S0 X k nb T1 T2 HK E1 E2 HQ HH.
destruct (QB_cf_split_push kQuarantineMax S0 X k nb T1 T2 HK E1 E2) as [H1 H2].
exact (QB_cf_intro kQuarantineMax X kQuarantineMax_entry HQ H1 H2 HH).
Qed.

(* Lane F1's QB_w (YGcfInstEnq.v, thread bound kQuarantineCacheMax + kQuarantineMax + kBatchBytes) gives QB_cf. *)
Lemma QB_cf_of_QB_w : forall X,
qc_bytes (st_qthread X) <= kQuarantineCacheMax + kQuarantineMax + kBatchBytes -> qc_bytes (st_qglobal X) <= kQuarantineMax ->
quar_n X <= queued_n X -> cf_hull_ok X -> QB_cf kQuarantineMax X.
Proof. intros X H1 H2 HQ HH. apply (QB_cf_intro kQuarantineMax X kQuarantineMax_entry HQ); [lia | exact H2 | exact HH]. Qed.

(* Within the drain, the cut invariant DRq_cf carries the tight bounds (YGcfInstDrainR.DRq_cf); at the drain's end
   DRq_cf_end gives qtight, whose byte clauses are the next call's start for QB_cf_split_push. *)

(* The batch bound of the drain premise, from the invariant (YGcfBatch.batches_bound_cf). *)
Lemma L24_of_Wf_cf : forall S, Wf_cf (as_universe B) S -> Z.of_nat (length (all_batches S)) <= L24MAX_cf.
Proof. intros S W. exact (batches_bound_cf _ _ _ _ S W). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The model at the drain's cuts.                                                                                *)
Ltac qk := unfold kQuarantineCacheMax, kQuarantineMax, kQuarantineMin in *.

Lemma RIx_cf_flat : forall U pp cc bb s P, RIx_cf U pp cc bb s [] P [] -> RIx_cf U pp cc bb s (flat_map b_items P) [] (map b_self P).
Proof.
intros U pp cc bb s P (W & IT & ND & BL & SF & NDS). unfold RIx_cf. cbn [app flat_map map] in *.
rewrite !app_nil_r. split; [exact W|]. split; [exact IT|]. split; [exact ND|]. split; [constructor|].
split; [exact SF | exact NDS].
Qed.

(* The cut after the transfer (Drain returns without recycling): the invariant holds whole. *)
Lemma drain_xfer_Wf_cf : forall U X S', Wf_cf U X -> kQuarantineCacheMax < qc_bytes (st_qthread X) -> drain_xfer X S' ->
Wf_cf U S'.
Proof.
intros U X S' W HT (_ & ->). unfold YFeuC.transfer_g.
pose proof (WfR_transfer_cf U 0 0 0 X (WfR_of_WfP_cf _ _ _ _ _ W) HT) as WT. cbv zeta in WT.
apply WfP_of_WfR_cf; [exact WT|]. intros c Hc.
pose proof (xfr_cdef_cf _ _ _ (xfr_transfer_cf X) c Hc) as E. rewrite (wfc_compl0 _ _ _ _ _ W c Hc) in E. lia.
Qed.

(* The cut at Recycle's call of DoRecycle: the recycle invariant at the temp list [P]. *)
(* The cut's queues only LOSE items: the transfer moves the thread's batches to the global queue, the merge keeps
   every item (mres_cf's first clause) and the pop drops a prefix.  The shadow's exemption set reads this. *)
Lemma drain_xfer_q_sub_cf : forall X S', drain_xfer X S' ->
forall b, In b (map ck_beg (q_items S')) -> In b (map ck_beg (q_items X)).
Proof.
intros X S' (_ & ->) b Hb. unfold q_items, all_batches, YFeuC.transfer_g in *.
cbn [qc_list st_qthread st_qglobal set_qglobal set_qthread qc0 app] in Hb.
rewrite flat_map_app, map_app, in_app_iff in Hb. rewrite flat_map_app, map_app, in_app_iff. tauto.
Qed.

Lemma drain_recyc_q_sub_cf : forall X S' P, drain_recyc X S' P ->
forall b, In b (map ck_beg (q_items S')) -> In b (map ck_beg (q_items X)).
Proof.
intros X S' P (_ & gm & ex & g' & popped & EM & EP & -> & _) b Hb.
pose proof (merge_choice_mres_cf _ _ _ EM) as (M1 & _).
apply pop_batches_spec_cf in EP as (P0 & _ & EL & _).
unfold q_items, all_batches in Hb |- *.
cbn [qc_list st_qthread st_qglobal set_qglobal set_qthread qc0 app] in Hb.
assert (SUB : In b (map ck_beg (flat_map b_items (qc_list gm)))).
{ rewrite EL, flat_map_app, map_app, in_app_iff. right. exact Hb. }
rewrite M1 in SUB. unfold YFeuC.transfer_g in SUB.
cbn [qc_list st_qthread st_qglobal] in SUB.
rewrite flat_map_app, map_app, in_app_iff in SUB. rewrite flat_map_app, map_app, in_app_iff. tauto.
Qed.

Lemma drain_recyc_DRq_cf : forall X S' P,
Wf_cf (as_universe B) X -> quar_n X <= queued_n X -> kQuarantineCacheMax < qc_bytes (st_qthread X) ->
qc_bytes (st_qthread X) + qc_bytes (st_qglobal X) <= 2 ^ 31 -> cf_hull_ok X ->
drain_recyc X S' P -> DRq_cf kQuarantineMax S' (flat_map b_items P) (map b_self P).
Proof.
intros X S' P W HQ HT HJ HH (_ & gm & ex & g' & popped & EM & EP & -> & ->).
pose proof (WfR_transfer_cf (as_universe B) 0 0 0 X (WfR_of_WfP_cf _ _ _ _ _ W) HT) as WT. cbv zeta in WT.
set (sT := set_qglobal _ (set_qthread qc0 X)) in WT.
assert (EMC : merge_choice_cf (st_qglobal sT) = (gm, ex)) by exact EM.
pose proof (merge_choice_mres_cf _ _ _ EMC) as MR. pose proof MR as (M1 & M2 & M3 & M4 & M5 & M6).
pose proof (RI_merge_cf (as_universe B) 0 0 0 sT gm ex WT MR) as RIM.
pose proof EP as EP0. apply pop_batches_spec_cf in EP as (P0 & Epop & EL & EB). cbn [rev app] in Epop. subst popped.
destruct g' as [gl gb]. cbn [qc_list qc_bytes] in EL, EB.
pose proof (RI_pop_cf (as_universe B) 0 0 0 (set_qglobal gm sT) P0 gl (proj1 RIM) EL) as RIP.
pose proof (RIx_merge_pop_cf (as_universe B) 0 0 0 (set_qglobal gm sT) ex P0 gl _ RIM M3 EL RIP) as RX.
set (S1 := set_qglobal (mkQC gl gb) (set_qthread qc0 X)).
assert (ES : set_qglobal (mkQC gl (qc_bytes (st_qglobal (set_qglobal gm sT)) - sum_bytes P0)) (set_qglobal gm sT) = S1)
  by (unfold S1; rewrite EB; reflexivity).
rewrite ES in RX.
assert (ES2 : set_qglobal (mkQC gl gb) (set_qglobal gm sT) = S1) by reflexivity.
pose proof (xfr_transfer_cf X) as XFT. fold sT in XFT.
pose proof (xfr_merge_cf sT gm ex MR) as XFM.
pose proof (xfr_pop_cf (set_qglobal gm sT) P0 gl gb EL) as XFP. rewrite ES2 in XFP.
pose proof (unq_transfer_cf X) as UQT. fold sT in UQT.
pose proof (unq_merge_cf sT gm M1) as UQM.
pose proof (unq_pop_cf (set_qglobal gm sT) P0 gl gb EL) as UQP. rewrite ES2 in UQP.
pose proof (flat_items_empty_cf ex M3) as FE.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
- exact (RIx_cf_flat _ _ _ _ _ _ RX).
- intros c Hc.
  assert (XF : xfr_cf X S1 (fun c' => if c' =? kBatchClass then - Z.of_nat (length (ex ++ P0)) else 0)).
  { eapply xfr_trans_cf; [exact XFT | eapply xfr_trans_cf; [exact XFM | exact XFP | intros; reflexivity] |].
    intros c' _. cbn beta. rewrite length_app, Nat2Z.inj_add. destruct (c' =? kBatchClass); lia. }
  rewrite (xfr_cdef_cf _ _ _ XF c Hc), (wfc_compl0 _ _ _ _ _ W c Hc), length_map. cbn beta.
  destruct (Z.eqb_spec c kBatchClass) as [->|Hne]; [ring | lia].
- rewrite UQP, UQM, UQT, flat_map_app, FE. cbn [app]. unfold unq_cf in *. lia.
- unfold S1. cbn [st_qthread set_qglobal set_qthread qc_bytes qc0]. qk. lia.
- unfold S1. cbn [st_qglobal set_qglobal qc_bytes].
  destruct (pop_batches_stop_cf _ _ _ _ _ EP0 (Nat.lt_succ_diag_r _)) as [Hmin|Hnil].
  + cbn [qc_bytes] in Hmin. qk. lia.
  + cbn [qc_list] in Hnil. subst gl. rewrite app_nil_r in EL.
    pose proof (wq_bytes_g _ (wfr_quarantine _ _ _ _ _ WT)) as QB. fold sT in QB.
    rewrite EB, <- EL, M4, QB. qk. lia.
- (* the sizes: the popped items are items of the merged queue, before the pop, whose wfr_qsize bounds them *)
  pose proof (wfr_qsize _ _ _ _ _ (proj1 RIM)) as QS.
  unfold q_items, all_batches in QS. cbn [st_qthread st_qglobal set_qglobal set_qthread qc_list qc0] in QS.
  rewrite flat_map_app, FE. cbn [app].
  rewrite EL in QS. rewrite !flat_map_app, ?Forall_app in QS. tauto.
- (* the pending bytes: the popped items are a prefix of the merged queue, whose items are the entry's queued items,
     and those are bounded by the two queues' bytes (YG08.sum_bytes_items), i.e. by QB_cf's joint bound *)
  rewrite flat_map_app, FE. cbn [app].
  pose proof (wfc_quarantine _ _ _ _ _ W) as WQ.
  assert (QX : queued_n X <= qc_bytes (st_qthread X) + qc_bytes (st_qglobal X)).
  { rewrite (wq_bytes_t _ WQ), (wq_bytes_g _ WQ), !YG08.sum_bytes_items.
    unfold queued_n, q_items, all_batches. rewrite flat_map_app, items_n_app. unfold kBatchBytes. lia. }
  pose proof (proj1 RIP) as WP. pose proof (wq_items _ (wfr_quarantine _ _ _ _ _ WP)) as IP.
  pose proof (wfr_chunks _ _ _ _ _ WP) as CKP.
  assert (GL0 : 0 <= items_n (flat_map b_items gl)).
  { apply YGcfRoom.items_n_nonneg. apply Forall_forall. intros x Hx.
    assert (Hq : In x (q_items (set_qglobal (mkQC gl (qc_bytes (st_qglobal (set_qglobal gm sT)) - sum_bytes P0)) (set_qglobal gm sT)))).
    { unfold q_items, all_batches. cbn [st_qthread st_qglobal set_qglobal set_qthread qc_list qc0 sT app]. exact Hx. }
    destruct (proj1 (Forall_forall _ _) IP x Hq) as [Hin _].
    destruct (proj1 (Forall_forall _ _) CKP x Hin) as [[R0 _] _].
    unfold ck_n, req_size. destruct (Z.eqb_spec (ck_req x) 0); lia. }
  assert (IGM : items_n (flat_map b_items (qc_list gm)) = queued_n X).
  { rewrite M1. unfold sT, YFeuC.transfer_g, queued_n, q_items, all_batches.
    cbn [qc_list st_qglobal set_qglobal set_qthread]. rewrite !flat_map_app, !items_n_app. lia. }
  rewrite EL, flat_map_app, items_n_app in IGM. lia.
- (* the caches are inited: the thread queue is over its cap, so it holds a batch, so wfr_qinited applies *)
  intros _. assert (AB : all_batches X <> []).
  { unfold all_batches. intros E. apply app_eq_nil in E as [E _].
    pose proof (wq_bytes_t _ (wfc_quarantine _ _ _ _ _ W)) as BT.
    clear - E BT HT. rewrite E in BT. unfold sum_bytes in BT. cbn [fold_right] in BT. unfold kQuarantineCacheMax in HT. lia. }
  pose proof (wfc_qinited _ _ _ _ _ W AB) as CI. unfold S1. cbn [st_cache_inited set_qglobal set_qthread]. exact CI.
- (* the admission: the cut moves only the queues, so both meters are the entry's *)
  apply (cf_hull_counts _ X); [reflexivity | reflexivity | exact HH].
Qed.

(* Nothing pending: the invariant is whole again, and the quarantine is tight. *)
Lemma DRq_cf_end : forall NMAXD S, DRq_cf NMAXD S [] [] -> Wf_cf (as_universe B) S /\ qtight S.
Proof.
intros NMAXD S (RX & CD & UQ & Q1 & Q2 & _ & _ & _ & _). split.
- apply WfP_of_WfR_cf; [exact (proj1 RX)|]. intros c Hc. rewrite (CD c Hc). cbn [length]. destruct (c =? kBatchClass); lia.
- unfold qtight. split; [exact Q1|]. split; [exact Q2|]. unfold unq_cf in UQ. cbn [items_n fold_right] in UQ. lia.
Qed.

(* The pending items' sizes, for the walks' size premises (DMwalkIF.drq_sizes / nmaxd_ok / lmaxd_ok), stated in
   their unfolded form (the layer imports no walk file) and PARAMETRIC in the contract's bound: the small arm
   takes the quarantine's entry bound, the big arm the unit's malloc limit (Main, 2026-10-30).  The extent bound
   needs only that the bound is past the primary cap, since a primary chunk's class is at most twice kMaxSize and
   a secondary chunk's map grows with its request (sec_map_size_mono_cf). *)
Lemma rz_log_bounds_cf : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.

Lemma rz_log_mono_cf : forall m n, m <= n -> rz_log m <= rz_log n.
Proof.
intros m n H. unfold rz_log.
repeat match goal with |- context [if (?a <=? ?b) then _ else _] => destruct (Z.leb_spec a b) end; lia.
Qed.

Lemma rz_size_mono_cf : forall m n, 0 <= m <= n -> rz_size m <= rz_size n.
Proof.
intros m n H. unfold rz_size.
pose proof (rz_log_bounds_cf m) as [M0 _]. pose proof (rz_log_bounds_cf n) as [N0 _].
rewrite !Z.shiftl_mul_pow2 by assumption.
apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; [lia | apply rz_log_mono_cf; lia].
Qed.

Lemma needed_size_mono_cf : forall m n, 0 <= m <= n -> needed_size m <= needed_size n.
Proof.
intros m n H. pose proof (rz_size_mono_cf m n H) as RZ.
pose proof (rz_size_bounds m) as [RM _]. pose proof (rz_size_bounds n) as [RN _].
assert (RU : rounded_size m <= rounded_size n).
{ unfold rounded_size, round_up. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
unfold needed_size, needed_primary in *.
destruct (from_primary m) eqn:FM; destruct (from_primary n) eqn:FN; try lia;
  unfold from_primary, needed_primary in FM, FN;
  repeat match goal with
  | E : (_ <=? _) = true |- _ => apply Z.leb_le in E
  | E : (_ <=? _) = false |- _ => apply Z.leb_gt in E
  end; lia.
Qed.

Lemma sec_map_size_mono_cf : forall m n, 0 <= m <= n -> sec_map_size m <= sec_map_size n.
Proof.
intros m n H. unfold sec_map_size, round_up.
pose proof (needed_size_mono_cf m n H) as NS.
assert (DV : (needed_size m + kPage - 1) / kPage <= (needed_size n + kPage - 1) / kPage)
  by (apply Z.div_le_mono; [unfold kPage; lia | lia]).
pose proof (Z.mul_le_mono_nonneg_r _ _ kPage ltac:(unfold kPage; lia) DV). lia.
Qed.

Lemma sec_map_size_ge_cf : forall n, 0 <= n -> n <= sec_map_size n.
Proof.
intros n Hn. unfold sec_map_size.
pose proof (needed_primary_bounds n Hn) as (NB1 & _ & _). pose proof (rz_size_bounds n) as [RZ _].
pose proof (round_up_ge (needed_size n) kPage ltac:(unfold kPage; lia)) as [[G1 _] _].
unfold needed_size, req_size in *. destruct (from_primary n); destruct (Z.eqb_spec n 0); unfold kPage in *; lia.
Qed.

Definition NMAXD_cf : Z := kQuarantineMax + 1.
Definition LMAXD_cf : Z := sec_map_size kQuarantineMax.
(* The big arm's bound: the unit's malloc limit, which cf_malloc_max_bound caps at 2 ^ 30 - 15. *)
Definition NMAXD_big_cf : Z := cf_malloc_max.
Definition LMAXD_big_cf : Z := sec_map_size cf_malloc_max.
(* The batch class's allocated bound (DMwalkIF.rmaxd_ok): the class's free array begins at kFreeArrayOffset, so no
   user byte of the class lies above it (DMwalkIF.v:304-308). *)
Definition RMAXD_cf : Z := kFreeArrayOffset.

Lemma rmaxd_ok_cf : 2 ^ 31 <= RMAXD_cf <= kFreeArrayOffset.
Proof. unfold RMAXD_cf, kFreeArrayOffset. lia. Qed.

Lemma nmaxd_ok_cf : 2 ^ 28 <= NMAXD_cf <= 2 ^ 30.
Proof. unfold NMAXD_cf, kQuarantineMax. lia. Qed.

Lemma lmaxd_ok_cf : NMAXD_cf <= LMAXD_cf <= 2 ^ 31 - 8192.
Proof. unfold NMAXD_cf, LMAXD_cf. vm_compute. split; discriminate. Qed.

(* The big arm's bounds: NMAXD_big_cf is the unit's malloc limit (cf_malloc_max_bound caps it at 2 ^ 30 - 15), and
   its mapped extent is one secondary map of that request, inside WalkB1's raised cap (DMwalkIF.v:417). *)
Lemma nmaxd_ok_big_cf : 2 ^ 28 <= NMAXD_big_cf -> NMAXD_big_cf <= 2 ^ 30.
Proof. intros H. unfold NMAXD_big_cf in *. pose proof YG08cf.cf_malloc_max_bound as MB. assert (2 ^ 30 = 1073741824) by reflexivity. lia. Qed.

Lemma lmaxd_ok_big_cf : NMAXD_big_cf <= LMAXD_big_cf <= 2 ^ 31 - 8192.
Proof.
unfold NMAXD_big_cf, LMAXD_big_cf. pose proof YG08cf.cf_malloc_max_bound as MB. pose proof cf_malloc_max_pos as MP.
assert (P20 : 2 ^ 20 = 1048576) by reflexivity. assert (P30 : 2 ^ 30 = 1073741824) by reflexivity.
assert (M0 : 0 <= cf_malloc_max) by lia. assert (M1 : cf_malloc_max <= 2 ^ 30) by lia.
pose proof (sec_map_size_ge_cf cf_malloc_max M0) as GE.
pose proof (sec_map_size_mono_cf cf_malloc_max (2 ^ 30) (conj M0 M1)) as MO.
assert (SM : sec_map_size (2 ^ 30) <= 2 ^ 31 - 8192) by (vm_compute; discriminate). lia.
Qed.

Lemma drq_sizes_cf : forall NMAXD, 2 * kMaxSize + 96 <= NMAXD ->
forall S its zs k, DRq_cf NMAXD S its zs -> In k its ->
0 <= ck_n k < NMAXD + 1 /\ ck_extent k <= sec_map_size NMAXD.
Proof.
intros NMAXD HN S its zs k (RX & _ & _ & _ & _ & SZ & _ & _ & _) Hk.
pose proof (proj1 (Forall_forall _ _) SZ k Hk) as Hn.
destruct RX as (W & IT & _).
destruct (proj1 (Forall_forall _ _) IT k ltac:(apply in_app_iff; left; exact Hk)) as [Hin _].
destruct (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ W) k Hin) as [[R0 _] _].
assert (Hr : ck_req k <= NMAXD)
  by (unfold ck_n, req_size in Hn; destruct (Z.eqb_spec (ck_req k) 0); unfold kMaxSize in *; lia).
split; [unfold ck_n, req_size in *; destruct (Z.eqb_spec (ck_req k) 0); lia|].
unfold ck_extent. destruct (from_primary (ck_req k)) eqn:FP.
- (* a primary chunk's class is at most twice the primary cap, and the bound is past it *)
  pose proof (YG0l.class_weight_bound (ck_req k) R0 FP) as CW.
  pose proof (needed_primary_bounds (ck_req k) R0) as (NB1 & _ & _).
  pose proof (sec_map_size_ge_cf NMAXD ltac:(unfold kMaxSize in *; lia)) as GE.
  pose proof (rz_size_bounds (ck_req k)) as [RZ _].
  unfold from_primary in FP. apply Z.leb_le in FP. unfold req_size in NB1.
  destruct (Z.eqb_spec (ck_req k) 0); unfold kMaxSize in *; lia.
- (* a secondary chunk's map grows with its request *)
  pose proof (sec_map_size_mono_cf (ck_req k) NMAXD ltac:(lia)) as MO.
  unfold kPage in *. lia.
Qed.
Section Ir.
(* the unit's instance object, as YGcfInstBase.ARX_cf takes it *)
Variable IOK : Z -> Prop.

(* Indexed and shaped as YGcfInstBase.ARX_cf (:90-93): its third conjunct, the errbuf is mapped (YGcfXs.xs_mapped_cf),
   reads only the secondaries and the model's maps, so the drain's cuts keep it; its fourth and fifth, the per-class
   exhausted bytes and the error-message buffer's object (YGcfInstBase.exh_cell_cf / errb_cells_cf), read cells no
   drain step writes (each walk's post keeps them with YGcfInstBase.exh_cell_cf_frame / errb_cells_cf_frame). *)
Definition ARXr_cf : list Z -> Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop :=
fun Hp inst ly S W mem md => IOK inst /\ ARcfR im_segs B ly S Hp W mem md /\ xs_mapped_cf ly S md.

Lemma ARXr_cf_iok : forall Hp inst ly S W mem md, ARXr_cf Hp inst ly S W mem md -> IOK inst.
Proof. intros Hp inst ly S W mem md H. exact (proj1 H). Qed.
Lemma ARXr_cf_ARcfR : forall Hp inst ly S W mem md, ARXr_cf Hp inst ly S W mem md -> ARcfR im_segs B ly S Hp W mem md.
Proof. intros Hp inst ly S W mem md H. exact (proj1 (proj2 H)). Qed.
Lemma ARXr_cf_xsm : forall Hp inst ly S W mem md, ARXr_cf Hp inst ly S W mem md -> xs_mapped_cf ly S md.
Proof. intros Hp inst ly S W mem md H. exact (proj2 (proj2 H)). Qed.
(* the cells are the relation's own fields now (field round 2) *)
Lemma ARXr_cf_exh : forall Hp inst ly S W mem md, ARXr_cf Hp inst ly S W mem md ->
exh_cell_cf B ly S (aview im_segs (w_H W) mem).
Proof. intros Hp inst ly S W mem md (_ & HA & _). exact (amr_exh_cell _ _ _ _ _ (proj1 HA)). Qed.
Lemma ARXr_cf_errb : forall Hp inst ly S W mem md, ARXr_cf Hp inst ly S W mem md ->
errb_cells_cf B ly S (aview im_segs (w_H W) mem).
Proof. intros Hp inst ly S W mem md (_ & HA & _). exact (amr_errb_cells _ _ _ _ _ (proj1 HA)). Qed.
(* H3's rd_img (DMcdR.v:98-100 @ ec7e5fd0be9) at ARXr := ARXr_cf: the image's constant cells hold at the cut. *)
Lemma rd_img_cf : forall Hp inst ly S W mem md, ARXr_cf Hp inst ly S W mem md ->
Forall (cell_holds B ly (aview im_segs (w_H W) mem)) (as_const B ly).
Proof. intros Hp inst ly S W mem md H. exact (amr_const _ _ _ _ _ (proj1 (ARXr_cf_ARcfR Hp inst ly S W mem md H))). Qed.
Lemma ARXr_cf_wfr : forall Hp inst ly S W mem md, ARXr_cf Hp inst ly S W mem md -> WfR_cf (as_universe B) 0 0 0 S.
Proof. intros Hp inst ly S W mem md (_ & M & _). exact (amr_wfr _ _ _ _ _ (proj1 M)). Qed.

(* The cut relation's ends: it holds of the relation's states, and gives ARcf back when nothing is pending. *)
Lemma ARXr_cf_intro : forall Hp inst ly S W mem md, IOK inst -> ARcf im_segs B ly S Hp W mem md -> xs_mapped_cf ly S md ->
ARXr_cf Hp inst ly S W mem md.
Proof.
intros Hp inst ly S W mem md HI HA HX.
exact (conj HI (conj (ARcfR_of_ARcf im_segs B ly S Hp W mem md HA) HX)).
Qed.
Lemma ARXr_cf_of_ARX_cf : forall Hp inst ly S W mem md, ARX_cf B IOK Hp inst ly S W mem md -> ARXr_cf Hp inst ly S W mem md.
Proof.
intros Hp inst ly S W mem md (HI & HA & HX). exact (ARXr_cf_intro Hp inst ly S W mem md HI HA HX).
Qed.

Lemma ARcf_of_ARXr_end : forall Hp inst ly S W mem md NMAXD, ARXr_cf Hp inst ly S W mem md -> DRq_cf NMAXD S [] [] ->
IOK inst /\ ARcf im_segs B ly S Hp W mem md /\ xs_mapped_cf ly S md /\ qtight S.
Proof.
intros Hp inst ly S W mem md NMAXD (HI & HA & HX) HD. destruct (DRq_cf_end NMAXD S HD) as [W0 QT].
split; [exact HI|]. split; [|exact (conj HX QT)].
(* nothing pending at the end: the quarantine is tight (qtight's third clause) *)
pose proof (no_pending_of_tight_cf _ _ _ _ S (amr_wfr _ _ _ _ _ (proj1 HA)) (proj2 (proj2 QT))) as NP.
exact (ARcf_of_ARcfR im_segs B ly S Hp W mem md HA (wfc_compl0 _ _ _ _ _ W0) NP).
Qed.

(* The same end, as the walk's relation: ARX_cf and the tight quarantine. *)
Lemma ARX_cf_of_ARXr_end : forall Hp inst ly S W mem md NMAXD, ARXr_cf Hp inst ly S W mem md -> DRq_cf NMAXD S [] [] ->
ARX_cf B IOK Hp inst ly S W mem md /\ qtight S.
Proof.
intros Hp inst ly S W mem md NMAXD H HD. destruct (ARcf_of_ARXr_end Hp inst ly S W mem md NMAXD H HD) as (HI & HA & HX & QT).
exact (conj (conj HI (conj HA HX)) QT).
Qed.
End Ir.
End I.

End U.
