(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfRoomCf.v at commit fec7cbb6287c (the cf layer of record, field rounds 1 + 2), module paths changed; the preset-side hunks kept on top are listed in the round6f report. *)
(* Modified by Theorem Labs, 2026-10-30: taken by path from proofs/cgif/cgif_file_fuzzer/lib/YGcfRoomCf.v at commit d0377850faab (the cf layer of record, field round 3 + the hull round + pf_ial_apart_t), module paths changed; the preset-side hunks kept on top are listed in the round6g report. *)
(* Theorem Labs, 2026-10-30: the cf room (the room half of the abudget restatement, Main's decisions of record
   2026-10-30, room choice (a), and the kit form of the allowance, Main 05:0xZ from a Theorem Labs lane's measurement). The
   definitions it reads are YG0ncf.v's (eager_cf, abudget_cf, ALedger_cf) and YGcfAbudget.v's (CF_HEAD); the hull term
   cf_hull, its cap CF_HULL_MAX and cf_hull_ok are YGcfNames.v's.
   The room of record is  E_BASE + eager_cf ly S md + abudget_kit_cf S + CF_HEAD <= ASAN_VM_LMIN  (room_rec_cf), where
   abudget_kit_cf is abudget_cf with its primary term (prim_committed + its shadow) and its pointer-array term
   (8 * st_sec_reserved) REPLACED by the kit's whole reservations PRIM_SPACE_cf / PTR_SPACE_cf (a Theorem Labs lane's Cker form).
   It bounds the REAL backing (Main 04:3xZ): vm_backing_used md is eager_used md plus the materialized lazy pages
   (YK04.vm_backing_used_split), eager_used md is bounded by the ledger's alc_eager_x, and the materialized pages are
   bounded by the CANONICAL lazy allowance C (the kit's a_backing_inv_k / a_lazy_canon_k, with RESMAX_k,
   commit 7bb12afd3646 A/AgreeBackingS.v:105 / :114, A/LazyResid.v:70), never by the world's raw
   A_bytes: the world keeps every dead secondary's hull, so raw A_bytes grows by one hull per recycle. C is a parameter
   here with the premise C <= abudget_kit_cf S, so these lemmas do not depend on how ledger_cf is finally stated.
   Contents: 1. the room and its kernel consequence (vm_backing_used md + G <= vm_limit for G <= CF_HEAD, hence
   mmap_noreserve_backed_ok and no refusable grant); 2. one call's grants (the internal file KERNEL-GRANT-CHECK.md's six map
   sites) and their total CALL_GRANT_MAX <= CF_HEAD; 3. the room at init and on live state, with its exact,
   unit-independent margin (the hull term is capped by CF_HULL_MAX under the unit's cf_hull_ok), and (3c) at a drain
   cut of the recycle walk (WfR_cf and qloose_cut, room_rec_cf_of_cut, with its own margin); 4. the
   eager + allowance forms for the callers that read eager_used + A (AGif4.ifs_room_w's shape, YGcfNilInit's band).
   No function is proved here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG08cf
YGcfAbudget YGcfLazyResid.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Z.Placement.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG03cf YG09.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* 2. One call's grants (constants first: they read no state).                    *)
(*    The six map sites of the internal file KERNEL-GRANT-CHECK.md, at their maxima for one    *)
(*    Allocate, Deallocate or Reallocate call (five bullets: the secondary bullet  *)
(*    covers two sites, MmapOrDie and MmapOrDieOnFatalError):                      *)
(*    - the errbuf remap (errb_map_cf, KMmapSec): the new buffer is mapped before  *)
(*      the old one is unmapped (form (A)), at most 2 * cf_nob together;           *)
(*    - the class's user map (map_more_user_cf, KMapUser, YG00cf.v:159-168): its  *)
(*      size round_up (total - mapped) kUserMapSize is NOT one kUserMapSize, but   *)
(*      the arm maps only when mapped + size <= kFreeArrayOffset, so it is at most *)
(*      kFreeArrayOffset, plus its shadow kFreeArrayOffset / 8;                    *)
(*    - the free-array growths (KMapFreeArray): at most 31 (one per class, a Theorem Labs lane's *)
(*      count), each kFreeArrayMapSize and its shadow;                              *)
(*    - one secondary map (MmapOrDie or MmapOrDieOnFatalError, KMmapSec):           *)
(*      sec_map_size n <= cf_nob (cf_sizes_ok) and its shadow hull's two edge pages *)
(*      and interior, cf_nob / 8 + 8192;                                            *)
(*    - the pointer array's commit (KMapPtrArray, never refused): 8 bytes per entry *)
(*      of one commit, 8 * kPtrArrayEntriesPerCommit.                               *)
(*    cf_nob is bounded by its field cf_nob_ok (<= 2 ^ 30), so the maxima are taken  *)
(*    at NOB_CF_MAX := 2 ^ 30.                                                      *)
Definition NOB_CF_MAX : Z := 2 ^ 30.
Definition G_ERRB_MAX : Z := 2 * NOB_CF_MAX.
Definition G_USER_MAX : Z := kFreeArrayOffset + kFreeArrayOffset / 8.
Definition G_FA_MAX : Z := 31 * (kFreeArrayMapSize + kFreeArrayMapSize / 8).
Definition G_SEC_MAX : Z := NOB_CF_MAX + (NOB_CF_MAX / 8 + 8192).
Definition G_PTR_MAX : Z := 8 * kPtrArrayEntriesPerCommit.
Definition call_grants_cf : list Z := [G_ERRB_MAX; G_USER_MAX; G_FA_MAX; G_SEC_MAX; G_PTR_MAX].
Definition CALL_GRANT_MAX : Z := fold_right Z.add 0 call_grants_cf.

Lemma CALL_GRANT_MAX_val : CALL_GRANT_MAX = 7592583168.
Proof. vm_compute. reflexivity. Qed.

Lemma CALL_GRANT_MAX_head : CALL_GRANT_MAX <= CF_HEAD.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma call_grants_cf_nonneg : Forall (fun g => 0 <= g) call_grants_cf.
Proof. repeat constructor; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* ---------------------------------------------------------------------------- *)
(* 3a. The maxima of the room's terms on live state (each term's bound is         *)
(*     YG08cf's): the eager part (the primary's 31 classes, the pointer-array      *)
(*     reservation, the live secondaries' bytes and the errbuf, <= cf_nob) and the  *)
(*     allowance (the kit form abudget_kit_cf: abudget_cf's terms with the primary *)
(*     and pointer-array terms replaced by PRIM_SPACE_cf / PTR_SPACE_cf; its hull    *)
(*     term is the unit's cf_hull <= CF_HULL_MAX under cf_hull_ok).             *)
Definition EAGER_CF_MAX : Z :=
31 * (kFreeArrayOffset + kFreeArrayMax) + 8 * kPtrArrayEntriesPerCommit + SEC_LIVE_MAX + NOB_CF_MAX.
(* The kit's whole reservations PRIM_SPACE_cf / PTR_SPACE_cf (with PRIM_SPACE_cf_val = 154,618,909,184 and
   PTR_SPACE_cf_val = 9,445,376) are a Theorem Labs lane's, YGcfLazyResid.v: Cker counts cgif's whole primary reservation
   (ly_prim ly, kPrimResvSize) and the pointer array's (ly_Q ly, kPtrArrayResv), each with its shull, and these are
   their closed upper bounds. *)
Definition ABUDGET_KIT_MAX : Z :=
A_BASE_CF + PRIM_SPACE_cf + PTR_SPACE_cf + SEC_LIVE_MAX + CF_HULL_MAX + NOB_CF_MAX.
Definition ROOM_CF_NEED : Z := E_BASE + EAGER_CF_MAX + ABUDGET_KIT_MAX + CF_HEAD.

(* The margin, exact and unit-independent (the hull cap CF_HULL_MAX = 2 ^ 35 + 2 ^ 37 is in ROOM_CF_NEED). The room
   left for the hull term is this margin + CF_HULL_MAX = 194,337,607,168 B (the internal file LEDGER-FORM-PROPOSAL.md section 7). *)
Lemma room_cf_margin : ASAN_VM_LMIN - ROOM_CF_NEED = 22538915328.
Proof. vm_compute. reflexivity. Qed.

Lemma ROOM_CF_NEED_fits : ROOM_CF_NEED <= ASAN_VM_LMIN.
Proof. pose proof room_cf_margin. lia. Qed.

(* The drain cut's pending allowance (AbudgetRestate, for CfF2b's drain relation ARcfR). At a cut of the recycle walk
   the pending items have left the queues but are still quarantined, so quar_n exceeds queued_n by their bytes; CfF2b's
   DRq_cf (YGcfInstDrainR.v) bounds them by 2 ^ 31 (its conjuncts unq_cf S <= items_n its and items_n its <= 2 ^ 31,
   the latter from QB_cf's first conjunct). qloose_cut is qloose (YG01.v:339) with that allowance added to its third
   conjunct. Each pending byte is at most one more byte of sec_live_bytes, which eager_cf and abudget_kit_cf each count
   once: ROOM_CF_CUT_EXTRA = 2 ^ 31 + 2 ^ 31. The live hulls grow by at most one eighth of it, to
   (SEC_LIVE_MAX + CUT_PEND_MAX) / 8 + 8192 * kPtrArrayEntriesPerCommit = 3,087,007,744 (live_hulls_cut_val), which is
   cf_hull_bound's premise (YGcfNames.v), so the hull term stays within CF_HULL_MAX under cf_hull_ok and needs no
   extra room. *)
Definition CUT_PEND_MAX : Z := 2 ^ 31.

Definition qloose_cut (S : astate) : Prop :=
qc_bytes (st_qthread S) <= 2 ^ 29 /\ qc_bytes (st_qglobal S) <= 2 ^ 30 /\ quar_n S <= queued_n S + 2 ^ 30 + CUT_PEND_MAX.

Lemma qloose_cut_of_qloose : forall S, qloose S -> qloose_cut S.
Proof. intros S (A & B & C). unfold qloose_cut, CUT_PEND_MAX. lia. Qed.

(* DRq_cf's conjuncts give it directly (its = the cut's pending items). *)
Lemma qloose_cut_of_pending : forall S its, YG03cf.unq_cf S <= items_n its ->
qc_bytes (st_qthread S) <= kQuarantineCacheMax -> qc_bytes (st_qglobal S) <= kQuarantineMax -> items_n its <= 2 ^ 31 ->
qloose_cut S.
Proof.
intros S its HU HT HG HN. unfold qloose_cut, CUT_PEND_MAX. unfold YG03cf.unq_cf, kQuarantineCacheMax, kQuarantineMax in *. lia.
Qed.

Definition ROOM_CF_CUT_EXTRA : Z := CUT_PEND_MAX + CUT_PEND_MAX.

Lemma ROOM_CF_CUT_EXTRA_val : ROOM_CF_CUT_EXTRA = 4294967296.
Proof. vm_compute. reflexivity. Qed.

(* The margin at a cut, exact and unit-independent: room_cf_margin less ROOM_CF_CUT_EXTRA. *)
Lemma room_cf_cut_margin : ASAN_VM_LMIN - (ROOM_CF_NEED + ROOM_CF_CUT_EXTRA) = 18243948032.
Proof. vm_compute. reflexivity. Qed.

Lemma ROOM_CF_CUT_fits : ROOM_CF_NEED + ROOM_CF_CUT_EXTRA <= ASAN_VM_LMIN.
Proof. pose proof room_cf_cut_margin. lia. Qed.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 1. The room of record and the real backing.                                    *)
(* The allowance in the kit's form (Main 05:0xZ): abudget_cf with its primary term and its pointer-array term replaced
   by the kit's whole reservations. a Theorem Labs lane's Cker A0 ly S nev (YGcfLazyResid.v) is bounded by A_bytes A0 +
   PRIM_SPACE_cf + PTR_SPACE_cf + sec_live_bytes S + sec_live_hulls S + 2 * kPage * nev; AbudgetRestate proves
   Cker <= abudget_kit_cf S from it. *)
Definition abudget_kit_cf (S : astate) : Z :=
abudget_cf S - (prim_committed S + prim_committed S / 8) - 8 * st_sec_reserved S + PRIM_SPACE_cf + PTR_SPACE_cf.

Definition room_rec_cf (ly : alayout) (S : astate) (md : Model) : Prop :=
E_BASE + eager_cf ly S md + abudget_kit_cf S + CF_HEAD <= ASAN_VM_LMIN.

(* The backing fact in the kit's canonical form: the materialized lazy pages are bounded by the canonical lazy
   allowance C. C is the slot of the unit's named backing premise; its instance is a Theorem Labs lane's Cker (YGcfLazyResid.v:
   the whole primary reservation and the pointer array with their shulls, every mapped secondary with its hull, and
   2 * page_size per evicted secondary; mat_canon_of_resid_cf concludes mat_canon_cf (Cker A0 ly S (k - qsec_cf S)) md
   by unfolding), with C <= abudget_kit_cf S from AbudgetRestate. Route of record (VERIFY 05:07Z): mat_canon_cf stays
   a NAMED premise until E1 (SRr_stepM and its lemma, owner a Theorem Labs lane) and E2 (after the madvise, the recycle walk
   touches no page of [PB, PE) except the two edge pages, owner H4) discharge it; otherwise route (B), the footprint
   LIFT's cgif instance with a named holder. The room only reads it. *)
Definition mat_canon_cf (C : Z) (md : Model) : Prop :=
Z.of_nat (length (m_vm_materialized md)) * page_size <= C.

(* The real backing below the room: eager_used by the ledger's alc_eager_x, the materialized pages by
   C <= abudget_kit_cf S (the canonical form's side). *)
Lemma backing_room_cf : forall segs ly S md C G,
ALedger_cf segs ly S md -> mat_canon_cf C md -> C <= abudget_kit_cf S -> room_rec_cf ly S md -> G <= CF_HEAD ->
vm_backing_used md + G <= vm_limit (m_vmmaps md).
Proof.
intros segs ly S md C G L MC LC R HG.
pose proof (alc_eager_x _ _ _ _ L) as EX. pose proof (alc_limit _ _ _ _ L) as LIM.
unfold mat_canon_cf, room_rec_cf in *. rewrite vm_backing_used_split. lia.
Qed.

(* The canonical form of the room, as Main stated it: eager_used md + C + G <= vm_limit. *)
Lemma room_canon_cf : forall segs ly S md C G,
ALedger_cf segs ly S md -> C <= abudget_kit_cf S -> room_rec_cf ly S md -> G <= CF_HEAD ->
eager_used md + C + G <= vm_limit (m_vmmaps md).
Proof.
intros segs ly S md C G L LC R HG.
pose proof (alc_eager_x _ _ _ _ L) as EX. pose proof (alc_limit _ _ _ _ L) as LIM.
unfold room_rec_cf in R. lia.
Qed.

(* No map of at most CF_HEAD bytes is refused for want of backing. *)
Lemma backed_ok_room_cf : forall segs ly S md C flags G,
ALedger_cf segs ly S md -> mat_canon_cf C md -> C <= abudget_kit_cf S -> room_rec_cf ly S md -> G <= CF_HEAD ->
mmap_noreserve_backed_ok flags md G = true.
Proof.
intros segs ly S md C flags G L MC LC R HG.
pose proof (backing_room_cf segs ly S md C G L MC LC R HG) as B.
unfold mmap_noreserve_backed_ok. destruct (mmap_noreserve_b flags); [reflexivity|]. apply Z.leb_le. exact B.
Qed.

(* ... and, with a gap of its size (vm_gap_available, which grant_ok_na_pin gives: YK13.grant_na_pin_gap), no such
   map is refusable (the room's form of YK13.grant_na_pin_not_grant_refusable). *)
Lemma grant_not_refusable_room_cf : forall segs ly S md C flags G,
ALedger_cf segs ly S md -> mat_canon_cf C md -> C <= abudget_kit_cf S -> room_rec_cf ly S md -> G <= CF_HEAD ->
Z.Placement.vm_gap_available (m_vmmaps md) G = true ->
Z.Placement.mmap_grant_refusable flags md G = false.
Proof.
intros segs ly S md C flags G L MC LC R HG GAP.
unfold Z.Placement.mmap_grant_refusable.
rewrite (backed_ok_room_cf segs ly S md C flags G L MC LC R HG), GAP. reflexivity.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2b. Every grant of one call. The room is the call's ENTRY premise (state S,     *)
(*     model md); at any later point of the call the model md' has backed at most  *)
(*     u bytes more, u being the call's grants so far, and keeps the limit. The     *)
(*     next grant n then fits when u + n <= CALL_GRANT_MAX.                          *)
Lemma call_grant_room_cf : forall segs ly S md md' C u n,
ALedger_cf segs ly S md -> mat_canon_cf C md -> C <= abudget_kit_cf S -> room_rec_cf ly S md ->
vm_backing_used md' <= vm_backing_used md + u -> vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) ->
u + n <= CALL_GRANT_MAX ->
vm_backing_used md' + n <= vm_limit (m_vmmaps md').
Proof.
intros segs ly S md md' C u n L MC LC R BU EL UN.
pose proof CALL_GRANT_MAX_head as H.
pose proof (backing_room_cf segs ly S md C (u + n) L MC LC R ltac:(lia)) as B. rewrite EL. lia.
Qed.

Lemma call_backed_ok_cf : forall segs ly S md md' C u flags n,
ALedger_cf segs ly S md -> mat_canon_cf C md -> C <= abudget_kit_cf S -> room_rec_cf ly S md ->
vm_backing_used md' <= vm_backing_used md + u -> vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) ->
u + n <= CALL_GRANT_MAX ->
mmap_noreserve_backed_ok flags md' n = true.
Proof.
intros segs ly S md md' C u flags n L MC LC R BU EL UN.
pose proof (call_grant_room_cf segs ly S md md' C u n L MC LC R BU EL UN) as B.
unfold mmap_noreserve_backed_ok. destruct (mmap_noreserve_b flags); [reflexivity|]. apply Z.leb_le. exact B.
Qed.

Lemma call_grant_not_refusable_cf : forall segs ly S md md' C u flags n,
ALedger_cf segs ly S md -> mat_canon_cf C md -> C <= abudget_kit_cf S -> room_rec_cf ly S md ->
vm_backing_used md' <= vm_backing_used md + u -> vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) ->
u + n <= CALL_GRANT_MAX -> Z.Placement.vm_gap_available (m_vmmaps md') n = true ->
Z.Placement.mmap_grant_refusable flags md' n = false.
Proof.
intros segs ly S md md' C u flags n L MC LC R BU EL UN GAP.
unfold Z.Placement.mmap_grant_refusable.
rewrite (call_backed_ok_cf segs ly S md md' C u flags n L MC LC R BU EL UN), GAP. reflexivity.
Qed.

(* The six sites' own sizes are within their maxima. The errbuf map: n <= cf_nob (ERRB_ROOM, YG00cf.v:107) and the
   old buffer at most cf_nob more (errb_cap_cf <= cf_nob). The secondary map: sec_map_size n <= cf_nob for every
   request below cf_malloc_max (cf_sizes_ok). *)
Lemma errb_map_fits_cf : forall n old, 0 <= n <= cf_nob -> 0 <= old <= cf_nob -> old + n <= G_ERRB_MAX.
Proof. intros n old Hn Ho. pose proof cf_nob_ok. unfold G_ERRB_MAX, NOB_CF_MAX. lia. Qed.

Lemma sec_map_fits_cf : forall n, 0 <= n < cf_malloc_max ->
sec_map_size n + (sec_map_size n / 8 + 8192) <= G_SEC_MAX.
Proof.
intros n Hn. pose proof (cf_sizes_ok n Hn) as S1. pose proof cf_nob_ok as S2.
assert (D : sec_map_size n / 8 <= NOB_CF_MAX / 8) by (apply Z.div_le_mono; unfold NOB_CF_MAX; lia).
unfold G_SEC_MAX, NOB_CF_MAX in *. lia.
Qed.

(* The user map: the arm maps only when mapped + map_size <= kFreeArrayOffset (YG00cf.v:167). *)
Lemma user_map_fits_cf : forall mapped map_size, 0 <= mapped -> 0 <= map_size ->
mapped + map_size <= kFreeArrayOffset -> map_size + map_size / 8 <= G_USER_MAX.
Proof.
intros mapped map_size H1 H2 H3.
assert (D : map_size / 8 <= kFreeArrayOffset / 8) by (apply Z.div_le_mono; lia).
unfold G_USER_MAX. lia.
Qed.

Lemma fa_maps_fit_cf : forall j, 0 <= j <= 31 -> j * (kFreeArrayMapSize + kFreeArrayMapSize / 8) <= G_FA_MAX.
Proof. intros j Hj. unfold G_FA_MAX, kFreeArrayMapSize. change (262144 / 8) with 32768. lia. Qed.

(* ---------------------------------------------------------------------------- *)
(* 3b. The room at init and on live state.                                        *)

(* At init: no primary, no secondary, no errbuf entry; eager_cf is 0 and abudget_kit_cf is A_BASE_CF + PRIM_SPACE_cf +
   PTR_SPACE_cf. *)
Lemma room_rec_cf_init : forall ly md, room_rec_cf ly init_state md.
Proof.
intros ly md. unfold room_rec_cf, eager_cf, abudget_kit_cf, abudget_cf.
replace (prim_committed init_state) with 0 by reflexivity.
replace (st_sec_reserved init_state) with 0 by reflexivity.
replace (sec_live_bytes init_state) with 0 by reflexivity.
rewrite cf_hull_init.
replace (errb_cap_cf init_state) with 0 by reflexivity.
replace (sec_extents ly init_state ++ errb_zone ly init_state) with (@nil (Z * Z)) by reflexivity.
replace (esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) []) with 0 by reflexivity.
assert (V : E_BASE + A_BASE_CF + PRIM_SPACE_cf + PTR_SPACE_cf + CF_HEAD <= ASAN_VM_LMIN)
  by (apply Z.leb_le; vm_compute; reflexivity).
replace (0 / 8) with 0 by reflexivity.
rewrite PRIM_SPACE_cf_val, PTR_SPACE_cf_val in *.
unfold E_BASE, A_BASE_CF, CF_HEAD, ASAN_VM_LMIN, A_BASE, EV_A, EV_MAX in *. lia.
Qed.

(* The errbuf extent is one extent of errb_cap_cf bytes, or none. *)
Lemma esec_errb_zone_le : forall ly S na lz, 0 <= errb_cap_cf S < 2 ^ 64 -> esec na lz (errb_zone ly S) <= errb_cap_cf S.
Proof.
intros ly S na lz Hc. unfold errb_zone, xs_cf.
destruct (last_cap_idx (st_secs S) 0 None).
- apply esec_one_le. cbn [snd]. exact Hc.
- unfold esec. cbn. lia.
Qed.

(* On live state (the relation's Wf_cf, at a loose quarantine, with the run row): every term of the room is below its
   maximum, and ROOM_CF_NEED fits. *)
Theorem eager_cf_bound : forall U ly S md, Wf_cf U S -> qloose S -> eager_cf ly S md <= EAGER_CF_MAX.
Proof.
intros U ly S md W QL. unfold eager_cf. rewrite esec_app.
pose proof (prim_committed_bound_cf U 0 0 0 S W) as P.
pose proof (sec_arr_reserved_cf U 0 0 0 S W) as R.
pose proof (sec_bytes_bound_cf U 0 0 0 S W QL) as SB.
pose proof (errb_cap_bound_cf U 0 0 0 S W) as EB. pose proof cf_nob_ok as NO.
pose proof (sec_extents_sizes_sum ly S (sec_extents_sizes64_cf U ly S W)
  (vm_noaccess (m_vmmaps md)) (m_vm_lazy md)) as E1.
pose proof (esec_errb_zone_le ly S (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) ltac:(lia)) as E2.
unfold EAGER_CF_MAX, NOB_CF_MAX. lia.
Qed.

Theorem abudget_kit_cf_bound : forall U S, Wf_cf U S -> qloose S -> cf_hull_ok S ->
abudget_kit_cf S <= ABUDGET_KIT_MAX.
Proof.
intros U S W QL HT. unfold abudget_kit_cf, abudget_cf, ABUDGET_KIT_MAX.
pose proof (sec_bytes_bound_cf U 0 0 0 S W QL) as SB.
pose proof (errb_cap_bound_cf U 0 0 0 S W) as EB. pose proof cf_nob_ok as NO.
pose proof (live_hulls_bound_cf U 0 0 0 S W QL) as LH.
assert (V : SEC_LIVE_MAX / 8 + 8192 * kPtrArrayEntriesPerCommit = 2818572288) by (vm_compute; reflexivity).
pose proof (cf_hull_bound S HT ltac:(lia)) as HH.
unfold NOB_CF_MAX, CF_HULL_MAX in *. lia.
Qed.

(* On live state the kit form is at least abudget_cf (the primary and pointer-array terms are below the whole
   reservations), so an allowance bounded by abudget_cf S (ARcf's ledger conjunct) is bounded by abudget_kit_cf S. *)
Lemma abudget_le_kit_cf : forall U S, Wf_cf U S -> abudget_cf S <= abudget_kit_cf S.
Proof.
intros U S W. unfold abudget_kit_cf.
pose proof (prim_committed_bound_cf U 0 0 0 S W) as P.
pose proof (sec_arr_reserved_cf U 0 0 0 S W) as R.
assert (E : 31 * (kFreeArrayOffset + kFreeArrayMax) = 133143986176) by (vm_compute; reflexivity).
rewrite E in P.
assert (D : prim_committed S / 8 <= 16642998272)
  by (change 16642998272 with (133143986176 / 8); apply Z.div_le_mono; lia).
assert (R2 : st_sec_reserved S <= 16384) by (destruct R as [[_ R1] _]; exact R1).
rewrite PRIM_SPACE_cf_val, PTR_SPACE_cf_val. lia.
Qed.

Theorem room_rec_cf_of_live : forall U ly S md, Wf_cf U S -> qloose S -> cf_hull_ok S ->
room_rec_cf ly S md.
Proof.
intros U ly S md W QL HT. unfold room_rec_cf.
pose proof (eager_cf_bound U ly S md W QL) as E. pose proof (abudget_kit_cf_bound U S W QL HT) as A.
pose proof ROOM_CF_NEED_fits as F.
unfold ROOM_CF_NEED in F. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 3c. The room at a drain cut (the room of record for CfF2b's drain relation).   *)
(*     At a cut the state has WfR_cf, not Wf_cf (a recycle may have taken a record *)
(*     that no cache holds yet, so Compl0 can fail), and qloose_cut, not qloose.   *)
(*     The bounds are YG08cf's, re-proved over WfR_cf: they read only wfr_         *)
(*     len_regions, reg0, classes, chunks, chunks_nodup, live, quarantine and      *)
(*     secondary, never wfc_compl0, so WfR_cf gives every one and no premise is    *)
(*     added. qloose_cut adds CUT_PEND_MAX to the quarantine's bound, and so to    *)
(*     sec_live_bytes and (by one eighth) to the live hulls, which stay within     *)
(*     cf_hull_bound's premise (live_hulls_cut_val), so the hull term keeps its    *)
(*     cap CF_HULL_MAX under the unit's cf_hull_ok.                                 *)
Lemma prim_committed_bound_R : forall U pp cc bb s, YG03cf.WfR_cf U pp cc bb s ->
0 <= prim_committed s <= 31 * (kFreeArrayOffset + kFreeArrayMax).
Proof.
intros U pp cc bb s W.
pose proof (YG03cf.wfr_len_regions _ _ _ _ _ W) as LR. pose proof (YG03cf.wfr_reg0 _ _ _ _ _ W) as R0.
assert (B : forall j, (1 <= j < length (st_regions s))%nat ->
0 <= rg_mapped_user (nth j (st_regions s) region0) + rg_mapped_fa (nth j (st_regions s) region0)
<= kFreeArrayOffset + kFreeArrayMax).
{ intros j Hj. rewrite LR in Hj.
pose proof (YG03cf.wfr_classes _ _ _ _ _ W (Z.of_nat j) ltac:(lia)) as C. unfold wf_class_cf, reg, znth in C. rewrite Nat2Z.id in C.
pose proof (wrc_fa _ _ _ _ _ _ C) as [F1 _]. pose proof (wrc_fa_bound _ _ _ _ _ _ C) as F2.
pose proof (wrc_mapped_bound _ _ _ _ _ _ C) as M. pose proof (wrc_alloc _ _ _ _ _ _ C). lia. }
unfold prim_committed. unfold reg, znth in R0. change (Z.to_nat 0) with 0%nat in R0.
destruct (st_regions s) as [|r0 rest]; [discriminate LR|]. cbn [nth] in R0. subst r0.
cbn [length] in LR. injection LR as LR.
assert (G : forall l, (forall j, (j < length l)%nat ->
0 <= rg_mapped_user (nth j l region0) + rg_mapped_fa (nth j l region0) <= kFreeArrayOffset + kFreeArrayMax) ->
0 <= fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 l
<= (kFreeArrayOffset + kFreeArrayMax) * Z.of_nat (length l)).
{ intros l Hl. induction l as [|r t IH]; [cbn; lia|]. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
pose proof (Hl 0%nat ltac:(cbn; lia)) as H0. cbn in H0. specialize (IH ltac:(intros j Hj; apply (Hl (S j)); cbn; lia)). lia. }
specialize (G rest ltac:(intros j Hj; exact (B (S j) ltac:(cbn [length]; lia)))).
rewrite LR in G. cbn [fold_right region0 rg_mapped_user rg_mapped_fa]. lia.
Qed.

Lemma nsec_le_arr_R : forall U pp cc bb s, YG03cf.WfR_cf U pp cc bb s ->
YG09.nsec_l (st_chunks s) <= Z.of_nat (length (st_sec_arr s)).
Proof.
intros U pp cc bb s W. pose proof (wsc_arr_chunks _ (YG03cf.wfr_secondary _ _ _ _ _ W)) as Sac.
pose proof (YG03cf.wfr_chunks_nodup _ _ _ _ _ W) as ND. pose proof (YG03cf.wfr_chunks _ _ _ _ _ W) as CK.
set (idx := fun l : list chunk => flat_map (fun k => match ck_beg k with PSec r _ => [r] | _ => [] end) l).
assert (L : forall l, YG09.nsec_l l = Z.of_nat (length (idx l))).
{ induction l as [|k t IH]; [reflexivity|]. unfold YG09.nsec_l, idx in *. cbn [fold_right flat_map]. rewrite length_app, Nat2Z.inj_add, <- IH.
destruct (ck_beg k); cbn [length]; lia. }
rewrite L. apply Nat2Z.inj_le. apply NoDup_incl_length.
- assert (G : forall l, Forall (chunk_ok_cf s) l -> NoDup (map ck_beg l) -> NoDup (idx l) /\ (forall r, In r (idx l) -> In (PSec r kPage) (map ck_beg l))).
{ induction l as [|k t IH]; intros Hc Hn; [split; [constructor | intros r []]|].
inversion Hc as [|k' t' Hk Ht]; subst. cbn [map] in Hn. inversion Hn as [|b' m' Hni Hnt]; subst. destruct (IH Ht Hnt) as [I1 I2].
unfold idx in *. cbn [flat_map map]. destruct (ck_beg k) as [|off|r o|cid pos] eqn:Eb; cbn [app].
- split; [exact I1 | intros r Hr; right; exact (I2 r Hr)].
- split; [exact I1 | intros r Hr; right; exact (I2 r Hr)].
- destruct Hk as [_ Hk]. rewrite Eb in Hk. destruct Hk as (_ & -> & _). split.
+ constructor; [|exact I1]. intros Hin. apply Hni. exact (I2 r Hin).
+ intros r' [<-|Hr]; [left; reflexivity | right; exact (I2 r' Hr)].
- split; [exact I1 | intros r Hr; right; exact (I2 r Hr)]. }
exact (proj1 (G _ CK ND)).
- intros r Hr. apply Sac. unfold idx in Hr. apply in_flat_map in Hr as (k & Hk & Hr).
destruct (ck_beg k) as [|off|r' o|cid pos] eqn:Eb; try destruct Hr as [<-|[]]; try destruct Hr.
pose proof (proj1 (Forall_forall _ _) CK k Hk) as [_ Hok]. rewrite Eb in Hok. destruct Hok as (_ & -> & _). exists k. auto.
Qed.

Lemma sec_arr_reserved_R : forall U pp cc bb s, YG03cf.WfR_cf U pp cc bb s ->
Z.of_nat (length (st_sec_arr s)) <= st_sec_reserved s <= kPtrArrayEntriesPerCommit /\ 0 <= st_sec_reserved s.
Proof.
intros U pp cc bb s W. pose proof (wsc_reserved _ (YG03cf.wfr_secondary _ _ _ _ _ W)) as R1.
pose proof (wsc_reserved_al _ (YG03cf.wfr_secondary _ _ _ _ _ W)) as R2. lia.
Qed.

Lemma sec_extents_sizes64_R : forall U pp cc bb ly s, YG03cf.WfR_cf U pp cc bb s ->
Forall (fun e => 0 <= snd e < 2 ^ 64) (sec_extents ly s).
Proof.
intros U pp cc bb ly s W. pose proof (YG03cf.wfr_chunks _ _ _ _ _ W) as CK. unfold sec_extents. apply Forall_forall. intros e He.
apply in_flat_map in He as (k & Hk & He). pose proof (proj1 (Forall_forall _ _) CK k Hk) as [Hn _].
destruct (ck_beg k) as [|o|r o|c p]; try destruct He as [<-|[]]; try destruct He. cbn [snd].
pose proof (sec_map_size_page (ck_req k) ltac:(lia)). pose proof (cf_sizes_ok (ck_req k) Hn). pose proof cf_nob_ok.
unfold kPage in *. lia.
Qed.

Lemma errb_cap_bound_R : forall U pp cc bb s, YG03cf.WfR_cf U pp cc bb s -> 0 <= errb_cap_cf s <= cf_nob.
Proof.
intros U pp cc bb s W. pose proof (wsc_lens _ (YG03cf.wfr_secondary _ _ _ _ _ W)) as L. pose proof cf_nob_nonneg as N.
unfold errb_cap_cf, errb_e.
destruct (filter is_errb_cap (st_secs s)) as [|a l] eqn:E; [cbn [last sm_len]; lia|].
assert (Hin : In (last (a :: l) (mkSec 0 ERRB_CAP_TAG false)) (filter is_errb_cap (st_secs s)))
by (rewrite E; apply last_in_cons).
apply filter_In in Hin as [Hin _]. pose proof (proj1 (Forall_forall _ _) L _ Hin) as B. cbv beta in B. lia.
Qed.

Lemma sec_bytes_live_R : forall U pp cc bb s, YG03cf.WfR_cf U pp cc bb s ->
0 <= sec_live_bytes s <= blocks_bytes s + quar_n s + (2 ^ 14 + 1) * Z.of_nat (length (st_sec_arr s)).
Proof.
intros U pp cc bb s W. pose proof (YG03cf.wfr_chunks _ _ _ _ _ W) as CK.
assert (R0 : Forall (fun k => 0 <= ck_req k) (st_chunks s)) by (eapply Forall_impl; [|exact CK]; intros k [Hk _]; lia).
pose proof (sec_bytes_le_cf _ R0) as B1. pose proof (sec_bytes_nonneg _ R0) as B0. pose proof (nsec_le_arr_R U pp cc bb s W) as B2.
change (sec_bytes (st_chunks s)) with (sec_live_bytes s) in B1, B0. change (reqbytes (st_chunks s)) with (blocks_bytes s) in B1.
change (quar_nl (st_chunks s)) with (quar_n s) in B1. lia.
Qed.

(* The quarantine's chunks at a cut: quar_n_loose_cf's bound plus the pending allowance. *)
Lemma quar_n_cut_R : forall U pp cc bb s, YG03cf.WfR_cf U pp cc bb s -> qloose_cut s ->
quar_n s <= 2 ^ 29 + 2 ^ 31 + CUT_PEND_MAX.
Proof.
intros U pp cc bb s W (T1 & T2 & T3). pose proof (YG03cf.wfr_quarantine _ _ _ _ _ W) as Q.
assert (QN : queued_n s <= qc_bytes (st_qthread s) + qc_bytes (st_qglobal s)).
{ rewrite (wq_bytes_t _ Q), (wq_bytes_g _ Q), !sum_bytes_items. unfold queued_n, q_items, all_batches. rewrite flat_map_app, items_n_app.
unfold kBatchBytes. lia. }
unfold CUT_PEND_MAX in *. lia.
Qed.

Theorem sec_bytes_bound_cut_cf : forall U pp cc bb s, YG03cf.WfR_cf U pp cc bb s -> qloose_cut s ->
0 <= sec_live_bytes s <= SEC_LIVE_MAX + CUT_PEND_MAX.
Proof.
intros U pp cc bb s W QL. pose proof (sec_bytes_live_R U pp cc bb s W) as B.
pose proof (quar_n_cut_R U pp cc bb s W QL). pose proof (YG03cf.wfr_live _ _ _ _ _ W).
pose proof (sec_arr_reserved_R U pp cc bb s W).
unfold SEC_LIVE_MAX, LIVE_MAX, kPtrArrayEntriesPerCommit, CUT_PEND_MAX in *. lia.
Qed.

Theorem live_hulls_bound_cut_cf : forall U pp cc bb s, YG03cf.WfR_cf U pp cc bb s -> qloose_cut s ->
0 <= sec_live_hulls s <= (SEC_LIVE_MAX + CUT_PEND_MAX) / 8 + 8192 * kPtrArrayEntriesPerCommit.
Proof.
intros U pp cc bb s W QL. pose proof (YG03cf.wfr_chunks _ _ _ _ _ W) as CK.
assert (R0 : Forall (fun k => 0 <= ck_req k) (st_chunks s)) by (eapply Forall_impl; [|exact CK]; intros k [Hk _]; lia).
pose proof (live_hulls_le _ R0) as H. pose proof (nsec_le_arr_R U pp cc bb s W) as N.
pose proof (sec_arr_reserved_R U pp cc bb s W) as R. pose proof (sec_bytes_bound_cut_cf U pp cc bb s W QL) as SB.
change (sec_bytes (st_chunks s)) with (sec_live_bytes s) in H. unfold sec_live_hulls.
pose proof (Z.div_le_mono (sec_live_bytes s) (SEC_LIVE_MAX + CUT_PEND_MAX) 8 ltac:(lia) (proj2 SB)). lia.
Qed.

(* The cut's live-hull bound, the premise of cf_hull_bound (YGcfNames.v). *)
Lemma live_hulls_cut_val : (SEC_LIVE_MAX + CUT_PEND_MAX) / 8 + 8192 * kPtrArrayEntriesPerCommit = 3087007744.
Proof. vm_compute. reflexivity. Qed.

Theorem eager_cf_bound_cut : forall U ly S md, YG03cf.WfR_cf U 0 0 0 S -> qloose_cut S ->
eager_cf ly S md <= EAGER_CF_MAX + CUT_PEND_MAX.
Proof.
intros U ly S md W QL. unfold eager_cf. rewrite esec_app.
pose proof (prim_committed_bound_R U 0 0 0 S W) as P.
pose proof (sec_arr_reserved_R U 0 0 0 S W) as R.
pose proof (sec_bytes_bound_cut_cf U 0 0 0 S W QL) as SB.
pose proof (errb_cap_bound_R U 0 0 0 S W) as EB. pose proof cf_nob_ok as NO.
pose proof (sec_extents_sizes_sum ly S (sec_extents_sizes64_R U 0 0 0 ly S W)
  (vm_noaccess (m_vmmaps md)) (m_vm_lazy md)) as E1.
pose proof (esec_errb_zone_le ly S (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) ltac:(lia)) as E2.
unfold EAGER_CF_MAX, NOB_CF_MAX. lia.
Qed.

Theorem abudget_kit_cf_bound_cut : forall U S, YG03cf.WfR_cf U 0 0 0 S -> qloose_cut S -> cf_hull_ok S ->
abudget_kit_cf S <= ABUDGET_KIT_MAX + CUT_PEND_MAX.
Proof.
intros U S W QL HT. unfold abudget_kit_cf, abudget_cf, ABUDGET_KIT_MAX.
pose proof (sec_bytes_bound_cut_cf U 0 0 0 S W QL) as SB.
pose proof (live_hulls_bound_cut_cf U 0 0 0 S W QL) as LH. rewrite live_hulls_cut_val in LH.
pose proof (cf_hull_bound S HT (proj2 LH)) as HH.
pose proof (errb_cap_bound_R U 0 0 0 S W) as EB. pose proof cf_nob_ok as NO.
unfold NOB_CF_MAX. lia.
Qed.

(* abudget_le_kit_cf over WfR_cf (the primary and pointer-array bounds are WfR_cf's). *)
Lemma abudget_le_kit_R : forall U S, YG03cf.WfR_cf U 0 0 0 S -> abudget_cf S <= abudget_kit_cf S.
Proof.
intros U S W. unfold abudget_kit_cf.
pose proof (prim_committed_bound_R U 0 0 0 S W) as P.
pose proof (sec_arr_reserved_R U 0 0 0 S W) as R.
assert (E : 31 * (kFreeArrayOffset + kFreeArrayMax) = 133143986176) by (vm_compute; reflexivity).
rewrite E in P.
assert (D : prim_committed S / 8 <= 16642998272)
  by (change 16642998272 with (133143986176 / 8); apply Z.div_le_mono; lia).
assert (R2 : st_sec_reserved S <= 16384) by (destruct R as [[_ R1] _]; exact R1).
rewrite PRIM_SPACE_cf_val, PTR_SPACE_cf_val. lia.
Qed.

Theorem room_rec_cf_of_cut : forall U ly S md, YG03cf.WfR_cf U 0 0 0 S -> qloose_cut S -> cf_hull_ok S ->
room_rec_cf ly S md.
Proof.
intros U ly S md W QL HT. unfold room_rec_cf.
pose proof (eager_cf_bound_cut U ly S md W QL) as E. pose proof (abudget_kit_cf_bound_cut U S W QL HT) as A.
pose proof ROOM_CF_CUT_fits as F.
unfold ROOM_CF_NEED, ROOM_CF_CUT_EXTRA in F. lia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 4. The eager + allowance forms. room_canon_cf (section 1) is the form for any   *)
(*    allowance A <= abudget_kit_cf S. A caller that reads eager_used md + A_bytes  *)
(*    (w_A W) (AGif4.ifs_room_w's shape) can use it only where its caller has       *)
(*    A_bytes (w_A W) <= abudget_kit_cf S, e.g. ARcf's interim ledger conjunct      *)
(*    A_bytes (w_A W) <= abudget_cf S with abudget_le_kit_cf, or YGcfNilInit's band  *)
(*    at init. ifs_room_w over the raw A_bytes is NOT derivable once dead hulls      *)
(*    outgrow the canonical residue: that case needs ifs_room_w over the canonical  *)
(*    allowance (an AGif4 / kit item, not this file's).                             *)

(* The CfInstSec premise without the double count (room_gen_cf's shape, YGcfInstSec.v:530-532): eager by eager_cf,
   the allowance by abudget_kit_cf, each once, from live state alone, at any head R <= CF_HEAD. *)
Lemma room_live_canon_cf : forall U segs ly S md A R,
Wf_cf U S -> qloose S -> cf_hull_ok S -> ALedger_cf segs ly S md -> A <= abudget_kit_cf S -> R <= CF_HEAD ->
eager_used md + A + R <= vm_limit (m_vmmaps md).
Proof.
intros U segs ly S md A R W QL HT L HA HR.
exact (room_canon_cf segs ly S md A R L HA (room_rec_cf_of_live U ly S md W QL HT) HR).
Qed.

(* Every unit's room ROOMW at its least value fits: YGcfMallocComposeE.nmaxw_cf_ok asks
   2 * (cf_malloc_max + 4 * 4096) + (cf_malloc_max + 4 * 4096) / 8 + 8192 + 2 ^ 19 <= ROOMW with
   cf_malloc_max + 4 * 4096 <= 2 ^ 30 (fuzz_reply: 1,072,709,632, so its least ROOMW is 2,280,040,448). *)
Lemma ROOMW_nmaxw_fits : forall m, 0 <= m -> m + 4 * 4096 <= 2 ^ 30 ->
2 * (m + 4 * 4096) + (m + 4 * 4096) / 8 + 8192 + 2 ^ 19 <= CF_HEAD.
Proof.
intros m H0 H1. change (2 ^ 30) with 1073741824 in H1.
assert (D : (m + 4 * 4096) / 8 <= 134217728) by (change 134217728 with (1073741824 / 8); apply Z.div_le_mono; lia).
unfold CF_HEAD. change (2 ^ 33) with 8589934592. change (2 ^ 19) with 524288. lia.
Qed.

(* YGcfNilInit's band premise (cls1_band_expose_cf's, YGcfNilInit.v:61, and ARcf_nil_init's ROOM, :92) from the same
   room: at init the room holds (room_rec_cf_init), the band is 469,766,144 bytes <= CF_HEAD, and the allowance is at
   most abudget_kit_cf init_state. *)
Lemma room_init_band_cf : forall segs ly md A,
ALedger_cf segs ly init_state md -> A <= abudget_kit_cf init_state ->
eager_used md + A + cls1_band_bytes_cf <= vm_limit (m_vmmaps md).
Proof.
intros segs ly md A L HA.
assert (HB : cls1_band_bytes_cf <= CF_HEAD) by (rewrite cls1_band_bytes_cf_val; apply Z.leb_le; vm_compute; reflexivity).
exact (room_canon_cf segs ly init_state md A cls1_band_bytes_cf L HA (room_rec_cf_init ly md) HB).
Qed.

End U.
