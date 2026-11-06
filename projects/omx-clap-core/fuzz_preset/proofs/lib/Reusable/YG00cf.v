(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: free_cf takes Quarantine::Put's size test (a chunk above the
   quarantine's max_size is recycled at once, not enqueued). Evidence: the internal file BIG-ARM.md section 4. *)
(* Theorem Labs, 2026-10: fuzz_preset's second allocator instance (suffix cf), the MODEL.
   cgif's map_more_user (YG00.v:279-295) closes the class-full case with a VACUOUS mcheck at :285, so a full
   class is "impossible". On preset a class DOES fill on accepted input (class 17 maps 3,584 MiB = kFreeArrayOffset,
   measured). This file replaces that one check by the arm the binary runs, in cgif's vocabulary, ported from
   msgpack-c's released refusal (proofs/msgpack-c/unpack_pack_fuzzer/lib/Spec/AsanCtrl.v:284, exh_report :363-371,
   release ref b6a0088adc): report, flag the class, return NULL; no IFail.
   cgif's YG00.v is NOT edited; class 24 keeps cgif's vacuous arm, by calling cgif's own functions.
   No address: the image pcs come from the class CfImg (YGcfNames.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YGcfNames.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------- *)
(* 1. The two bits of genuine state, inside cgif's astate.                        *)
(*                                                                                *)
(* (a) The per-class exhausted byte (RegionInfo + 68, set by `sb a0,68(s0)`,      *)
(*     cleared by `sb zero,68(s0)` at the end of a successful populate). It is a  *)
(*     PER-CLASS bit, so it lives in the per-class field rg_holes, as a sentinel  *)
(*     hole at offset EXH_HOLE with length 0. A zero-length hole at a negative    *)
(*     offset is inert everywhere cgif reads holes: prim_hole_at (YG0n.v:289-290) *)
(*     asks in_zr a (base + off, 0), always false; cut_ok (YG0n.v:291-295) does   *)
(*     not read holes; areq_ok's hole conditions (YG01.v:19, :23-24) hold because *)
(*     fst h + snd h = -1 <= off for every real offset off >= 0. cgif's own       *)
(*     del_hole / add_hole (YG00.v:257-260) do the toggling, and no cgif call     *)
(*     site can touch the sentinel: map_more_user deletes at rg_mapped_user >= 0  *)
(*     and ensure_free_array at kFreeArrayOffset + rg_mapped_fa >= 0.             *)
Definition EXH_HOLE : Z := -1.
Definition exh_mem_cf (s : astate) (c : Z) : bool :=
existsb (fun h => fst h =? EXH_HOLE) (rg_holes (reg s c)).
Definition set_exh_cf (c : Z) : M unit :=
r <- get_region c ;;
set_region c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r)
(add_hole (EXH_HOLE, 0) (rg_holes r))).
Definition clear_exh_cf (c : Z) : M unit :=
r <- get_region c ;;
set_region c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r)
(del_hole EXH_HOLE (rg_holes r))).

(* (b) The process-wide error-message buffer. "Has it been mapped yet" is not a    *)
(*     function of any existing field: the per-class byte is cleared at the end of *)
(*     every successful populate, so a successful map leaves the byte 0 while the  *)
(*     next map would fail. It is encoded as st_secs entries with no chunk         *)
(*     (report §2c (E1)): sec_extents (YG0n.v:192-193) is built from st_chunks, so *)
(*     such an entry adds a ly_sec slot without entering sec_extents, layout_le    *)
(*     already lets ly_sec extend for new indices (YG0f.v:70), and KMmapSec is     *)
(*     already a refusable kreq (YG0d.v:67).                                       *)
(*     A real secondary has sm_size = needed_size n >= 64513; the two control      *)
(*     entries carry a NEGATIVE sm_size, so they can never be confused with one,    *)
(*     and their sm_live is ALWAYS false, which is what keeps cgif's wf_sec intact: *)
(*     ws_arr_live (YG01.v:304-305) makes membership of st_sec_arr equivalent to    *)
(*     `sm_live = true`, so a control entry with sm_live = false is outside that    *)
(*     equivalence and needs no exemption. ws_arr_chunks (:303) is likewise         *)
(*     untouched, since no chunk points at a control entry, and ws_lens (:308) holds *)
(*     because the capacity is far below SEC_LEN_MAX. "Mapped" is therefore read     *)
(*     from the TAG, never from sm_live.                                            *)
(*     The capacity entry is APPENDED on every (re)map, because a remap gets a new  *)
(*     address and layout_le (YG0f.v:65-70) pins ly_sec at every index below        *)
(*     length (st_secs S); the superseded entry is re-tagged DEAD. The size entry   *)
(*     carries no address and is updated in place.                                  *)
Definition ERRB_CAP_TAG : Z := -1.
Definition ERRB_SZ_TAG : Z := -2.
Definition ERRB_DEAD_TAG : Z := -3.
Definition is_errb_cap (sm : secmap) : bool := sm_size sm =? ERRB_CAP_TAG.
Definition is_errb_sz (sm : secmap) : bool := sm_size sm =? ERRB_SZ_TAG.
Definition is_errb_any (sm : secmap) : bool := sm_size sm <? 0.
Definition errb_e (s : astate) : secmap :=
last (filter is_errb_cap (st_secs s)) (mkSec 0 ERRB_CAP_TAG false).
(* Mapped iff a CURRENT capacity entry exists. Never sm_live: control entries are
   always sm_live = false, so that wf_sec's ws_arr_live stays exactly cgif's. *)
Definition errb_mapped_cf (s : astate) : bool := existsb is_errb_cap (st_secs s).
(* Z.max 0 keeps the capacity structurally non-negative, so the budget layer needs no
   invariant to add it: an absent or retired entry reads as 0. *)
Definition errb_cap_cf (s : astate) : Z := Z.max 0 (sm_len (errb_e s)).
Lemma errb_cap_cf_nonneg : forall s, 0 <= errb_cap_cf s.
Proof. intros s. unfold errb_cap_cf. lia. Qed.
Fixpoint find_sz (l : list secmap) (i : nat) : option nat :=
match l with [] => None | sm :: t => if is_errb_sz sm then Some i else find_sz t (S i) end.
Definition errb_size_cf (s : astate) : Z :=
match find_sz (st_secs s) 0 with
| Some i => match nth_error (st_secs s) i with Some sm => sm_len sm | None => 0 end
| None => 0
end.
Definition errb_set_size (ns : Z) : M unit :=
modify (fun s =>
match find_sz (st_secs s) 0 with
| Some i => set_secs (lupd (st_secs s) i (mkSec ns ERRB_SZ_TAG false)) s
| None => set_secs (st_secs s ++ [mkSec ns ERRB_SZ_TAG false]) s
end).
(* Re-tag every current capacity entry DEAD: the remap unmaps the old buffer. *)
Definition errb_retire : M unit :=
modify (fun s => set_secs (map (fun sm => if is_errb_cap sm then mkSec (sm_len sm) ERRB_DEAD_TAG false else sm)
(st_secs s)) s).
(* The room one class-full report needs. One report appends exh_len1 + exh_len2 c, at
   most 33 + 60 + 2 + 5 = 100 bytes, and a remap rounds up to a page; 2 ^ 12 + kPage
   covers both the KMmapSec admissibility (YGcfTok.v's areq_ok_cf_errb) and the new
   capacity entry's wsc_lens bound. It is a CALL PREMISE, carried by acall_pre_cf and
   ml_malloc_cf, because the number of reports comes from the program, not from the
   allocator: the per-class flag clears on every successful populate. *)
Definition ERRB_ROOM {cp : CfParams} (s : astate) : Prop := errb_size_cf s + 2 ^ 12 + kPage <= cf_nob.
(* At most one CURRENT capacity entry, and every control entry dead to wf_sec.
   A field of ARmcf (YG0ncf.v), not of Wf_cf, so cgif's invariant is untouched. *)
Definition wf_errb_cf (s : astate) : Prop :=
(length (filter is_errb_cap (st_secs s)) <= 1)%nat /\
Forall (fun sm => is_errb_any sm = true -> sm_live sm = false) (st_secs s).

Section CF.
Context {ci : CfImg}.

(* The runtime's MmapOrDie: a refused map ends the process, so the model spins.
   msgpack's emb_realloc does the same (AsanCtrl.v:336-349, aundef_ USpin at :341).
   It TICKS, like cgif's own secondary mmap (YG0j.v:374), so that the lower bounds
   `length (st_secs s) + cc <= st_nev s` (YG01.v:331, :344) survive the two control
   entries this instance appends. *)
Definition errb_map_cf (want : Z) : M unit :=
let ncap := round_up want kPage in
tick ;;
z <- askz (KMmapSec ncap) ;;
if z =? 0 then spin cf_pc_errb_die
else errb_retire ;; modify (fun s => set_secs (st_secs s ++ [mkSec ncap ERRB_CAP_TAG false]) s).

(* One Printf's worth of bytes into the buffer. The first print of the process maps
   64 KiB (Append -> MmapOrDie; Append's entry: fuzz_preset asan 0x55d0c, fuzz_reply asan 0x563c0, cgif asan-ubsan 0x54bec); a later print that overflows the buffer
   remaps it. __sanitizer_silent_reports is 1 on this image, so there is no write
   syscall and no event beyond the map. *)
Definition errb_append_cf (len : Z) : M unit :=
s <- get ;;
if negb (errb_mapped_cf s) then
errb_map_cf ERRB_INIT ;;
s1 <- get ;;
(if errb_cap_cf s1 <? len then errb_map_cf len else ret tt) ;;
errb_set_size len
else
let ns := errb_size_cf s + len in
(if errb_cap_cf s <? ns then errb_map_cf ns else ret tt) ;;
errb_set_size ns.

(* The two Printfs of the class-full report, gated on the class's own byte: the
   binary reads RegionInfo + 68 (lbu a0,68(s0)) and prints only when it is clear. *)
Definition errb_report_cf (c : Z) : M unit :=
s <- get ;;
if exh_mem_cf s c then ret tt
else errb_append_cf exh_len1 ;; errb_append_cf (exh_len2 c).

(* ---------------------------------------------------------------------------- *)
(* 2. The arm. cgif's map_more_user (YG00.v:279-295) with line 285's vacuous       *)
(*    `mcheck (rg_mapped_user r + map_size <=? kFreeArrayOffset) 222820` replaced  *)
(*    by the real refusal. Class 24 keeps cgif's text, by calling cgif's function: *)
(*    preset cannot fill class 24 (capacity kFreeArrayOffset / kBatchBytes =       *)
(*    458,752 against a worst case of 118,869), and a class-24 refusal is fatal on *)
(*    the free side whatever the malloc side says (cgif spins at YG00.v:448).      *)
Definition map_more_user_cf (c need : Z) : M bool :=
if c =? kBatchClass then map_more_user c need
else
r <- get_region c ;;
let size := class_size c in
let total := rg_alloc_user r + need * size in
if rg_mapped_user r <? total then
let map_size := round_up (total - rg_mapped_user r) kUserMapSize in
if rg_mapped_user r + map_size <=? kFreeArrayOffset then
z <- askz (KMapUser c (rg_mapped_user r) map_size) ;;
if aGranted z then
set_region c (mkRegion (rg_mapped_user r + map_size) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r)
(del_hole (rg_mapped_user r) (rg_holes r))) ;; ret true
else
(if aDestroyed z
then set_region c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r)
(add_hole (rg_mapped_user r, map_size) (rg_holes r)))
else ret tt) ;; ret false
else errb_report_cf c ;; set_exh_cf c ;; ret false
else ret true.

(* populate clears the class's byte at the end of a successful carve (sb zero,68(s0)). *)
Definition populate_cf (c : Z) (need : Z) : M bool :=
if c =? kBatchClass then populate c need
else
ok <- map_more_user_cf c need ;;
if negb ok then ret false
else
r <- get_region c ;;
let size := class_size c in
let new_cnt := (rg_mapped_user r - rg_alloc_user r) / size in
let total_freed := fa_len (rg_free r) + new_cnt in
ok2 <- ensure_free_array c total_freed false ;;
if negb ok2 then ret false
else
r2 <- get_region c ;;
set_region c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2 + new_cnt * size) (rg_mapped_fa r2)
(FRun (rg_alloc_user r2) new_cnt :: rg_free r2) (rg_holes r2)) ;;
clear_exh_cf c ;;
ret true.

(* The rest of the chain is cgif's text with populate_cf threaded through
   (YG00.v:311-323, :330-349, :411-429). *)
Definition get_from_allocator_cf (c : Z) (n : Z) : M (option (list Z)) :=
r <- get_region c ;;
ok <- (if fa_len (rg_free r) <? n then populate_cf c (n - fa_len (rg_free r)) else ret true) ;;
if negb ok then ret None
else
r2 <- get_region c ;;
if fa_len (rg_free r2) <? n then ret None
else match fa_pop_n 10000%nat (class_size c) n (rg_free r2) [] with
| None => fail (FModel 1)
| Some (tops, rest) =>
set_region c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2) (rg_mapped_fa r2) rest (rg_holes r2)) ;;
ret (Some tops)
end.
Definition refill_if_empty_cf (c : Z) : M unit :=
p <- get_pc c ;;
match pc_chunks p with
| [] => got <- get_from_allocator_cf c (pc_max p / 2) ;;
match got with
| None => ret tt
| Some tops => set_pc c (mkPC (pc_max p) (cache_fill_order tops))
end
| _ => ret tt
end.
Definition cache_alloc_cf (c : Z) : M (option Z) :=
init_cache_if_needed ;;
refill_if_empty_cf c ;;
p <- get_pc c ;;
match pc_chunks p with
| [] => ret None
| l => let off := last l 0 in
set_pc c (mkPC (pc_max p) (removelast l)) ;;
ret (Some (region_off c + off))
end.
Definition malloc_cf (n : Z) (trace : list Z) : M sptr :=
tick ;;
mcheck (n <? kMaxAllowedMalloc - kPage) cf_pc_malloc_max ;;
ob <- (if from_primary n
then o <- cache_alloc_cf (chunk_class n) ;;
ret (match o with Some off => Some (PPrim off) | None => None end)
else sec_alloc n) ;;
match ob with
| None => ret PNull
| Some beg =>
depot_put trace ;;
let k := mkChunk beg n CAllocated in
(if needs_remap (ck_n k) then
z <- askz (KShadowRemap (ck_user k) (8 * (ck_n k / 8))) ;;
if aGranted z then ret tt else spin cf_pc_spin_shadow
else ret tt) ;;
modify (fun s => set_chunks (upd_chunk (st_chunks s) k) s) ;;
ret (ck_user k)
end.

(* ---------------------------------------------------------------------------- *)
(* 3. The quarantine drain, with the REAL MergeBatches.                           *)
(* cgif's maybe_drain (YG00.v:528-539) checks `2 * (kBatchBytes * L) <=? qc_bytes` *)
(* with an mcheck (:536): it asserts the MERGE condition is false and makes the    *)
(* merge case an IFail. That case is reachable: any quarantine of small chunks     *)
(* (one full batch of 1,021 one-byte items weighs 8,192 + 1,021 B, below 2 * 8,192),*)
(* which is fuzz_reply's whole class-1 load. cgif's own proofs never reach it only *)
(* because its regime caps st_nev at 8,192, below the 16,384 frees a merge needs.  *)
(* SOURCE: compiler-rt/lib/sanitizer_common/sanitizer_quarantine.h at tag           *)
(*   llvmorg-20.1.8: Recycle :147; CHECK_GE(cache_size, overhead_size) :159;        *)
(*   kOverheadThresholdPercents = 100 :163; the test `cache_size > overhead_size &&  *)
(*   overhead_size * (100 + 100) > cache_size * 100` :164-166; the MergeBatches call *)
(*   :167; MergeBatches :250-271.                                                    *)
(* BINARY: preset's IMAGES OF RECORD (pau-preset-rebuilt: A pin d83eb25dbf0df6d5 / twin f0d2e8d40c7e3ed0,      *)
(*   B pin f8f98a95bc524311 / twin 3b5e1a099b535acf), the internal file neutral_dis.py listing                              *)
(*   omx-clap-core-preset-ranout/<image>/fuzz_preset of Quarantine<..>::Recycle (symbol                    *)
(*   _ZN11__sanitizer10QuarantineIN6__asan18QuarantineCallbackENS1_9AsanChunkEE7RecycleEmS2_, 484 bytes),   *)
(*   at A 0x342dc / B 0x34360; by OFFSET from its entry, the same words on both images:                    *)
(*   +0x60 ld cache_size; +0x64 ld L; +0x68 slli overhead = L << 13 (L * kBatchBytes); +0x6c bltu          *)
(*   cache < overhead -> the CHECK_GE die path; +0x70 bgeu overhead >= cache -> no merge; +0x74 lui 0x190 *)
(*   / +0x7c mul = L * 1,638,400 = overhead * 200; +0x78 li 100 / +0x80 mul = cache * 100; +0x84 bgeu     *)
(*   cache * 100 >= overhead * 200 -> no merge; else +0xa4 jal +0x1e4 = MergeBatches. Same threshold and  *)
(*   order as the source. (An earlier version of this note read the ORIGINAL 10-26 image, 93f1eb09, where *)
(*   Recycle is at 0x3424c: same offsets and words, 0x90 lower.) No statement or proof uses these pcs.    *)
(* The CHECK_GE never fires on a well-formed quarantine (each batch weighs at least *)
(* kBatchBytes plus its items, wf_quar), so the model omits that die path.          *)
(* MergeBatches: while a batch and its successor have count + count <= kBatchSlots  *)
(* (can_merge), move the successor's items into it and extract the now-empty        *)
(* successor into the to-deallocate list, KEEPING the same current batch; else      *)
(* advance. qc_bytes drops by kBatchBytes per extracted batch (SizeSub).            *)
Fixpoint merge_batches_cf (fuel : nat) (l : list batch) : list batch * list batch :=
match fuel with
| O => (l, [])
| S f =>
match l with
| b1 :: b2 :: t =>
if (length (b_items b1) + length (b_items b2) <=? Z.to_nat kBatchSlots)%nat then
let '(rest, ex) := merge_batches_cf f (mkBatch (b_self b1) (b_items b1 ++ b_items b2) :: t) in
(rest, mkBatch (b_self b2) [] :: ex)
else
let '(rest, ex) := merge_batches_cf f (b2 :: t) in
(b1 :: rest, ex)
| _ => (l, [])
end
end.

(* cgif's maybe_drain with :536's mcheck replaced by the real branch. The extracted
   empty batches go first into DoRecycle's list (they were enqueued during the merge),
   then the dequeued ones; recycling an empty batch only frees its self (cache_dealloc
   kBatchClass), which do_recycle already does. *)
Definition maybe_drain_cf : M unit :=
s <- get ;;
if qc_bytes (st_qthread s) <=? kQuarantineCacheMax then ret tt
else
let g := mkQC (qc_list (st_qglobal s) ++ qc_list (st_qthread s)) (qc_bytes (st_qglobal s) + qc_bytes (st_qthread s)) in
put (set_qglobal g (set_qthread qc0 s)) ;;
if qc_bytes g <=? kQuarantineMax then ret tt
else
let L := Z.of_nat (length (qc_list g)) in
let '(gm, ex) :=
if (kBatchBytes * L <? qc_bytes g) && (qc_bytes g <? 2 * (kBatchBytes * L))
then let '(l', ex) := merge_batches_cf (length (qc_list g)) (qc_list g) in
(mkQC l' (qc_bytes g - kBatchBytes * Z.of_nat (length ex)), ex)
else (g, []) in
let '(g', popped) := pop_batches (S (length (qc_list gm))) gm [] in
modify (set_qglobal g') ;;
do_recycle (length (ex ++ popped)) (ex ++ popped).

(* free_cf: cgif's free (YG00.v:540-558) with maybe_drain_cf. Its two "not a live block"
   checks are tagged FModel, not with cgif's image pcs (YG00.v:549, :551), so the shared
   text holds no address: both are IFail in either form, vacuous in amreal and refuted
   by ml_free_cf's premise (p = PNull \/ In (p, n) (blocks s)). enqueue and depot_put
   are cgif's, unchanged (enqueue keeps class kBatchClass's vacuous arm).
   Quarantine::Put's size test (compiler-rt llvmorg-20.1.8 sanitizer_quarantine.h:96-108; cgif 0x35690
   `bgeu max_size, size`): a chunk whose user size [ck_n] is above the quarantine's max_size is not quarantined;
   RecyclePassThrough (asan_allocator.cpp:255-263) frees it at once through QuarantineCallback::Recycle, which is
   [recycle_chunk], the function DoRecycle runs on each drained chunk. max_size is the cell inst + 0x318, which
   maybe_drain_cf's drain test reads too; both read it as kQuarantineMax, and each unit's const-cell list (as_const)
   pins the cell to that value. Put's tail test (`c->Size() > max_cache_size`) runs on both sides: maybe_drain_cf.
   The open machine premises over free_cf (YG0dcf.afree_realizes_cf; YGcfMallocCompose's
   adealloc_realizes_raw_cf_em / afree_realizes_cf_of_parts; YGcfMallocComposeE; YGcfReallocCompose; YGcfRealloc)
   now cover the recycle side as well: the Deallocate walk discharges it by its big-block arm (DGbigIF.DIfaceBig;
   the internal file BIG-ARM.md), and DIface's enqueue arms only for req_size n <= kQuarantineMax (YGcfDIface.di_shape_cf). *)
Definition free_cf (p : sptr) (trace : list Z) : M unit :=
tick ;;
s <- get ;;
(if st_internal_inited s then ret tt else modify (set_internal_inited true)) ;;
match p with
| PNull => ret tt
| _ =>
s <- get ;;
match find_user (st_chunks s) p with
| None => fail (FModel 11)
| Some k =>
(if match ck_state k with CAllocated => true | _ => false end then ret tt else fail (FModel 12)) ;;
depot_put trace ;;
let k' := mkChunk (ck_beg k) (ck_req k) CQuarantined in
modify (fun s => set_chunks (upd_chunk (st_chunks s) k') s) ;;
(if ck_n k' <=? kQuarantineMax then enqueue k' else recycle_chunk k') ;;
maybe_drain_cf
end
end.

(* Class kBatchClass keeps cgif's vacuous class-full arm on BOTH sides (malloc_cf's
   populate_cf and free_cf's enqueue call cgif's populate / map_more_user for it), so
   both model laws carry this room premise, and acall_pre_cf carries it for the walks. *)
Definition batch_room_cf (s : astate) : Prop :=
rg_mapped_user (reg s kBatchClass) + kUserMapSize <= kFreeArrayOffset.

End CF.

(* ---------------------------------------------------------------------------- *)
(* The refusal is a RETURN, not a failure: the arm yields PNull with the class     *)
(* flagged, and never IFail. These are the shape facts the leaf and the walk use. *)
Lemma add_hole_exh : forall l, existsb (fun h => fst h =? EXH_HOLE) (add_hole (EXH_HOLE, 0) l) = true.
Proof. intros l. unfold add_hole. cbn [existsb fst]. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma del_hole_exh : forall l, existsb (fun h => fst h =? EXH_HOLE) (del_hole EXH_HOLE l) = false.
Proof.
intros l. unfold del_hole. induction l as [|h t IH]; [reflexivity|].
cbn [filter]. destruct (fst h =? EXH_HOLE) eqn:E; cbn [negb].
- exact IH.
- cbn [existsb]. rewrite E. cbn [orb]. exact IH.
Qed.

(* The sentinel is inert in every place cgif reads a hole. *)
Lemma exh_hole_inert_lo : forall off : Z, 0 <= off -> EXH_HOLE + 0 <= off.
Proof. intros off H. unfold EXH_HOLE. lia. Qed.

(* A control entry is never a real secondary: needed_size n >= 64513 > 0 for every
   secondary request, while both tags are negative. *)
Lemma errb_tags_negative : ERRB_CAP_TAG < 0 /\ ERRB_SZ_TAG < 0.
Proof. unfold ERRB_CAP_TAG, ERRB_SZ_TAG. lia. Qed.
