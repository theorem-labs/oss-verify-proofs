(* CARRIED from commit 0deb5310273b0d538ec2a1697f391a1c8ad21c34,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfNames.v, sha256 ac8f42f6b2565a74892c6dbad22e2ed1aa3f182b2baed880c774bd2662702d5b (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: synced to proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfNames.v at a0fed4266a1b (CfImg gains cf_pc_deallocate / cf_pc_memcpy / cf_pc_snprintf / cf_pc_wrap_realloc / cf_img_lo / cf_img_top / the GOT and stack-guard fields); cgif's field set is a subset of it, so no field is lost. *)
(* Taken by path from a working branch a0fed4266a1b, provisional. *)
(* Theorem Labs, 2026-10: the event-free SECOND allocator instance (suffix cf), shared side.
   ONE instance shared by several units: everything a unit fixes is a PARAMETER here
   (CfImg for the image, CfParams for the sizes and the class set), never baked into the shared text.
   This file fixes the NAMES and TYPES. It is imported by no cgif core file; no cgif file is edited.
   Every name whose body is not yet written is a Section Variable, never an Axiom and never Admitted.
   Module names used: cgif_file's own (YG00, YG01, YG0d, YG0f, YG0n, YG0v, YK*, YA0i, YA0n, YM05) plus our cf
   files, so the same text compiles under either unit's prefix. YM05 (RunCeil) is a cgif_file module, not a
   unit-only one, so it is admissible in shared text. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0a. The IMAGE parameters. Every image address the shared text needs     *)
(*     enters through this class, so one shared text serves every image.   *)
(*     The LABEL fields (cf_pc_map_user, cf_pc_free_array, cf_pc_sec_idx,   *)
(*     cf_pc_malloc_max, cf_pc_depot_*, cf_pc_spin_*, cf_pc_errb_die) are   *)
(*     opaque model labels, never compared with a machine pc (amreal binds  *)
(*     them by `_`, YG0d.v:77-78); they are kept for consistency with       *)
(*     AGif0's mtag binding. Other unit-shared cgif functions keep cgif's   *)
(*     own label values, which is equally sound.                            *)
(*     malloc_context_size is 30 (kUnwindMax, YG00.v:37), so every          *)
(*     interceptor takes UnwindImpl's long branch: no pc here is a          *)
(*     short-branch pc and no c-asan ranout numeral is imported.            *)
Class CfImg := MkCfImg {
  cf_pc_map_user : Z;        (* YG00.v:285's tag; the cf arm replaces that mcheck, so this is used
                                only where class kBatchClass keeps cgif's vacuous text *)
  cf_pc_free_array : Z;      (* YG00.v:267 *)
  cf_pc_sec_idx : Z;         (* YG00.v:358 *)
  cf_pc_malloc_max : Z;      (* YG00.v:421 *)
  cf_pc_depot_ids : Z;       (* YG00.v:415 *)
  cf_pc_depot_frames : Z;    (* YG00.v:416 *)
  cf_pc_spin_freearray : Z;  (* YG00.v:278 *)
  cf_pc_spin_ptrarray : Z;   (* YG00.v:363 *)
  cf_pc_spin_shadow : Z;     (* YG00.v:433, :487 *)
  cf_pc_errb_die : Z;        (* NEW: MmapOrDie on the first class-full print *)
  cf_errbuf_obj : Z;         (* the error-message-buffer object; its vector is at +0 / +16 / +32 *)
  cf_exh_off : Z;            (* the per-class exhausted byte, RegionInfo + 68, stride 128 *)
  cf_pc_set_shadow_f5 : Z;   (* __asan_set_shadow_f5, for the frame-area consumer *)
  cf_pc_allocate : Z;        (* __asan::Allocator::Allocate's entry, c-asan's AllocG pcA *)
  cf_pc_poison : Z;          (* __asan_poison_memory_region, the harness's head hide *)
  cf_pc_unpoison : Z;        (* __asan_unpoison_memory_region, the harness's head show *)
  cf_pc_strcmp : Z;          (* __wrap_strcmp's entry *)
  cf_pc_strlen : Z;          (* __wrap_strlen's entry *)
  (* the realloc twin of the code record's pc_malloc_ra0 (cgif YG0f.v's acode, which this instance
     does not edit): the return pc that seeds call_trace for a realloc call *)
  cf_pc_realloc_ra0 : Z;
  cf_pc_wrap_realloc : Z;    (* the realloc interceptor's entry *)
  cf_pc_memcpy : Z;          (* memcpy's entry as called from the realloc path *)
  cf_got_memcpy : Z;         (* the GOT cell holding memcpy's address *)
  cf_real_memcpy : Z;        (* the real (uninstrumented) memcpy *)
  (* the image's own bounds: the lowest page-rounded PT_LOAD address and the page-rounded PT_LOAD end (the same
     rule as the per-unit YImgTop.v's IMG_LO / IMG_TOP). In the class so that no shared file imports one unit's
     YImgTop.v: each unit's generated CfImg instance carries its own. *)
  cf_img_lo : Z;
  cf_img_top : Z;
  (* the snprintf field's image facts (aa_snprintf_cf; the row text is YGcallSnp.v asnprintf_realizes_xrom) *)
  cf_pc_snprintf : Z;          (* __wrap_snprintf's entry (= __interceptor_trampoline_snprintf) *)
  cf_got_stack_chk_guard : Z;  (* the GOT cell holding &__stack_chk_guard that musl's printf chain loads *)
  cf_stack_chk_guard : Z;      (* __stack_chk_guard, the canary object (the GOT cell's initial content) *)
  cf_snprintf_glue : Z;        (* stack depth from __wrap_snprintf's entry down to musl vfprintf's entry *)
  cf_pc_deallocate : Z;        (* __asan::Allocator::Deallocate's entry, a Theorem Labs lane's DeallocG pcD *)
  (* Printf's two writable image cells (field round 3): the cells and the values __asan::AsanInitInternal stores
     in them at start-up (the ELF's own contents are "SanitizerTool" and 0). The silent GOT word ReportFile::Write
     tests is not here: it stays an image fact of the report walk (Main, 2026-10-30). *)
  cf_toolname_cell : Z;        (* __sanitizer::SanitizerToolName, the tool-name pointer *)
  cf_toolname_val : Z;         (* its start value: the address of the string "AddressSanitizer" *)
  cf_pfcb_cell : Z;            (* __sanitizer::PrintfAndReportCallback, the cell Printf calls through *)
  cf_pfcb_val : Z;             (* its start value: AppendToErrorMessageBuffer's entry *)
  (* the image's relocation-read-only range, PT_GNU_RELRO [p_vaddr, p_vaddr + p_memsz) (field round 3): an overlay byte
     at a non-owned address there equals the image's byte (YG0dcf.arodata_ok_cf), so reads there are the image's *)
  cf_relro_lo : Z;
  cf_relro_hi : Z;
  (* field round 3 part 3c: the read-only bytes the refill's class-full report reads (VSNPrintf's two formats, the tool
     name, the two jump-table words for 's' / 'u'), as (base, length) pairs read with in_zr, in that order; arodata_ok_cf
     covers them as it covers RELRO, so no call needs the overlay normal form (memnorm) *)
  cf_ro_reads : list (Z * Z)
}.

(* An errbuf step's effect on st_secs (errb_map_cf appends a capacity entry and re-tags the old one; errb_set_size
   grows its size entry in place or appends it; errb_retire re-tags): the old entries keep their place, a secondary's
   entry (sm_size >= 0) is untouched, an errbuf control entry (sm_size < 0) stays one and its sm_len does not shrink,
   and every appended entry is a control entry with sm_len >= 0. *)
Definition secs_errb_grow (l l' : list secmap) : Prop :=
(length l <= length l')%nat /\
(forall i sm, nth_error l i = Some sm -> exists sm', nth_error l' i = Some sm' /\
  (0 <= sm_size sm -> sm' = sm) /\ (sm_size sm < 0 -> sm_size sm' < 0 /\ sm_len sm <= sm_len sm')) /\
(forall i sm', (length l <= i)%nat -> nth_error l' i = Some sm' -> sm_size sm' < 0 /\ 0 <= sm_len sm').

(* THE ONE errbuf filter of the hull meters (Main 2026-10-30): an st_secs entry is a USER secondary iff its sm_size
   is >= 0; the errbuf's control entries carry a negative sm_size (YG00cf.v:56-63) and stay out of every meter (the
   errbuf is eager: eager_cf counts it by esec and errb_cap_cf charges it; it has no lazy hull). *)
Definition sec_user_cf (e : secmap) : bool := 0 <=? sm_size e.

(* ---------------------------------------------------------------------- *)
(* 0b. The UNIT parameters: the sizes and the frame-area class set, with    *)
(*     their side conditions as fields, so a unit instance must prove them  *)
(*     and no shared lemma depends on a unit's value.                       *)
(*     cf_malloc_max replaces cgif's MALLOC_MAX = 2 ^ 28 (YG00.v:39), too   *)
(*     small for both units. cf_nob replaces cgif's NOB = 2 ^ 29            *)
(*     (YF06.v:133, :171) where a unit needs a larger secondary.            *)
(*     cf_place_limit is c-asan's counting limit for the LPS placement      *)
(*     lemma at cf_nob (LPS-PLACEMENT-REUSE.md §5: 80,953 at 2 ^ 29;        *)
(*     37,264 at 2 ^ 30), supplied by the instance from c-asan's lemma.     *)
(*     Each unit's instance (lib/A/CfParams<unit>.v) records its values and  *)
(*     their sources. The request bound is n < cf_malloc_max, so the         *)
(*     admissible n runs to cf_malloc_max - 1, and cf_sizes_ok must hold     *)
(*     there: sec_map_size n is about n + 12,294, so cf_malloc_max = 2 ^ 30  *)
(*     overshoots cf_nob = 2 ^ 30, while 2 ^ 30 - 2 ^ 20 fits.               *)
(* The hulls of the LIVE secondaries (the chunks' extents' shadow hulls, the term asecA puts in w_A, YG0n.v:386-387).
   Moved here from YG0ncf.v (unchanged) so that CfParams's hull laws can name it. *)
Definition sec_live_hulls (S : astate) : Z :=
fold_right (fun k acc => match ck_beg k with
| PSec _ _ => Z.max 0 (sec_map_size (ck_req k) / 8 + 8192) + acc
| _ => acc end) 0 (st_chunks S).

(* The run's USER-secondary count and mapped total (the two meters a unit's driver bounds). Moved here from
   YG0ncf.v (unchanged) so that CfParams's hull laws can name them, as sec_live_hulls above. Both fold over
   st_secs under sec_user_cf, so the errbuf's control entries do not enter either meter. *)
Definition nsec_cf (S : astate) : Z := fold_right (fun sm acc => (if sec_user_cf sm then 1 else 0) + acc) 0 (st_secs S).
Definition sec_T_cf (S : astate) : Z :=
fold_right (fun sm acc => (if sec_user_cf sm then sm_len sm else 0) + acc) 0 (st_secs S).

(* The count rule of one malloc_cf n (and of the realloc forms over it) that returns q: at most d more user entries
   and at most t more bytes of their sm_len. Moved here from YGcfSecsStep.v (unchanged) so that CfParams's
   admission law cf_hull_adm_post can name secs_call_post, as nsec_cf / sec_T_cf above. *)
Definition secs_step (d t : Z) (s s' : astate) : Prop :=
nsec_cf s' <= nsec_cf s + d /\ sec_T_cf s' <= sec_T_cf s + t.
Definition secs_call_d (n : Z) (q : sptr) : Z :=
match q with PNull => 0 | _ => if from_primary n then 0 else 1 end.
Definition secs_call_t (n : Z) (q : sptr) : Z :=
match q with PNull => 0 | _ => if from_primary n then 0 else sec_map_size n end.
Definition secs_call_post (n : Z) (s : astate) (r : sptr * astate) : Prop :=
secs_step (secs_call_d n (fst r)) (secs_call_t n (fst r)) s (snd r).

(* The closed cap on every unit's hull term cf_hull (below): preset's sec_hulls_cf under its meter
   (<= 2 ^ 33 + 8192 * 2 ^ 17), reply after F1 the live hulls + 16384 per recycled secondary (<= 3,087,007,744 +
   16384 * 2 ^ 23 = 140,525,961,216, cf_hull_bound). The room of record leaves ASAN_VM_LMIN - ROOM_CF_NEED =
   22,538,915,328 B over it on live state and ASAN_VM_LMIN - (ROOM_CF_NEED + ROOM_CF_CUT_EXTRA) = 18,243,948,032 B at a
   drain cut (YGcfRoomCf.room_cf_margin / room_cf_cut_margin, by vm_compute). *)
Definition CF_HULL_MAX : Z := 2 ^ 35 + 2 ^ 37.

(* A run's st_secs between two states S, S' of one call or composition (cf_hull_mono_back): entries keep their place, their
   mapped length does not shrink, a dead entry stays dead, a user entry stays a user entry and a control entry a control
   entry, and appended entries have sm_len >= 0 (sec_alloc appends, sec_dealloc kills in place, the errbuf steps append
   or grow in place). *)
Definition secs_grow (l l' : list secmap) : Prop :=
(length l <= length l')%nat /\
(forall i sm, nth_error l i = Some sm -> exists sm', nth_error l' i = Some sm' /\ sm_len sm <= sm_len sm' /\
  (sm_live sm = false -> sm_live sm' = false) /\ (0 <= sm_size sm -> 0 <= sm_size sm') /\
  (sm_size sm < 0 -> sm_size sm' < 0)) /\
(forall i sm', (length l <= i)%nat -> nth_error l' i = Some sm' -> 0 <= sm_len sm').

Class CfParams := MkCfParams {
  cf_malloc_max : Z;
  cf_nob : Z;
  cf_place_limit : Z;
  cf_sec_live_max : Z;
  cf_fs_classes : list Z;
  cf_head : Z;               (* the bytes a harness hides at a block's start; 0 when it hides none *)
  cf_malloc_max_pos : 2 ^ 20 <= cf_malloc_max;
  cf_sizes_ok : forall n, 0 <= n < cf_malloc_max -> sec_map_size n <= cf_nob;
  (* the cf request bound never shrinks cgif's, so chunk_ok_cf_of_chunk_ok holds *)
  cf_malloc_max_ge : MALLOC_MAX <= cf_malloc_max;
  cf_nob_ok : cf_nob <= 2 ^ 30;
  cf_sec_live_nonneg : 0 <= cf_sec_live_max;
  cf_sec_live_ok : cf_sec_live_max <= cf_place_limit;
  (* what lets wf_sec_cf_of_wf_sec go through: the cf cap is never below cgif's *)
  cf_nob_sec_len : SEC_LEN_MAX <= cf_nob;
  (* keeps wsc_reserved at cgif's single-commit form, so YG07's sec_arr_small is
     replaced by a FIELD and not by a second-commit model. Each unit's instance records
     its value against its walk-provable count. *)
  cf_sec_live_commit : cf_sec_live_max < kPtrArrayEntriesPerCommit;
  cf_head_nonneg : 0 <= cf_head;
  (* the hidden head ends on a shadow-granule boundary, so AR_shadow_law_cf's block_shadow
     can start at p + cf_head (p is 16-aligned); 0 for a harness that hides no head. *)
  cf_head_al : cf_head mod 8 = 0;
  cf_fs_classes_ok : Forall (fun c => 0 <= c <= 10) cf_fs_classes;
  (* c-asan's LPS placement lemma (commit 820536849e5, SecGrantP.v):
     its NOB bounds and its counting condition at cf_place_limit (c-asan's limits: 80,953
     at NOB 2 ^ 29, 37,264 at 2 ^ 30; 80,954 fails at 2 ^ 29). *)
  cf_nob_lo : 536870912 <= cf_nob;
  cf_nob_al : cf_nob mod 4096 = 0;
  cf_place_ok : 0x2aaaaaaab000 + (257 * 25 + cf_place_limit) * (2 * cf_nob) + cf_nob <= 0x7fff7f800000;
  (* at least one secondary may be live, so ROOM_cf holds at the allocator's initial state *)
  cf_sec_live_pos : 0 < cf_sec_live_max;
  (* the unit's bound on the USER st_secs entries of a run, N = nsec_cf S (YG0ncf.v; sec_user_cf): preset's meter
     (YG0ncf.sec_meter_ok_cf) and reply's admission, which bounds kf = D + qsec_cf S (D its recycled secondaries) since
     D + qsec_cf S <= nsec_cf S (YGcfCker.kf_le_nsec_cf). Each unit's instance
     records its value and its source (fuzz_reply 2 ^ 23: 16384 * 2 ^ 23 fits the room, measured 5.56e6 evictions,
     frame SHADOW-REFUND.md:83; preset 2 ^ 17, frame PRESET-KMAX.md). *)
  cf_kmax : Z;
  cf_kmax_ok : 0 <= cf_kmax <= 2 ^ 24;
  (* the live-secondary cap stays strictly below the placement limit (Main 2026-10-30, from a Theorem Labs lane's F4):
     the errbuf grant's placement needs length (st_sec_arr S) + length (xs_cf ly S) <= cf_place_limit with
     length xs_cf <= 1 (YG0ncf.v xs_cf_length), which cf_sec_live_ok (<=) does not give. *)
  cf_sec_live_place_lt : cf_sec_live_max < cf_place_limit;
  (* the unit's bound on T, the MAPPED bytes of the USER st_secs entries of a run (sec_T_cf, YG0ncf.v: secondary maps,
     live and recycled; the errbuf's control entries stay out). With N = nsec_cf S <= cf_kmax it bounds
     sec_hulls_cf by cf_sec_total := cf_T_max / 8 + 8192 * cf_kmax (below). The unit's driver proves the meter
     sec_meter_ok_cf S (N <= cf_kmax, T <= cf_T_max) from the input length (Main 2026-10-30, route (B) counting).
     Each unit's instance records its value and its source (preset: frame/SEC-TOTAL-MEASURE.md; reply:
     frame/kmax/sec-total-reply.md). *)
  cf_T_max : Z;
  cf_T_max_ok : 0 <= cf_T_max <= 2 ^ 38;
  (* THE HULL TERM of abudget_cf (Main 2026-10-30, the fields form): the hulls the world's allowance holds for the
     secondaries. Preset (on wle, no hull refund): cf_hull := sec_hulls_cf (cgif's sec_hulls over the user entries of
     st_secs, sec_user_cf), cf_hull_ok := sec_meter_ok_cf, cf_rec_drop := fun _ => 0. Reply (after F1, the recycle
     re-hides the hull's interior): cf_hull := reply_hull_cf (sec_live_hulls S + 16384 * dead_secs_cf S, D = the user
     entries that are dead), cf_hull_ok := nsec_cf S <= cf_kmax (cf_kmax = 2 ^ 23 at reply), cf_rec_drop :=
     reply_rec_drop_cf (the hull less the 16384 the dead entry keeps; the re-hidden interior is at least LEN / 8 - 7168,
     a Theorem Labs lane). The laws below are what the layer and the walks use; each unit proves them for its instance
     (YGcfAbudget.v section 6 gives both instances' discharge lemmas). *)
  cf_hull : astate -> Z;
  cf_hull_ok : astate -> Prop;
  cf_rec_drop : Z -> Z;
  cf_hull_init : cf_hull init_state = 0;
  (* steps that touch neither st_secs nor the secondary chunks (primary grants and frees, the free-array growth) *)
  cf_hull_frame : forall S S', st_secs S' = st_secs S -> sec_live_hulls S' = sec_live_hulls S -> cf_hull S' = cf_hull S;
  (* a granted secondary map of L bytes: its user entry (z = its needed size, >= 0) is appended live and its chunk adds
     its hull *)
  cf_hull_alloc : forall S S' L z, 0 <= L -> 0 <= z -> st_secs S' = st_secs S ++ [mkSec L z true] ->
    sec_live_hulls S' = sec_live_hulls S + Z.max 0 (L / 8 + 8192) -> cf_hull S + Z.max 0 (L / 8 + 8192) <= cf_hull S';
  (* an errbuf step *)
  cf_hull_errb : forall S S', secs_errb_grow (st_secs S) (st_secs S') -> sec_live_hulls S' = sec_live_hulls S ->
    cf_hull S <= cf_hull S';
  (* a secondary recycle: the chunk leaves st_chunks, its live entry turns dead; the hull term drops by at most what
     the world drops beyond the map (0 on wle; the re-hidden interior under F1) *)
  cf_hull_recycle : forall X X2 pre k post r off sm, st_chunks X = pre ++ k :: post -> st_chunks X2 = pre ++ post ->
    ck_beg k = PSec r off -> nth_error (st_secs X) r = Some sm -> sm_live sm = true -> 0 <= sm_size sm ->
    sm_len sm = sec_map_size (ck_req k) -> st_secs X2 = lupd (st_secs X) r (mkSec (sm_len sm) (sm_size sm) false) ->
    cf_hull X - cf_hull X2 <= cf_rec_drop (sm_len sm);
  (* the cap, given the bound on the live hulls at a drain cut, which also covers live state (AbudgetRestate
     2026-10-30, option (A)): 3,087,007,744 = (SEC_LIVE_MAX + CUT_PEND_MAX) / 8 + 8192 * kPtrArrayEntriesPerCommit
     (YGcfRoomCf.live_hulls_cut_val; the cut's bound live_hulls_bound_cut_cf), above live state's
     SEC_LIVE_MAX / 8 + 8192 * kPtrArrayEntriesPerCommit = 2,818,572,288 (YG08cf.live_hulls_bound_cf). Preset's
     sec_hulls_cf ignores it; reply's 3,087,007,744 + 16384 * 2 ^ 23 = 140,525,961,216 <= CF_HULL_MAX. *)
  cf_hull_bound : forall S, cf_hull_ok S -> sec_live_hulls S <= 3087007744 -> cf_hull S <= CF_HULL_MAX;
  (* the admission is backward-monotone along a run (Main 2026-10-30): the meters only grow, so a composition that holds
     cf_hull_ok at its own post derives it at an inner state *)
  cf_hull_mono_back : forall S S', secs_grow (st_secs S) (st_secs S') -> cf_hull_ok S' -> cf_hull_ok S;
  (* the admission reads only the two meters (Main 2026-10-30, for the realloc form): a step that moves neither the
     user count nor the user mapped total carries cf_hull_ok in either direction, with no hull arithmetic. Both
     instances are meters-only: preset's sec_meter_ok_cf is the pair of bounds, reply's is the count bound. *)
  cf_hull_counts : forall S S', nsec_cf S' = nsec_cf S -> sec_T_cf S' = sec_T_cf S -> cf_hull_ok S' -> cf_hull_ok S;
  (* the start state's admission: both meters are 0 at init (YGcfAbudget.v section 6: preset_hull_ok_init,
     reply_hull_ok_init) *)
  cf_hull_ok_init : cf_hull_ok init_state;
  (* an errbuf step keeps the admission (Main 2026-10-30): it leaves every user entry of st_secs as it is and appends
     only control entries (sm_size < 0), so neither meter moves (YGcfAbudget.v section 6: preset_hull_ok_errb,
     reply_hull_ok_errb) *)
  cf_hull_ok_errb : forall S S', secs_errb_grow (st_secs S) (st_secs S') -> sec_live_hulls S' = sec_live_hulls S ->
    cf_hull_ok S -> cf_hull_ok S';
  (* the ENTRY HEADROOM of one allocator call of request n (Main + a Theorem Labs lane 2026-10-30, for the primed realloc):
     admission with room for the call's own charge, so the call's post is admitted. Each unit states it in the CHARGE
     form of secs_call_post (reply: nsec_cf S + (if from_primary n then 0 else 1) <= cf_kmax; preset adds the T
     charge), and proves the law by its meters (YGcfAbudget.v section 6: reply_hull_adm_post, preset_hull_adm_post) *)
  cf_hull_adm : astate -> Z -> Prop;
  cf_hull_adm_post : forall S n q S', cf_hull_adm S n -> secs_call_post n S (q, S') -> cf_hull_ok S'
}.

(* Content constants, no address and no unit: ERRB_INIT is kErrorMessageBufferSize;
   exh_len1 / exh_len2 are the two Printf lengths of the class-full report
   (msgpack Spec/AsanCtrl.v:335, :361, :362, at release ref b6a0088adc). *)
Definition ERRB_INIT : Z := 65536.
Definition ndigits (z : Z) : Z :=
  if z <? 10 then 1 else if z <? 100 then 2 else if z <? 1000 then 3 else if z <? 10000 then 4 else 5.
Definition exh_len1 : Z := 33.
Definition exh_len2 (c : Z) : Z := 60 + ndigits c + ndigits (class_size c).
(* kAsanUserPoisonedMemoryMagic, the value __asan_poison_memory_region writes.
   cgif's own shadow values are YG00.v:40-43. *)
Definition shUserPoison : Z := 0xf7.

(* The room ceiling of the lib interface. It replaces cgif's `st_nev S + EV_LIB <=
   EV_MAX` by `abudget_cf S + CF_LIB <= CF_MAX` (h-pre-b1, closedwalk-plan.md:352 §3c);
   CF_LIB, LIB_ROOM and PINV are h-pre-b1's, CF_MAX is ours.
   abudget_cf carries prim_committed, 8 * st_sec_reserved, sec_live_bytes, the live
   hulls and errb_cap, so ameter_cf is just E_BASE + abudget_cf: unlike cgif's ameter
   (YG0n.v:542), which adds those terms beside abudget and so counts sec_live_bytes
   twice, nothing is double-counted. mroom_cf S is E_BASE + abudget_cf S + VM_HEAD <=
   ASAN_VM_LMIN, which is exactly abudget_cf S <= CF_MAX.
   ASAN_VM_LMIN = 2 ^ 39 (YG0n.v:284), VM_HEAD = 2 ^ 30 (:543), E_BASE = 2 ^ 30 (:285),
   so CF_MAX = 2 ^ 39 - 2 ^ 31 = 547,608,330,240.
   What it has to cover, after start-up, is exactly what abudget_cf counts (c-asan,
   OPTS-REFUSAL-REUSE.md): prim_committed, at most 31 * (kFreeArrayOffset +
   kFreeArrayMax) = 1.33e11; the secondary reservations 8 * st_sec_reserved, at most
   8 * kMaxNumChunks = 8.4e6; and the live secondary bytes with their hulls. NO DEPOT
   TERM is needed: the depot lives in the nodes and store blocks, kNodesBlockSize =
   2 ^ 20 and kStoreBlockSize = 2 ^ 23 (YG0f.v:33-34), which are permanent maps of
   constant size made at start-up (perm_maps, YG0n.v:306-308) and already inside
   lazy_zones (:300-305); the depot grows only by filling them, under its own capacity
   checks (kDepotIdsPerBlock = 65,536 and kStoreFramesPerBlock = 2 ^ 20, YG00.v:35-36,
   used at :407-408), so it adds no new map and no event-keyed term. *)
Definition CF_MAX : Z := ASAN_VM_LMIN - VM_HEAD - E_BASE.

(* The most free array a single free can add to prim_committed: the free path's
   return_to_allocator may grow a class's free array (YG00.v:461-466), and each is capped
   at kFreeArrayMax (cls_ok_cf's wrc_fa_bound), over at most 32 regions.
   FA_GROW_MAX = 32 * 2 ^ 29 = 17,179,869,184. abudget_cf counts the growth with its shadow
   (prim_committed / 8), so it rises by at most FA_GROW_MAX + FA_GROW_MAX / 8
   (YG0ncf.abudget_cf_fa_grow), and acall_pre_cf's conjunct `abudget_cf S + FA_GROW_MAX + FA_GROW_MAX / 8 <= CF_MAX`
   (YG0dcf.v) is exactly free_fa_grow_funded_cf's premise. *)
Definition FA_GROW_MAX : Z := 32 * kFreeArrayMax.

(* A_BASE_CF absorbs the whole event credit cgif's small regime can grant, so that
   cgif's abudget_ok implies ours at the conversion point ARcf_nil, once class 1's shadow
   band is exposed at the new world W' and sec_hulls S + cls1_band_bytes_cf fits the credit:
   EV_A * st_nev S < EV_A * EV_MAX whenever aregime holds in its small branch
   (YG01.v:308-309). A_BASE = 2 ^ 32 (YG0n.v:378), EV_A = 2 ^ 20 (:379),
   EV_MAX = 2 ^ 13 (YG00.v:38), so A_BASE_CF = 2 ^ 32 + 2 ^ 33 = 12,884,901,888. *)
Definition A_BASE_CF : Z := A_BASE + EV_A * EV_MAX.

(* The run row's hull total (Main 2026-10-30): the hulls of N <= cf_kmax entries of T <= cf_T_max mapped bytes are
   at most cf_T_max / 8 + 8192 * cf_kmax (YG0ncf.sec_hulls_le_meter). Unit-independent cap: 2 ^ 35 + 2 ^ 37. *)
Definition cf_sec_total {cp : CfParams} : Z := cf_T_max / 8 + 8192 * cf_kmax.
Lemma cf_sec_total_bound {cp : CfParams} : 0 <= cf_sec_total <= 2 ^ 35 + 2 ^ 37.
Proof.
unfold cf_sec_total. pose proof cf_T_max_ok as T. pose proof cf_kmax_ok as K.
assert (D : 0 <= cf_T_max / 8 <= 2 ^ 35) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). lia.
Qed.

Section Names.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------- *)
(* 1. The state invariant: YG01cf.v (written, green).                       *)
(*    WfP_cf = cgif's WfP (YG01.v:431-453), field by field:                 *)
(*      KEPT    the four event fields, which are LOWER bounds on st_nev     *)
(*              (:331, :332, :335, :344) and so survive any event count;    *)
(*      DROPPED wf_regime (:345), an UPPER bound on st_nev;                 *)
(*      CHANGED wf_classes to wf_class_cf, whose wrc_mapped_bound is        *)
(*              `rg_mapped_user r <= kFreeArrayOffset`, the bound the real  *)
(*              class-full arm maintains (it tests + map_size BEFORE the    *)
(*              map, YG00.v:285), in place of the 2 GiB `kUserMapSize *     *)
(*              EV_MAX` of YG01.v:380;                                      *)
(*      CHANGED wf_fa_room, whose slack 2 * (EV_MAX - st_nev) goes negative *)
(*              past EV_MAX, to the constant FA_SLACK;                      *)
(*      ADDED   wfc_compl0 (Compl0), which funds the free array in place of *)
(*              the event budget, and wfc_sec_live, which replaces          *)
(*              sec_arr_small (YG07.v:252-256).                             *)
Variable cls_ok_cf : forall (c : Z) (r : region) (p : pclass) (inited : bool) (ko bo : list Z), Prop.
Variable wf_class_cf : forall (s : astate) (c : Z), Prop.
Variable WfP_cf : forall (U : list (list Z)) (pp cc bb : Z) (s : astate), Prop.
Variable Wf_cf : forall (U : list (list Z)) (s : astate), Prop.
Variable sec_live_bound_cf : Prop.
Variable nrec_bound_cf : Prop.
Variable live_bound_cf : Prop.

(* ---------------------------------------------------------------------- *)
(* 2. The model with the class-full arm: YG00cf.v.                          *)
(*    malloc_cf keeps malloc's type (YG00.v:419), so a Theorem Labs lane's parametric    *)
(*    realloc (ReallocP.v's mt) instantiates over it by substitution.       *)
(*    free_cf is cgif's free with maybe_drain replaced by maybe_drain_cf,   *)
(*    the REAL MergeBatches (YG00cf.v); class kBatchClass keeps cgif's      *)
(*    vacuous arm on both sides.                                            *)
Variable errb_report_cf : forall (c : Z), M unit.
Variable map_more_user_cf : forall (c need : Z), M bool.
Variable populate_cf : forall (c need : Z), M bool.
Variable get_from_allocator_cf : forall (c n : Z), M (option (list Z)).
Variable refill_if_empty_cf : forall (c : Z), M unit.
Variable cache_alloc_cf : forall (c : Z), M (option Z).
Variable malloc_cf : Z -> list Z -> M sptr.
Variable free_cf : sptr -> list Z -> M unit.
Variable errb_mapped_cf : astate -> bool.
Variable errb_cap_cf : astate -> Z.
Variable errb_size_cf : astate -> Z.
Variable exh_mem_cf : forall (s : astate) (c : Z), bool.

(* ---------------------------------------------------------------------- *)
(* 3. The ghost set Hp, and the relational layer: YG0ncf.v.                 *)
(*    cgif's shadow_ok (YG0n.v:186-187) demands shadow 0 over every live    *)
(*    block's user bytes. A harness that hides a head (poisons the first    *)
(*    cf_head bytes of each block it hands out) breaks that, and the head   *)
(*    is NOT a function of the allocator state: it is poisoned after the    *)
(*    allocator returns and unpoisoned before the block goes back, and      *)
(*    blocks the runtime allocates for itself never have one.               *)
(*    Hp : list Z is a GHOST list of currently hidden block bases, carried  *)
(*    as an explicit argument. Not a field: cgif's `world` (YA0n.v:18-22)   *)
(*    and `astate` (YG00.v:154-168) are records this instance keeps, and an *)
(*    existential inside ARmcf would not let a poison step NAME the set it  *)
(*    grows. A unit whose harness hides nothing takes Hp = [], and          *)
(*    shadow_ok_cf_nil below says that is exactly cgif's shadow_ok.         *)
Definition in_head (Hp : list Z) (g : Z) : bool :=
  existsb (fun p => (p <=? g) && (g <? p + cf_head)) Hp.

Definition shadow_ok_cf (B : asyms) (ly : alayout) (Hp : list Z) (rd : reader) (S : astate) : Prop :=
  forall g v, g mod 8 = 0 -> ashadow B ly S g = Some v ->
    rd (shadow_addr g) = Some (if in_head Hp g then shUserPoison else v).

Lemma shadow_ok_cf_nil : forall B ly rd S, shadow_ok_cf B ly [] rd S <-> shadow_ok B ly rd S.
Proof.
intros B ly rd S. unfold shadow_ok_cf, shadow_ok, in_head. cbn [existsb].
split; intros H g v Hg Hv; exact (H g v Hg Hv).
Qed.

(* ARmcf = cgif's ARm (YG0n.v:205-225) with am_wf -> Wf_cf, am_cells over acells_cf
   (region_cells' RI+68 no longer pinned to 0, YG0n.v:38), am_shadow -> shadow_ok_cf,
   and ONE added field, am_hp_live: every base in Hp is the user base of a live block
   of size at least cf_head. Without it a stale base surviving a free makes malloc_cf's
   own post unprovable when the allocator hands the same address out again; with it,
   "the new block is not in Hp" is DERIVED, not assumed. *)
Variable acells_cf : astate -> list acell.
Variable ajunk_cf : forall (B : asyms) (ly : alayout) (S : astate), list (aexp * Z).
Variable region_cells_cf : forall (ly : alayout) (S : astate) (c : Z), list acell.
Variable ARmcf : forall (B : asyms) (ly : alayout) (S : astate) (Hp : list Z) (rd : reader), Prop.

Section Rel.
Variable segs : list Segment.
Variable B : asyms.

Variable ALedger_cf : forall (ly : alayout) (S : astate) (md : Model), Prop.
Variable abudget_cf : astate -> Z.
Variable abudget_ok_cf : forall (ly : alayout) (S : astate) (W : world segs), Prop.
Variable ahs_cf : forall (ly : alayout) (S : astate) (H : word -> bool) (mem : word -> option byte), Prop.
Variable ARcf : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model), Prop.
Variable ameter_cf : astate -> Z.
Variable mroom_cf : astate -> Prop.
Variable qmeter_cf : astate -> Prop.

(* ---------------------------------------------------------------------- *)
(* 4. The call forms over ARcf: YG0dcf.v. 21 of the 23 declarations of      *)
(*    YG0d.v are restated; chain_pre (:218) and call_trace (:224) name      *)
(*    neither AR nor Wf and are reused as they stand. acall_pre_cf is       *)
(*    YG0d.v:238-246 with `aregime S` (:228) DROPPED and qmeter (:234)      *)
(*    replaced by qmeter_cf, which has no EV_A * st_nev term. Every         *)
(*    allocator call leaves Hp unchanged, so one Hp runs through pre and    *)
(*    post; only a harness poison / unpoison step moves it.                 *)
Variable acall_pre_cf : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)), Prop.
Variable acall_post_cf : forall (stk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (E : Z -> Prop)
  (ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model), Prop.
Variable ecall_pre_cf : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model), Prop.
Variable ascratch_cf : forall (stk : Z) (regs : bvmap 5 word) (a : Z), Prop.
Variable malloc_leaf_cf : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (n : Z)
  (r : sptr * astate) (W' : world segs) (c' : config), Prop.
Variable free_leaf_cf : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p : sptr) (n : Z)
  (r : unit * astate) (W' : world segs) (c' : config), Prop.
Variable amalloc_realizes_cf : Prop.
Variable afree_realizes_cf : Prop.
(* its primed twin under the re-hide (F1 row R1): YG0dcfR.afree_realizes_cf_rh *)
Variable afree_realizes_cf_rh : Prop.
Variable astack_malloc_realizes_cf : Z -> Prop.
Variable astack_free_law_cf : Prop.
Variable aset_shadow_realizes_cf : forall (pc v : Z), Prop.
Variable dest_ok_cf : forall (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (d n : Z), Prop.
Variable src_ok_cf : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (s n : Z), Prop.
Variable aintrin_realizes_cf : memop -> Z -> Prop.
Variable amemcmp_realizes_cf : Z -> Prop.
Variable abcmp_realizes_cf : Z -> Prop.
Variable amemchr0_realizes_cf : Z -> Prop.
Variable astrnlen_realizes_cf : Z -> Prop.
(* strndup: strnlen, malloc of k + 1, copy, NUL.
   Defined in YG0dcf.v over malloc_cf, landing in strndup_leaf_cf. *)
Variable astrndup_realizes_cf : Z -> Z -> Prop.
Variable ablocks_cf : forall (ly : alayout) (S : astate), list (Z * Z).

(* The shadow law of YG0s.v:771 (AR_shadow_law_ok) is FALSE for a unit whose harness
   hides a head: it derives block_shadow over the WHOLE user range from am_shadow.
   AR_shadow_law_ok_cf restates it over shadow_ok_cf with Hp: shadow 0 on
   [p + cf_head, p + req_size n) always, and on [p, p + cf_head) exactly when p is not
   in Hp; shadow_hull_vis is unchanged, since presence does not depend on the value.
   The other YG0s shadow laws need no cf form: AR_zshadow_law_ok (:65) is the stack and
   the static zero ranges, ashadow_total (:729) and hull_inside (:751) are presence and
   geometry, and shadow_addr_bounds (:92) / shadow_range_below (:105) / owned_shadow_*
   (:112, :155) are address arithmetic. *)
Variable AR_shadow_law_ok_cf : Prop.
Variable AR_zshadow_law_ok_cf : Prop.

(* The harness steps that move Hp, and the realloc pre / post pair.
   The ALLOCATOR never moves Hp; only (b) and (c) do.
   (a) malloc_cf success: Hp unchanged; the new block is not in Hp, so its whole user
       range has shadow 0 and a harness may write its head before hiding it.
   (b) poison p: Hp := p :: Hp, for p a live base of size at least cf_head.
   (c) unpoison p: Hp := remove Z.eq_dec p Hp.
   (d) realloc success, old block p freed, new block q: POST Hp' = remove p Hp. Stated
       in the POST, not as a precondition, because ReallocP.v's cpre does not receive p
       while its rleaf does; and it must be the post, since p's head granules become
       quarantine 0xfd, so leaving p in Hp would make shadow_ok_cf false.
   (e) realloc NULL: the old block, its bytes, its shadow and Hp are all unchanged. *)
Variable hp_malloc_cf : Prop.
Variable ahead_poison_law : Prop.
Variable ahead_unpoison_law : Prop.
Variable realloc_cf_hp_post_ok : Prop.
Variable realloc_cf_hp_post_null : Prop.
(* The realloc contract: the instances of c-asan's ReallocP.v P forms (91224afc3ad) at
   mt := malloc_cf, cpre := acall_pre_cf at a fixed Hp, rpre := fun _ _ => True (no
   aregime), nmax := cf_malloc_max, lmax := LIVE_MAX, rleaf / mleaf := our leaves, with
   the Hp effects (d) / (e) in the post. arealloc_null_realizes_cf takes no B, as
   arealloc_null_realizesP does not. *)
Variable arealloc_realizes_cf : Prop.
(* its primed twin under the re-hide (F1 row R1): YG0dcfR.arealloc_realizes_cf_rh *)
Variable arealloc_realizes_cf_rh : Prop.
Variable arealloc_null_realizes_cf : Prop.
(* The harness's two shadow calls over ARcf, in port-fm's shape
   (FMupoison.v at 8d043571f33: upoison_ok_one :202, ARU_poison_step :263,
   ARU_unpoison_step :333; its ARU_nil :37 is the precedent for shadow_ok_cf_nil).
   A poison of [p, p + cf_head) adds p to Hp, an unpoison removes it: laws (b) / (c).
   The pcs are per-image code-table fields, never literals here. *)
Variable apoison_realizes_cf : Prop.
Variable aunpoison_realizes_cf : Prop.
(* The forced-success arm, PROVED from live state instead of assumed (a harness whose realloc
   sites abort() on a refusal needs "no PNull" as a fact). If the request is secondary, or its class has room by the
   arm's own test, or a free chunk is already cached, malloc_cf does not return PNull.
   It replaces cgif's amalloc04_rule (YC5d.v:56-72), which simply promised success. *)
Variable malloc_cf_success_of_room : Prop.
(* The lib interface's room, h-pre-b1's premise shape with our ceiling. CF_LIB is the
   per-call allowance the walk layer chooses; LIB_ROOM and CF_MAX are ours. *)
Variable abudget_cf_of_state : astate -> Z.
Definition LIB_ROOM (CF_LIB : Z) (S : astate) : Prop := abudget_cf_of_state S + CF_LIB <= CF_MAX.
(* The closed-walk layer (h-pre-b1 / K0). Rule used: cgif's EXACT argument order and
   result type, with Hp inserted right after S and Hp' right after S'.
   afn_pre is YCbq.v:337-344 (AR + ret_ok + astk_ok :332 + the present stack window +
   achain :217 + qtight); ajournal is YCbq.v:351-354. astk_ok and achain name neither
   AR nor Wf, so both are REUSED unchanged.
   ajournal_cf KEEPS k, because cgif's has it (YCbq.v:354, used at :356 as
   `st_nev S' <= st_nev S + k`): that is a RELATIVE per-segment event count, not a cap
   on st_nev, so it survives the event-free re-base untouched and dropping it would
   lose a real fact. It also takes Hp', because a journalled segment may call the
   harness's allocation wrappers, which poison and unpoison.
   apost_base has NO cgif original in this unit (searched all of lib/: zero
   definitions), so its shape is K0's, with Hp in the pre and the post Hp as Q's third
   argument. *)
Variable afn_pre_cf : forall (STK : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)), Prop.
Variable ajournal_cf : forall (STK sp0 : Z) (FP : list (Z * Z))
  (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
  (own : list (Z * Z))
  (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs) (mem' : word -> option byte)
  (md' : Model) (k : Z), Prop.
Variable apost_base_cf : forall (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word)
  (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
  (Q : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  world segs -> config -> Prop.
(* The switch point RUNQM: cgif's AR at S implies ARcf at S with Hp = [], at an exposed world
   W' (wle W W') that adds class 1's shadow band. Wf_cf's part is WfP_cf_of_WfP (YG01cf.v);
   the rest of ARmcf is copied verbatim, and am_hp_live is trivial at Hp = []. The driver
   switches once, at main (init_state); every site before it keeps cgif's AR. *)
Variable ARcf_nil : Prop.
Variable AR_laws_cf : Prop.

(* The NULL post and the three lemmas c-asan's parametric realloc consumes. The OOM
   cell's ADDRESS is per image (as_oom_byte B), never a literal here; errno = 12 is
   stated only because that interface asks for it. *)
Variable malloc_cf_null_post : forall (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (n : Z)
  (r : sptr * astate) (W' : world segs) (c' : config), Prop.
Variable malloc_cf_null_blocks : Prop.
Variable malloc_cf_post_pre : Prop.
Variable malloc_cf_copy_ok : Prop.

End Rel.

(* model_laws_cf is over Wf_cf and has NO `st_nev < EV_MAX` premise (YG0d.v:515, :517). *)
Variable model_laws_cf : Univ -> Prop.

End Names.

(* The API record the consumers take. aa_stack_malloc_cf carries the unit's frame-area
   class set as the parameter cf_fs_classes (cgif's YG0d.v:548 is cid = 1 \/ cid = 2;
   each unit's instance lists its live frame-area classes). aa_set_shadow_f5_cf is cgif_rgb's YG0e.v:48
   form at value 0xf5, with the pc the per-image field cf_pc_set_shadow_f5.
   In YG0dcf.v this record is built over the real definitions and takes only (segs B);
   here the components are Variables, so the stub's record carries them as parameters. *)
Section API.
Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable AR_laws_cf : forall (segs : list Segment) (B : asyms), Prop.
Variable model_laws_cf : Univ -> Prop.
Variable amalloc_realizes_cf : forall (segs : list Segment) (B : asyms), Prop.
Variable afree_realizes_cf : forall (segs : list Segment) (B : asyms), Prop.
Variable astack_malloc_realizes_cf : forall (segs : list Segment) (B : asyms) (cid : Z), Prop.
Variable astack_free_law_cf : forall (segs : list Segment) (B : asyms), Prop.
Variable aset_shadow_realizes_cf : forall (segs : list Segment) (B : asyms) (pc v : Z), Prop.
Variable aintrin_realizes_cf : forall (segs : list Segment) (B : asyms) (op : memop) (pc : Z), Prop.
Variable amemcmp_realizes_cf : forall (segs : list Segment) (B : asyms) (pc : Z), Prop.
Variable abcmp_realizes_cf : forall (segs : list Segment) (B : asyms) (pc : Z), Prop.
(* c-libc-stdio's interceptor contracts (YGcfStr.v, cold/c-libc-stdio-presetstr), cgif's call-form
   shape over ARcf. *)
Variable astrcmp_realizes_cf : forall (segs : list Segment) (B : asyms) (pc : Z), Prop.
Variable astrlen_realizes_cf : forall (segs : list Segment) (B : asyms) (pc : Z), Prop.
Variable arealloc_realizes_cf : forall (segs : list Segment) (B : asyms), Prop.
Variable arealloc_null_realizes_cf : forall (segs : list Segment), Prop.
Variable apoison_realizes_cf : forall (segs : list Segment) (B : asyms), Prop.
Variable aunpoison_realizes_cf : forall (segs : list Segment) (B : asyms), Prop.
(* the snprintf row (YGcallSnp.v asnprintf_realizes_xrom, c-omx-alloc's, at ARx := ARcf segs B); the instance fixes
   the format family, the window, the canary cells, the image range, the read-only ranges and the relro range *)
Variable asnprintf_realizes_cf : forall (segs : list Segment) (B : asyms) (pc : Z), Prop.

Record AsanAPI_cf (segs : list Segment) (B : asyms) := {
  aa_laws_cf : forall {fx : YK11.FPState}, AR_laws_cf segs B;
  aa_model_cf : model_laws_cf (as_universe B);
  aa_malloc_cf : forall {fx : YK11.FPState}, amalloc_realizes_cf segs B;
  aa_free_cf : forall {fx : YK11.FPState}, afree_realizes_cf segs B;
  aa_stack_malloc_cf : forall {fx : YK11.FPState} cid, In cid cf_fs_classes -> astack_malloc_realizes_cf segs B cid;
  aa_stack_free_cf : forall {fx : YK11.FPState}, astack_free_law_cf segs B;
  aa_realloc_cf : forall {fx : YK11.FPState}, arealloc_realizes_cf segs B;
  aa_realloc_null_cf : forall {fx : YK11.FPState}, arealloc_null_realizes_cf segs;
  aa_poison_cf : forall {fx : YK11.FPState}, apoison_realizes_cf segs B;
  aa_unpoison_cf : forall {fx : YK11.FPState}, aunpoison_realizes_cf segs B;
  aa_set_shadow_f5_cf : forall {fx : YK11.FPState}, aset_shadow_realizes_cf segs B cf_pc_set_shadow_f5 0xf5;
  aa_asan_memcpy_cf : forall {fx : YK11.FPState}, aintrin_realizes_cf segs B OCpy (pc_asan_memcpy (as_code B));
  aa_asan_memset_cf : forall {fx : YK11.FPState}, aintrin_realizes_cf segs B OSet (pc_asan_memset (as_code B));
  aa_memcpy_icpt_cf : forall {fx : YK11.FPState}, aintrin_realizes_cf segs B OCpy (pc_wrap_memcpy (as_code B));
  aa_memset_icpt_cf : forall {fx : YK11.FPState}, aintrin_realizes_cf segs B OSet (pc_wrap_memset (as_code B));
  aa_memcmp_cf : forall {fx : YK11.FPState}, amemcmp_realizes_cf segs B (pc_wrap_memcmp (as_code B));
  aa_bcmp_cf : forall {fx : YK11.FPState}, abcmp_realizes_cf segs B (pc_wrap_bcmp (as_code B));
  aa_strcmp_cf : forall {fx : YK11.FPState}, astrcmp_realizes_cf segs B cf_pc_strcmp;
  aa_strlen_cf : forall {fx : YK11.FPState}, astrlen_realizes_cf segs B cf_pc_strlen;
  aa_snprintf_cf : forall {fx : YK11.FPState}, asnprintf_realizes_cf segs B cf_pc_snprintf
}.
End API.
