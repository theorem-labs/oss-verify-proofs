(* copied from proofs/cgif/cgif_file_fuzzer/lib/YGcfNames.v @ 95e6f1d72b6 (c-asan, frozen), module paths changed only. *)
(* prefix-only copy of proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfNames.v@6e9ff2e6573c487199f2990b43c5e19cce86e581, do not edit (single writer: h-mani-a8; send change requests to h-mani-a8 as diffs). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free SECOND allocator instance (suffix cf), shared side.
   ONE instance for two units, fuzz_preset and fuzz_reply: everything a unit fixes is a PARAMETER here
   (CfImg for the image, CfParams for the sizes and the class set), never baked into the shared text.
   This file fixes the NAMES and TYPES. It is imported by no cgif core file; no cgif file is edited.
   Every name whose body is not yet written is a Section Variable, never an Axiom and never Admitted.
   Module names used: cgif_file's own (YG00, YG01, YG0d, YG0f, YG0n, YG0v, YK*, YA0i, YA0n, YM05) plus our cf
   files, so the same text compiles under either unit's prefix. YM05 (RunCeil) is a cgif_file module, not a
   preset-only one, so it is admissible in shared text. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/Reusable/YGcfNames.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0a. The IMAGE parameters. cgif's YG00 is not image-free: its FCheck and  *)
(*     spin pc arguments are image pcs in decimal (222820 at YG00.v:285 =   *)
(*     0x36664; cgif_rgb's same check is 222756). Every such pc enters      *)
(*     through this class, so one shared text serves every image.          *)
(*     malloc_context_size is 30 (kUnwindMax, YG00.v:37), so every          *)
(*     interceptor takes UnwindImpl's long branch: no pc here is a          *)
(*     short-branch pc and no c-asan ranout numeral is imported.            *)
Class CfImg := MkCfImg {
  cf_pc_map_user : Z;        (* YG00.v:285's tag; the cf arm replaces that mcheck, so this is used
                                only where class kBatchClass keeps cgif's vacuous text *)
  cf_pc_free_array : Z;      (* YG00.v:267 *)
  cf_pc_sec_idx : Z;         (* YG00.v:358 *)
  cf_pc_malloc_max : Z;      (* YG00.v:413 *)
  cf_pc_depot_ids : Z;       (* YG00.v:407 *)
  cf_pc_depot_frames : Z;    (* YG00.v:408 *)
  cf_pc_spin_freearray : Z;  (* YG00.v:278 *)
  cf_pc_spin_ptrarray : Z;   (* YG00.v:363 *)
  cf_pc_spin_shadow : Z;     (* YG00.v:425, :479 *)
  cf_pc_errb_die : Z;        (* NEW: MmapOrDie on the first class-full print *)
  cf_errbuf_obj : Z;         (* the error-message-buffer object; its vector is at +0 / +16 / +32 *)
  cf_exh_off : Z;            (* the per-class exhausted byte, RegionInfo + 68, stride 128 *)
  cf_pc_set_shadow_f5 : Z;   (* __asan_set_shadow_f5, for the frame-area consumer *)
  cf_pc_allocate : Z;        (* __asan::Allocator::Allocate's entry, c-asan's AllocG pcA *)
  cf_pc_poison : Z;          (* __asan_poison_memory_region, the harness's head hide *)
  cf_pc_unpoison : Z;        (* __asan_unpoison_memory_region, the harness's head show *)
  cf_pc_strcmp : Z;          (* __wrap_strcmp, 13 call sites in preset *)
  cf_pc_strlen : Z;          (* __wrap_strlen, 8 call sites in preset *)
  (* the realloc twin of the code record's pc_malloc_ra0 (cgif YG0f.v's acode, which this instance
     does not edit): the return pc that seeds call_trace for a realloc call *)
  cf_pc_realloc_ra0 : Z
}.

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
(*     Instances: preset 2 ^ 29 - 2 ^ 20 / 2 ^ 29 / measured / [0; 1; 3];   *)
(*     reply 2 ^ 30 - 2 ^ 20 / 2 ^ 30 / measured / [0; 1]. Reply's largest    *)
(*     request is exactly 2 ^ 29, and the bound is n < cf_malloc_max, so the   *)
(*     admissible n runs to cf_malloc_max - 1: at 2 ^ 30 that is 2 ^ 30 - 1,   *)
(*     whose sec_map_size is about 2 ^ 30 + 12,293 > cf_nob, and cf_sizes_ok   *)
(*     would fail. 2 ^ 30 - 2 ^ 20 admits 2 ^ 29 and keeps the map under NOB.  *)
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
     replaced by a FIELD and not by a second-commit model. Preset instantiates 16,000
     against a walk-provable 13,367 (SEC-PROOF.txt); reply 2 ^ 10 against 513. *)
  cf_sec_live_commit : cf_sec_live_max < kPtrArrayEntriesPerCommit;
  cf_head_nonneg : 0 <= cf_head;
  (* the hidden head ends on a shadow-granule boundary, so AR_shadow_law_cf's block_shadow
     can start at p + cf_head (p is 16-aligned): preset 16, reply 0. *)
  cf_head_al : cf_head mod 8 = 0;
  cf_fs_classes_ok : Forall (fun c => 0 <= c <= 10) cf_fs_classes;
  (* c-asan's LPS placement lemma (cold/c-asan-realloc-primary 820536849e5, SecGrantP.v):
     its NOB bounds and its counting condition at cf_place_limit. Preset: 2 ^ 29 with
     80,953 (80,954 fails); reply: 2 ^ 30 with 37,264. *)
  cf_nob_lo : 536870912 <= cf_nob;
  cf_nob_al : cf_nob mod 4096 = 0;
  cf_place_ok : 0x2aaaaaaab000 + (257 * 25 + cf_place_limit) * (2 * cf_nob) + cf_nob <= 0x7fff7f800000;
  (* at least one secondary may be live, so ROOM_cf holds at the allocator's initial state *)
  cf_sec_live_pos : 0 < cf_sec_live_max
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
   return_to_allocator may grow a class's free array (YG00.v:453-458), and each is capped
   at kFreeArrayMax (cls_ok_cf's wrc_fa_bound), over at most 32 regions. acall_pre_cf
   carries `abudget_cf S + FA_GROW_MAX <= CF_MAX`, so every such growth keeps mroom_cf,
   the LPS MAP_FIXED map is funded, and its refusal (a spin) is unreachable.
   FA_GROW_MAX = 32 * 2 ^ 29 = 17,179,869,184. *)
Definition FA_GROW_MAX : Z := 32 * kFreeArrayMax.

(* A_BASE_CF absorbs the whole event credit cgif's small regime can grant, so that
   cgif's abudget_ok implies ours at the conversion point ARcf_nil:
   EV_A * st_nev S < EV_A * EV_MAX whenever aregime holds in its small branch
   (YG01.v:201-202). A_BASE = 2 ^ 32 (YG0n.v:378), EV_A = 2 ^ 20 (:379),
   EV_MAX = 2 ^ 13 (YG00.v:38), so A_BASE_CF = 2 ^ 32 + 2 ^ 33 = 12,884,901,888. *)
Definition A_BASE_CF : Z := A_BASE + EV_A * EV_MAX.

Section Names.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------- *)
(* 1. The state invariant: YG01cf.v (written, green).                       *)
(*    WfP_cf = cgif's WfP (YG01.v:324-346), field by field:                 *)
(*      KEPT    the four event fields, which are LOWER bounds on st_nev     *)
(*              (:331, :332, :335, :344) and so survive any event count;    *)
(*      DROPPED wf_regime (:345), an UPPER bound on st_nev;                 *)
(*      CHANGED wf_classes to wf_class_cf, whose wrc_mapped_bound is        *)
(*              `rg_mapped_user r <= kFreeArrayOffset`, the bound the real  *)
(*              class-full arm maintains (it tests + map_size BEFORE the    *)
(*              map, YG00.v:285), in place of the 2 GiB `kUserMapSize *     *)
(*              EV_MAX` of YG01.v:273;                                      *)
(*      CHANGED wf_fa_room, whose slack 2 * (EV_MAX - st_nev) goes negative *)
(*              past EV_MAX, to the constant FA_SLACK;                      *)
(*      ADDED   wfc_compl0 (Compl0), which funds the free array in place of *)
(*              the event budget, and wfc_sec_live, which replaces          *)
(*              sec_arr_small (YG07.v:272-276).                             *)
Variable cls_ok_cf : forall (c : Z) (r : region) (p : pclass) (inited : bool) (ko bo : list Z), Prop.
Variable wf_class_cf : forall (s : astate) (c : Z), Prop.
Variable WfP_cf : forall (U : list (list Z)) (pp cc bb : Z) (s : astate), Prop.
Variable Wf_cf : forall (U : list (list Z)) (s : astate), Prop.
Variable sec_live_bound_cf : Prop.
Variable nrec_bound_cf : Prop.
Variable live_bound_cf : Prop.

(* ---------------------------------------------------------------------- *)
(* 2. The model with the class-full arm: YG00cf.v.                          *)
(*    malloc_cf keeps malloc's type (YG00.v:411), so c-asan's parametric    *)
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
(*    YG0d.v:226-234 with `aregime S` (:228) DROPPED and qmeter (:234)      *)
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
(* strndup (fuzz_reply's drain, 15 <= n <= 5,999): strnlen, malloc of k + 1, copy, NUL.
   Defined in YG0dcf.v over malloc_cf, landing in strndup_leaf_cf. *)
Variable astrndup_realizes_cf : Z -> Prop.
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
Variable arealloc_null_realizes_cf : Prop.
(* The harness's two shadow calls over ARcf, in port-fm's shape
   (FMupoison.v at 8d043571f33: upoison_ok_one :202, ARU_poison_step :263,
   ARU_unpoison_step :333; its ARU_nil :37 is the precedent for shadow_ok_cf_nil).
   A poison of [p, p + cf_head) adds p to Hp, an unpoison removes it: laws (b) / (c).
   The pcs are per-image code-table fields, never literals here. *)
Variable apoison_realizes_cf : Prop.
Variable aunpoison_realizes_cf : Prop.
(* The forced-success arm, PROVED from live state instead of assumed (preset audit N3,
   reply §5: at the harness's realloc sites a refusal is an abort(), so the walk needs
   "no PNull" as a fact). If the request is secondary, or its class has room by the
   arm's own test, or a free chunk is already cached, malloc_cf does not return PNull.
   It replaces cgif's amalloc04_rule (YC5d.v:56-72), which simply promised success. *)
Variable malloc_cf_success_of_room : Prop.
(* The lib interface's room, h-pre-b1's premise shape with our ceiling. CF_LIB is the
   per-call allowance the walk layer chooses; LIB_ROOM and CF_MAX are ours. *)
Variable abudget_cf_of_state : astate -> Z.
Definition LIB_ROOM (CF_LIB : Z) (S : astate) : Prop := abudget_cf_of_state S + CF_LIB <= CF_MAX.
(* The closed-walk layer (h-pre-b1 / K0). Rule used: cgif's EXACT argument order and
   result type, with Hp inserted right after S and Hp' right after S'.
   afn_pre is YCbq.v:335-342 (AR + ret_ok + astk_ok :332 + the present stack window +
   achain :217 + qtight); ajournal is YCbq.v:349-352. astk_ok and achain name neither
   AR nor Wf, so both are REUSED unchanged.
   ajournal_cf KEEPS k, because cgif's has it (YCbq.v:352, used at :356 as
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
(* The switch point RUNQM: cgif's AR at S implies ARcf at S with Hp = []. Wf_cf's part
   is WfP_cf_of_WfP (YG01cf.v); the rest of ARmcf is copied verbatim, and am_hp_live is
   trivial at Hp = []. Every driver site before the first harness call keeps cgif's AR. *)
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
Variable model_laws_cf : list (list Z) -> Prop.

End Names.

(* The API record the consumers take. aa_stack_malloc_cf carries the unit's frame-area
   class set as the parameter cf_fs_classes (cgif's YG0d.v:536 is cid = 1 \/ cid = 2;
   preset needs [0; 1; 3], reply [0; 1]). aa_set_shadow_f5_cf is cgif_rgb's YG0e.v:48
   form at value 0xf5, with the pc the per-image field cf_pc_set_shadow_f5.
   In YG0dcf.v this record is built over the real definitions and takes only (segs B);
   here the components are Variables, so the stub's record carries them as parameters. *)
Section API.
Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable AR_laws_cf : forall (segs : list Segment) (B : asyms), Prop.
Variable model_laws_cf : list (list Z) -> Prop.
Variable amalloc_realizes_cf : forall (segs : list Segment) (B : asyms), Prop.
Variable afree_realizes_cf : forall (segs : list Segment) (B : asyms), Prop.
Variable astack_malloc_realizes_cf : forall (segs : list Segment) (B : asyms) (cid : Z), Prop.
Variable astack_free_law_cf : forall (segs : list Segment) (B : asyms), Prop.
Variable aset_shadow_realizes_cf : forall (segs : list Segment) (B : asyms) (pc v : Z), Prop.
Variable aintrin_realizes_cf : forall (segs : list Segment) (B : asyms) (op : memop) (pc : Z), Prop.
Variable amemcmp_realizes_cf : forall (segs : list Segment) (B : asyms) (pc : Z), Prop.
Variable abcmp_realizes_cf : forall (segs : list Segment) (B : asyms) (pc : Z), Prop.
Variable amemchr0_realizes_cf : forall (segs : list Segment) (B : asyms) (pc : Z), Prop.
Variable astrnlen_realizes_cf : forall (segs : list Segment) (B : asyms) (pc : Z), Prop.
Variable astrndup_realizes_cf : forall (segs : list Segment) (B : asyms) (pc : Z), Prop.
(* c-libc-stdio's interceptor contracts (YGcfStr.v, cold/c-libc-stdio-presetstr), cgif's call-form
   shape over ARcf; preset calls __wrap_strcmp at 13 sites and __wrap_strlen at 8. *)
Variable astrcmp_realizes_cf : forall (segs : list Segment) (B : asyms) (pc : Z), Prop.
Variable astrlen_realizes_cf : forall (segs : list Segment) (B : asyms) (pc : Z), Prop.
Variable arealloc_realizes_cf : forall (segs : list Segment) (B : asyms), Prop.
Variable arealloc_null_realizes_cf : forall (segs : list Segment), Prop.
Variable apoison_realizes_cf : forall (segs : list Segment) (B : asyms), Prop.
Variable aunpoison_realizes_cf : forall (segs : list Segment) (B : asyms), Prop.

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
  aa_memchr_cf : forall {fx : YK11.FPState}, amemchr0_realizes_cf segs B (pc_wrap_memchr (as_code B));
  aa_strnlen_cf : forall {fx : YK11.FPState}, astrnlen_realizes_cf segs B (pc_wrap_strnlen (as_code B));
  aa_pc_strndup_cf : Z;
  aa_strndup_cf : forall {fx : YK11.FPState}, astrndup_realizes_cf segs B aa_pc_strndup_cf;
  aa_strcmp_cf : forall {fx : YK11.FPState}, astrcmp_realizes_cf segs B cf_pc_strcmp;
  aa_strlen_cf : forall {fx : YK11.FPState}, astrlen_realizes_cf segs B cf_pc_strlen
}.
End API.
