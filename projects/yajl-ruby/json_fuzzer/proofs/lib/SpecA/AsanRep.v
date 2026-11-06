(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition zw (z : Z) : word := Z_to_bv 64 z.
Definition zb (z : Z) : byte := Z_to_bv 8 z.
Definition zeros (n : nat) : list byte := repeat (zb 0) n.
Definition boolz (b : bool) : Z := if b then 1 else 0.

(* [comment removed for export] *)
Definition aic_flags_strdef (IC : aimg_consts) : Z := if aic_asan_flags IC =? 0xab378 then 0x13f6a else 0x13fa3.
Definition asan_flags_bytes (IC : aimg_consts) : list Z :=
  [0xff;0xff;0xff;0xff;0x00;0x01;0x00;0x00; 0x00;0x04;0x00;0x00;0x10;0x00;0x00;0x00; 0x00;0x08;0x00;0x00;0x00;0x00;0x00;0x00; 0x01;0x00;0x00;0x00;0x00;0x01;0x01;0x01;
   0x10;0x00;0x00;0x00;0x14;0x00;0x00;0x00; 0x00;0x00;0x00;0x00;0x00;0x10;0x00;0x00; 0x00;0x00;0x00;0x00;0xbe;0x00;0x00;0x00; 0x55;0x00;0x00;0x00;0x01;0x00;0x00;0x00;
   0x00;0x00;0x00;0x00;0x00;0x00;0x00;0x00; 0x00;0x00;0x00;0x00;0x01;0x00;0x01;0x00; 0x01;0x00;0x00;0x01;0x01;0x01;0x01;0x01; 0x01;0x00;0x00;0x00;0x00;0x00;0x00;0x00;
   0x01;0x00;0x00;0x00;0x02;0x00;0x00;0x00; aic_flags_strdef IC mod 256;(aic_flags_strdef IC / 256) mod 256;(aic_flags_strdef IC / 65536) mod 256;0x00;0x00;0x00;0x00;0x00; 0x01;0x01;0x01;0x00;0x00;0x00;0x00;0x00; 0x01;0x00;0x00;0x00;0x00;0x00;0x00;0x00].

Section REP.
Variable segs : list Segment.
Variable E : aenv.
Let IC := ae_ic E.
Let INST : Z := ae_instance E.
Let SB : Z := ae_space_beg E.
Let RI : Z := ae_region_info E.
Let T : Z := ae_thread E.

#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition region_of (s : astate) (c : Z) : region := get_region s c.

(* [comment removed for export] *)
Definition chunk_list (s : astate) : list (Z * chunkmeta) := map_to_list (as_chunks s).

(* [comment removed for export] *)
Fixpoint batch_nexts (l : list batch) : list Z :=
  match l with [] => [] | [b] => [0] | b :: (b' :: _ as rest) => b_addr b' :: batch_nexts rest end.
Definition list_first (l : list batch) : Z := match l with [] => 0 | b :: _ => b_addr b end.
Definition list_last (l : list batch) : Z := match l with [] => 0 | _ => b_addr (List.last l (mkBatch 0 [] 0)) end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition arep_instance (s : astate) (m : mem) : Prop :=
  RW m (INST + kInsSpaceBeg) [C8 (zw SB); C4 (zw 0xffffffff); C4 (zw 0); C8 (zw RI); C1 (zb 0)]
  /\ RW m (INST + kInsSecondary) [C8 (zw kPageSize); C8 (zw (ae_ptr_array E)); C8 (zw (ae_ptr_array E)); C8 (zw (2^23))]
  /\ RW m (INST + kInsNReserved) [C8 (zw (as_ptr_committed s)); C8 (zw (n_chunks s)); C1 (zb 0)]   (* [comment removed for export] *)
  /\ RW m (INST + kInsSecStats) [C8 (zw (ss_n_allocs (as_sec_stats s))); C8 (zw (ss_n_frees (as_sec_stats s)));
                                 C8 (zw (ss_cur (as_sec_stats s))); C8 (zw (ss_max (as_sec_stats s)))]
  /\ (exists bsl, u64arr segs m (INST + kInsSecStats + 32) bsl /\ length bsl = 64%nat)   (* [comment removed for export] *)
  /\ RW m (INST + kInsSecMutex) [C4 (zw 0)]                                                (* [comment removed for export] *)
  /\ RW m (INST + kInsGlobalStats + 16) [C8 (zw (as_glob_allocated s)); C8 (zw (as_glob_mapped s))]
  /\ RW m (INST + kInsQuarantine + 64) [C8 (zw kQuarantineMax); C8 (zw kQuarantineMin); C8 (zw kThreadQuarantineMax)]
  /\ RW m (INST + kInsQMutex) [C4 (zw 0)]                                               (* [comment removed for export] *)
  /\ RW m (INST + kInsQGlobal) [C8 (zw (qcount (as_gq s))); C8 (zw (list_first (as_gq s))); C8 (zw (list_last (as_gq s))); C8 (zw (gq_bytes s))]
  /\ RW m (INST + kInsFallbackMutex) [C1 (zb 0)]
  /\ RW m (INST + kInsMaxUserDefined) [C8 (zw (2^40)); C2 (zw kMinRedzone); C2 (zw kMaxRedzone); C1 (zb 1)].

(* [comment removed for export] *)
Definition arep_instanceL (qm : Z) (s : astate) (m : mem) : Prop :=
  RW m (INST + kInsSpaceBeg) [C8 (zw SB); C4 (zw 0xffffffff); C4 (zw 0); C8 (zw RI); C1 (zb 0)]
  /\ RW m (INST + kInsSecondary) [C8 (zw kPageSize); C8 (zw (ae_ptr_array E)); C8 (zw (ae_ptr_array E)); C8 (zw (2^23))]
  /\ RW m (INST + kInsNReserved) [C8 (zw (as_ptr_committed s)); C8 (zw (n_chunks s)); C1 (zb 0)]
  /\ RW m (INST + kInsSecStats) [C8 (zw (ss_n_allocs (as_sec_stats s))); C8 (zw (ss_n_frees (as_sec_stats s)));
                                 C8 (zw (ss_cur (as_sec_stats s))); C8 (zw (ss_max (as_sec_stats s)))]
  /\ (exists bsl, u64arr segs m (INST + kInsSecStats + 32) bsl /\ length bsl = 64%nat)
  /\ RW m (INST + kInsSecMutex) [C4 (zw 0)]
  /\ RW m (INST + kInsGlobalStats + 16) [C8 (zw (as_glob_allocated s)); C8 (zw (as_glob_mapped s))]
  /\ RW m (INST + kInsQuarantine + 64) [C8 (zw kQuarantineMax); C8 (zw kQuarantineMin); C8 (zw kThreadQuarantineMax)]
  /\ RW m (INST + kInsQMutex) [C4 (zw qm)]
  /\ RW m (INST + kInsQGlobal) [C8 (zw (qcount (as_gq s))); C8 (zw (list_first (as_gq s))); C8 (zw (list_last (as_gq s))); C8 (zw (gq_bytes s))]
  /\ RW m (INST + kInsFallbackMutex) [C1 (zb 0)]
  /\ RW m (INST + kInsMaxUserDefined) [C8 (zw (2^40)); C2 (zw kMinRedzone); C2 (zw kMaxRedzone); C1 (zb 1)].
Lemma arep_instanceL_0 : forall s m, arep_instanceL 0 s m <-> arep_instance s m.
Proof. intros s m. unfold arep_instanceL, arep_instance. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition region_cells (r : region) : list cell :=
  [C8 (zw 0); C4 (zw 0); C4 (zw 0);                          (* [comment removed for export] *)
   C8 (zw (rg_num_freed r)); C8 (zw (rg_mapped_fa r)); C8 (zw (rg_alloc_user r)); C8 (zw 0);
   C8 (zw (rg_mapped_user r)); C8 (zw 0);
   C4 (zw 0); C1 (zb 0); CB 3 (zeros 3);                        (* [comment removed for export] *)
   C8 (zw (rg_n_allocated r)); C8 (zw (rg_n_freed r));
   C8 (zw 0); C8 (zw 0); C8 (zw 0); C8 (zw 0); C8 (zw 0)].     (* [comment removed for export] *)

Definition arep_regioninfo (s : astate) (m : mem) : Prop :=
  forall c, 0 <= c < kNumClasses -> RW m (RI + kRegSize * c) (region_cells (region_of s c)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition arep_region_mem (s : astate) (m : mem) : Prop :=
  forall c, 0 <= c < kNumClasses ->
    let r := region_of s c in
    wr_at segs m (region_beg SB c) (rg_mapped_user r)
    /\ exists junk, u32arr segs m (free_array SB c) (map zw (rg_free r) ++ junk)
                 /\ 4 * Z.of_nat (length (rg_free r) + length junk) = rg_mapped_fa r.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition row_max_count (c : Z) : Z := if c =? 31 then 16 else max_count c.
Definition row_class_size (c : Z) : Z := if c =? 31 then 64 else class_size c.
Lemma row_max_count_reg : forall c, 1 <= c <= kLargestClassID -> row_max_count c = max_count c.
Proof. intros c Hc. unfold row_max_count, kLargestClassID in *. destruct (Z.eqb_spec c 31); [lia| reflexivity]. Qed.
Lemma row_class_size_reg : forall c, 1 <= c <= kLargestClassID -> row_class_size c = class_size c.
Proof. intros c Hc. unfold row_class_size, kLargestClassID in *. destruct (Z.eqb_spec c 31); [lia| reflexivity]. Qed.
Definition percls_cells (s : astate) (c : Z) : list cell :=
  let l := get_cache s c in
  [C4 (zw (zlen l)); C4 (zw (if as_cache_inited s then row_max_count c else 0)); C8 (zw (if as_cache_inited s then row_class_size c else 0))].

Definition tstats_words (t : tstats) : list word :=
  map zw [ts_mallocs t; ts_malloced t; ts_malloced_redzones t; ts_frees t; ts_freed t; ts_real_frees t; ts_really_freed t;
          ts_reallocs t; ts_realloced t; ts_mmaps t; ts_mmaped t; ts_munmaps t; ts_munmaped t; ts_malloc_large t].

Definition arep_thread (s : astate) (m : mem) : Prop :=
  RW m (T + kThrStackTop) [C8 (zw (ae_stack_top E)); C8 (zw (ae_stack_bottom E))]
  /\ RW m (T + 40) [C1 (zb 0)]                                                     (* [comment removed for export] *)
  /\ RW m (T + kThrQCache) [C8 (zw (qcount (as_tq s))); C8 (zw (list_first (as_tq s))); C8 (zw (list_last (as_tq s))); C8 (zw (tq_bytes s))]
  /\ (forall c, 0 <= c < kNumClasses ->
        RW m (T + kThrCache + kPerClassSize * c) (percls_cells s c)
        /\ exists junk, u32arr segs m (T + kThrCache + kPerClassSize * c + 16) (map zw (get_cache s c) ++ junk)
                       /\ (length (get_cache s c) + length junk = 16)%nat)
  /\ RW m (T + kThrCacheStats + 16) [C8 (zw (as_cache_allocated s)); C8 (zw (as_cache_mapped s))]
  /\ u64arr segs m (T + kThrStats) (tstats_words (as_ts s))
  /\ u64arr segs m (T + kThrStats + 112) (map (fun c => zw (match ts_by_size (as_ts s) !! c with Some v => v | None => 0 end)) (ziota 0 32))
  /\ RW m (T + kThrUnwinding) [C1 (zb 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition arep_secondary (s : astate) (m : mem) : Prop :=
  (as_ptr_committed s = 0 /\ as_sec s = []
   \/ as_ptr_committed s = kChunksBlockCount
      /\ exists junk, u64arr segs m (ae_ptr_array E) (map (fun c => zw (sc_map_beg c)) (as_sec s) ++ junk)
                      /\ (length (as_sec s) + length junk = Z.to_nat kChunksBlockCount)%nat)
  /\ forall i c, nth_error (as_sec s) i = Some c ->
       RW m (sc_map_beg c) [C8 (zw (sc_map_beg c)); C8 (zw (sc_map_size c)); C8 (zw (sc_needed c)); C8 (zw (Z.of_nat i))]
       /\ wr_at segs m (sc_map_beg c) (sc_map_size c).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hdr_state (st : cstate) : Z := match st with CAllocated _ => kChunkAllocated | CQuarantined _ _ => kChunkQuarantine end.
Definition hdr_alloc_id (st : cstate) : Z := match st with CAllocated i => i | CQuarantined i _ => i end.

(* [comment removed for export] *)
Definition arep_chunk (cm : chunkmeta) (m : mem) : Prop :=
  (exists b1, Z.land b1 127 = kHeaderByte1 /\
   RW m (cm_chunk_beg cm) [C1 (zb (hdr_state (cm_state cm))); C1 (zb b1); C2 (zw (cm_n cm / 2^32)); C4 (zw (cm_n cm)); C8 (zw (hdr_alloc_id (cm_state cm)))])
  /\ (16 < 16 * 2 ^ cm_rz_log cm -> RW m (cm_alloc_beg cm) [C8 (zw kAllocBegMagicVal); C8 (zw (cm_chunk_beg cm))])
  /\ match cm_state cm with
     | CQuarantined _ fid => RW m (cm_user_beg cm) [C8 (zw fid)]
     | CAllocated _ => True
     end.

Definition arep_chunks (s : astate) (m : mem) : Prop :=
  forall cb cm, as_chunks s !! cb = Some cm -> cb = cm_chunk_beg cm /\ arep_chunk cm m.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition arep_batch (s : astate) (b : batch) (next : Z) (m : mem) : Prop :=
  RW m (b_addr b) [C8 (zw next); C8 (zw (b_size b)); C8 (zw (zlen (b_items b)))]
  /\ exists junk, u64arr segs m (b_addr b + 24) (map (fun cb => zw cb) (b_items b) ++ junk)
                 /\ (length (b_items b) + length junk = Z.to_nat kBatchCap)%nat.

Fixpoint arep_batch_list (s : astate) (l : list batch) (m : mem) : Prop :=
  match l with
  | [] => True
  | b :: rest => arep_batch s b (match rest with [] => 0 | b' :: _ => b_addr b' end) m /\ arep_batch_list s rest m
  end.

Definition arep_batches (s : astate) (m : mem) : Prop :=
  arep_batch_list s (as_tq s) m /\ arep_batch_list s (as_gq s) m.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Variable DepotR : astate -> mem -> Prop.
Definition arep_depot (s : astate) (m : mem) : Prop := DepotR s m.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition arep_globals (s : astate) (m : mem) : Prop :=
  u8arr segs m (aic_asan_flags IC) (map zb (asan_flags_bytes IC))
  /\ RW m (aic_common_flags IC + 34) [C1 (zb 1)]                         (* [comment removed for export] *)
  /\ RW m (aic_common_flags IC + 120) [C8 (zw kClearShadowMmapThreshold)]
  /\ RW m (aic_common_flags IC + 219) [C1 (zb 1)]                        (* [comment removed for export] *)
  /\ RW m (aic_shadow_dyn_addr IC) [C8 (zw kShadowBase)]
  /\ RW m (aic_kHighMemEnd IC) [C8 (zw kHighMemEnd); C8 (zw 0); C8 (zw 0)]   (* [comment removed for export] *)
  /\ RW m (aic_can_poison_memory IC) [C1 (zb 1)]
  /\ RW m (aic_asan_inited IC) [C1 (zb 1)]
  /\ RW m (aic_malloc_context_size IC) [C4 (zw kMallocContextSize)]
  /\ RW m (aic_page_size_cached IC) [C8 (zw kPageSize)]
  /\ RW m (aic_dying_flag IC) [C4 (zw 0)]
  /\ RW m (aic_stack_anchor IC) [C8 (zw (ae_sp0 E - kStackAnchorDelta))]
  /\ RW m (aic_REAL_memcpy_var IC) [C8 (zw (aic_musl_memcpy IC)); C8 (zw (aic_musl_memset IC))]
  /\ u64arr segs m (aic_malloc_hook_table IC) (map zw (repeat 0 10))
  /\ RW m (aic_internal_alloc_initialized IC) [C1 (zb (boolz (as_ia_inited s))); C1 (zb 0)]
  /\ (as_ia_inited s = true ->
        RW m (aic_internal_allocator_instance IC + kIaPageSizeOff) [C8 (zw kPageSize); C8 (zw (aic_internal_allocator_instance IC + kIaChunksPtrOff + 8))])
  /\ u8arr segs m (aic_internal_allocator_instance IC + 8) (zeros (Z.to_nat 0x40000))   (* [comment removed for export] *)
  /\ wr_at segs m (aic_internal_allocator_instance IC) 0x81030.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition chunk_shadow (cm : chunkmeta) (a : Z) : Z :=
  let ub := cm_user_beg cm in
  let n := cm_n cm in
  match cm_state cm with
  | CAllocated _ =>
      if a <? ub then kAsanHeapLeftRedzoneMagic
      else if a <? ub + (n / 8) * 8 then 0
      else if (a <? ub + n) then n mod 8                 (* [comment removed for export] *)
      else kAsanHeapLeftRedzoneMagic
  | CQuarantined _ _ =>
      if a <? ub then kAsanHeapLeftRedzoneMagic
      else if a <? ub + round_up n 8 then kAsanHeapFreeMagic
      else kAsanHeapLeftRedzoneMagic
  end.

(* [comment removed for export] *)
Definition block_span (cm : chunkmeta) : Z :=
  match cm_prim cm with Some c => class_size c | None => map_size (cm_n cm) - kPageSize end.
Definition find_chunk (s : astate) (a : Z) : option chunkmeta :=
  map_fold (fun _ cm acc => match acc with
                            | Some _ => acc
                            | None => if (cm_alloc_beg cm <=? a) && (a <? cm_alloc_beg cm + block_span cm) then Some cm else None
                            end) None (as_chunks s).

Definition in_some_region_map (s : astate) (a : Z) : bool :=
  existsb (fun c => let r := region_of s c in (region_beg SB c <=? a) && (a <? region_beg SB c + rg_mapped_user r)) (ziota 0 32)
  || existsb (fun c => let r := region_of s c in (free_array SB c <=? a) && (a <? free_array SB c + rg_mapped_fa r)) (ziota 0 32).
Definition in_some_sec_map (s : astate) (a : Z) : bool :=
  existsb (fun c => (sc_map_beg c <=? a) && (a <? sc_map_beg c + sc_map_size c)) (as_sec s).

(* [comment removed for export] *)
Definition in_fakestack (a : Z) : bool := (ae_fs_beg E <=? a) && (a <? ae_fs_beg E + ae_fs_len E).
(* [comment removed for export] *)
Definition kIArenaLen : Z := 65536.
Definition in_iarena (a : Z) : bool := (ae_iarena E <=? a) && (a <? ae_iarena E + kIArenaLen).
(* [comment removed for export] *)
Definition in_reginfo (a : Z) : bool := (SB + kSpaceSize <=? a) && (a <? SB + kSpaceSize + kPageSize).
(* [comment removed for export] *)
Definition sh_excluded (a : Z) : bool := in_fakestack a || in_iarena a || in_reginfo a.
(* [comment removed for export] *)
Definition in_img (a : Z) : bool := (fst (ae_img E) <=? a) && (a <? fst (ae_img E) + snd (ae_img E)).
(* [comment removed for export] *)
Definition sh_default_dom (a : Z) : bool :=
  ((0 <=? a) && (a <? kLowAppEnd) && negb (in_img a)) || ((kHighMemBeg <=? a) && (a <=? kHighMemEnd)).

(* [comment removed for export] *)
Definition Sh (s : astate) (a : Z) : option Z :=
  if in_some_region_map s a || in_some_sec_map s a then
    Some (match find_chunk s a with Some cm => chunk_shadow cm a | None => kAsanHeapLeftRedzoneMagic end)
  else if sh_default_dom a && negb (sh_excluded a) then Some 0
  else None.

Definition arep_shadow (s : astate) (m : mem) : Prop :=
  forall g v, Sh s (8 * g) = Some v -> RW m (kShadowBase + g) [C1 (zb v)].

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ARep (s : astate) (m : mem) : Prop :=
  arep_instance s m /\ arep_regioninfo s m /\ arep_region_mem s m /\ arep_thread s m
  /\ arep_secondary s m /\ arep_chunks s m /\ arep_batches s m /\ arep_depot s m
  /\ arep_globals s m /\ arep_shadow s m.
(* [comment removed for export] *)
Definition ARepL (qm : Z) (s : astate) (m : mem) : Prop :=
  arep_instanceL qm s m /\ arep_regioninfo s m /\ arep_region_mem s m /\ arep_thread s m
  /\ arep_secondary s m /\ arep_chunks s m /\ arep_batches s m /\ arep_depot s m
  /\ arep_globals s m /\ arep_shadow s m.
Lemma ARepL_0 : forall s m, ARepL 0 s m <-> ARep s m.
Proof. intros s m. unfold ARepL, ARep. rewrite arep_instanceL_0. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition carved (s : astate) (c : Z) (a : Z) : Prop :=
  exists k, 0 <= k /\ a = region_beg SB c + k * class_size c /\ (k + 1) * class_size c <= rg_alloc_user (region_of s c).

(* [comment removed for export] *)
Definition in_free (s : astate) (c a : Z) : Prop := In (compact_of_chunk SB c a) (rg_free (region_of s c)).
Definition in_cache (s : astate) (c a : Z) : Prop := In (compact_of_chunk SB c a) (get_cache s c).
Definition is_chunk_block (s : astate) (a : Z) : Prop := exists cb cm, as_chunks s !! cb = Some cm /\ cm_alloc_beg cm = a.
(* [comment removed for export] *)
Definition all_batches (D : list batch) (s : astate) : list batch := as_tq s ++ as_gq s ++ D.
Definition is_batch (D : list batch) (s : astate) (a : Z) : Prop := exists b, In b (all_batches D s) /\ b_addr b = a.

Definition wf_regions (s : astate) : Prop :=
  (forall c r, as_regions s !! c = Some r -> 1 <= c <= kLargestClassID)
  /\ forall c, 1 <= c <= kLargestClassID ->
       let r := region_of s c in
       0 <= rg_alloc_user r <= rg_mapped_user r /\ rg_mapped_user r mod kUserMapSize = 0 /\ rg_mapped_user r <= kFreeArrayOffset
       /\ rg_alloc_user r mod class_size c = 0
       /\ 0 <= rg_mapped_fa r /\ rg_mapped_fa r mod kFreeArrayMapSize = 0 /\ rg_mapped_fa r <= kFreeArraySize
       /\ 4 * rg_num_freed r <= rg_mapped_fa r
       /\ List.NoDup (rg_free r)
       /\ (forall x, In x (rg_free r) -> carved s c (chunk_of_compact SB c x) /\ (16 * x) mod class_size c = 0)
       /\ 0 <= rg_n_allocated r /\ 0 <= rg_n_freed r.

Definition wf_cache (s : astate) : Prop :=
  (forall c l, as_cache s !! c = Some l -> 1 <= c <= kLargestClassID)
  /\ (as_cache_inited s = false -> as_cache s = ∅ /\ as_regions s = ∅)
  /\ forall c, 1 <= c <= kLargestClassID ->
       zlen (get_cache s c) <= max_count c /\ List.NoDup (get_cache s c)
       /\ forall x, In x (get_cache s c) -> carved s c (chunk_of_compact SB c x) /\ (16 * x) mod class_size c = 0 /\ ~ In x (rg_free (region_of s c)).

Definition wf_chunk (P : list Z) (D : list batch) (s : astate) (cb : Z) (cm : chunkmeta) : Prop :=
  cb = cm_chunk_beg cm /\ 1 <= cm_n cm < 2^40 /\ cm_rz_log cm = rz_log (cm_n cm)
  /\ match cm_prim cm with
     | Some c => from_primary (cm_n cm) = true /\ c = malloc_class (cm_n cm) /\ carved s c (cm_alloc_beg cm)
                 /\ ~ in_free s c (cm_alloc_beg cm) /\ ~ in_cache s c (cm_alloc_beg cm) /\ ~ is_batch D s (cm_alloc_beg cm)
     | None => from_primary (cm_n cm) = false
               /\ exists sc, In sc (as_sec s) /\ cm_alloc_beg cm = sc_map_beg sc + kPageSize
                             /\ sc_map_size sc = map_size (cm_n cm) /\ sc_needed sc = needed (cm_n cm)
     end
  /\ match cm_state cm with
     | CAllocated i => 1 <= i
     | CQuarantined i j => 1 <= i /\ 1 <= j /\ (In cb P \/ exists b, In b (all_batches D s) /\ In cb (b_items b))
     end.

Definition wf_chunks (P : list Z) (D : list batch) (s : astate) : Prop :=
  (forall cb cm, as_chunks s !! cb = Some cm -> wf_chunk P D s cb cm)
  /\ (forall cb1 cm1 cb2 cm2, as_chunks s !! cb1 = Some cm1 -> as_chunks s !! cb2 = Some cm2 -> cb1 <> cb2 -> cm_alloc_beg cm1 <> cm_alloc_beg cm2).

(* [comment removed for export] *)
Definition wf_batch (D : list batch) (s : astate) (b : batch) : Prop :=
  carved s kBatchClass (b_addr b) /\ ~ in_free s kBatchClass (b_addr b) /\ ~ in_cache s kBatchClass (b_addr b) /\ ~ is_chunk_block s (b_addr b)
  /\ zlen (b_items b) <= kBatchCap
  /\ b_size b = kBatchSize + fold_right (fun cb acc => chunk_used_size s cb + acc) 0 (b_items b)
  /\ List.NoDup (b_items b)
  /\ forall cb, In cb (b_items b) -> exists cm i j, as_chunks s !! cb = Some cm /\ cm_state cm = CQuarantined i j.

(* [comment removed for export] *)
Definition wf_dbatch (s : astate) (b : batch) : Prop :=
  carved s kBatchClass (b_addr b) /\ ~ in_free s kBatchClass (b_addr b) /\ ~ in_cache s kBatchClass (b_addr b) /\ ~ is_chunk_block s (b_addr b)
  /\ List.NoDup (b_items b).

Definition wf_quarantine (D : list batch) (s : astate) : Prop :=
  (forall b, In b (as_tq s ++ as_gq s) -> wf_batch D s b /\ 1 <= zlen (b_items b))
  /\ (forall b, In b D -> wf_dbatch s b)
  /\ List.NoDup (map b_addr (all_batches D s))
  /\ (forall b1 b2 cb, In b1 (all_batches D s) -> In b2 (all_batches D s) -> In cb (b_items b1) -> In cb (b_items b2) -> b1 = b2).
  (* [comment removed for export] *)

Definition wf_secondary (s : astate) : Prop :=
  (as_ptr_committed s = 0 /\ as_sec s = [] \/ as_ptr_committed s = kChunksBlockCount)
  /\ n_chunks s <= as_ptr_committed s
  /\ (forall sc, In sc (as_sec s) ->
        sc_map_beg sc mod kPageSize = 0 /\ app_mem (sc_map_beg sc) (sc_map_size sc) /\ sc_map_beg sc + sc_map_size sc <= alloc_ceiling
        /\ 0 < sc_map_size sc /\ sc_map_size sc mod kPageSize = 0
        /\ (sc_map_beg sc + sc_map_size sc <= SB \/ SB + kSpaceSize <= sc_map_beg sc)
        /\ (forall r, In r (ae_reserved E) -> sc_map_beg sc + sc_map_size sc <= fst r \/ fst r + snd r <= sc_map_beg sc))   (* [comment removed for export] *)
       (* [comment removed for export] *)
  /\ List.NoDup (map sc_map_beg (as_sec s))
  /\ (forall a b, In a (as_sec s) -> In b (as_sec s) -> a <> b ->
        sc_map_beg a + sc_map_size a <= sc_map_beg b \/ sc_map_beg b + sc_map_size b <= sc_map_beg a).

(* [comment removed for export] *)
Definition img_sep (X L : Z) : Prop := X + L <= fst (ae_img E) \/ fst (ae_img E) + snd (ae_img E) <= X.

(* [comment removed for export] *)
Definition wf_env : Prop :=
  SB mod 2^16 = 0 /\ kHighMemBeg <= ae_resv_beg E /\ ae_resv_beg E <= SB /\ SB + kSpaceSize + 0x1000 <= ae_resv_beg E + 0x2000011000
  /\ ae_resv_beg E + 0x2000011000 <= alloc_ceiling
  /\ ae_stack_bottom E < ae_stack_top E
  /\ In (ae_resv_beg E, 0x2000011000) (ae_reserved E)      (* [comment removed for export] *)
  /\ In (ae_ptr_array E, 0x800000) (ae_reserved E)
  (* [comment removed for export] *)
  /\ In (ae_fs_beg E, ae_fs_len E) (ae_reserved E) /\ app_mem (ae_fs_beg E) (ae_fs_len E) /\ 0 <= ae_fs_len E
  /\ (ae_fs_beg E + ae_fs_len E <= ae_resv_beg E \/ ae_resv_beg E + 0x2000011000 <= ae_fs_beg E)
  (* [comment removed for export] *)
  /\ In (T, 4096) (ae_reserved E) /\ app_mem T 4096 /\ T + 4096 <= alloc_ceiling
  /\ app_mem (ae_ptr_array E) 0x800000 /\ ae_ptr_array E + 0x800000 <= alloc_ceiling /\ ae_fs_beg E + ae_fs_len E <= alloc_ceiling
  /\ (T + 4096 <= ae_resv_beg E \/ ae_resv_beg E + 0x2000011000 <= T)
  /\ (ae_ptr_array E + 0x800000 <= ae_resv_beg E \/ ae_resv_beg E + 0x2000011000 <= ae_ptr_array E)
  /\ (T + 4096 <= ae_fs_beg E \/ ae_fs_beg E + ae_fs_len E <= T)
  /\ (ae_ptr_array E + 0x800000 <= ae_fs_beg E \/ ae_fs_beg E + ae_fs_len E <= ae_ptr_array E)
  /\ (T + 4096 <= ae_ptr_array E \/ ae_ptr_array E + 0x800000 <= T)
  (* [comment removed for export] *)
  /\ In (ae_iarena E, kIArenaLen) (ae_reserved E) /\ app_mem (ae_iarena E) kIArenaLen /\ ae_iarena E + kIArenaLen <= alloc_ceiling
  /\ (ae_iarena E + kIArenaLen <= ae_resv_beg E \/ ae_resv_beg E + 0x2000011000 <= ae_iarena E)
  /\ ae_iarena E mod 4096 = 0
  (* [comment removed for export] *)
  /\ In (ae_img E) (ae_reserved E) /\ 0x10000 <= fst (ae_img E) /\ fst (ae_img E) + snd (ae_img E) <= kLowAppEnd
  /\ img_sep T 4096 /\ img_sep (ae_ptr_array E) 0x800000 /\ img_sep (ae_fs_beg E) (ae_fs_len E) /\ img_sep (ae_iarena E) kIArenaLen.

(* [comment removed for export] *)
Definition wf_depot (s : astate) : Prop :=
  List.NoDup (map depot_hash (ae_keys0 E ++ as_keys s)) /\ zlen (as_keys s) <= as_ndepot_ins s /\ ae_frames0 E <= as_frames s.

(* [comment removed for export] *)
Definition AQbound (s : astate) : Prop := tq_bytes s <= kThreadQuarantineMax /\ gq_bytes s <= kQuarantineMax.

Definition AWf (P : list Z) (D : list batch) (s : astate) : Prop :=
  wf_env /\ wf_regions s /\ wf_cache s /\ wf_chunks P D s /\ wf_quarantine D s /\ wf_secondary s /\ wf_depot s.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition live_blocks (s : astate) : list (Z * Z) :=
  map (fun p => (cm_user_beg (snd p), cm_n (snd p)))
      (List.filter (fun p => match cm_state (snd p) with CAllocated _ => true | _ => false end) (chunk_list s)).

Definition is_live_block (s : astate) (p n : Z) : Prop :=
  exists cm i, as_chunks s !! (p - kChunkHeaderSize) = Some cm /\ cm_user_beg cm = p /\ cm_n cm = n /\ cm_state cm = CAllocated i.

(* [comment removed for export] *)
Definition allocator_static_ranges : list (Z * Z) :=
  [(INST, 3632); (aic_internal_alloc_initialized IC, 2); (aic_internal_allocator_instance IC, 0x81250);
   (aic_theDepot IC, 0x400020); (aic_stackStore IC, 0x10000)].

End REP.
End RC__1.
