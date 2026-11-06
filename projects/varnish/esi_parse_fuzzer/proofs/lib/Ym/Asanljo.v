(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kSpaceSize        : Z := 2^37.          (* [comment removed for export] *)
Definition kSpaceReserve     : Z := 2^37 + 0x11000. (* [comment removed for export] *)
Definition kRegionSizeLog    : Z := 32.
Definition kRegionSize       : Z := 2^32.          (* [comment removed for export] *)
Definition kNumClasses       : Z := 32.            (* [comment removed for export] *)
Definition kLargestClassID   : Z := 30.
Definition kBatchClassID     : Z := 31.
Definition kMaxSize          : Z := 0x10000.       (* [comment removed for export] *)
Definition kMinSize          : Z := 32.            (* [comment removed for export] *)
Definition kMidClass         : Z := 16.
Definition kMidSize          : Z := 512.
Definition kUserMapSize      : Z := 2^18.          (* [comment removed for export] *)
Definition kFreeArrayMapSize : Z := 2^18.          (* [comment removed for export] *)
Definition kFreeArraySize    : Z := 2^29.          (* [comment removed for export] *)
Definition kFreeArrayOffset  : Z := 0xE0000000.    (* [comment removed for export] *)
Definition kRegionInfoSize   : Z := 128.           (* [comment removed for export] *)
Definition kCompactPtrScale  : Z := 16.            (* [comment removed for export] *)
Definition kMaxNumCachedHint : Z := 8.             (* [comment removed for export] *)
Definition kMaxBytesCachedLog: Z := 10.            (* [comment removed for export] *)
Definition kPerClassSize     : Z := 80.            (* [comment removed for export] *)
Definition kReleaseToOSIntervalNever : Z := -1.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kPageSize         : Z := 4096.
Definition kMaxNumChunks     : Z := 2^20.          (* [comment removed for export] *)
Definition kChunksBlockCount : Z := 2^14.          (* [comment removed for export] *)
Definition kPtrArrayReserve  : Z := 0x800000.
Definition kSecondaryHeaderSize : Z := 32.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kChunkHeaderSize  : Z := 16.
Definition kChunkHeader2Size : Z := 8.             (* [comment removed for export] *)
Definition kAllocBegMagic    : Z := 0xCC6E96B9CC6E96B9. (* [comment removed for export] *)
Definition CHUNK_INVALID     : Z := 0.
Definition CHUNK_ALLOCATED   : Z := 2.
Definition CHUNK_QUARANTINE  : Z := 3.
Definition FROM_MALLOC       : Z := 1.             (* [comment removed for export] *)
Definition kHdrByte1Malloc   : Z := 0x11.          (* [comment removed for export] *)
Definition kInvalidTidShifted: Z := 0xFFFFFFFF00000000. (* [comment removed for export] *)
Definition kMainTid          : Z := 0.             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kMinRedzone       : Z := 16.            (* [comment removed for export] *)
Definition kMaxRedzone       : Z := 2048.          (* [comment removed for export] *)
Definition kMinRedzoneLog    : Z := 0.             (* [comment removed for export] *)
Definition kMaxRedzoneLog    : Z := 7.             (* [comment removed for export] *)
Definition kMaxPrimaryUser   : Z := 64512.         (* [comment removed for export] *)
Definition kMaxUserDefinedMallocSize : Z := 2^40.  (* [comment removed for export] *)
Definition kMallocAlign      : Z := 8.             (* [comment removed for export] *)
Definition kShadowGranularity: Z := 8.

(* [comment removed for export] *)
Definition kShadowOffset     : Z := 0x7fff8000.    (* [comment removed for export] *)
Definition kLowMemEnd        : Z := 0x7fff7fff.    (* [comment removed for export] *)
Definition kLowShadowBeg     : Z := 0x7fff8000.    (* [comment removed for export] *)
Definition kLowShadowMapBeg  : Z := 0x7fff7000.    (* [comment removed for export] *)
Definition kShadowGapBeg     : Z := 0x8fff7000.    (* [comment removed for export] *)
Definition kHighShadowMapBeg : Z := 0x2008fff7000. (* [comment removed for export] *)
Definition kHighShadowMapSize: Z := 0xdfff0001000.
Definition kHighMemBeg       : Z := 0x10007fff8000. (* [comment removed for export] *)
Definition kHighMemEnd       : Z := 2^47 - 1.      (* [comment removed for export] *)
Definition kClearShadowMmapThreshold : Z := 0x10000. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kAsanHeapLeftRedzoneMagic : Z := 0xfa.
Definition kAsanHeapFreeMagic        : Z := 0xfd.
Definition kAsanInternalHeapMagic    : Z := 0xfe.

(* [comment removed for export] *)
Definition kQuarantineMaxSize   : Z := 2^28.       (* [comment removed for export] *)
Definition kQuarantineMinSize   : Z := 0xE666661.  (* [comment removed for export] *)
Definition kQuarantineCacheSize : Z := 2^20.       (* [comment removed for export] *)
Definition kQuarantineBatchCount: Z := 1021.       (* [comment removed for export] *)
Definition kQuarantineBatchBytes: Z := 8192.       (* [comment removed for export] *)
Definition kQuarantineBatchClass: Z := 24.
Definition kOverheadThresholdPercents : Z := 100.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kMaxMallocFillSize : Z := 0x1000.       (* [comment removed for export] *)
Definition kMallocFillByte    : Z := 0xbe.         (* [comment removed for export] *)
Definition kMaxFreeFillSize   : Z := 0.            (* [comment removed for export] *)
Definition kMallocContextSize : Z := 30.           (* [comment removed for export] *)
Definition kStackTraceMax     : Z := 255.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kDepotTabBits      : Z := 20.           (* [comment removed for export] *)
Definition kDepotTabBytes     : Z := 0x400000.
Definition kDepotLockBit      : Z := 2^31.         (* [comment removed for export] *)
Definition kDepotNodeSize     : Z := 16.           (* [comment removed for export] *)
Definition kDepotNodesL1      : Z := 2^15.         (* [comment removed for export] *)
Definition kDepotNodesBlock   : Z := 0x100000.     (* [comment removed for export] *)
Definition kStackStoreBlockFrames : Z := 2^20.     (* [comment removed for export] *)
Definition kStackStoreBlockBytes  : Z := 0x800000.
Definition kMurmur2Mul        : Z := 0xC6A4A7935BD1E995. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kMallocIcptFrame   : Z := 2128.         (* [comment removed for export] *)
Definition kCallocIcptFrame   : Z := 2144.         (* [comment removed for export] *)
Definition kStackObjOffset    : Z := 2128.         (* [comment removed for export] *)
Definition kStackObjOffsetCR  : Z := 2136.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition MAP_PRIVATE_ANON          : Z := 0x22.
Definition MAP_PRIVATE_ANON_FIXED    : Z := 0x32.
Definition MAP_PRIVATE_ANON_NORESERVE: Z := 0x4022.
Definition MAP_FIXED_NORESERVE       : Z := 0x4032.
Definition PROT_RW                   : Z := 3.
Definition SYS_mmap   : Z := 222.
Definition SYS_munmap : Z := 215.
Definition ENOMEM     : Z := 12.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record alayout := mkALayout {
  (* [comment removed for export] *)
  al_free_stub     : Z;   al_malloc_stub  : Z;   al_calloc_stub : Z;   al_realloc_stub : Z;
  (* [comment removed for export] *)
  al_free_icpt     : Z;   al_malloc_icpt  : Z;   al_calloc_icpt : Z;   al_realloc_icpt : Z;
  (* [comment removed for export] *)
  al_pc_malloc     : Z;   al_pc_free      : Z;   al_pc_calloc   : Z;   al_pc_realloc   : Z;
  (* [comment removed for export] *)
  al_asan_malloc   : Z;   al_asan_free    : Z;   al_asan_calloc : Z;   al_asan_realloc : Z;
  al_asan_reallocarray : Z;
  al_Allocate      : Z;   al_Deallocate   : Z;   al_Reallocate  : Z;   al_QuarantineChunk : Z;
  al_cb_Recycle    : Z;   (* [comment removed for export] *)
  al_RZSize2Log    : Z;
  (* [comment removed for export] *)
  al_Combined_Allocate : Z;  al_Refill : Z;  al_GetFromAllocator : Z;  al_PopulateFreeArray : Z;
  al_EnsureFreeArraySpace : Z;  al_Large_Allocate : Z;  al_Large_Deallocate : Z;  al_Large_GetBlockBegin : Z;
  al_LocalCache_Deallocate : Z;  al_LocalCache_Drain : Z;  al_ReturnToAllocator : Z;  al_MaybeReleaseToOS : Z;
  (* [comment removed for export] *)
  al_Q_Put : Z;  al_Q_Enqueue : Z;  al_Q_Drain : Z;  al_Q_Recycle : Z;  al_Q_MergeBatches : Z;  al_Q_DoRecycle : Z;
  (* [comment removed for export] *)
  al_PoisonShadow : Z;  al_ReserveShadowMemoryRange : Z;  al_MmapFixedNoReserve : Z;  al_OnUnmap_Flush : Z;
  al_MapWithCallback : Z;  al_MmapFixedOrDieOnFatalError : Z;  al_MmapFixedImpl : Z;  al_MmapOrDieOnFatalError : Z;
  al_MmapOrDie : Z;  al_MmapNoReserveOrDie : Z;  al_UnmapOrDie : Z;  al_internal_mmap : Z;  al_internal_munmap : Z;
  al_IncreaseTotalMmap : Z;  al_GetNamedMappingFd : Z;  al_ReleaseMemoryPagesToOS : Z;  al_internal_madvise : Z;
  (* [comment removed for export] *)
  al_TryAsanInitFromRtl : Z;  al_GetMallocContextSize : Z;  al_GetCurrentPc : Z;  al_UnwindImpl : Z;
  al_Unwind : Z;  al_UnwindFast : Z;  al_GetCurrentThread : Z;  al_AsanTSDGet : Z;  al_stack_top : Z;  al_stack_bottom : Z;
  al_GetCurrentThreadStats : Z;  al_StackDepotPut : Z;  al_Depot_Put : Z;  al_Depot_lock : Z;  al_Depot_find : Z;
  al_Node_store : Z;  al_StackStore_Store : Z;  al_StackStore_Alloc : Z;  al_TwoLevelMap_Create : Z;
  (* [comment removed for export] *)
  al_RunMallocHooks : Z;  al_RunFreeHooks : Z;  al_lsan_Disabled : Z;  al_internal_allocator : Z;
  al_internal_memset : Z;  al_internal_memcpy : Z;  al_SetErrnoOnNull : Z;  al_AllocatorMayReturnNull : Z;
  al_RssLimitExceeded : Z;  al_SetAllocatorOutOfMemory : Z;  al_AsanInited : Z;  al_MonotonicNanoTime : Z;
  al_LockSlow : Z;  al_SemWait : Z;  al_SemPost : Z;  al_sched_yield_stub : Z;  al_CheckFailed : Z;  al_Die : Z;
  (* [comment removed for export] *)
  al_ReportOutOfMemory : Z;  al_ReportCallocOverflow : Z;  al_ReportReallocArrayOverflow : Z;
  al_ReportDoubleFree : Z;  al_ReportFreeNotMalloced : Z;  al_ReportAllocationSizeTooBig : Z;  al_ReportRssLimitExceeded : Z;
  (* [comment removed for export] *)
  al_spin_freearray : Z;  al_spin_batch : Z;  al_spin_poison_gap : Z;  al_spin_mmap_die : Z;
  al_spin_munmap_die : Z;  al_spin_shadow_noreserve : Z;  al_spin_reserved_init : Z;  al_spin_other : Z;
  (* [comment removed for export] *)
  al_musl_memset : Z;  al_musl_memcpy : Z;  al_errno_location : Z;

  (* [comment removed for export] *)
  al_instance : Z;              (* [comment removed for export] *)
  al_asan_flags : Z;            (* [comment removed for export] *)
  al_common_flags : Z;          (* [comment removed for export] *)
  al_shadow_base_var : Z;       (* [comment removed for export] *)
  al_kHighMemEnd_var : Z;  al_kMidMemBeg_var : Z;  al_kMidMemEnd_var : Z;
  al_asan_inited : Z;           (* [comment removed for export] *)
  al_malloc_context_size : Z;   (* [comment removed for export] *)
  al_can_poison_memory : Z;     (* [comment removed for export] *)
  al_unknown_thread_stats : Z;
  al_real_memset_cell : Z;      (* [comment removed for export] *)
  al_real_memcpy_cell : Z;      (* [comment removed for export] *)
  al_page_size_cache : Z;       (* [comment removed for export] *)
  al_may_return_null : Z;       (* [comment removed for export] *)
  al_rss_limit_exceeded : Z;    (* [comment removed for export] *)
  al_internal_alloc_inited : Z; (* [comment removed for export] *)
  al_internal_allocator_inst : Z; (* [comment removed for export] *)
  al_malloc_hooks : Z;          (* [comment removed for export] *)
  al_dying_flag : Z;            (* [comment removed for export] *)
  al_total_mmaped : Z;          (* [comment removed for export] *)
  al_theDepot : Z;              (* [comment removed for export] *)
  al_depot_n_uniq_ids : Z;      (* [comment removed for export] *)
  al_depot_nodes_map1 : Z;      (* [comment removed for export] *)
  al_stackStore : Z;            (* [comment removed for export] *)
  (* [comment removed for export] *)
  al_got_page_size : Z;  al_got_common_flags : Z;  al_got_asan_flags : Z;  al_got_shadow_base : Z;
  al_got_kMidMemBeg : Z;  al_got_kMidMemEnd : Z;  al_got_kHighMemEnd : Z;  al_got_real_memset : Z;  al_got_real_memcpy : Z;
  al_got_sealed : Z;            (* [comment removed for export] *)
  al_got_dying_flag : Z;
  (* [comment removed for export] *)
  al_ro_debruijn64 : Z;  al_ro_log2tab_a : Z;  al_ro_log2tab_b : Z;  al_ro_log2tab_c : Z;  al_ro_log2tab_d : Z;
  al_ro_alloc_beg_magic : Z;  al_ro_murmur_m : Z;  al_ro_murmur_k1 : Z;  al_ro_murmur_k2 : Z;
  (* [comment removed for export] *)
  al_tp : Z;  al_errno : Z;
  (* [comment removed for export] *)
  al_image_lo : Z;  al_text_lo : Z;  al_text_hi : Z;  al_rw_lo : Z;  al_image_hi : Z;  al_brk0 : Z
}.

(* [comment removed for export] *)
Definition AL_pasan : alayout := {|
  al_free_stub := 0x5896c;  al_malloc_stub := 0x58970;  al_calloc_stub := 0x58974;  al_realloc_stub := 0x58978;
  al_free_icpt := 0x5897c;  al_malloc_icpt := 0x58b4c;  al_calloc_icpt := 0x58d74;  al_realloc_icpt := 0x58fac;
  al_pc_malloc := 0x58c14;  al_pc_free := 0x58ab4;  al_pc_calloc := 0x58e48;  al_pc_realloc := 0x590e8;
  al_asan_malloc := 0x37140;  al_asan_free := 0x36e60;  al_asan_calloc := 0x37b24;  al_asan_realloc := 0x37c04;
  al_asan_reallocarray := 0 (* [comment removed for export] *);
  al_Allocate := 0x3719c;  al_Deallocate := 0x36e88;  al_Reallocate := 0x37cb0;  al_QuarantineChunk := 0x3b410;
  al_cb_Recycle := 0x394d4;  al_RZSize2Log := 0x3c7e4;
  al_Combined_Allocate := 0x3b91c;  al_Refill := 0x3c06c;  al_GetFromAllocator := 0x3c16c;  al_PopulateFreeArray := 0x3c474;
  al_EnsureFreeArraySpace := 0x3a138;  al_Large_Allocate := 0x3bbf4;  al_Large_Deallocate := 0x39aa0;  al_Large_GetBlockBegin := 0x39758;
  al_LocalCache_Deallocate := 0x398d8;  al_LocalCache_Drain := 0x39c6c;  al_ReturnToAllocator := 0x39e10;  al_MaybeReleaseToOS := 0x3a2b8;
  al_Q_Put := 0x3b588;  al_Q_Enqueue := 0x3b738;  al_Q_Drain := 0x38e90;  al_Q_Recycle := 0x39034;  al_Q_MergeBatches := 0x39218;  al_Q_DoRecycle := 0x3939c;
  al_PoisonShadow := 0x59d94;  al_ReserveShadowMemoryRange := 0x727a0;  al_MmapFixedNoReserve := 0x74750;  al_OnUnmap_Flush := 0x58678;
  al_MapWithCallback := 0x749e0;  al_MmapFixedOrDieOnFatalError := 0x6c920;  al_MmapFixedImpl := 0x6c7a8;  al_MmapOrDieOnFatalError := 0x6c35c;
  al_MmapOrDie := 0x6c160;  al_MmapNoReserveOrDie := 0x6c698;  al_UnmapOrDie := 0x6c2e0;  al_internal_mmap := 0x6aa90;  al_internal_munmap := 0x6aa9c;
  al_IncreaseTotalMmap := 0x66974;  al_GetNamedMappingFd := 0x6ce3c;  al_ReleaseMemoryPagesToOS := 0x73e90;  al_internal_madvise := 0x6aab8;
  al_TryAsanInitFromRtl := 0x5fe00;  al_GetMallocContextSize := 0x60b88;  al_GetCurrentPc := 0x7975c;  al_UnwindImpl := 0x60b98;
  al_Unwind := 0x79dc0;  al_UnwindFast := 0x79764;  al_GetCurrentThread := 0x62600;  al_AsanTSDGet := 0x5aefc;  al_stack_top := 0x627c4;  al_stack_bottom := 0x6281c;
  al_GetCurrentThreadStats := 0x617cc;  al_StackDepotPut := 0x78dd8;  al_Depot_Put := 0x78df8;  al_Depot_lock := 0x7956c;  al_Depot_find := 0x794b8;
  al_Node_store := 0x78af0;  al_StackStore_Store := 0x767dc;  al_StackStore_Alloc := 0x76900;  al_TwoLevelMap_Create := 0x795fc;
  al_RunMallocHooks := 0x66ee8;  al_RunFreeHooks := 0x66fa4;  al_lsan_Disabled := 0x862d8;  al_internal_allocator := 0x6467c;
  al_internal_memset := 0x6a290;  al_internal_memcpy := 0x6a214;  al_SetErrnoOnNull := 0x72b70;  al_AllocatorMayReturnNull := 0x64ca4;
  al_RssLimitExceeded := 0x64ccc;  al_SetAllocatorOutOfMemory := 0x64c94;  al_AsanInited := 0x5eef0;  al_MonotonicNanoTime := 0x73768;
  al_LockSlow := 0x6c00c;  al_SemWait := 0x6c0cc;  al_SemPost := 0x6c11c;  al_sched_yield_stub := 0x6abf0;  al_CheckFailed := 0x71f98;  al_Die := 0x71ecc;
  al_ReportOutOfMemory := 0x5d434;  al_ReportCallocOverflow := 0x5cd50;  al_ReportReallocArrayOverflow := 0 (* [comment removed for export] *);
  al_ReportDoubleFree := 0x5c0ec;  al_ReportFreeNotMalloced := 0x5c5f8;  al_ReportAllocationSizeTooBig := 0x6d6b8;  al_ReportRssLimitExceeded := 0x5cfa0;
  al_spin_freearray := 0x3a2a4;  al_spin_batch := 0x3b8c8;  al_spin_poison_gap := 0x5a238;  al_spin_mmap_die := 0x6630c;
  al_spin_munmap_die := 0x663dc;  al_spin_shadow_noreserve := 0x74814;  al_spin_reserved_init := 0x749a4;  al_spin_other := 0x7e6fc;
  al_musl_memset := 0xa25c8;  al_musl_memcpy := 0xa21c4;  al_errno_location := 0x986a0;

  al_instance := 0xb1d58;  al_asan_flags := 0xb2bb8;  al_common_flags := 0x146ee8;  al_shadow_base_var := 0xb53b8;
  al_kHighMemEnd_var := 0xb60a0;  al_kMidMemBeg_var := 0xb60a8;  al_kMidMemEnd_var := 0xb60b0;
  al_asan_inited := 0xb6098;  al_malloc_context_size := 0xb60bc;  al_can_poison_memory := 0xb4c1c;  al_unknown_thread_stats := 0xb60e8;
  al_real_memset_cell := 0xab038;  al_real_memcpy_cell := 0xab030;  al_page_size_cache := 0x144e60;
  al_may_return_null := 0x137621;  al_rss_limit_exceeded := 0x137622;  al_internal_alloc_inited := 0x144e48;  al_internal_allocator_inst := 0xb65c0;
  al_malloc_hooks := 0x146e80;  al_dying_flag := 0x146edc;  al_total_mmaped := 0x144e78;
  al_theDepot := 0x197298;  al_depot_n_uniq_ids := 0x597298;  al_depot_nodes_map1 := 0x5972a8;  al_stackStore := 0x187288;
  al_got_page_size := 0xa9170;  al_got_common_flags := 0xa9180;  al_got_asan_flags := 0xa9188;  al_got_shadow_base := 0xa9190;
  al_got_kMidMemBeg := 0xa9198;  al_got_kMidMemEnd := 0xa91a0;  al_got_kHighMemEnd := 0xa91a8;  al_got_real_memset := 0xa91b0;  al_got_real_memcpy := 0xa91b8;
  al_got_sealed := 0xa91d0;  al_got_dying_flag := 0xa91d8;
  al_ro_debruijn64 := 0x103b8;  al_ro_log2tab_a := 0x103e8;  al_ro_log2tab_b := 0x10428;  al_ro_log2tab_c := 0x10468;  al_ro_log2tab_d := 0x10528;
  al_ro_alloc_beg_magic := 0x10328;  al_ro_murmur_m := 0x102e8;  al_ro_murmur_k1 := 0x10308;  al_ro_murmur_k2 := 0x103a0;
  al_tp := 0x5e83d8;  al_errno := 0x5e8334;
  al_image_lo := 0x10000;  al_text_lo := 0x35000;  al_text_hi := 0xa8000;  al_rw_lo := 0xa8000;  al_image_hi := 0x60a000;  al_brk0 := 0x60a000
|}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition off_primary_reserved_base : Z := 0.     (* [comment removed for export] *)
Definition off_primary_reserved_size : Z := 8.
Definition off_SpaceBeg              : Z := 32.    (* [comment removed for export] *)
Definition off_release_interval      : Z := 40.    (* [comment removed for export] *)
Definition off_RegionInfo_ptr        : Z := 48.    (* [comment removed for export] *)
Definition off_PremappedHeap         : Z := 56.    (* [comment removed for export] *)
Definition off_secondary             : Z := 64.    (* [comment removed for export] *)
Definition off_sec_page_size         : Z := 64.
Definition off_sec_chunks            : Z := 72.    (* [comment removed for export] *)
Definition off_sec_ptr_array_base    : Z := 80.
Definition off_sec_ptr_array_size    : Z := 88.
Definition off_sec_n_reserved        : Z := 112.
Definition off_sec_n_chunks          : Z := 120.
Definition off_sec_chunks_sorted     : Z := 128.   (* [comment removed for export] *)
Definition off_sec_stat_n_allocs     : Z := 136.
Definition off_sec_stat_n_frees      : Z := 144.
Definition off_sec_stat_cur_alloc    : Z := 152.
Definition off_sec_stat_max_alloc    : Z := 160.
Definition off_sec_stat_by_size_log  : Z := 168.   (* [comment removed for export] *)
Definition off_sec_mutex             : Z := 680.   (* [comment removed for export] *)
Definition off_global_stats          : Z := 688.   (* [comment removed for export] *)
Definition off_gstat_allocated       : Z := 704.
Definition off_gstat_mapped          : Z := 712.
Definition off_quarantine            : Z := 728.   (* [comment removed for export] *)
Definition off_q_max_size            : Z := 792.   (* [comment removed for export] *)
Definition off_q_min_size            : Z := 800.
Definition off_q_max_cache_size      : Z := 808.
Definition off_q_cache_mutex         : Z := 880.   (* [comment removed for export] *)
Definition off_q_recycle_mutex       : Z := 881.   (* [comment removed for export] *)
Definition off_q_cache_list_size     : Z := 888.   (* [comment removed for export] *)
Definition off_q_cache_first         : Z := 896.
Definition off_q_cache_last          : Z := 904.
Definition off_q_cache_bytes         : Z := 912.
Definition off_fallback_mutex        : Z := 984.
Definition off_fallback_alloc_cache  : Z := 992.
Definition off_fallback_q_cache      : Z := 3584.
Definition off_max_user_malloc       : Z := 3616.
Definition off_min_redzone           : Z := 3624.  (* [comment removed for export] *)
Definition off_max_redzone           : Z := 3626.  (* [comment removed for export] *)
Definition off_alloc_dealloc_mismatch: Z := 3628.  (* [comment removed for export] *)

Definition al_SpaceBeg_cell (L : alayout) : Z := al_instance L + off_SpaceBeg.
Definition al_RegionInfo_cell (L : alayout) : Z := al_instance L + off_RegionInfo_ptr.
Definition al_secondary (L : alayout) : Z := al_instance L + off_secondary.      (* [comment removed for export] *)
Definition al_global_stats (L : alayout) : Z := al_instance L + off_global_stats. (* [comment removed for export] *)
Definition al_quarantine (L : alayout) : Z := al_instance L + off_quarantine.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AL_pboth : alayout := {|
  al_free_stub := 0x5884c;  al_malloc_stub := 0x58850;  al_calloc_stub := 0x58854;  al_realloc_stub := 0x58858;
  al_free_icpt := 0x5885c;  al_malloc_icpt := 0x58a2c;  al_calloc_icpt := 0x58c54;  al_realloc_icpt := 0x58e8c;
  al_pc_malloc := 0x58af4;  al_pc_free := 0x58994;  al_pc_calloc := 0x58d28;  al_pc_realloc := 0x58fc8;
  al_asan_malloc := 0x37020;  al_asan_free := 0x36d40;  al_asan_calloc := 0x37a04;  al_asan_realloc := 0x37ae4;
  al_asan_reallocarray := 0 (* [comment removed for export] *);
  al_Allocate := 0x3707c;  al_Deallocate := 0x36d68;  al_Reallocate := 0x37b90;  al_QuarantineChunk := 0x3b2f0;
  al_cb_Recycle := 0x393b4;  al_RZSize2Log := 0x3c6c4;
  al_Combined_Allocate := 0x3b7fc;  al_Refill := 0x3bf4c;  al_GetFromAllocator := 0x3c04c;  al_PopulateFreeArray := 0x3c354;
  al_EnsureFreeArraySpace := 0x3a018;  al_Large_Allocate := 0x3bad4;  al_Large_Deallocate := 0x39980;  al_Large_GetBlockBegin := 0x39638;
  al_LocalCache_Deallocate := 0x397b8;  al_LocalCache_Drain := 0x39b4c;  al_ReturnToAllocator := 0x39cf0;  al_MaybeReleaseToOS := 0x3a198;
  al_Q_Put := 0x3b468;  al_Q_Enqueue := 0x3b618;  al_Q_Drain := 0x38d70;  al_Q_Recycle := 0x38f14;  al_Q_MergeBatches := 0x390f8;  al_Q_DoRecycle := 0x3927c;
  al_PoisonShadow := 0x59c74;  al_ReserveShadowMemoryRange := 0x72680;  al_MmapFixedNoReserve := 0x74630;  al_OnUnmap_Flush := 0x58558;
  al_MapWithCallback := 0x748c0;  al_MmapFixedOrDieOnFatalError := 0x6c800;  al_MmapFixedImpl := 0x6c688;  al_MmapOrDieOnFatalError := 0x6c23c;
  al_MmapOrDie := 0x6c040;  al_MmapNoReserveOrDie := 0x6c578;  al_UnmapOrDie := 0x6c1c0;  al_internal_mmap := 0x6a970;  al_internal_munmap := 0x6a97c;
  al_IncreaseTotalMmap := 0x66854;  al_GetNamedMappingFd := 0x6cd1c;  al_ReleaseMemoryPagesToOS := 0x73d70;  al_internal_madvise := 0x6a998;
  al_TryAsanInitFromRtl := 0x5fce0;  al_GetMallocContextSize := 0x60a68;  al_GetCurrentPc := 0x7963c;  al_UnwindImpl := 0x60a78;
  al_Unwind := 0x79ca0;  al_UnwindFast := 0x79644;  al_GetCurrentThread := 0x624e0;  al_AsanTSDGet := 0x5addc;  al_stack_top := 0x626a4;  al_stack_bottom := 0x626fc;
  al_GetCurrentThreadStats := 0x616ac;  al_StackDepotPut := 0x78cb8;  al_Depot_Put := 0x78cd8;  al_Depot_lock := 0x7944c;  al_Depot_find := 0x79398;
  al_Node_store := 0x789d0;  al_StackStore_Store := 0x766bc;  al_StackStore_Alloc := 0x767e0;  al_TwoLevelMap_Create := 0x794dc;
  al_RunMallocHooks := 0x66dc8;  al_RunFreeHooks := 0x66e84;  al_lsan_Disabled := 0x861b8;  al_internal_allocator := 0x6455c;
  al_internal_memset := 0x6a170;  al_internal_memcpy := 0x6a0f4;  al_SetErrnoOnNull := 0x72a50;  al_AllocatorMayReturnNull := 0x64b84;
  al_RssLimitExceeded := 0x64bac;  al_SetAllocatorOutOfMemory := 0x64b74;  al_AsanInited := 0x5edd0;  al_MonotonicNanoTime := 0x73648;
  al_LockSlow := 0x6beec;  al_SemWait := 0x6bfac;  al_SemPost := 0x6bffc;  al_sched_yield_stub := 0x6aad0;  al_CheckFailed := 0x71e78;  al_Die := 0x71dac;
  al_ReportOutOfMemory := 0x5d314;  al_ReportCallocOverflow := 0x5cc30;  al_ReportReallocArrayOverflow := 0 (* [comment removed for export] *);
  al_ReportDoubleFree := 0x5bfcc;  al_ReportFreeNotMalloced := 0x5c4d8;  al_ReportAllocationSizeTooBig := 0x6d598;  al_ReportRssLimitExceeded := 0x5ce80;
  al_spin_freearray := 0x3a184;  al_spin_batch := 0x3b7a8;  al_spin_poison_gap := 0x5a118;  al_spin_mmap_die := 0x661ec;
  al_spin_munmap_die := 0x662bc;  al_spin_shadow_noreserve := 0x746f4;  al_spin_reserved_init := 0x74884;  al_spin_other := 0x7e5dc;
  al_musl_memset := 0xa1f90;  al_musl_memcpy := 0xa1b8c;  al_errno_location := 0x98068;

  al_instance := 0xb1558;  al_asan_flags := 0xb23b8;  al_common_flags := 0x1466e8;  al_shadow_base_var := 0xb4bb8;
  al_kHighMemEnd_var := 0xb58a0;  al_kMidMemBeg_var := 0xb58a8;  al_kMidMemEnd_var := 0xb58b0;
  al_asan_inited := 0xb5898;  al_malloc_context_size := 0xb58bc;  al_can_poison_memory := 0xb441c;  al_unknown_thread_stats := 0xb58e8;
  al_real_memset_cell := 0xaaa18;  al_real_memcpy_cell := 0xaaa10;  al_page_size_cache := 0x144660;
  al_may_return_null := 0x136e21;  al_rss_limit_exceeded := 0x136e22;  al_internal_alloc_inited := 0x144648;  al_internal_allocator_inst := 0xb5dc0;
  al_malloc_hooks := 0x146680;  al_dying_flag := 0x1466dc;  al_total_mmaped := 0x144678;
  al_theDepot := 0x196a98;  al_depot_n_uniq_ids := 0x596a98;  al_depot_nodes_map1 := 0x596aa8;  al_stackStore := 0x186a88;
  al_got_page_size := 0xa8b50;  al_got_common_flags := 0xa8b60;  al_got_asan_flags := 0xa8b68;  al_got_shadow_base := 0xa8b70;
  al_got_kMidMemBeg := 0xa8b78;  al_got_kMidMemEnd := 0xa8b80;  al_got_kHighMemEnd := 0xa8b88;  al_got_real_memset := 0xa8b90;  al_got_real_memcpy := 0xa8b98;
  al_got_sealed := 0xa8bb0;  al_got_dying_flag := 0xa8bb8;
  al_ro_debruijn64 := 0x103b8;  al_ro_log2tab_a := 0x103e8;  al_ro_log2tab_b := 0x10428;  al_ro_log2tab_c := 0x10468;  al_ro_log2tab_d := 0x10528;
  al_ro_alloc_beg_magic := 0x10328;  al_ro_murmur_m := 0x102e8;  al_ro_murmur_k1 := 0x10308;  al_ro_murmur_k2 := 0x103a0;
  al_tp := 0x5e7bd8;  al_errno := 0x5e7b34;
  al_image_lo := 0x10000;  al_text_lo := 0x35000;  al_text_hi := 0xa8000;  al_rw_lo := 0xa8000;  al_image_hi := 0x60a000;  al_brk0 := 0x60a000
|}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition off_fl_quarantine_size_mb : Z := 4.
Definition off_fl_thread_local_quarantine_size_kb : Z := 8.
Definition off_fl_redzone : Z := 12.
Definition off_fl_max_redzone : Z := 16.
Definition off_fl_max_malloc_fill_size : Z := 44.
Definition off_fl_max_free_fill_size : Z := 48.
Definition off_fl_malloc_fill_byte : Z := 52.
Definition off_fl_free_fill_byte : Z := 56.
Definition off_fl_protect_shadow_gap : Z := 78.   (* [comment removed for export] *)
Definition off_fl_poison_heap : Z := 84.          (* [comment removed for export] *)
Definition off_fl_poison_partial : Z := 85.       (* [comment removed for export] *)
Definition off_fl_alloc_dealloc_mismatch : Z := 87. (* [comment removed for export] *)
Definition off_fl_new_delete_type_mismatch : Z := 88.
Definition off_fl_realloc_zero_frees : Z := 113.  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition off_cf_fast_unwind_on_malloc : Z := 34. (* [comment removed for export] *)
Definition off_cf_clear_shadow_mmap_threshold : Z := 120. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition space_beg_of (b6 : Z) : Z := b6 + 0x10000 - b6 mod 0x10000.
  (* [comment removed for export] *)
Definition region_beg (space_beg c : Z) : Z := space_beg + c * kRegionSize.
Definition free_array_beg (space_beg c : Z) : Z := region_beg space_beg c + kFreeArrayOffset.
Definition region_info_addr (space_beg c : Z) : Z := space_beg + kSpaceSize + kRegionInfoSize * c.

Lemma space_beg_aligned : forall b6, 0 <= b6 -> space_beg_of b6 mod 0x10000 = 0.
Proof. intros b6 H. unfold space_beg_of.
  replace (b6 + 0x10000 - b6 mod 0x10000) with ((b6 - b6 mod 0x10000) + 1 * 0x10000) by lia.
  rewrite Z_mod_plus_full. rewrite <- Zminus_mod_idemp_l. rewrite Z.sub_diag. reflexivity. Qed.
Lemma space_beg_range : forall b6, 0 <= b6 -> b6 < space_beg_of b6 <= b6 + 0x10000.
Proof. intros b6 H. unfold space_beg_of. pose proof (Z.mod_pos_bound b6 0x10000 ltac:(lia)). lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
