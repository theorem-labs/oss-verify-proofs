(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition a_text_lo : Z := 384052.  Definition a_text_hi : Z := 1542284.
Definition a_data_lo : Z := 1580352.  Definition a_data_hi : Z := 1592808.
Definition a_asan_globals_lo : Z := 1592816.  Definition a_asan_globals_hi : Z := 1598128.
Definition a_bss_lo : Z := 1598144.  Definition a_bss_hi : Z := 7208408.
Definition a_got_lo : Z := 1572456.  Definition a_got_hi : Z := 1576232.
Definition a_main : Z := 738712.

Definition K_SHADOW_OFFSET : Z := 2147450880.
Definition K_kHighMemEnd : Z := 140737488355327.
Definition K_kMidMemBeg : Z := 0.
Definition K_kMidMemEnd : Z := 0.
Definition K_LOW_SHADOW_lo : Z := 2147446784.  Definition K_LOW_SHADOW_hi : Z := 2415882240.
Definition K_SHADOW_GAP_lo : Z := 2415882240.  Definition K_SHADOW_GAP_hi : Z := 2201439137792.
Definition K_HIGH_SHADOW_lo : Z := 2201439137792.  Definition K_HIGH_SHADOW_hi : Z := 17594333495296.
Definition K_kSpaceSize : Z := 137438953472.
Definition K_kNumClasses : Z := 32.
Definition K_kNumClassesRounded : Z := 32.
Definition K_kRegionSize : Z := 4294967296.
Definition K_kFreeArraySize : Z := 536870912.
Definition K_kUserMapSize : Z := 262144.
Definition K_kFreeArrayMapSize : Z := 262144.
Definition K_kCompactPtrScale : Z := 4.
Definition K_kMinSize : Z := 32.
Definition K_kMidSize : Z := 512.
Definition K_kMidClass : Z := 16.
Definition K_kMaxSize : Z := 65536.
Definition K_kBatchClassID : Z := 31.
Definition K_kMaxNumCachedHint : Z := 8.
Definition K_kMaxBytesCachedLog : Z := 10.
Definition K_kChunkHeaderSize : Z := 16.
Definition K_kChunkHeader2Size : Z := 8.
Definition K_CHUNK_INVALID : Z := 0.
Definition K_CHUNK_ALLOCATED : Z := 2.
Definition K_CHUNK_QUARANTINE : Z := 3.
Definition K_kAsanHeapLeftRedzoneMagic : Z := 250.
Definition K_kAsanHeapFreeMagic : Z := 253.
Definition K_kAllocBegMagic : Z := 14730877155918386873.
Definition K_kMaxAllowedMallocSize : Z := 1099511627776.
Definition K_secondary_kMaxNumChunks : Z := 1048576.
Definition K_secondary_kChunksBlockCount : Z := 16384.
Definition K_quarantine_QuarantineBatch_kSize : Z := 1021.
Definition K_malloc_context_size : Z := 30.
Definition K_clear_shadow_mmap_threshold : Z := 18446744073709551615.

Definition g_instance : Z := 1598232.
Definition g_asan_flags : Z := 1601912.
Definition g_common_flags : Z := 2208936.
Definition g_shadow_memory_dynamic_address : Z := 1612152.
Definition g_detect_stack_use_after_return : Z := 1612160.
Definition g_asan_inited : Z := 1615448.
Definition g_kHighMemEnd : Z := 1615456.
Definition g_kMidMemBeg : Z := 1615464.
Definition g_kMidMemEnd : Z := 1615472.
Definition g_malloc_context_size_cell : Z := 1615484.
Definition g_can_poison_memory : Z := 1610204.
Definition g_tsd_key_inited : Z := 1610208.
Definition g_tsd_key : Z := 1610212.
Definition g_unknown_thread_stats : Z := 1615528.
Definition g_internal_alloc_placeholder : Z := 1616768.
Definition g_rss_limit_exceeded : Z := 2145250.
Definition g_internal_allocator_initialized : Z := 2200584.
Definition g_PageSizeCached : Z := 2200608.
Definition g_g_total_mmaped : Z := 2200632.
Definition g_MFHooks : Z := 2208832.
Definition g_sealed_report_in_progress : Z := 2208924.
Definition g_read_stage : Z := 6995920.
Definition g_GOT_sealed_init : Z := 1572616.
Definition g_GOT_sealed_report : Z := 1572624.
Definition g_GOT_common_flags : Z := 1572536.
Definition g_GOT_asan_flags : Z := 1572544.
Definition g_GOT_shadow_offset_cell : Z := 1572552.
Definition g_GOT_kMidMemBeg : Z := 1572560.
Definition g_GOT_kMidMemEnd : Z := 1572568.
Definition g_GOT_kHighMemEnd : Z := 1572576.
Definition g_GOT_real_memset : Z := 1572584.
Definition g_GOT_PageSizeCached : Z := 1572520.
Definition g_GOT_detect_uar : Z := 1572640.
Definition g_REAL_memset : Z := 1580864.
Definition g_REAL_memcpy : Z := 1580856.

Definition off_i_allocator_primary : Z := 0.
Definition off_i_allocator_secondary : Z := 64.
Definition off_i_allocator_stats : Z := 688.
Definition off_i_quarantine : Z := 728.
Definition off_i_fallback_mutex : Z := 984.
Definition off_i_max_user_defined_malloc_size : Z := 3616.
Definition off_i_min_redzone : Z := 3624.
Definition off_i_max_redzone : Z := 3626.

Definition off_pr_address_range_base : Z := 0.
Definition off_pr_address_range_size : Z := 8.
Definition off_pr_address_range_name : Z := 16.
Definition off_pr_address_range_os_handle : Z := 24.
Definition off_pr_nonconstspacebeg : Z := 32.
Definition off_pr_release_to_os_interval_ms : Z := 40.
Definition off_pr_regioninfospace : Z := 48.
Definition off_pr_premappedheap : Z := 56.

Definition off_ri_mutex_state : Z := 0.
Definition off_ri_mutex_writers_readers : Z := 8.
Definition off_ri_num_freed_chunks : Z := 16.
Definition off_ri_mapped_free_array : Z := 24.
Definition off_ri_allocated_user : Z := 32.
Definition off_ri_allocated_meta : Z := 40.
Definition off_ri_mapped_user : Z := 48.
Definition off_ri_mapped_meta : Z := 56.
Definition off_ri_rand_state : Z := 64.
Definition off_ri_exhausted : Z := 68.
Definition off_ri_stats_n_allocated : Z := 72.
Definition off_ri_stats_n_freed : Z := 80.
Definition off_ri_rtoi_n_freed_at_last_release : Z := 88.
Definition off_ri_rtoi_num_releases : Z := 96.
Definition off_ri_rtoi_last_release_at_ns : Z := 104.
Definition off_ri_rtoi_last_released_bytes : Z := 112.

Definition off_lma_page_size : Z := 0.
Definition off_lma_chunks : Z := 8.
Definition off_lma_ptr_array_address_range : Z := 16.
Definition off_lma_ptr_array_n_reserved : Z := 48.
Definition off_lma_n_chunks : Z := 56.
Definition off_lma_chunks_sorted : Z := 64.
Definition off_lma_stats_n_allocs : Z := 72.
Definition off_lma_stats_n_frees : Z := 80.
Definition off_lma_stats_currently_allocated : Z := 88.
Definition off_lma_stats_max_allocated : Z := 96.
Definition off_lma_stats_by_size_log_64 : Z := 104.
Definition off_lma_mutex : Z := 616.

Definition off_q_pad0_64 : Z := 0.
Definition off_q_max_size : Z := 64.
Definition off_q_min_size : Z := 72.
Definition off_q_max_cache_size : Z := 80.
Definition off_q_pad1_64 : Z := 88.
Definition off_q_cache_mutex : Z := 152.
Definition off_q_recycle_mutex : Z := 153.
Definition off_q_cache : Z := 160.

Definition off_qc_list_size : Z := 0.
Definition off_qc_list_first : Z := 8.
Definition off_qc_list_last : Z := 16.
Definition off_qc_size : Z := 24.

Definition off_qb_next : Z := 0.
Definition off_qb_size : Z := 8.
Definition off_qb_count : Z := 16.
Definition off_qb_batch_1021 : Z := 24.

Definition off_tctx_tid : Z := 8.
Definition off_tctx_thread : Z := 152.

Definition off_t_context : Z := 0.
Definition off_t_stack_top : Z := 8.
Definition off_t_stack_bottom : Z := 16.
Definition off_t_next_stack_top : Z := 24.
Definition off_t_next_stack_bottom : Z := 32.
Definition off_t_stack_switching : Z := 40.
Definition off_t_tls_begin : Z := 48.
Definition off_t_tls_end : Z := 56.
Definition off_t_dtls : Z := 64.
Definition off_t_fake_stack : Z := 72.
Definition off_t_malloc_storage_quarantine_cache : Z := 80.
Definition off_t_malloc_storage_allocator_cache : Z := 208.
Definition off_t_stats : Z := 2800.
Definition off_t_unwinding : Z := 3168.

Definition off_lc_per_class_32 : Z := 0.
Definition off_lc_stats : Z := 2560.

Definition off_pc_count : Z := 0.
Definition off_pc_max_count : Z := 4.
Definition off_pc_class_size : Z := 8.
Definition off_pc_chunks_16 : Z := 16.

Definition off_st_mallocs : Z := 0.
Definition off_st_malloced : Z := 8.
Definition off_st_malloced_redzones : Z := 16.
Definition off_st_frees : Z := 24.
Definition off_st_freed : Z := 32.
Definition off_st_real_frees : Z := 40.
Definition off_st_really_freed : Z := 48.
Definition off_st_reallocs : Z := 56.
Definition off_st_realloced : Z := 64.
Definition off_st_mmaps : Z := 72.
Definition off_st_mmaped : Z := 80.
Definition off_st_munmaps : Z := 88.
Definition off_st_munmaped : Z := 96.
Definition off_st_malloc_large : Z := 104.
Definition off_st_malloced_by_size_32 : Z := 112.

Definition off_ch_chunk_state : Z := 0.
Definition off_ch_alloc_type_2 : Z := 1.
Definition off_ch_user_requested_size_hi : Z := 2.
Definition off_ch_user_requested_size_lo : Z := 4.
Definition off_ch_alloc_context_id : Z := 8.
Definition off_ch_free_context_id : Z := 16.

Definition off_lch_magic : Z := 0.
Definition off_lch_chunk_header : Z := 8.

Definition off_lh_map_beg : Z := 0.
Definition off_lh_map_size : Z := 8.
Definition off_lh_size : Z := 16.
Definition off_lh_chunk_idx : Z := 24.

Definition size_classes : list (Z * Z * Z) := [
  (1, 32, 16);
  (2, 64, 16);
  (3, 96, 16);
  (4, 128, 16);
  (5, 160, 12);
  (6, 192, 10);
  (7, 224, 8);
  (8, 256, 8);
  (9, 288, 6);
  (10, 320, 6);
  (11, 352, 4);
  (12, 384, 4);
  (13, 416, 4);
  (14, 448, 4);
  (15, 480, 4);
  (16, 512, 4);
  (17, 768, 2);
  (18, 1024, 2);
  (19, 1536, 2);
  (20, 2048, 2);
  (21, 3072, 2);
  (22, 4096, 2);
  (23, 6144, 2);
  (24, 8192, 2);
  (25, 12288, 2);
  (26, 16384, 2);
  (27, 24576, 2);
  (28, 32768, 2);
  (29, 49152, 2);
  (30, 65536, 2);
  (31, 64, 16) ]%list.
