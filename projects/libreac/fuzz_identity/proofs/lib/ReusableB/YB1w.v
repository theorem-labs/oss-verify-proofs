(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/YB1w.v (donor image sha256 1c29845fe605), with its addresses changed; 7 of its 520 lines of code are new or changed and 99 lines of the source are left out. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x2308c.
Definition tfib_text_lo : Z := 0x30a20.  Definition tfib_text_hi : Z := 0x9a038.
Definition tfib_init_array_lo : Z := 0x9b038.  Definition tfib_init_array_hi : Z := 0x9b058.
Definition tfib_fini_array_lo : Z := 0x9b058.  Definition tfib_fini_array_hi : Z := 0x9b068.
Definition tfib_preinit_array_lo : Z := 0x9b068.  Definition tfib_preinit_array_hi : Z := 0x9b070.
Definition tfib_data_rel_ro_lo : Z := 0x9b080.  Definition tfib_data_rel_ro_hi : Z := 0x9c630.
Definition tfib_got_lo : Z := 0x9c630.  Definition tfib_got_hi : Z := 0x9d388.
Definition tfib_data_lo : Z := 0x9e388.  Definition tfib_data_hi : Z := 0xa0f40.
Definition tfib_asan_globals_lo : Z := 0xa0f40.  Definition tfib_asan_globals_hi : Z := 0xa1c00.
Definition tfib_bss_lo : Z := 0xa1c00.  Definition tfib_bss_hi : Z := 0x5f9b30.
Definition tfib_tbss_lo : Z := 0x9a038.  Definition tfib_tbss_hi : Z := 0x9a04c.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5fa000.
Definition tfib_entry : Z := 0x30a20.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x30a20.  Definition tfib_E_start : Z := 0x30a68.
Definition tfib_A_do_init : Z := 0x30a68.  Definition tfib_E_do_init : Z := 0x30adc.
Definition tfib_A_do_fini : Z := 0x30adc.  Definition tfib_E_do_fini : Z := 0x30b6c.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30b6c.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x30ba8.
Definition tfib_A_InitializeAllocator : Z := 0x30d18.  Definition tfib_E_InitializeAllocator : Z := 0x30d30.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30d30.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30e9c.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x313f8.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31554.
Definition tfib_A_asan_free : Z := 0x31928.  Definition tfib_E_asan_free : Z := 0x31950.
Definition tfib_A_Allocator_Deallocate : Z := 0x31950.  Definition tfib_E_Allocator_Deallocate : Z := 0x31c08.
Definition tfib_A_asan_malloc : Z := 0x31c08.  Definition tfib_E_asan_malloc : Z := 0x31c64.
Definition tfib_A_Allocator_Allocate : Z := 0x31c64.  Definition tfib_E_Allocator_Allocate : Z := 0x325ec.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32d24.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32e68.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32f54.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32fb0.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32fb0.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x33200.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33200.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x332f4.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x332f4.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x333dc.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x33810.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x339f4.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x33cb0.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33f34.
(* Theorem Labs, 2026-10-29: six rows added, the asan-ubsan twin of identity's A/AB1w.v rows (six functions
   that the table lacked), each E = st_value + st_size in the asan-ubsan image's own .symtab
   (fuzz_identity.debug), verified row by row.
   The release's final pass had deleted the LLVMFuzzerTestOneInput row. *)
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x80774.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x82800.  (* LLVMFuzzerTestOneInput: LLVMFuzzerTestOneInput, size 0x208c *)
Definition tfib_A_stack_malloc_0 : Z := 0x3cfe8.  Definition tfib_E_stack_malloc_0 : Z := 0x3d15c.  (* __asan_stack_malloc_0: __asan_stack_malloc_0 *)
Definition tfib_A_stack_malloc_3 : Z := 0x3d15c.  Definition tfib_E_stack_malloc_3 : Z := 0x3d308.  (* __asan_stack_malloc_3: __asan_stack_malloc_3 *)
Definition tfib_A_stack_malloc_4 : Z := 0x3d308.  Definition tfib_E_stack_malloc_4 : Z := 0x3d4d4.  (* __asan_stack_malloc_4: __asan_stack_malloc_4 *)
Definition tfib_A_MemToShadow_2 : Z := 0x3d4d4.  Definition tfib_E_MemToShadow_2 : Z := 0x3d610.  (* _ZN6__asanL11MemToShadowEm: _ZN6__asanL11MemToShadowEm, size 0x13c (copy 2 of 5) *)
Definition tfib_A_StackDepotNode_store : Z := 0x724ac.  Definition tfib_E_StackDepotNode_store : Z := 0x72508.  (* _ZN11__sanitizer14StackDepotNode5storeEjRKNS_10StackTraceEy: _ZN11__sanitizer14StackDepotNode5storeEjRKNS_10StackTraceEy, size 0x5c *)
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33f34.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x340b4.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x340b4.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x3427c.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x3427c.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x34448.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x34448.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x344e8.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x344e8.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x345ec.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34914.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34a5c.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x34a5c.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x34a94.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x3522c.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x35514.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35bec.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x35d64.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35d64.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35f14.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35f14.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x360f8.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x360f8.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x363d0.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x363d0.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x36848.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x36848.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x36948.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x36948.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36c50.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36c50.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36fc0.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x36fc0.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x370d8.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x374dc.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x375c4.
Definition tfib_A_AsanActivate : Z := 0x375c4.  Definition tfib_E_AsanActivate : Z := 0x376a0.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x37b7c.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x37c64.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c71c.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3c7f4.
Definition tfib_A_FakeStack_Create : Z := 0x3c7f4.  Definition tfib_E_FakeStack_Create : Z := 0x3c8e0.
Definition tfib_A_FakeStack_Allocate : Z := 0x3cb9c.  Definition tfib_E_FakeStack_Allocate : Z := 0x3ce84.
Definition tfib_A_SetTLSFakeStack : Z := 0x3cfb8.  Definition tfib_E_SetTLSFakeStack : Z := 0x3cfe8.
Definition tfib_A_buf_of : Z := 0x82800.  Definition tfib_E_buf_of : Z := 0x82830.  Definition tfib_A_check_str : Z := 0x82830.  Definition tfib_E_check_str : Z := 0x828ac.  Definition tfib_A_put_dec : Z := 0x828ac.  Definition tfib_E_put_dec : Z := 0x82bb8.  Definition tfib_A_reac_box_family_of : Z := 0x82c20.  Definition tfib_E_reac_box_family_of : Z := 0x82d14.  Definition tfib_A_reac_box_family_stem : Z := 0x82d14.  Definition tfib_E_reac_box_family_stem : Z := 0x82d74.  Definition tfib_A_reac_box_name : Z := 0x82d74.  Definition tfib_E_reac_box_name : Z := 0x835d0.  Definition tfib_A_sb_dec : Z := 0x835d0.  Definition tfib_E_sb_dec : Z := 0x83838.  Definition tfib_A_sb_ch : Z := 0x83838.  Definition tfib_E_sb_ch : Z := 0x83944.  Definition tfib_A_reac_box_catalogue_defect : Z := 0x83944.  Definition tfib_E_reac_box_catalogue_defect : Z := 0x83a30.  Definition tfib_A_reac_box_catalogue : Z := 0x83a30.  Definition tfib_E_reac_box_catalogue : Z := 0x83a84.  Definition tfib_A_reac_identity_init : Z := 0x83a84.  Definition tfib_E_reac_identity_init : Z := 0x83aa8.  Definition tfib_A_reac_identity_ingest : Z := 0x83aa8.  Definition tfib_E_reac_identity_ingest : Z := 0x8406c.  Definition tfib_A_reac_identity_fw_str : Z := 0x8406c.  Definition tfib_E_reac_identity_fw_str : Z := 0x842a0.  Definition tfib_A_reac_identity_reac_ver_str : Z := 0x842a0.  Definition tfib_E_reac_identity_reac_ver_str : Z := 0x84460.  Definition tfib_A_write_uint : Z := 0x84460.  Definition tfib_E_write_uint : Z := 0x846b0.


Definition tfib_A_asan_InitializeFlags : Z := 0x3d610.  Definition tfib_E_asan_InitializeFlags : Z := 0x3e63c.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3ed48.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3fb64.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3fb64.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x40130.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x40884.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x40af4.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x40af4.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x40dfc.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x420dc.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x421f4.
Definition tfib_A_strlen : Z := 0x421f4.  Definition tfib_E_strlen : Z := 0x421f8.
Definition tfib_A_strnlen : Z := 0x421f8.  Definition tfib_E_strnlen : Z := 0x421fc.
Definition tfib_A_strcmp : Z := 0x421fc.  Definition tfib_E_strcmp : Z := 0x42200.
Definition tfib_A_strchr : Z := 0x42200.  Definition tfib_E_strchr : Z := 0x42204.
Definition tfib_A_memcmp : Z := 0x42204.  Definition tfib_E_memcmp : Z := 0x42208.
Definition tfib_A_memchr : Z := 0x4220c.  Definition tfib_E_memchr : Z := 0x42210.
Definition tfib_A_frexpl : Z := 0x42210.  Definition tfib_E_frexpl : Z := 0x42214.
Definition tfib_A_read : Z := 0x42214.  Definition tfib_E_read : Z := 0x42218.
Definition tfib_A_fwrite : Z := 0x42218.  Definition tfib_E_fwrite : Z := 0x4221c.
Definition tfib_A_time : Z := 0x4221c.  Definition tfib_E_time : Z := 0x42220.
Definition tfib_A_gmtime_r : Z := 0x42220.  Definition tfib_E_gmtime_r : Z := 0x42224.
Definition tfib_A_vprintf : Z := 0x42224.  Definition tfib_E_vprintf : Z := 0x42228.
Definition tfib_A_vfprintf : Z := 0x42228.  Definition tfib_E_vfprintf : Z := 0x4222c.
Definition tfib_A_vsnprintf : Z := 0x4222c.  Definition tfib_E_vsnprintf : Z := 0x42230.
Definition tfib_A_thunk_417bc : Z := 0x42234.  Definition tfib_E_thunk_417bc : Z := 0x42238.
Definition tfib_A_clock_gettime : Z := 0x42238.  Definition tfib_E_clock_gettime : Z := 0x4223c.
Definition tfib_A_wcrtomb : Z := 0x4223c.  Definition tfib_E_wcrtomb : Z := 0x42240.
Definition tfib_A_wctomb : Z := 0x42240.  Definition tfib_E_wctomb : Z := 0x42244.
Definition tfib_A_thunk_417cc : Z := 0x42244.  Definition tfib_E_thunk_417cc : Z := 0x4224c.
Definition tfib_A_pthread_attr_getstack : Z := 0x4224c.  Definition tfib_E_pthread_attr_getstack : Z := 0x42250.
Definition tfib_A_tls_get_addr_thunk : Z := 0x42250.  Definition tfib_E_tls_get_addr_thunk : Z := 0x42254.

Definition tfib_A_thunk_417dc : Z := 0x42254.  Definition tfib_E_thunk_417dc : Z := 0x42258.

Definition tfib_A_thunk_417e4 : Z := 0x42258.  Definition tfib_E_thunk_417e4 : Z := 0x4225c.
Definition tfib_A_thunk_417e8 : Z := 0x4225c.  Definition tfib_E_thunk_417e8 : Z := 0x42260.
Definition tfib_A_thunk_417ec : Z := 0x42260.  Definition tfib_E_thunk_417ec : Z := 0x42264.
Definition tfib_A_thunk_417f0 : Z := 0x42264.  Definition tfib_E_thunk_417f0 : Z := 0x42268.
Definition tfib_A_sem_timedwait : Z := 0x42268.  Definition tfib_E_sem_timedwait : Z := 0x4226c.
Definition tfib_A_thunk_417f8 : Z := 0x4226c.  Definition tfib_E_thunk_417f8 : Z := 0x42270.
Definition tfib_A_pthread_setcancelstate : Z := 0x42270.  Definition tfib_E_pthread_setcancelstate : Z := 0x42274.
Definition tfib_A_send : Z := 0x42274.  Definition tfib_E_send : Z := 0x42278.
Definition tfib_A_sendto : Z := 0x42278.  Definition tfib_E_sendto : Z := 0x4227c.
Definition tfib_A_sigaltstack : Z := 0x4227c.  Definition tfib_E_sigaltstack : Z := 0x42280.
Definition tfib_A_thunk_4180c : Z := 0x42280.  Definition tfib_E_thunk_4180c : Z := 0x42284.
Definition tfib_A_icpt_strlen : Z := 0x42284.  Definition tfib_E_icpt_strlen : Z := 0x42518.
Definition tfib_A_icpt_strnlen : Z := 0x42518.  Definition tfib_E_icpt_strnlen : Z := 0x427ac.
Definition tfib_A_icpt_strcmp : Z := 0x427b0.  Definition tfib_E_icpt_strcmp : Z := 0x42ce0.
Definition tfib_A_icpt_strchr : Z := 0x42ce0.  Definition tfib_E_icpt_strchr : Z := 0x42fc0.
Definition tfib_A_icpt_memcmp : Z := 0x43858.  Definition tfib_E_icpt_memcmp : Z := 0x43914.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x43914.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x439d0.
Definition tfib_A_icpt_memchr : Z := 0x439d0.  Definition tfib_E_icpt_memchr : Z := 0x43ca0.
Definition tfib_A_icpt_frexpl : Z := 0x43ca0.  Definition tfib_E_icpt_frexpl : Z := 0x43f18.
Definition tfib_A_icpt_read : Z := 0x43f18.  Definition tfib_E_icpt_read : Z := 0x44188.
Definition tfib_A_icpt_fwrite : Z := 0x44188.  Definition tfib_E_icpt_fwrite : Z := 0x443fc.
Definition tfib_A_icpt_time : Z := 0x443fc.  Definition tfib_E_icpt_time : Z := 0x44698.
Definition tfib_A_icpt_gmtime_r : Z := 0x448a0.  Definition tfib_E_icpt_gmtime_r : Z := 0x44ae0.
Definition tfib_A_icpt_vprintf : Z := 0x44ae0.  Definition tfib_E_icpt_vprintf : Z := 0x44b7c.
Definition tfib_A_printf_common_format_interceptor : Z := 0x44b7c.  Definition tfib_E_printf_common_format_interceptor : Z := 0x45644.
Definition tfib_A_icpt_vfprintf : Z := 0x45644.  Definition tfib_E_icpt_vfprintf : Z := 0x456f8.
Definition tfib_A_icpt_vsnprintf : Z := 0x456f8.  Definition tfib_E_icpt_vsnprintf : Z := 0x45a10.
Definition tfib_A_icpt_clock_gettime : Z := 0x45b8c.  Definition tfib_E_icpt_clock_gettime : Z := 0x45de4.
Definition tfib_A_icpt_wcrtomb : Z := 0x45de4.  Definition tfib_E_icpt_wcrtomb : Z := 0x46354.
Definition tfib_A_icpt_wctomb : Z := 0x46354.  Definition tfib_E_icpt_wctomb : Z := 0x466b0.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x4677c.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46b64.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46b70.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46bec.


Definition tfib_A_icpt_sem_timedwait : Z := 0x46df8.  Definition tfib_E_icpt_sem_timedwait : Z := 0x47090.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x470c0.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x472e8.
Definition tfib_A_icpt_send : Z := 0x472e8.  Definition tfib_E_icpt_send : Z := 0x4759c.
Definition tfib_A_icpt_sendto : Z := 0x4759c.  Definition tfib_E_icpt_sendto : Z := 0x47860.
Definition tfib_A_icpt_sigaltstack : Z := 0x47860.  Definition tfib_E_icpt_sigaltstack : Z := 0x47abc.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x47b90.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47d40.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x48a84.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x5175c.
Definition tfib_A_memset : Z := 0x518b8.  Definition tfib_E_memset : Z := 0x518bc.
Definition tfib_A_memcpy : Z := 0x518bc.  Definition tfib_E_memcpy : Z := 0x518c0.
Definition tfib_A_asan_memcpy : Z := 0x518c0.  Definition tfib_E_asan_memcpy : Z := 0x51d5c.
Definition tfib_A_asan_memset : Z := 0x51d5c.  Definition tfib_E_asan_memset : Z := 0x51f9c.
Definition tfib_A_icpt_memset : Z := 0x51f9c.  Definition tfib_E_icpt_memset : Z := 0x5228c.
Definition tfib_A_icpt_memcpy : Z := 0x5228c.  Definition tfib_E_icpt_memcpy : Z := 0x5287c.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x5287c.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x528b4.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x528b4.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x528b8.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x528b8.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x528bc.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x528bc.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x5291c.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52968.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52aa4.
Definition tfib_A_free : Z := 0x52c10.  Definition tfib_E_free : Z := 0x52c14.
Definition tfib_A_malloc : Z := 0x52c14.  Definition tfib_E_malloc : Z := 0x52c18.
Definition tfib_A_icpt_free : Z := 0x52c18.  Definition tfib_E_icpt_free : Z := 0x52de8.
Definition tfib_A_icpt_malloc : Z := 0x52de8.  Definition tfib_E_icpt_malloc : Z := 0x52f44.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x53010.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x53014.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x53014.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x53114.
Definition tfib_A_SetCanPoisonMemory : Z := 0x53a90.  Definition tfib_E_SetCanPoisonMemory : Z := 0x53aa0.
Definition tfib_A_CanPoisonMemory : Z := 0x53aa0.  Definition tfib_E_CanPoisonMemory : Z := 0x53ab4.
Definition tfib_A_PoisonShadow : Z := 0x53ab4.  Definition tfib_E_PoisonShadow : Z := 0x53fb0.
Definition tfib_A_MemToShadow_checked : Z := 0x53fb0.  Definition tfib_E_MemToShadow_checked : Z := 0x540ec.
Definition tfib_A_asan_region_is_poisoned : Z := 0x5443c.  Definition tfib_E_asan_region_is_poisoned : Z := 0x54780.
Definition tfib_A_AsanTSDInit : Z := 0x54ba0.  Definition tfib_E_AsanTSDInit : Z := 0x54c1c.
Definition tfib_A_AsanTSDGet : Z := 0x54c1c.  Definition tfib_E_AsanTSDGet : Z := 0x54c5c.
Definition tfib_A_AsanTSDSet : Z := 0x54c5c.  Definition tfib_E_AsanTSDSet : Z := 0x54c9c.
Definition tfib_A_PlatformTSDDtor : Z := 0x54c9c.  Definition tfib_E_PlatformTSDDtor : Z := 0x54d20.
Definition tfib_A_InstallAtForkHandler : Z := 0x54d20.  Definition tfib_E_InstallAtForkHandler : Z := 0x54d3c.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54d9c.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x54de0.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x554f8.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x55704.
Definition tfib_A_ReportDoubleFree : Z := 0x55e0c.  Definition tfib_E_ReportDoubleFree : Z := 0x5609c.
Definition tfib_A_ReportGenericError : Z := 0x57978.  Definition tfib_E_ReportGenericError : Z := 0x58234.
Definition tfib_A_AsanInited : Z := 0x589c0.  Definition tfib_E_AsanInited : Z := 0x589d8.
Definition tfib_A_asan_report_load1 : Z := 0x589d8.  Definition tfib_E_asan_report_load1 : Z := 0x58a28.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58a28.  Definition tfib_E_asan_report_exp_load1 : Z := 0x58a78.
Definition tfib_A_asan_report_load2 : Z := 0x58a78.  Definition tfib_E_asan_report_load2 : Z := 0x58ac8.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58ac8.  Definition tfib_E_asan_report_exp_load2 : Z := 0x58b18.
Definition tfib_A_asan_report_load4 : Z := 0x58b18.  Definition tfib_E_asan_report_load4 : Z := 0x58b68.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58b68.  Definition tfib_E_asan_report_exp_load4 : Z := 0x58bb8.
Definition tfib_A_asan_report_load8 : Z := 0x58bb8.  Definition tfib_E_asan_report_load8 : Z := 0x58c08.
Definition tfib_A_asan_report_exp_load8 : Z := 0x58c08.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58c58.
Definition tfib_A_asan_report_load16 : Z := 0x58c58.  Definition tfib_E_asan_report_load16 : Z := 0x58ca8.
Definition tfib_A_asan_report_exp_load16 : Z := 0x58ca8.  Definition tfib_E_asan_report_exp_load16 : Z := 0x58cf8.
Definition tfib_A_asan_report_store1 : Z := 0x58cf8.  Definition tfib_E_asan_report_store1 : Z := 0x58d48.
Definition tfib_A_asan_report_exp_store1 : Z := 0x58d48.  Definition tfib_E_asan_report_exp_store1 : Z := 0x58d98.
Definition tfib_A_asan_report_store2 : Z := 0x58d98.  Definition tfib_E_asan_report_store2 : Z := 0x58de8.
Definition tfib_A_asan_report_exp_store2 : Z := 0x58de8.  Definition tfib_E_asan_report_exp_store2 : Z := 0x58e38.
Definition tfib_A_asan_report_store4 : Z := 0x58e38.  Definition tfib_E_asan_report_store4 : Z := 0x58e88.
Definition tfib_A_asan_report_exp_store4 : Z := 0x58e88.  Definition tfib_E_asan_report_exp_store4 : Z := 0x58ed8.
Definition tfib_A_asan_report_store8 : Z := 0x58ed8.  Definition tfib_E_asan_report_store8 : Z := 0x58f28.
Definition tfib_A_asan_report_exp_store8 : Z := 0x58f28.  Definition tfib_E_asan_report_exp_store8 : Z := 0x58f78.
Definition tfib_A_asan_report_store16 : Z := 0x58f78.  Definition tfib_E_asan_report_store16 : Z := 0x58fc8.
Definition tfib_A_asan_report_exp_store16 : Z := 0x58fc8.  Definition tfib_E_asan_report_exp_store16 : Z := 0x59018.
Definition tfib_A_asan_report_load_n : Z := 0x59018.  Definition tfib_E_asan_report_load_n : Z := 0x59068.
Definition tfib_A_asan_report_exp_load_n : Z := 0x59068.  Definition tfib_E_asan_report_exp_load_n : Z := 0x590b8.
Definition tfib_A_asan_report_store_n : Z := 0x590b8.  Definition tfib_E_asan_report_store_n : Z := 0x59108.
Definition tfib_A_asan_report_exp_store_n : Z := 0x59108.  Definition tfib_E_asan_report_exp_store_n : Z := 0x59158.
Definition tfib_A_InitializeHighMemEnd : Z := 0x59158.  Definition tfib_E_InitializeHighMemEnd : Z := 0x591d8.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x591d8.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x5958c.
Definition tfib_A_AsanInitInternal : Z := 0x5961c.  Definition tfib_E_AsanInitInternal : Z := 0x598d0.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x598d0.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x59970.
Definition tfib_A_thunk_59674 : Z := 0x59b38.  Definition tfib_E_thunk_59674 : Z := 0x59b3c.
Definition tfib_A_asan_init : Z := 0x59b3c.  Definition tfib_E_asan_init : Z := 0x59bd0.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x59bd0.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x59bd4.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x59e38.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5a160.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5a160.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x5a340.
Definition tfib_A_InitializeShadowMemory : Z := 0x5a340.  Definition tfib_E_InitializeShadowMemory : Z := 0x5a648.
Definition tfib_A_SetMallocContextSize : Z := 0x5a648.  Definition tfib_E_SetMallocContextSize : Z := 0x5a658.
Definition tfib_A_GetMallocContextSize : Z := 0x5a658.  Definition tfib_E_GetMallocContextSize : Z := 0x5a668.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5a668.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5a7b8.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5ab98.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5ae38.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5b29c.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5b2d4.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5b57c.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5b588.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5b588.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5b614.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5b614.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5b67c.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5b67c.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5b6f4.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5b6f4.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5b75c.
Definition tfib_A_AsanThread_Create : Z := 0x5bcc0.  Definition tfib_E_AsanThread_Create : Z := 0x5be5c.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5beb8.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5c0d0.
Definition tfib_A_GetCurrentThread : Z := 0x5c0d0.  Definition tfib_E_GetCurrentThread : Z := 0x5c0f0.
Definition tfib_A_AsanThread_stack_top : Z := 0x5c294.  Definition tfib_E_AsanThread_stack_top : Z := 0x5c2ec.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5c2ec.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5c344.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c344.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5c574.
Definition tfib_A_AsanThread_Init : Z := 0x5c574.  Definition tfib_E_AsanThread_Init : Z := 0x5c968.
Definition tfib_A_CreateMainThread : Z := 0x5caa8.  Definition tfib_E_CreateMainThread : Z := 0x5cbb8.
Definition tfib_A_SetCurrentThread : Z := 0x5cbb8.  Definition tfib_E_SetCurrentThread : Z := 0x5cc98.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5ce9c.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5cfd8.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5e14c.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5e2a4.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5e5e8.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5e634.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5e634.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5e640.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5e670.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5e67c.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5e67c.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5e688.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e6a4.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e970.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e970.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5ed30.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x5fc8c.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x5fc98.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5fc98.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5fd70.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5fd70.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5fe0c.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60330.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60374.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x605ec.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x60700.
Definition tfib_A_RunMallocHooks : Z := 0x608a4.  Definition tfib_E_RunMallocHooks : Z := 0x6095c.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x6095c.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x60960.
Definition tfib_A_RunFreeHooks : Z := 0x60960.  Definition tfib_E_RunFreeHooks : Z := 0x60a0c.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x60a40.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x60a8c.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60d50.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60f90.
Definition tfib_A_sanitizer_set_report_path : Z := 0x6158c.  Definition tfib_E_sanitizer_set_report_path : Z := 0x615a4.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x616e8.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x616f0.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x631b4.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x634c4.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x634c4.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x63608.
Definition tfib_A_FlagParser_ParseString : Z := 0x63608.  Definition tfib_E_FlagParser_ParseString : Z := 0x636fc.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x63890.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x638f0.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x638f0.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x63930.
Definition tfib_A_internal_atoll : Z := 0x63930.  Definition tfib_E_internal_atoll : Z := 0x63a1c.
Definition tfib_A_internal_simple_strtoll : Z := 0x63a1c.  Definition tfib_E_internal_simple_strtoll : Z := 0x63b78.
Definition tfib_A_internal_memchr : Z := 0x63b78.  Definition tfib_E_internal_memchr : Z := 0x63b98.
Definition tfib_A_internal_memcmp : Z := 0x63b98.  Definition tfib_E_internal_memcmp : Z := 0x63bd0.
Definition tfib_A_internal_memcpy : Z := 0x63bd0.  Definition tfib_E_internal_memcpy : Z := 0x63bf4.
Definition tfib_A_internal_memmove : Z := 0x63bf4.  Definition tfib_E_internal_memmove : Z := 0x63c4c.
Definition tfib_A_internal_memset : Z := 0x63c4c.  Definition tfib_E_internal_memset : Z := 0x63cac.
Definition tfib_A_internal_strcspn : Z := 0x63cac.  Definition tfib_E_internal_strcspn : Z := 0x63d00.
Definition tfib_A_internal_strdup : Z := 0x63d34.  Definition tfib_E_internal_strdup : Z := 0x63da0.
Definition tfib_A_internal_strlen : Z := 0x63da0.  Definition tfib_E_internal_strlen : Z := 0x63dbc.
Definition tfib_A_internal_strchrnul : Z := 0x63e4c.  Definition tfib_E_internal_strchrnul : Z := 0x63e94.
Definition tfib_A_internal_strrchr : Z := 0x63e94.  Definition tfib_E_internal_strrchr : Z := 0x63ed4.
Definition tfib_A_internal_strnlen : Z := 0x64004.  Definition tfib_E_internal_strnlen : Z := 0x64034.
Definition tfib_A_internal_strncpy : Z := 0x64078.  Definition tfib_E_internal_strncpy : Z := 0x640e8.
Definition tfib_A_internal_strstr : Z := 0x640e8.  Definition tfib_E_internal_strstr : Z := 0x6417c.
Definition tfib_A_mem_is_zero : Z := 0x6417c.  Definition tfib_E_mem_is_zero : Z := 0x64230.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64230.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64240.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64240.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64420.
Definition tfib_A_internal_iserror : Z := 0x6442c.  Definition tfib_E_internal_iserror : Z := 0x6444c.
Definition tfib_A_internal_mmap : Z := 0x6444c.  Definition tfib_E_internal_mmap : Z := 0x64458.
Definition tfib_A_internal_munmap : Z := 0x64458.  Definition tfib_E_internal_munmap : Z := 0x64464.
Definition tfib_A_internal_mprotect : Z := 0x64464.  Definition tfib_E_internal_mprotect : Z := 0x64474.
Definition tfib_A_internal_madvise : Z := 0x64474.  Definition tfib_E_internal_madvise : Z := 0x644a0.
Definition tfib_A_internal_close : Z := 0x644a0.  Definition tfib_E_internal_close : Z := 0x644ac.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x644ac.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x644d0.
Definition tfib_A_internal_read : Z := 0x644d0.  Definition tfib_E_internal_read : Z := 0x64508.
Definition tfib_A_internal_write : Z := 0x64508.  Definition tfib_E_internal_write : Z := 0x64540.
Definition tfib_A_internal_ftruncate : Z := 0x64540.  Definition tfib_E_internal_ftruncate : Z := 0x64578.
Definition tfib_A_internal_dup : Z := 0x64578.  Definition tfib_E_internal_dup : Z := 0x64584.
Definition tfib_A_internal_dup2_dup3 : Z := 0x64584.  Definition tfib_E_internal_dup2_dup3 : Z := 0x64594.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x64594.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x645ac.
Definition tfib_A_internal_sched_yield : Z := 0x645ac.  Definition tfib_E_internal_sched_yield : Z := 0x645b8.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x645b8.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x64604.
Definition tfib_A_internal_execve : Z := 0x64604.  Definition tfib_E_internal_execve : Z := 0x64610.
Definition tfib_A_internal_exit_exit_group : Z := 0x64610.  Definition tfib_E_internal_exit_exit_group : Z := 0x64624.
Definition tfib_A_FileExists_newfstatat : Z := 0x64624.  Definition tfib_E_FileExists_newfstatat : Z := 0x646a4.
Definition tfib_A_DirExists_newfstatat : Z := 0x646a4.  Definition tfib_E_DirExists_newfstatat : Z := 0x64708.
Definition tfib_A_GetTid_gettid : Z := 0x64708.  Definition tfib_E_GetTid_gettid : Z := 0x64714.
Definition tfib_A_GetEnv : Z := 0x64714.  Definition tfib_E_GetEnv : Z := 0x64844.
Definition tfib_A_FutexWait : Z := 0x64948.  Definition tfib_E_FutexWait : Z := 0x6496c.
Definition tfib_A_FutexWake : Z := 0x6496c.  Definition tfib_E_FutexWake : Z := 0x64990.
Definition tfib_A_internal_ptrace : Z := 0x64990.  Definition tfib_E_internal_ptrace : Z := 0x6499c.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x6499c.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x649ac.
Definition tfib_A_internal_getpid : Z := 0x649ac.  Definition tfib_E_internal_getpid : Z := 0x649b8.
Definition tfib_A_internal_getppid : Z := 0x649b8.  Definition tfib_E_internal_getppid : Z := 0x649c4.
Definition tfib_A_internal_prctl : Z := 0x649c4.  Definition tfib_E_internal_prctl : Z := 0x649d0.
Definition tfib_A_internal_sigaltstack : Z := 0x649d0.  Definition tfib_E_internal_sigaltstack : Z := 0x649dc.
Definition tfib_A_internal_fork_clone : Z := 0x649dc.  Definition tfib_E_internal_fork_clone : Z := 0x649f4.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x649f4.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x64b20.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65260.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65378.
Definition tfib_A_GetPageSizeCached : Z := 0x65378.  Definition tfib_E_GetPageSizeCached : Z := 0x65380.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65380.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x6542c.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x6542c.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x6554c.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x65614.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x65694.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x656f0.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x657bc.
Definition tfib_A_thunk_653ec : Z := 0x658b8.  Definition tfib_E_thunk_653ec : Z := 0x658bc.
Definition tfib_A_CheckASLR : Z := 0x658bc.  Definition tfib_E_CheckASLR : Z := 0x658c0.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x65b0c.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x65b10.
Definition tfib_A_MmapOrDie : Z := 0x65b1c.  Definition tfib_E_MmapOrDie : Z := 0x65c28.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x65c28.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x65c9c.
Definition tfib_A_UnmapOrDie : Z := 0x65c9c.  Definition tfib_E_UnmapOrDie : Z := 0x65d18.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x65d18.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x65e28.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x66054.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x66158.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x66164.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x662dc.
Definition tfib_A_thunk_66008 : Z := 0x664d4.  Definition tfib_E_thunk_66008 : Z := 0x664d8.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x667f8.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x66a04.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x66fbc.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x66fc8.
Definition tfib_A_Printf : Z := 0x66fcc.  Definition tfib_E_Printf : Z := 0x67018.
Definition tfib_A_SharedPrintfCode : Z := 0x67018.  Definition tfib_E_SharedPrintfCode : Z := 0x67074.
Definition tfib_A_Report : Z := 0x67074.  Definition tfib_E_Report : Z := 0x670c0.
Definition tfib_A_SuppressionContext_ctor : Z := 0x68bb8.  Definition tfib_E_SuppressionContext_ctor : Z := 0x68c14.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68c14.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x68e50.
Definition tfib_A_SuppressionContext_Parse : Z := 0x68e50.  Definition tfib_E_SuppressionContext_Parse : Z := 0x69174.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x69714.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x697e4.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x697e4.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x69b34.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x69e24.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6a29c.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6ab5c.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6ae80.
Definition tfib_A_AddDieCallback : Z := 0x6b73c.  Definition tfib_E_AddDieCallback : Z := 0x6b7c4.
Definition tfib_A_Die : Z := 0x6b888.  Definition tfib_E_Die : Z := 0x6b948.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b948.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b954.
Definition tfib_A_CheckFailed : Z := 0x6b954.  Definition tfib_E_CheckFailed : Z := 0x6ba0c.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6c064.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6c15c.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6c15c.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6c288.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6c4b0.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6c52c.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6c560.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c848.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6cc3c.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6cd0c.
Definition tfib_A_AndroidLogInit : Z := 0x6d0f0.  Definition tfib_E_AndroidLogInit : Z := 0x6d0f4.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6d124.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6d16c.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d16c.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6d3b8.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x6d3bc.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x6d4c8.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6d4c8.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6d5cc.
Definition tfib_A_thunk_6d37c : Z := 0x6d848.  Definition tfib_E_thunk_6d37c : Z := 0x6d84c.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d910.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d9b0.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6da3c.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6db00.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6db00.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6db88.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6db88.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6dc00.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6dc00.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6dce4.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6dda0.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6ded4.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6e10c.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6e23c.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6e29c.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6e368.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6e39c.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6e4e8.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x70198.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x702bc.
Definition tfib_A_StackStore_Alloc : Z := 0x702bc.  Definition tfib_E_StackStore_Alloc : Z := 0x703f0.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x70ca4.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x70d58.

Definition tfib_A_StackDepotPut : Z := 0x72794.  Definition tfib_E_StackDepotPut : Z := 0x727b4.
Definition tfib_A_StackDepotBase_Put : Z := 0x727b4.  Definition tfib_E_StackDepotBase_Put : Z := 0x72a38.
Definition tfib_A_StackDepotBase_Get : Z := 0x72a38.  Definition tfib_E_StackDepotBase_Get : Z := 0x72b48.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x73118.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x73120.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73120.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73280.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x73280.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x732f4.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x7377c.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73894.
Definition tfib_A_thunk_762d8 : Z := 0x768e0.  Definition tfib_E_thunk_762d8 : Z := 0x768e4.
Definition tfib_A_thunk_77ab0 : Z := 0x780b8.  Definition tfib_E_thunk_77ab0 : Z := 0x780bc.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x79ae4.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x79ba0.
Definition tfib_A_Unwind_Trace_callback : Z := 0x79ba0.  Definition tfib_E_Unwind_Trace_callback : Z := 0x79c78.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a25c.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7a62c.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a8fc.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a9b4.
Definition tfib_A_thunk_7b6f8 : Z := 0x7bd0c.  Definition tfib_E_thunk_7b6f8 : Z := 0x7bd10.
Definition tfib_A_lsan_register_root_region : Z := 0x7c918.  Definition tfib_E_lsan_register_root_region : Z := 0x7cc48.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7cc48.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7d0d0.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x80030.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x800ac.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x800ac.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x8015c.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x8015c.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x80174.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80174.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x802bc.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x802bc.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x802c8.
Definition tfib_A_asan_default_options_cli_c : Z := 0x802c8.  Definition tfib_E_asan_default_options_cli_c : Z := 0x802d4.
Definition tfib_A_main : Z := 0x802d4.  Definition tfib_E_main : Z := 0x80598.
Definition tfib_A_target_alloc_init : Z := 0x80598.  Definition tfib_E_target_alloc_init : Z := 0x8059c.
Definition tfib_A_target_alloc_count : Z := 0x8059c.  Definition tfib_E_target_alloc_count : Z := 0x805a4.
(* tfib_E_target_run is target_run THROUGH oft_exit_guard - the exit walk's region, not target_run's own
   end: this image's .symtab has target_run 0x805a4..0x806fc and oft_exit_guard 0x806fc..0x8072c. The A
   core states the same region against its own image (lib/A/AB1w.v: 0x8053c..0x806c4), so each copy is
   derived from the image it describes. *)
Definition tfib_A_target_run : Z := 0x805a4.  Definition tfib_E_target_run : Z := 0x8072c.
Definition tfib_A_emit_printf : Z := 0x8072c.  Definition tfib_E_emit_printf : Z := 0x80774.


Definition tfib_A_asan_module_ctor : Z := 0x82bb8.  Definition tfib_E_asan_module_ctor : Z := 0x82bf0.








Definition tfib_A_asan_module_dtor : Z := 0x82bf0.  Definition tfib_E_asan_module_dtor : Z := 0x82c20.






Definition tfib_A_extenddftf2 : Z := 0x846c0.  Definition tfib_E_extenddftf2 : Z := 0x84850.
Definition tfib_A_sysconf : Z := 0x8a4a0.  Definition tfib_E_sysconf : Z := 0x8a6c8.
Definition tfib_A_init : Z := 0x8a6c8.  Definition tfib_E_init : Z := 0x8a6cc.
Definition tfib_A_init_libc : Z := 0x8a6cc.  Definition tfib_E_init_libc : Z := 0x8a8f8.
Definition tfib_A_libc_start_init : Z := 0x8a8f8.  Definition tfib_E_libc_start_init : Z := 0x8a944.
Definition tfib_A_libc_start_main : Z := 0x8a944.  Definition tfib_E_libc_start_main : Z := 0x8a9a4.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8a9a4.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8a9ec.
Definition tfib_A_init_tls : Z := 0x8aac4.  Definition tfib_E_init_tls : Z := 0x8ad74.
Definition tfib_A_init_ssp : Z := 0x8ad74.  Definition tfib_E_init_ssp : Z := 0x8add4.
Definition tfib_A_stack_chk_fail : Z := 0x8add4.  Definition tfib_E_stack_chk_fail : Z := 0x8addc.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8ae24.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8aeb8.
Definition tfib_A_Exit : Z := 0x8aeb8.  Definition tfib_E_Exit : Z := 0x8aed4.
Definition tfib_A_funcs_on_exit : Z := 0x8af04.  Definition tfib_E_funcs_on_exit : Z := 0x8afcc.
Definition tfib_A_cxa_atexit_atexit : Z := 0x8afd0.  Definition tfib_E_cxa_atexit_atexit : Z := 0x8b094.
Definition tfib_A_libc_exit_fini : Z := 0x8b09c.  Definition tfib_E_libc_exit_fini : Z := 0x8b0e8.
Definition tfib_A_exit : Z := 0x8b0e8.  Definition tfib_E_exit : Z := 0x8b15c.
Definition tfib_A_open : Z := 0x8b35c.  Definition tfib_E_open : Z := 0x8b440.
Definition tfib_A_syscall_ret : Z := 0x8b440.  Definition tfib_E_syscall_ret : Z := 0x8b478.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8b478.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x8b620.
Definition tfib_A_calloc : Z := 0x8bbe4.  Definition tfib_E_calloc : Z := 0x8bd1c.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8bd1c.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x8bd20.
Definition tfib_A_libc_free : Z := 0x8bd20.  Definition tfib_E_libc_free : Z := 0x8beec.
Definition tfib_A_get_meta : Z := 0x8beec.  Definition tfib_E_get_meta : Z := 0x8bffc.
Definition tfib_A_alloc_meta : Z := 0x8c3d4.  Definition tfib_E_alloc_meta : Z := 0x8c6ac.
Definition tfib_A_libc_malloc_impl : Z := 0x8c6ac.  Definition tfib_E_libc_malloc_impl : Z := 0x8ca1c.
Definition tfib_A_alloc_slot : Z := 0x8ca1c.  Definition tfib_E_alloc_slot : Z := 0x8d2c0.
Definition tfib_A_enframe : Z := 0x8d2c0.  Definition tfib_E_enframe : Z := 0x8d410.
Definition tfib_A_malloc_allzerop : Z := 0x8d410.  Definition tfib_E_malloc_allzerop : Z := 0x8d588.
Definition tfib_A_getrlimit : Z := 0x8f238.  Definition tfib_E_getrlimit : Z := 0x8f330.
Definition tfib_A_getrusage : Z := 0x8f330.  Definition tfib_E_getrusage : Z := 0x8f358.
Definition tfib_A_setrlimit : Z := 0x8f358.  Definition tfib_E_setrlimit : Z := 0x8f420.
Definition tfib_A_mmap : Z := 0x8f848.  Definition tfib_E_mmap : Z := 0x8f934.
Definition tfib_A_mprotect : Z := 0x8f934.  Definition tfib_E_mprotect : Z := 0x8f97c.
Definition tfib_A_munmap : Z := 0x8fa50.  Definition tfib_E_munmap : Z := 0x8fa98.
Definition tfib_A_sched_yield : Z := 0x8fd5c.  Definition tfib_E_sched_yield : Z := 0x8fd80.
Definition tfib_A_raise_tkill_path : Z := 0x8fddc.  Definition tfib_E_raise_tkill_path : Z := 0x8fe54.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x8fe54.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x90028.
Definition tfib_A_musl_sigaltstack : Z := 0x90120.  Definition tfib_E_musl_sigaltstack : Z := 0x901ac.

Definition tfib_A_lockfile : Z := 0x907ec.  Definition tfib_E_lockfile : Z := 0x908e8.
Definition tfib_A_unlockfile : Z := 0x908e8.  Definition tfib_E_unlockfile : Z := 0x90948.



Definition tfib_A_stdio_read : Z := 0x904d8.  Definition tfib_E_stdio_read : Z := 0x905f0.
Definition tfib_A_stdio_write : Z := 0x905f8.  Definition tfib_E_stdio_write : Z := 0x90788.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x904a8.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x904ac.
Definition tfib_A_stdio_close : Z := 0x904ac.  Definition tfib_E_stdio_close : Z := 0x904d8.
Definition tfib_A_fwritex : Z := 0x90d7c.  Definition tfib_E_fwritex : Z := 0x90eb4.
Definition tfib_A_musl_fwrite : Z := 0x90eb4.  Definition tfib_E_musl_fwrite : Z := 0x90f6c.
Definition tfib_A_towrite : Z := 0x90f6c.  Definition tfib_E_towrite : Z := 0x90fc0.
Definition tfib_A_stdio_exit : Z := 0x90bd8.  Definition tfib_E_stdio_exit : Z := 0x90d7c.
Definition tfib_A_ofl_lock : Z := 0x90fc0.  Definition tfib_E_ofl_lock : Z := 0x90ff0.

Definition tfib_A_musl_vfprintf : Z := 0x9113c.  Definition tfib_E_musl_vfprintf : Z := 0x912ec.
Definition tfib_A_printf_core : Z := 0x912ec.  Definition tfib_E_printf_core : Z := 0x9211c.
Definition tfib_A_pop_arg : Z := 0x9211c.  Definition tfib_E_pop_arg : Z := 0x92250.
Definition tfib_A_pad : Z := 0x92250.  Definition tfib_E_pad : Z := 0x92324.
Definition tfib_A_fmt_fp : Z := 0x92324.  Definition tfib_E_fmt_fp : Z := 0x939ec.
Definition tfib_A_thunk_931e0 : Z := 0x8b838.  Definition tfib_E_thunk_931e0 : Z := 0x8b83c.
Definition tfib_A_musl_wctomb : Z := 0x8fbc4.  Definition tfib_E_musl_wctomb : Z := 0x8fbe8.
Definition tfib_A_musl_wcrtomb : Z := 0x8fa98.  Definition tfib_E_musl_wcrtomb : Z := 0x8fbc4.
Definition tfib_A_fpclassifyl : Z := 0x8de28.  Definition tfib_E_fpclassifyl : Z := 0x8de6c.
Definition tfib_A_letf2 : Z := 0x8d660.  Definition tfib_E_letf2 : Z := 0x8d728.
Definition tfib_A_multf3 : Z := 0x8d728.  Definition tfib_E_multf3 : Z := 0x8de28.
Definition tfib_A_floatsitf : Z := 0x8e684.  Definition tfib_E_floatsitf : Z := 0x8e78c.
Definition tfib_A_scalbn : Z := 0x8f090.  Definition tfib_E_scalbn : Z := 0x8f128.
Definition tfib_A_subtf3 : Z := 0x8e674.  Definition tfib_E_subtf3 : Z := 0x8e684.
Definition tfib_A_addtf3 : Z := 0x8de6c.  Definition tfib_E_addtf3 : Z := 0x8e638.
Definition tfib_A_fe_getround : Z := 0x8e638.  Definition tfib_E_fe_getround : Z := 0x8e668.
Definition tfib_A_fixunstfsi : Z := 0x939f4.  Definition tfib_E_fixunstfsi : Z := 0x93a88.
Definition tfib_A_floatunsitf : Z := 0x93a88.  Definition tfib_E_floatunsitf : Z := 0x93b74.
Definition tfib_A_fixtfsi : Z := 0x8f128.  Definition tfib_E_fixtfsi : Z := 0x8f1d0.
Definition tfib_A_divtf3 : Z := 0x8e78c.  Definition tfib_E_divtf3 : Z := 0x8f090.
Definition tfib_A_musl_vprintf : Z := 0x9424c.  Definition tfib_E_musl_vprintf : Z := 0x94268.
Definition tfib_A_stdout_write : Z := 0x90ffc.  Definition tfib_E_stdout_write : Z := 0x9109c.
Definition tfib_A_thunk_95368 : Z := 0x94800.  Definition tfib_E_thunk_95368 : Z := 0x94804.
Definition tfib_A_musl_memcmp : Z := 0x948d0.  Definition tfib_E_musl_memcmp : Z := 0x94900.
Definition tfib_A_musl_memcpy : Z := 0x94900.  Definition tfib_E_musl_memcpy : Z := 0x94d04.
Definition tfib_A_musl_memset : Z := 0x94d04.  Definition tfib_E_musl_memset : Z := 0x94dfc.
Definition tfib_A_musl_strchr : Z := 0x94dfc.  Definition tfib_E_musl_strchr : Z := 0x94e38.
Definition tfib_A_strchrnul : Z := 0x94e38.  Definition tfib_E_strchrnul : Z := 0x94f18.
Definition tfib_A_musl_strlen : Z := 0x94f50.  Definition tfib_E_musl_strlen : Z := 0x94fe0.
Definition tfib_A_musl_strnlen : Z := 0x9518c.  Definition tfib_E_musl_strnlen : Z := 0x951d0.
Definition tfib_A_musl_memchr : Z := 0x94804.  Definition tfib_E_musl_memchr : Z := 0x948d0.
Definition tfib_A_lock : Z := 0x951d0.  Definition tfib_E_lock : Z := 0x95458.
Definition tfib_A_unlock : Z := 0x95458.  Definition tfib_E_unlock : Z := 0x954cc.
Definition tfib_A_syscall_cp_c : Z := 0x954cc.  Definition tfib_E_syscall_cp_c : Z := 0x954f0.
Definition tfib_A_syscall_cp_sccp : Z := 0x954f0.  Definition tfib_E_syscall_cp_sccp : Z := 0x954f4.
Definition tfib_A_pthread_atfork : Z := 0x95530.  Definition tfib_E_pthread_atfork : Z := 0x955d4.
Definition tfib_A_mremap : Z := 0x8f97c.  Definition tfib_E_mremap : Z := 0x8fa50.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x965a8.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x965c4.
Definition tfib_A_pthread_key_create : Z := 0x96950.  Definition tfib_E_pthread_key_create : Z := 0x96a24.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0x96d6c.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0x96e88.
Definition tfib_A_pthread_setspecific : Z := 0x96eec.  Definition tfib_E_pthread_setspecific : Z := 0x96f20.
Definition tfib_A_set_thread_area : Z := 0x96f28.  Definition tfib_E_set_thread_area : Z := 0x96f34.
Definition tfib_A_thunk_96f9c : Z := 0x96f20.  Definition tfib_E_thunk_96f9c : Z := 0x96f28.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x97854.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9790c.
Definition tfib_A_close : Z := 0x99f24.  Definition tfib_E_close : Z := 0x99f78.
Definition tfib_A_musl_read : Z := 0x9a004.  Definition tfib_E_musl_read : Z := 0x9a038.
Definition tfib_A_vm_wait : Z := 0x97564.  Definition tfib_E_vm_wait : Z := 0x975b4.
Definition tfib_D_str_sealed : Z := 0x1183e.
Definition tfib_D_init_array_0_3 : Z := 0x9b038.
Definition tfib_D_fini_array_0_1 : Z := 0x9b058.
Definition tfib_D_GOT_common_flags : Z := 0x9c680.
Definition tfib_D_GOT_flags : Z := 0x9c688.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9c690.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9c698.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9c6a0.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9c6a8.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9d1f8.
Definition tfib_D_REAL_read : Z := 0x9e3c8.
Definition tfib_D_REAL_memcpy : Z := 0x9e4f0.
Definition tfib_D_REAL_memset : Z := 0x9e4f8.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa1c58.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa2ab8.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa52b8.
Definition tfib_D_asan_inited : Z := 0xa5f98.
Definition tfib_D_replace_intrin_cached : Z := 0xa5f99.
Definition tfib_D_kHighMemEnd : Z := 0xa5fa0.
Definition tfib_D_kMidMemBeg : Z := 0xa5fa8.
Definition tfib_D_kMidMemEnd : Z := 0xa5fb0.
Definition tfib_D_malloc_context_size : Z := 0xa5fbc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x136de8.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5fa000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x30a20.
Definition tfib_at_rw_lo : Z := 0x9e000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x63c4c.
Definition tfib_at_x_imemcpy : Z := 0x63bd0.
Definition tfib_at_x_memset : Z := 0x94d04.
Definition tfib_at_x_memcpy : Z := 0x94900.
Definition tfib_at_x_memiszero : Z := 0x6417c.
Definition tfib_at_x_istrncpy : Z := 0x64078.
Definition tfib_at_x_sealed : Z := 0x1183e.
Definition tfib_at_x_popfree : Z := 0x36e0c.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8a704.
Definition tfib_at_x_envscan_k : Z := 0x8a710.
Definition tfib_at_x_pnscan : Z := 0x8a7c8.
Definition tfib_at_x_pnscan_k : Z := 0x8a7d4.
Definition tfib_at_stops_more : list Z := (0x34a80 :: 0x360a4 :: 0x53f58 :: 0x5a310 :: 0x5a324 :: 0x5a338 :: 0x5fcc8 :: 0x5fd98 :: 0x6d2c4 :: 0x6e1d0 :: 0x6e360 :: 0x780b8 :: nil)%list.
