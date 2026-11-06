(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1w.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AB1w.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_role's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AB1w.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From Stdlib Require Import ZArith.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22f0c.
Definition tfib_text_lo : Z := 0x306ac.
Definition tfib_init_array_lo : Z := 0x9a388.  Definition tfib_init_array_hi : Z := 0x9a3a8.
Definition tfib_fini_array_lo : Z := 0x9a3a8.  Definition tfib_fini_array_hi : Z := 0x9a3b8.
Definition tfib_preinit_array_lo : Z := 0x9a3b8.  Definition tfib_preinit_array_hi : Z := 0x9a3c0.
Definition tfib_data_rel_ro_lo : Z := 0x9a3c0.  Definition tfib_data_rel_ro_hi : Z := 0x9aa70.
Definition tfib_got_lo : Z := 0x9aa70.  Definition tfib_got_hi : Z := 0x9b7c8.
Definition tfib_data_lo : Z := 0x9c7c8.  Definition tfib_data_hi : Z := 0x9f378.
Definition tfib_asan_globals_lo : Z := 0x9f380.  Definition tfib_asan_globals_hi : Z := 0x9ffc0.
Definition tfib_bss_lo : Z := 0x9ffc0.  Definition tfib_bss_hi : Z := 0x5f7ef0.
Definition tfib_tbss_lo : Z := 0x99388.  Definition tfib_tbss_hi : Z := 0x9939c.
Definition tfib_img_lo : Z := 0x10000.  Definition tfib_img_hi : Z := 0x5f8000.
Definition tfib_entry : Z := 0x306ac.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x306ac.  Definition tfib_E_start : Z := 0x306f4.
Definition tfib_A_do_init : Z := 0x306f4.  Definition tfib_E_do_init : Z := 0x30768.
Definition tfib_A_do_fini : Z := 0x30768.  Definition tfib_E_do_fini : Z := 0x307f8.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x307f8.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x30834.
Definition tfib_A_InitializeAllocator : Z := 0x309a4.  Definition tfib_E_InitializeAllocator : Z := 0x309bc.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x309bc.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30b28.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x31084.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x311e0.
Definition tfib_A_asan_free : Z := 0x315b4.  Definition tfib_E_asan_free : Z := 0x315dc.
Definition tfib_A_Allocator_Deallocate : Z := 0x315dc.  Definition tfib_E_Allocator_Deallocate : Z := 0x31894.
Definition tfib_A_asan_malloc : Z := 0x31894.  Definition tfib_E_asan_malloc : Z := 0x318f0.
Definition tfib_A_Allocator_Allocate : Z := 0x318f0.  Definition tfib_E_Allocator_Allocate : Z := 0x32278.
Definition tfib_A_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x329b0.  Definition tfib_E_AsanChunkView_GetAsanChunk_ptr_helper : Z := 0x32af4.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32be0.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32c3c.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32c3c.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x32e8c.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32e8c.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32f80.
Definition tfib_A_Allocator_SharedInitCode : Z := 0x32f80.  Definition tfib_E_Allocator_SharedInitCode : Z := 0x33068.
Definition tfib_A_QuarantineCache_MergeBatches_Transfer : Z := 0x3349c.  Definition tfib_E_QuarantineCache_MergeBatches_Transfer : Z := 0x33680.
Definition tfib_A_QuarantineCache_DequeueBatch : Z := 0x33680.  Definition tfib_E_QuarantineCache_DequeueBatch : Z := 0x33804.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x3393c.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33bc0.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33bc0.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x33d40.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33d40.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33f08.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x33f08.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x340d4.
Definition tfib_A_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x340d4.  Definition tfib_E_SizeClassAllocator64_ReturnToAllocator_helper : Z := 0x34174.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x34174.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x34278.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x345a0.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x346e8.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x346e8.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x34720.
Definition tfib_A_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x34eb8.  Definition tfib_E_SizeClassAllocator64_ReleaseFreeMemoryToOS_Packe : Z := 0x351a0.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35878.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x359f0.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x359f0.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x35ba0.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35ba0.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x35d84.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x35d84.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x3605c.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x3605c.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x364d4.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x364d4.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x365d4.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x365d4.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x368dc.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x368dc.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36c4c.
Definition tfib_A_Allocator_ComputeRZLog : Z := 0x36c4c.  Definition tfib_E_Allocator_ComputeRZLog : Z := 0x36d64.
Definition tfib_A_LargeMmapAllocator_EnsureSortedChunks : Z := 0x3706c.  Definition tfib_E_LargeMmapAllocator_EnsureSortedChunks : Z := 0x37168.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x37168.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x37250.
Definition tfib_A_AsanActivate : Z := 0x37250.  Definition tfib_E_AsanActivate : Z := 0x3732c.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x37808.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x378f0.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3c3a8.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3c480.
Definition tfib_A_FakeStack_Create : Z := 0x3c480.  Definition tfib_E_FakeStack_Create : Z := 0x3c56c.
Definition tfib_A_FakeStack_Allocate : Z := 0x3c828.  Definition tfib_E_FakeStack_Allocate : Z := 0x3cb10.
Definition tfib_A_SetTLSFakeStack : Z := 0x3cc44.  Definition tfib_E_SetTLSFakeStack : Z := 0x3cc74.
Definition tfib_A_asan_stack_malloc_4 : Z := 0x3cc74.  Definition tfib_E_asan_stack_malloc_4 : Z := 0x3ce40.

Definition tfib_A_check_absent : Z := 0x82a80.  Definition tfib_E_check_absent : Z := 0x82aac.  Definition tfib_A_check_role : Z := 0x82aac.  Definition tfib_E_check_role : Z := 0x82ad8.  Definition tfib_A_check_malformed : Z := 0x82ad8.  Definition tfib_E_check_malformed : Z := 0x82b08.  Definition tfib_A_check_answer : Z := 0x82b08.  Definition tfib_E_check_answer : Z := 0x82b5c.  Definition tfib_A_check_code : Z := 0x82b5c.  Definition tfib_E_check_code : Z := 0x82bac.  Definition tfib_A_pod_write_ent : Z := 0x82bac.  Definition tfib_E_pod_write_ent : Z := 0x82eb4.  Definition tfib_A_pod_nearest : Z := 0x82eb4.  Definition tfib_E_pod_nearest : Z := 0x83034.  Definition tfib_A_reac_role_refuse_code : Z := 0x8309c.  Definition tfib_E_reac_role_refuse_code : Z := 0x83108.  Definition tfib_A_reac_role_cfg_changes : Z := 0x83108.  Definition tfib_E_reac_role_cfg_changes : Z := 0x83114.  Definition tfib_A_reac_role_cfg_apply_state : Z := 0x83114.  Definition tfib_E_reac_role_cfg_apply_state : Z := 0x83130.  Definition tfib_A_reac_role_prop_parse : Z := 0x83130.  Definition tfib_E_reac_role_prop_parse : Z := 0x836c4.  Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x80020.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x82a80.
Definition tfib_A_asan_InitializeFlags : Z := 0x3cf7c.  Definition tfib_E_asan_InitializeFlags : Z := 0x3dfa8.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3e6b4.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3f4d0.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3f4d0.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x3fa9c.
Definition tfib_A_asan_register_globals : Z := 0x3fa9c.  Definition tfib_E_asan_register_globals : Z := 0x3fb08.
Definition tfib_A_asan_unregister_globals : Z := 0x3fb08.  Definition tfib_E_asan_unregister_globals : Z := 0x3fb70.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x401f0.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x40460.
Definition tfib_A_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x40460.  Definition tfib_E_asan_before_dynamic_init_asan_after_dynamic_init : Z := 0x40768.
Definition tfib_A_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x40edc.  Definition tfib_E_RoundUpTo_size_CHECK_helper_sanitizer_common_h_C : Z := 0x4102c.
Definition tfib_A_asan_globals_RegisterGlobal_vector_push_back : Z := 0x41a48.  Definition tfib_E_asan_globals_RegisterGlobal_vector_push_back : Z := 0x41b60.
Definition tfib_A_strlen : Z := 0x41b60.  Definition tfib_E_strlen : Z := 0x41b64.
Definition tfib_A_strnlen : Z := 0x41b64.  Definition tfib_E_strnlen : Z := 0x41b68.
Definition tfib_A_strcmp : Z := 0x41b68.  Definition tfib_E_strcmp : Z := 0x41b6c.
Definition tfib_A_strchr : Z := 0x41b6c.  Definition tfib_E_strchr : Z := 0x41b70.
Definition tfib_A_memcmp : Z := 0x41b70.  Definition tfib_E_memcmp : Z := 0x41b74.

Definition tfib_A_memchr : Z := 0x41b74.  Definition tfib_E_memchr : Z := 0x41b78.
Definition tfib_A_frexpl : Z := 0x41b78.  Definition tfib_E_frexpl : Z := 0x41b7c.
Definition tfib_A_read : Z := 0x41b7c.  Definition tfib_E_read : Z := 0x41b80.
Definition tfib_A_fwrite : Z := 0x41b80.  Definition tfib_E_fwrite : Z := 0x41b84.
Definition tfib_A_time : Z := 0x41b84.  Definition tfib_E_time : Z := 0x41b88.
Definition tfib_A_gmtime_r : Z := 0x41b88.  Definition tfib_E_gmtime_r : Z := 0x41b8c.
Definition tfib_A_vprintf : Z := 0x41b8c.  Definition tfib_E_vprintf : Z := 0x41b90.
Definition tfib_A_vfprintf : Z := 0x41b90.  Definition tfib_E_vfprintf : Z := 0x41b94.
Definition tfib_A_vsnprintf : Z := 0x41b94.  Definition tfib_E_vsnprintf : Z := 0x41b98.
Definition tfib_A_vfprintf_2 : Z := 0x41b98.  Definition tfib_E_vfprintf_2 : Z := 0x41b9c.
Definition tfib_A_thunk_417bc : Z := 0x41b9c.  Definition tfib_E_thunk_417bc : Z := 0x41ba0.
Definition tfib_A_clock_gettime : Z := 0x41ba0.  Definition tfib_E_clock_gettime : Z := 0x41ba4.
Definition tfib_A_wcrtomb : Z := 0x41ba4.  Definition tfib_E_wcrtomb : Z := 0x41ba8.
Definition tfib_A_wctomb : Z := 0x41ba8.  Definition tfib_E_wctomb : Z := 0x41bac.
Definition tfib_A_thunk_417cc : Z := 0x41bac.  Definition tfib_E_thunk_417cc : Z := 0x41bb4.
Definition tfib_A_pthread_attr_getstack : Z := 0x41bb4.  Definition tfib_E_pthread_attr_getstack : Z := 0x41bb8.
Definition tfib_A_tls_get_addr_thunk : Z := 0x41bb8.  Definition tfib_E_tls_get_addr_thunk : Z := 0x41bbc.

Definition tfib_A_thunk_417dc : Z := 0x41bbc.  Definition tfib_E_thunk_417dc : Z := 0x41bc0.

Definition tfib_A_thunk_417e4 : Z := 0x41bc0.  Definition tfib_E_thunk_417e4 : Z := 0x41bc4.
Definition tfib_A_thunk_417e8 : Z := 0x41bc4.  Definition tfib_E_thunk_417e8 : Z := 0x41bc8.
Definition tfib_A_thunk_417ec : Z := 0x41bc8.  Definition tfib_E_thunk_417ec : Z := 0x41bcc.
Definition tfib_A_thunk_417f0 : Z := 0x41bcc.  Definition tfib_E_thunk_417f0 : Z := 0x41bd0.
Definition tfib_A_sem_timedwait : Z := 0x41bd0.  Definition tfib_E_sem_timedwait : Z := 0x41bd4.
Definition tfib_A_thunk_417f8 : Z := 0x41bd4.  Definition tfib_E_thunk_417f8 : Z := 0x41bd8.
Definition tfib_A_pthread_setcancelstate : Z := 0x41bd8.  Definition tfib_E_pthread_setcancelstate : Z := 0x41bdc.
Definition tfib_A_send : Z := 0x41bdc.  Definition tfib_E_send : Z := 0x41be0.
Definition tfib_A_sendto : Z := 0x41be0.  Definition tfib_E_sendto : Z := 0x41be4.
Definition tfib_A_sigaltstack : Z := 0x41be4.  Definition tfib_E_sigaltstack : Z := 0x41be8.
Definition tfib_A_thunk_4180c : Z := 0x41be8.  Definition tfib_E_thunk_4180c : Z := 0x41bec.
Definition tfib_A_icpt_strlen : Z := 0x41bec.  Definition tfib_E_icpt_strlen : Z := 0x41e80.
Definition tfib_A_icpt_strnlen : Z := 0x41e80.  Definition tfib_E_icpt_strnlen : Z := 0x42114.
Definition tfib_A_icpt_strcmp : Z := 0x42118.  Definition tfib_E_icpt_strcmp : Z := 0x42648.
Definition tfib_A_icpt_strchr : Z := 0x42648.  Definition tfib_E_icpt_strchr : Z := 0x42928.
Definition tfib_A_icpt_memcmp : Z := 0x431c0.  Definition tfib_E_icpt_memcmp : Z := 0x4327c.

Definition tfib_A_icpt_memchr : Z := 0x4327c.  Definition tfib_E_icpt_memchr : Z := 0x4354c.
Definition tfib_A_icpt_frexpl : Z := 0x4354c.  Definition tfib_E_icpt_frexpl : Z := 0x437c4.
Definition tfib_A_icpt_read : Z := 0x437c4.  Definition tfib_E_icpt_read : Z := 0x43a34.
Definition tfib_A_icpt_fwrite : Z := 0x43a34.  Definition tfib_E_icpt_fwrite : Z := 0x43ca8.
Definition tfib_A_icpt_time : Z := 0x43ca8.  Definition tfib_E_icpt_time : Z := 0x43f44.
Definition tfib_A_icpt_gmtime_r : Z := 0x4414c.  Definition tfib_E_icpt_gmtime_r : Z := 0x4438c.
Definition tfib_A_icpt_vprintf : Z := 0x4438c.  Definition tfib_E_icpt_vprintf : Z := 0x44428.
Definition tfib_A_printf_common_format_interceptor : Z := 0x44428.  Definition tfib_E_printf_common_format_interceptor : Z := 0x44ef0.
Definition tfib_A_icpt_vfprintf : Z := 0x44ef0.  Definition tfib_E_icpt_vfprintf : Z := 0x44fa4.
Definition tfib_A_icpt_vsnprintf : Z := 0x44fa4.  Definition tfib_E_icpt_vsnprintf : Z := 0x452bc.
Definition tfib_A_icpt_vfprintf_2 : Z := 0x452bc.  Definition tfib_E_icpt_vfprintf_2 : Z := 0x45394.
Definition tfib_A_icpt_clock_gettime : Z := 0x45438.  Definition tfib_E_icpt_clock_gettime : Z := 0x45690.
Definition tfib_A_icpt_wcrtomb : Z := 0x45690.  Definition tfib_E_icpt_wcrtomb : Z := 0x45c00.
Definition tfib_A_icpt_wctomb : Z := 0x45c00.  Definition tfib_E_icpt_wctomb : Z := 0x45f5c.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x46028.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x46410.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x4641c.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x46498.


Definition tfib_A_icpt_sem_timedwait : Z := 0x466a4.  Definition tfib_E_icpt_sem_timedwait : Z := 0x4693c.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x4696c.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x46b94.
Definition tfib_A_icpt_send : Z := 0x46b94.  Definition tfib_E_icpt_send : Z := 0x46e48.
Definition tfib_A_icpt_sendto : Z := 0x46e48.  Definition tfib_E_icpt_sendto : Z := 0x4710c.
Definition tfib_A_icpt_sigaltstack : Z := 0x4710c.  Definition tfib_E_icpt_sigaltstack : Z := 0x47368.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x4743c.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x475ec.
Definition tfib_A_icpt_diouxXn : Z := 0x475ec.  Definition tfib_E_icpt_diouxXn : Z := 0x47784.
Definition tfib_A_InitializeCommonInterceptors : Z := 0x48330.  Definition tfib_E_InitializeCommonInterceptors : Z := 0x51008.
Definition tfib_A_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x51008.  Definition tfib_E_InitializeSignalInterceptors_or_syscall_hooks : Z := 0x51164.
Definition tfib_A_memset : Z := 0x51164.  Definition tfib_E_memset : Z := 0x51168.
Definition tfib_A_memcpy : Z := 0x51168.  Definition tfib_E_memcpy : Z := 0x5116c.
Definition tfib_A_asan_memcpy : Z := 0x5116c.  Definition tfib_E_asan_memcpy : Z := 0x51608.
Definition tfib_A_asan_memset : Z := 0x51608.  Definition tfib_E_asan_memset : Z := 0x51848.
Definition tfib_A_icpt_memset : Z := 0x51848.  Definition tfib_E_icpt_memset : Z := 0x51b38.
Definition tfib_A_icpt_memcpy : Z := 0x51b38.  Definition tfib_E_icpt_memcpy : Z := 0x52128.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52128.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x52160.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x52160.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x52164.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x52164.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x52168.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x52168.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x521c8.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52214.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x52350.
Definition tfib_A_AsanCheckIncompatibleRT : Z := 0x52350.  Definition tfib_E_AsanCheckIncompatibleRT : Z := 0x52354.
Definition tfib_A_AsanCheckDynamicRTPrereqs : Z := 0x52354.  Definition tfib_E_AsanCheckDynamicRTPrereqs : Z := 0x524bc.
Definition tfib_A_free : Z := 0x524bc.  Definition tfib_E_free : Z := 0x524c0.
Definition tfib_A_malloc : Z := 0x524c0.  Definition tfib_E_malloc : Z := 0x524c4.
Definition tfib_A_icpt_free : Z := 0x524c4.  Definition tfib_E_icpt_free : Z := 0x52694.
Definition tfib_A_icpt_malloc : Z := 0x52694.  Definition tfib_E_icpt_malloc : Z := 0x527f0.
Definition tfib_A_icpt_cfree_or_DlsymFree : Z := 0x527f0.  Definition tfib_E_icpt_cfree_or_DlsymFree : Z := 0x528bc.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x528bc.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x528c0.
Definition tfib_A_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x528c0.  Definition tfib_E_DlsymAlloc_PointerIsMine_internal_allocator_From : Z := 0x529c0.
Definition tfib_A_HeapProfile_Insert_asan_memory_profile : Z := 0x52ce8.  Definition tfib_E_HeapProfile_Insert_asan_memory_profile : Z := 0x52e54.
Definition tfib_A_SetCanPoisonMemory : Z := 0x5333c.  Definition tfib_E_SetCanPoisonMemory : Z := 0x5334c.
Definition tfib_A_CanPoisonMemory : Z := 0x5334c.  Definition tfib_E_CanPoisonMemory : Z := 0x53360.
Definition tfib_A_PoisonShadow : Z := 0x53360.  Definition tfib_E_PoisonShadow : Z := 0x5385c.
Definition tfib_A_MemToShadow_checked : Z := 0x5385c.  Definition tfib_E_MemToShadow_checked : Z := 0x53998.
Definition tfib_A_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x53998.  Definition tfib_E_asan_poison_stack_memory_PoisonAlignedStackMemor : Z := 0x53b38.
Definition tfib_A_asan_unpoison_stack_memory : Z := 0x53b38.  Definition tfib_E_asan_unpoison_stack_memory : Z := 0x53cb8.
Definition tfib_A_asan_region_is_poisoned : Z := 0x53ce8.  Definition tfib_E_asan_region_is_poisoned : Z := 0x5402c.
Definition tfib_A_AsanTSDInit : Z := 0x5444c.  Definition tfib_E_AsanTSDInit : Z := 0x544c8.
Definition tfib_A_AsanTSDGet : Z := 0x544c8.  Definition tfib_E_AsanTSDGet : Z := 0x54508.
Definition tfib_A_AsanTSDSet : Z := 0x54508.  Definition tfib_E_AsanTSDSet : Z := 0x54548.
Definition tfib_A_PlatformTSDDtor : Z := 0x54548.  Definition tfib_E_PlatformTSDDtor : Z := 0x545cc.
Definition tfib_A_InstallAtForkHandler : Z := 0x545cc.  Definition tfib_E_InstallAtForkHandler : Z := 0x545e8.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54648.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x5468c.
Definition tfib_A_ScopedInErrorReport_ReportError_helper : Z := 0x54da4.  Definition tfib_E_ScopedInErrorReport_ReportError_helper : Z := 0x54fb0.
Definition tfib_A_ReportDoubleFree : Z := 0x556b8.  Definition tfib_E_ReportDoubleFree : Z := 0x55948.
Definition tfib_A_ReportGenericError : Z := 0x57224.  Definition tfib_E_ReportGenericError : Z := 0x57ae0.
Definition tfib_A_AsanInited : Z := 0x5826c.  Definition tfib_E_AsanInited : Z := 0x58284.
Definition tfib_A_asan_report_load1 : Z := 0x58284.  Definition tfib_E_asan_report_load1 : Z := 0x582d4.
Definition tfib_A_asan_report_exp_load1 : Z := 0x582d4.  Definition tfib_E_asan_report_exp_load1 : Z := 0x58324.
Definition tfib_A_asan_report_load2 : Z := 0x58324.  Definition tfib_E_asan_report_load2 : Z := 0x58374.
Definition tfib_A_asan_report_exp_load2 : Z := 0x58374.  Definition tfib_E_asan_report_exp_load2 : Z := 0x583c4.
Definition tfib_A_asan_report_load4 : Z := 0x583c4.  Definition tfib_E_asan_report_load4 : Z := 0x58414.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58414.  Definition tfib_E_asan_report_exp_load4 : Z := 0x58464.
Definition tfib_A_asan_report_load8 : Z := 0x58464.  Definition tfib_E_asan_report_load8 : Z := 0x584b4.
Definition tfib_A_asan_report_exp_load8 : Z := 0x584b4.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58504.
Definition tfib_A_asan_report_load16 : Z := 0x58504.  Definition tfib_E_asan_report_load16 : Z := 0x58554.
Definition tfib_A_asan_report_exp_load16 : Z := 0x58554.  Definition tfib_E_asan_report_exp_load16 : Z := 0x585a4.
Definition tfib_A_asan_report_store1 : Z := 0x585a4.  Definition tfib_E_asan_report_store1 : Z := 0x585f4.
Definition tfib_A_asan_report_exp_store1 : Z := 0x585f4.  Definition tfib_E_asan_report_exp_store1 : Z := 0x58644.
Definition tfib_A_asan_report_store2 : Z := 0x58644.  Definition tfib_E_asan_report_store2 : Z := 0x58694.
Definition tfib_A_asan_report_exp_store2 : Z := 0x58694.  Definition tfib_E_asan_report_exp_store2 : Z := 0x586e4.
Definition tfib_A_asan_report_store4 : Z := 0x586e4.  Definition tfib_E_asan_report_store4 : Z := 0x58734.
Definition tfib_A_asan_report_exp_store4 : Z := 0x58734.  Definition tfib_E_asan_report_exp_store4 : Z := 0x58784.
Definition tfib_A_asan_report_store8 : Z := 0x58784.  Definition tfib_E_asan_report_store8 : Z := 0x587d4.
Definition tfib_A_asan_report_exp_store8 : Z := 0x587d4.  Definition tfib_E_asan_report_exp_store8 : Z := 0x58824.
Definition tfib_A_asan_report_store16 : Z := 0x58824.  Definition tfib_E_asan_report_store16 : Z := 0x58874.
Definition tfib_A_asan_report_exp_store16 : Z := 0x58874.  Definition tfib_E_asan_report_exp_store16 : Z := 0x588c4.
Definition tfib_A_asan_report_load_n : Z := 0x588c4.  Definition tfib_E_asan_report_load_n : Z := 0x58914.
Definition tfib_A_asan_report_exp_load_n : Z := 0x58914.  Definition tfib_E_asan_report_exp_load_n : Z := 0x58964.
Definition tfib_A_asan_report_store_n : Z := 0x58964.  Definition tfib_E_asan_report_store_n : Z := 0x589b4.
Definition tfib_A_asan_report_exp_store_n : Z := 0x589b4.  Definition tfib_E_asan_report_exp_store_n : Z := 0x58a04.
Definition tfib_A_InitializeHighMemEnd : Z := 0x58a04.  Definition tfib_E_InitializeHighMemEnd : Z := 0x58a84.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x58a84.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x58e38.
Definition tfib_A_AsanInitInternal : Z := 0x58ec8.  Definition tfib_E_AsanInitInternal : Z := 0x5917c.
Definition tfib_A_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5917c.  Definition tfib_E_AsanInitFromRtl_ENSURE_ASAN_INITED : Z := 0x5921c.
Definition tfib_A_thunk_59674 : Z := 0x593e4.  Definition tfib_E_thunk_59674 : Z := 0x593e8.
Definition tfib_A_asan_init : Z := 0x593e8.  Definition tfib_E_asan_init : Z := 0x5947c.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5947c.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x59480.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x59480.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x594e4.
Definition tfib_A_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x59658.  Definition tfib_E_asan_handle_no_return_tiny_rtl_stub_2_insns : Z := 0x59660.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x596e4.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x59a0c.
Definition tfib_A_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x59a0c.  Definition tfib_E_ReserveShadowMemoryRanges_sealed_early_shadow_re : Z := 0x59bec.
Definition tfib_A_InitializeShadowMemory : Z := 0x59bec.  Definition tfib_E_InitializeShadowMemory : Z := 0x59ef4.
Definition tfib_A_SetMallocContextSize : Z := 0x59ef4.  Definition tfib_E_SetMallocContextSize : Z := 0x59f04.
Definition tfib_A_GetMallocContextSize : Z := 0x59f04.  Definition tfib_E_GetMallocContextSize : Z := 0x59f14.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x59f14.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5a064.
Definition tfib_A_AsanStats_Clear_ctor : Z := 0x5a444.  Definition tfib_E_AsanStats_Clear_ctor : Z := 0x5a6e4.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5ab48.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5ab80.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5ae28.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5ae34.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5ae34.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5aec0.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5aec0.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5af28.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5af28.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5afa0.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5afa0.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5b008.
Definition tfib_A_IsStackTraceSuppressed : Z := 0x5b008.  Definition tfib_E_IsStackTraceSuppressed : Z := 0x5b154.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5b3e0.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5b3ec.
Definition tfib_A_AsanThread_Create : Z := 0x5b56c.  Definition tfib_E_AsanThread_Create : Z := 0x5b708.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5b764.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5b97c.
Definition tfib_A_GetCurrentThread : Z := 0x5b97c.  Definition tfib_E_GetCurrentThread : Z := 0x5b99c.
Definition tfib_A_AsanThread_SetThreadStackAndTls : Z := 0x5b99c.  Definition tfib_E_AsanThread_SetThreadStackAndTls : Z := 0x5bb40.
Definition tfib_A_AsanThread_stack_top : Z := 0x5bb40.  Definition tfib_E_AsanThread_stack_top : Z := 0x5bb98.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5bb98.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5bbf0.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5bbf0.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5be20.
Definition tfib_A_AsanThread_Init : Z := 0x5be20.  Definition tfib_E_AsanThread_Init : Z := 0x5c214.
Definition tfib_A_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c214.  Definition tfib_E_AsanThread_ClearShadowForThreadStackAndTLS : Z := 0x5c320.
Definition tfib_A_CreateMainThread : Z := 0x5c354.  Definition tfib_E_CreateMainThread : Z := 0x5c464.
Definition tfib_A_SetCurrentThread : Z := 0x5c464.  Definition tfib_E_SetCurrentThread : Z := 0x5c544.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5c748.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5c884.
Definition tfib_A_weak_default_hook_ret : Z := 0x5d558.  Definition tfib_E_weak_default_hook_ret : Z := 0x5d55c.
Definition tfib_A_InternalAlloc_RawInternalAlloc : Z := 0x5d564.  Definition tfib_E_InternalAlloc_RawInternalAlloc : Z := 0x5d7a4.
Definition tfib_A_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5d9f8.  Definition tfib_E_InternalFree_LowLevelAllocator_free_to_freelist : Z := 0x5db50.
Definition tfib_A_internal_allocator_getter : Z := 0x5dd3c.  Definition tfib_E_internal_allocator_getter : Z := 0x5dd48.
Definition tfib_A_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5dd48.  Definition tfib_E_LowLevelAllocator_InternalAlloc_bump_allocator : Z := 0x5de94.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5de94.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5dee0.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5dee0.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5deec.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5df1c.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5df28.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5df28.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5df34.
Definition tfib_A_AllocatorMayReturnNull : Z := 0x5df34.  Definition tfib_E_AllocatorMayReturnNull : Z := 0x5df44.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5df50.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5e21c.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e21c.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5e5dc.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x5f538.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x5f544.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5f544.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5f61c.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5f61c.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5f6b8.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fbdc.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fc20.
Definition tfib_A_IncreaseTotalMmap : Z := 0x5fc20.  Definition tfib_E_IncreaseTotalMmap : Z := 0x5fc44.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x5fe98.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x5ffac.
Definition tfib_A_RunMallocHooks : Z := 0x60150.  Definition tfib_E_RunMallocHooks : Z := 0x60208.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x60208.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x6020c.
Definition tfib_A_RunFreeHooks : Z := 0x6020c.  Definition tfib_E_RunFreeHooks : Z := 0x602b8.
Definition tfib_A_sanitizer_free_hook_weak_default : Z := 0x602b8.  Definition tfib_E_sanitizer_free_hook_weak_default : Z := 0x602c0.
Definition tfib_A_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x602c0.  Definition tfib_E_sanitizer_ignore_free_hook_weak_default_ret_0 : Z := 0x602c4.
Definition tfib_A_SleepForSeconds_WaitForDebugger : Z := 0x602ec.  Definition tfib_E_SleepForSeconds_WaitForDebugger : Z := 0x60338.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x605fc.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x6083c.
Definition tfib_A_sanitizer_set_report_path : Z := 0x60e38.  Definition tfib_E_sanitizer_set_report_path : Z := 0x60e50.
Definition tfib_A_ReportFile_SetReportPath : Z := 0x60e50.  Definition tfib_E_ReportFile_SetReportPath : Z := 0x60f94.
Definition tfib_A_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x60f94.  Definition tfib_E_OverrideCommonFlags_no_op_flag_hook_2_insns : Z := 0x60f9c.
Definition tfib_A_FlagParser_ParseString_parse_flags : Z := 0x612e4.  Definition tfib_E_FlagParser_ParseString_parse_flags : Z := 0x62588.
Definition tfib_A_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x62588.  Definition tfib_E_FlagParser_PrintFlagDescriptions_gate_Verbosity : Z := 0x625ac.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x62a60.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x62d70.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x62d70.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x62eb4.
Definition tfib_A_FlagParser_ParseString : Z := 0x62eb4.  Definition tfib_E_FlagParser_ParseString : Z := 0x62fa8.
Definition tfib_A_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x6313c.  Definition tfib_E_RegisterFlag_T_FlagParser_RegisterHandler : Z := 0x6319c.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x6319c.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x631dc.
Definition tfib_A_internal_atoll : Z := 0x631dc.  Definition tfib_E_internal_atoll : Z := 0x632c8.
Definition tfib_A_internal_simple_strtoll : Z := 0x632c8.  Definition tfib_E_internal_simple_strtoll : Z := 0x63424.
Definition tfib_A_internal_memchr : Z := 0x63424.  Definition tfib_E_internal_memchr : Z := 0x63444.
Definition tfib_A_internal_memcmp : Z := 0x63444.  Definition tfib_E_internal_memcmp : Z := 0x6347c.
Definition tfib_A_internal_memcpy : Z := 0x6347c.  Definition tfib_E_internal_memcpy : Z := 0x634a0.
Definition tfib_A_internal_memmove : Z := 0x634a0.  Definition tfib_E_internal_memmove : Z := 0x634f8.
Definition tfib_A_internal_memset : Z := 0x634f8.  Definition tfib_E_internal_memset : Z := 0x63558.
Definition tfib_A_internal_strcspn : Z := 0x63558.  Definition tfib_E_internal_strcspn : Z := 0x635ac.
Definition tfib_A_internal_strcmp : Z := 0x635ac.  Definition tfib_E_internal_strcmp : Z := 0x635e0.
Definition tfib_A_internal_strdup : Z := 0x635e0.  Definition tfib_E_internal_strdup : Z := 0x6364c.
Definition tfib_A_internal_strlen : Z := 0x6364c.  Definition tfib_E_internal_strlen : Z := 0x63668.
Definition tfib_A_internal_strncmp : Z := 0x63668.  Definition tfib_E_internal_strncmp : Z := 0x636ac.
Definition tfib_A_internal_strchr : Z := 0x636ac.  Definition tfib_E_internal_strchr : Z := 0x636f8.
Definition tfib_A_internal_strchrnul : Z := 0x636f8.  Definition tfib_E_internal_strchrnul : Z := 0x63740.
Definition tfib_A_internal_strrchr : Z := 0x63740.  Definition tfib_E_internal_strrchr : Z := 0x63780.
Definition tfib_A_internal_strnlen : Z := 0x638b0.  Definition tfib_E_internal_strnlen : Z := 0x638e0.
Definition tfib_A_internal_strncpy : Z := 0x63924.  Definition tfib_E_internal_strncpy : Z := 0x63994.
Definition tfib_A_internal_strstr : Z := 0x63994.  Definition tfib_E_internal_strstr : Z := 0x63a28.
Definition tfib_A_mem_is_zero : Z := 0x63a28.  Definition tfib_E_mem_is_zero : Z := 0x63adc.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63adc.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63aec.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63aec.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63ccc.
Definition tfib_A_internal_iserror : Z := 0x63cd8.  Definition tfib_E_internal_iserror : Z := 0x63cf8.
Definition tfib_A_internal_mmap : Z := 0x63cf8.  Definition tfib_E_internal_mmap : Z := 0x63d04.
Definition tfib_A_internal_munmap : Z := 0x63d04.  Definition tfib_E_internal_munmap : Z := 0x63d10.
Definition tfib_A_internal_mprotect : Z := 0x63d10.  Definition tfib_E_internal_mprotect : Z := 0x63d20.
Definition tfib_A_internal_madvise : Z := 0x63d20.  Definition tfib_E_internal_madvise : Z := 0x63d4c.
Definition tfib_A_internal_close : Z := 0x63d4c.  Definition tfib_E_internal_close : Z := 0x63d58.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x63d58.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x63d7c.
Definition tfib_A_internal_read : Z := 0x63d7c.  Definition tfib_E_internal_read : Z := 0x63db4.
Definition tfib_A_internal_write : Z := 0x63db4.  Definition tfib_E_internal_write : Z := 0x63dec.
Definition tfib_A_internal_ftruncate : Z := 0x63dec.  Definition tfib_E_internal_ftruncate : Z := 0x63e24.
Definition tfib_A_internal_dup : Z := 0x63e24.  Definition tfib_E_internal_dup : Z := 0x63e30.
Definition tfib_A_internal_dup2_dup3 : Z := 0x63e30.  Definition tfib_E_internal_dup2_dup3 : Z := 0x63e40.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x63e40.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x63e58.
Definition tfib_A_internal_sched_yield : Z := 0x63e58.  Definition tfib_E_internal_sched_yield : Z := 0x63e64.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x63e64.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x63eb0.
Definition tfib_A_internal_execve : Z := 0x63eb0.  Definition tfib_E_internal_execve : Z := 0x63ebc.
Definition tfib_A_internal_exit_exit_group : Z := 0x63ebc.  Definition tfib_E_internal_exit_exit_group : Z := 0x63ed0.
Definition tfib_A_FileExists_newfstatat : Z := 0x63ed0.  Definition tfib_E_FileExists_newfstatat : Z := 0x63f50.
Definition tfib_A_DirExists_newfstatat : Z := 0x63f50.  Definition tfib_E_DirExists_newfstatat : Z := 0x63fb4.
Definition tfib_A_GetTid_gettid : Z := 0x63fb4.  Definition tfib_E_GetTid_gettid : Z := 0x63fc0.
Definition tfib_A_GetEnv : Z := 0x63fc0.  Definition tfib_E_GetEnv : Z := 0x640f0.
Definition tfib_A_FutexWait : Z := 0x641f4.  Definition tfib_E_FutexWait : Z := 0x64218.
Definition tfib_A_FutexWake : Z := 0x64218.  Definition tfib_E_FutexWake : Z := 0x6423c.
Definition tfib_A_internal_ptrace : Z := 0x6423c.  Definition tfib_E_internal_ptrace : Z := 0x64248.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x64248.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x64258.
Definition tfib_A_internal_getpid : Z := 0x64258.  Definition tfib_E_internal_getpid : Z := 0x64264.
Definition tfib_A_internal_getppid : Z := 0x64264.  Definition tfib_E_internal_getppid : Z := 0x64270.
Definition tfib_A_internal_prctl : Z := 0x64270.  Definition tfib_E_internal_prctl : Z := 0x6427c.
Definition tfib_A_internal_sigaltstack : Z := 0x6427c.  Definition tfib_E_internal_sigaltstack : Z := 0x64288.
Definition tfib_A_internal_fork_clone : Z := 0x64288.  Definition tfib_E_internal_fork_clone : Z := 0x642a0.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x642a0.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x643cc.
Definition tfib_A_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x645a4.  Definition tfib_E_GetNamedMappingFd_ReadProcess_openat_getdents64 : Z := 0x649a0.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64b0c.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64c24.
Definition tfib_A_GetPageSizeCached : Z := 0x64c24.  Definition tfib_E_GetPageSizeCached : Z := 0x64c2c.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64c2c.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64cd8.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x64cd8.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x64df8.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x64ec0.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x64f40.
Definition tfib_A_internal_sigaction_syscall_wrapper_selector : Z := 0x64f40.  Definition tfib_E_internal_sigaction_syscall_wrapper_selector : Z := 0x64f9c.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64f9c.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x65068.
Definition tfib_A_thunk_653ec : Z := 0x65164.  Definition tfib_E_thunk_653ec : Z := 0x65168.
Definition tfib_A_CheckASLR : Z := 0x65168.  Definition tfib_E_CheckASLR : Z := 0x6516c.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x653b8.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x653bc.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x653bc.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x653c8.
Definition tfib_A_MmapOrDie : Z := 0x653c8.  Definition tfib_E_MmapOrDie : Z := 0x654d4.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x654d4.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x65548.
Definition tfib_A_UnmapOrDie : Z := 0x65548.  Definition tfib_E_UnmapOrDie : Z := 0x655c4.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x655c4.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x656d4.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x65900.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x65a04.
Definition tfib_A_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x65a04.  Definition tfib_E_MmapFixedNoAccess_3_insn_arg_shim_0x65c98 : Z := 0x65a10.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x65a10.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x65b88.
Definition tfib_A_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x65b88.  Definition tfib_E_MmapFixedSuperNoReserve_3_insn_shim_MmapFixed_co : Z := 0x65b94.
Definition tfib_A_thunk_66008 : Z := 0x65d80.  Definition tfib_E_thunk_66008 : Z := 0x65d84.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x660a4.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x662b0.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x66868.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x66874.
Definition tfib_A_Printf : Z := 0x66878.  Definition tfib_E_Printf : Z := 0x668c4.
Definition tfib_A_SharedPrintfCode : Z := 0x668c4.  Definition tfib_E_SharedPrintfCode : Z := 0x66920.
Definition tfib_A_Report : Z := 0x66920.  Definition tfib_E_Report : Z := 0x6696c.
Definition tfib_A_SuppressionContext_ctor : Z := 0x68464.  Definition tfib_E_SuppressionContext_ctor : Z := 0x684c0.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x684c0.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x686fc.
Definition tfib_A_SuppressionContext_Parse : Z := 0x686fc.  Definition tfib_E_SuppressionContext_Parse : Z := 0x68a20.
Definition tfib_A_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x68fc0.  Definition tfib_E_GetSizeFromHdr_sanitizer_get_dtls_size_DTLS_prob : Z := 0x69090.
Definition tfib_A_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x69090.  Definition tfib_E_sanitizer_GetTls_DTLS_helper_sanitizer_tls_get_a : Z := 0x693e0.
Definition tfib_A_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x693e0.  Definition tfib_E_DTLS_Destroy_ForEachDVT_no_op_4_insns : Z := 0x693f0.
Definition tfib_A_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x6962c.  Definition tfib_E_InternalAllocatorLock_Unlock_or_stats_add_17_ins : Z := 0x69670.
Definition tfib_A_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x69670.  Definition tfib_E_ThreadContextBase_ctor_ThreadRegistry_init_helpe : Z := 0x696d0.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x696d0.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x69b48.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6a408.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6a72c.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6a734.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6a838.
Definition tfib_A_AddDieCallback : Z := 0x6afe8.  Definition tfib_E_AddDieCallback : Z := 0x6b070.
Definition tfib_A_Die : Z := 0x6b134.  Definition tfib_E_Die : Z := 0x6b1f4.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b1f4.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b200.
Definition tfib_A_CheckFailed : Z := 0x6b200.  Definition tfib_E_CheckFailed : Z := 0x6b2b8.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6b910.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6ba08.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6ba08.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6bb34.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6bd5c.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6bdd8.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6be0c.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c0f4.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x6c0f4.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x6c0f8.
Definition tfib_A_GetThreadStackAndTls : Z := 0x6c0f8.  Definition tfib_E_GetThreadStackAndTls : Z := 0x6c4e8.
Definition tfib_A_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6c4e8.  Definition tfib_E_GetThreadStackTopAndBottom_caller_ClearShadowFor : Z := 0x6c5b8.
Definition tfib_A_AndroidLogInit : Z := 0x6c99c.  Definition tfib_E_AndroidLogInit : Z := 0x6c9a0.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6c9d0.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6ca18.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6ca18.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6cc64.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x6cc64.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x6cc68.
Definition tfib_A_InternalMmapVector_push_back : Z := 0x6cc68.  Definition tfib_E_InternalMmapVector_push_back : Z := 0x6cd74.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6cd74.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6ce78.
Definition tfib_A_thunk_6d37c : Z := 0x6d0f4.  Definition tfib_E_thunk_6d37c : Z := 0x6d0f8.
Definition tfib_A_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6d19c.  Definition tfib_E_SetShadowRegionHugePageMode_DontDumpShadow_madvi : Z := 0x6d1bc.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d1bc.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d25c.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x6d2a8.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x6d2ac.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6d2e8.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6d3ac.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6d3ac.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6d434.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6d434.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6d4ac.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6d4ac.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6d590.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6d64c.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6d780.
Definition tfib_A_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6d9b8.  Definition tfib_E_MmapFixedImpl_MmapFixedOrDie_MmapFixedNoReserve : Z := 0x6dae8.
Definition tfib_A_MmapFixedNoReserve : Z := 0x6dae8.  Definition tfib_E_MmapFixedNoReserve : Z := 0x6db48.
Definition tfib_A_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6db48.  Definition tfib_E_MmapNoAccess_ReservedAddressRange_Init : Z := 0x6dc14.
Definition tfib_A_MprotectNoAccess : Z := 0x6dc28.  Definition tfib_E_MprotectNoAccess : Z := 0x6dc48.
Definition tfib_A_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6dc48.  Definition tfib_E_MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser : Z := 0x6dd94.
Definition tfib_A_MmapFixedOrDie : Z := 0x6dd94.  Definition tfib_E_MmapFixedOrDie : Z := 0x6dda4.
Definition tfib_A_MaybeStartBackgroudThread : Z := 0x6f59c.  Definition tfib_E_MaybeStartBackgroudThread : Z := 0x6f5e0.
Definition tfib_A_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x6f5e0.  Definition tfib_E_Atexit_internal_exit_hook_runner_12_insns_execut : Z := 0x6f610.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x6fa44.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x6fb68.
Definition tfib_A_StackStore_Alloc : Z := 0x6fb68.  Definition tfib_E_StackStore_Alloc : Z := 0x6fc9c.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x70550.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x70604.

Definition tfib_A_StackDepotPut : Z := 0x72040.  Definition tfib_E_StackDepotPut : Z := 0x72060.
Definition tfib_A_StackDepotBase_Put : Z := 0x72060.  Definition tfib_E_StackDepotBase_Put : Z := 0x722e4.
Definition tfib_A_StackDepotBase_Get : Z := 0x722e4.  Definition tfib_E_StackDepotBase_Get : Z := 0x723f4.
Definition tfib_A_StackDepotBase_find_bucket_chain_walk : Z := 0x727d4.  Definition tfib_E_StackDepotBase_find_bucket_chain_walk : Z := 0x72864.
Definition tfib_A_StackDepotBase_lock_bucket_spin_lock : Z := 0x72864.  Definition tfib_E_StackDepotBase_lock_bucket_spin_lock : Z := 0x72964.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x729c4.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x729cc.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x729cc.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x72b2c.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x72b2c.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x72ba0.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73028.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73140.
Definition tfib_A_thunk_762d8 : Z := 0x7618c.  Definition tfib_E_thunk_762d8 : Z := 0x76190.
Definition tfib_A_thunk_77ab0 : Z := 0x77964.  Definition tfib_E_thunk_77ab0 : Z := 0x77968.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x79390.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7944c.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7944c.  Definition tfib_E_Unwind_Trace_callback : Z := 0x79524.
Definition tfib_A_Unwind_GetIP_slow_unwind_helper : Z := 0x79524.  Definition tfib_E_Unwind_GetIP_slow_unwind_helper : Z := 0x79798.
Definition tfib_A_lsan_flags_init_helper : Z := 0x79ac4.  Definition tfib_E_lsan_flags_init_helper : Z := 0x79b08.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79b08.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79ed8.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a1a8.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a260.
Definition tfib_A_thunk_7b6f8 : Z := 0x7b5b8.  Definition tfib_E_thunk_7b6f8 : Z := 0x7b5bc.
Definition tfib_A_lsan_register_root_region : Z := 0x7c1c4.  Definition tfib_E_lsan_register_root_region : Z := 0x7c4f4.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7c4f4.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7c97c.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7c97c.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7c988.
Definition tfib_A_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x7f540.  Definition tfib_E_asan_malloc_hook_RunMallocHooks_target_sanitizer : Z := 0x7f558.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7f8dc.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7f958.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7f958.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x7fa08.
Definition tfib_A_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x7fa08.  Definition tfib_E_ubsan_MaybeCallUbsanDefaultOptions : Z := 0x7fa20.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7fa20.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7fb68.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x7fb68.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x7fb74.
Definition tfib_A_asan_default_options_cli_c : Z := 0x7fb74.  Definition tfib_E_asan_default_options_cli_c : Z := 0x7fb80.
Definition tfib_A_main : Z := 0x7fb80.  Definition tfib_E_main : Z := 0x7fe44.
Definition tfib_A_target_alloc_init : Z := 0x7fe44.  Definition tfib_E_target_alloc_init : Z := 0x7fe48.
Definition tfib_A_target_alloc_count : Z := 0x7fe48.  Definition tfib_E_target_alloc_count : Z := 0x7fe50.
Definition tfib_A_target_run : Z := 0x7fe50.  Definition tfib_E_target_run : Z := 0x7ffd8.
Definition tfib_A_emit_printf : Z := 0x7ffd8.  Definition tfib_E_emit_printf : Z := 0x80020.


Definition tfib_A_asan_module_ctor : Z := 0x83034.  Definition tfib_E_asan_module_ctor : Z := 0x8306c.








Definition tfib_A_asan_module_dtor : Z := 0x8306c.  Definition tfib_E_asan_module_dtor : Z := 0x8309c.






Definition tfib_A_extenddftf2 : Z := 0x83858.  Definition tfib_E_extenddftf2 : Z := 0x839e8.
Definition tfib_A_sysconf : Z := 0x8a0d0.  Definition tfib_E_sysconf : Z := 0x8a2f8.
Definition tfib_A_init : Z := 0x8a2f8.  Definition tfib_E_init : Z := 0x8a2fc.
Definition tfib_A_init_libc : Z := 0x8a2fc.  Definition tfib_E_init_libc : Z := 0x8a528.
Definition tfib_A_libc_start_init : Z := 0x8a528.  Definition tfib_E_libc_start_init : Z := 0x8a574.
Definition tfib_A_libc_start_main : Z := 0x8a574.  Definition tfib_E_libc_start_main : Z := 0x8a5d4.
Definition tfib_A_libc_start_main_stage2 : Z := 0x8a5d4.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8a61c.
Definition tfib_A_init_tls : Z := 0x8a6f4.  Definition tfib_E_init_tls : Z := 0x8a9a4.
Definition tfib_A_init_ssp : Z := 0x8a9a4.  Definition tfib_E_init_ssp : Z := 0x8aa04.
Definition tfib_A_stack_chk_fail : Z := 0x8aa04.  Definition tfib_E_stack_chk_fail : Z := 0x8aa0c.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8aa54.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x8aae8.
Definition tfib_A_Exit : Z := 0x8aae8.  Definition tfib_E_Exit : Z := 0x8ab04.
Definition tfib_A_funcs_on_exit : Z := 0x8ab34.  Definition tfib_E_funcs_on_exit : Z := 0x8abfc.
Definition tfib_A_fini_stub_ret : Z := 0x8abfc.  Definition tfib_E_fini_stub_ret : Z := 0x8ac00.
Definition tfib_A_cxa_atexit_atexit : Z := 0x8ac00.  Definition tfib_E_cxa_atexit_atexit : Z := 0x8acc4.
Definition tfib_A_libc_exit_fini_array_walker_stub : Z := 0x8acc4.  Definition tfib_E_libc_exit_fini_array_walker_stub : Z := 0x8acc8.
Definition tfib_A_musl_exit_helper_stub : Z := 0x8acc8.  Definition tfib_E_musl_exit_helper_stub : Z := 0x8accc.
Definition tfib_A_libc_exit_fini : Z := 0x8accc.  Definition tfib_E_libc_exit_fini : Z := 0x8ad18.
Definition tfib_A_exit : Z := 0x8ad18.  Definition tfib_E_exit : Z := 0x8ad8c.
Definition tfib_A_open : Z := 0x8af8c.  Definition tfib_E_open : Z := 0x8b070.
Definition tfib_A_syscall_ret : Z := 0x8b070.  Definition tfib_E_syscall_ret : Z := 0x8b0a8.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x8b0a8.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x8b250.
Definition tfib_A_calloc : Z := 0x8b814.  Definition tfib_E_calloc : Z := 0x8b94c.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8b94c.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x8b950.
Definition tfib_A_libc_free : Z := 0x8b950.  Definition tfib_E_libc_free : Z := 0x8bb1c.
Definition tfib_A_get_meta : Z := 0x8bb1c.  Definition tfib_E_get_meta : Z := 0x8bc2c.
Definition tfib_A_alloc_meta : Z := 0x8c004.  Definition tfib_E_alloc_meta : Z := 0x8c2dc.
Definition tfib_A_libc_malloc_impl : Z := 0x8c2dc.  Definition tfib_E_libc_malloc_impl : Z := 0x8c64c.
Definition tfib_A_alloc_slot : Z := 0x8c64c.  Definition tfib_E_alloc_slot : Z := 0x8cef0.
Definition tfib_A_enframe : Z := 0x8cef0.  Definition tfib_E_enframe : Z := 0x8d040.
Definition tfib_A_malloc_allzerop : Z := 0x8d040.  Definition tfib_E_malloc_allzerop : Z := 0x8d1b8.
Definition tfib_A_getrlimit : Z := 0x8e588.  Definition tfib_E_getrlimit : Z := 0x8e680.
Definition tfib_A_getrusage : Z := 0x8e680.  Definition tfib_E_getrusage : Z := 0x8e6a8.
Definition tfib_A_setrlimit : Z := 0x8e6a8.  Definition tfib_E_setrlimit : Z := 0x8e770.
Definition tfib_A_mmap : Z := 0x8eb98.  Definition tfib_E_mmap : Z := 0x8ec84.
Definition tfib_A_mprotect : Z := 0x8ec84.  Definition tfib_E_mprotect : Z := 0x8eccc.
Definition tfib_A_munmap : Z := 0x8eda0.  Definition tfib_E_munmap : Z := 0x8ede8.
Definition tfib_A_sched_yield : Z := 0x8f0ac.  Definition tfib_E_sched_yield : Z := 0x8f0d0.
Definition tfib_A_raise_tkill_path : Z := 0x8f12c.  Definition tfib_E_raise_tkill_path : Z := 0x8f1a4.
Definition tfib_A_sigaction_libc_sigaction : Z := 0x8f1a4.  Definition tfib_E_sigaction_libc_sigaction : Z := 0x8f378.
Definition tfib_A_musl_sigaltstack : Z := 0x8f470.  Definition tfib_E_musl_sigaltstack : Z := 0x8f4fc.
Definition tfib_A_fprintf : Z := 0x8fad8.  Definition tfib_E_fprintf : Z := 0x8fb3c.

Definition tfib_A_lockfile : Z := 0x8fb3c.  Definition tfib_E_lockfile : Z := 0x8fc38.
Definition tfib_A_unlockfile : Z := 0x8fc38.  Definition tfib_E_unlockfile : Z := 0x8fc98.



Definition tfib_A_stdio_read : Z := 0x8f828.  Definition tfib_E_stdio_read : Z := 0x8f940.
Definition tfib_A_stdio_write : Z := 0x8f948.  Definition tfib_E_stdio_write : Z := 0x8fad8.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8f7f8.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8f7fc.
Definition tfib_A_stdio_close : Z := 0x8f7fc.  Definition tfib_E_stdio_close : Z := 0x8f828.
Definition tfib_A_fwritex : Z := 0x900cc.  Definition tfib_E_fwritex : Z := 0x90204.
Definition tfib_A_musl_fwrite : Z := 0x90204.  Definition tfib_E_musl_fwrite : Z := 0x902bc.
Definition tfib_A_towrite : Z := 0x902bc.  Definition tfib_E_towrite : Z := 0x90310.
Definition tfib_A_stdio_exit : Z := 0x8ff28.  Definition tfib_E_stdio_exit : Z := 0x900cc.
Definition tfib_A_ofl_lock : Z := 0x90310.  Definition tfib_E_ofl_lock : Z := 0x90340.

Definition tfib_A_musl_vfprintf : Z := 0x9048c.  Definition tfib_E_musl_vfprintf : Z := 0x9063c.
Definition tfib_A_printf_core : Z := 0x9063c.  Definition tfib_E_printf_core : Z := 0x9146c.
Definition tfib_A_pop_arg : Z := 0x9146c.  Definition tfib_E_pop_arg : Z := 0x915a0.
Definition tfib_A_pad : Z := 0x915a0.  Definition tfib_E_pad : Z := 0x91674.
Definition tfib_A_fmt_fp : Z := 0x91674.  Definition tfib_E_fmt_fp : Z := 0x92d3c.
Definition tfib_A_thunk_931e0 : Z := 0x8b468.  Definition tfib_E_thunk_931e0 : Z := 0x8b46c.
Definition tfib_A_musl_wctomb : Z := 0x8ef14.  Definition tfib_E_musl_wctomb : Z := 0x8ef38.
Definition tfib_A_musl_wcrtomb : Z := 0x8ede8.  Definition tfib_E_musl_wcrtomb : Z := 0x8ef14.
Definition tfib_A_fpclassifyl : Z := 0x8d990.  Definition tfib_E_fpclassifyl : Z := 0x8d9d4.
Definition tfib_A_letf2 : Z := 0x836d4.  Definition tfib_E_letf2 : Z := 0x8379c.
Definition tfib_A_multf3 : Z := 0x8d290.  Definition tfib_E_multf3 : Z := 0x8d990.
Definition tfib_A_floatsitf : Z := 0x8d9d4.  Definition tfib_E_floatsitf : Z := 0x8dadc.
Definition tfib_A_scalbn : Z := 0x8e3e0.  Definition tfib_E_scalbn : Z := 0x8e478.
Definition tfib_A_subtf3 : Z := 0x83c68.  Definition tfib_E_subtf3 : Z := 0x83c78.
Definition tfib_A_addtf3 : Z := 0x83c78.  Definition tfib_E_addtf3 : Z := 0x84444.
Definition tfib_A_fe_getround : Z := 0x84444.  Definition tfib_E_fe_getround : Z := 0x84474.
Definition tfib_A_fixunstfsi : Z := 0x92d44.  Definition tfib_E_fixunstfsi : Z := 0x92dd8.
Definition tfib_A_floatunsitf : Z := 0x92dd8.  Definition tfib_E_floatunsitf : Z := 0x92ec4.
Definition tfib_A_fixtfsi : Z := 0x8e478.  Definition tfib_E_fixtfsi : Z := 0x8e520.
Definition tfib_A_divtf3 : Z := 0x8dadc.  Definition tfib_E_divtf3 : Z := 0x8e3e0.
Definition tfib_A_musl_vprintf : Z := 0x9359c.  Definition tfib_E_musl_vprintf : Z := 0x935b8.
Definition tfib_A_stdout_write : Z := 0x9034c.  Definition tfib_E_stdout_write : Z := 0x903ec.

Definition tfib_A_musl_memcmp : Z := 0x93c1c.  Definition tfib_E_musl_memcmp : Z := 0x93c4c.
Definition tfib_A_musl_memcpy : Z := 0x93c4c.  Definition tfib_E_musl_memcpy : Z := 0x94050.
Definition tfib_A_musl_memset : Z := 0x94050.  Definition tfib_E_musl_memset : Z := 0x94148.
Definition tfib_A_musl_strchr : Z := 0x94148.  Definition tfib_E_musl_strchr : Z := 0x94184.
Definition tfib_A_strchrnul : Z := 0x94184.  Definition tfib_E_strchrnul : Z := 0x94264.
Definition tfib_A_musl_strlen : Z := 0x9429c.  Definition tfib_E_musl_strlen : Z := 0x9432c.
Definition tfib_A_musl_strnlen : Z := 0x944d8.  Definition tfib_E_musl_strnlen : Z := 0x9451c.
Definition tfib_A_musl_memchr : Z := 0x93b50.  Definition tfib_E_musl_memchr : Z := 0x93c1c.
Definition tfib_A_lock : Z := 0x9451c.  Definition tfib_E_lock : Z := 0x947a4.
Definition tfib_A_unlock : Z := 0x947a4.  Definition tfib_E_unlock : Z := 0x94818.
Definition tfib_A_syscall_cp_c : Z := 0x94818.  Definition tfib_E_syscall_cp_c : Z := 0x9483c.
Definition tfib_A_syscall_cp_sccp : Z := 0x9483c.  Definition tfib_E_syscall_cp_sccp : Z := 0x94840.
Definition tfib_A_syscall_cp_c_tail_sccp_9_insns : Z := 0x94840.  Definition tfib_E_syscall_cp_c_tail_sccp_9_insns : Z := 0x94864.
Definition tfib_A_pthread_atfork : Z := 0x9487c.  Definition tfib_E_pthread_atfork : Z := 0x94920.
Definition tfib_A_mremap : Z := 0x8eccc.  Definition tfib_E_mremap : Z := 0x8eda0.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x958f4.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x95910.
Definition tfib_A_pthread_key_create : Z := 0x95c9c.  Definition tfib_E_pthread_key_create : Z := 0x95d70.
Definition tfib_A_lock_unlock_pair_user_futex : Z := 0x96014.  Definition tfib_E_lock_unlock_pair_user_futex : Z := 0x960b8.
Definition tfib_A_pthread_key_create_body_tsd_init : Z := 0x960b8.  Definition tfib_E_pthread_key_create_body_tsd_init : Z := 0x961d4.
Definition tfib_A_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x961d4.  Definition tfib_E_pthread_key_atfork_tsd_table_init_11_insns : Z := 0x96200.
Definition tfib_A_pthread_setspecific : Z := 0x96238.  Definition tfib_E_pthread_setspecific : Z := 0x9626c.
Definition tfib_A_set_thread_area : Z := 0x96274.  Definition tfib_E_set_thread_area : Z := 0x96280.
Definition tfib_A_thunk_96f9c : Z := 0x9626c.  Definition tfib_E_thunk_96f9c : Z := 0x96274.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x96ba0.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x96c58.
Definition tfib_A_close : Z := 0x99270.  Definition tfib_E_close : Z := 0x992c4.
Definition tfib_A_musl_read : Z := 0x99350.  Definition tfib_E_musl_read : Z := 0x99384.
Definition tfib_A_vm_wait : Z := 0x968b0.  Definition tfib_E_vm_wait : Z := 0x96900.
Definition tfib_D_str_sealed : Z := 0x11880.
Definition tfib_D_init_array_0_3 : Z := 0x9a388.
Definition tfib_D_fini_array_0_1 : Z := 0x9a3a8.
Definition tfib_D_GOT_common_flags : Z := 0x9aac0.
Definition tfib_D_GOT_flags : Z := 0x9aac8.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x9aad0.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x9aad8.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x9aae0.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x9aae8.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x9b638.
Definition tfib_D_environ_musl : Z := 0x9b760.
Definition tfib_D_REAL_read : Z := 0x9c800.
Definition tfib_D_REAL_memcpy : Z := 0x9c928.
Definition tfib_D_REAL_memset : Z := 0x9c930.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa0018.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa0e78.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa3678.
Definition tfib_D_asan_inited : Z := 0xa4358.
Definition tfib_D_replace_intrin_cached : Z := 0xa4359.
Definition tfib_D_kHighMemEnd : Z := 0xa4360.
Definition tfib_D_kMidMemBeg : Z := 0xa4368.
Definition tfib_D_kMidMemEnd : Z := 0xa4370.
Definition tfib_D_malloc_context_size : Z := 0xa437c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x1351a8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f68a0.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f8000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x306ac.
Definition tfib_at_rw_lo : Z := 0x9c000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x634f8.
Definition tfib_at_x_imemcpy : Z := 0x6347c.
Definition tfib_at_x_memset : Z := 0x94050.
Definition tfib_at_x_memcpy : Z := 0x93c4c.
Definition tfib_at_x_memiszero : Z := 0x63a28.
Definition tfib_at_x_istrncpy : Z := 0x63924.
Definition tfib_at_x_sealed : Z := 0x11880.
Definition tfib_at_x_popfree : Z := 0x36a98.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x8a334.
Definition tfib_at_x_envscan_k : Z := 0x8a340.
Definition tfib_at_x_pnscan : Z := 0x8a3f8.
Definition tfib_at_x_pnscan_k : Z := 0x8a404.
Definition tfib_at_stops_more : list Z := (0x3470c :: 0x35d30 :: 0x53804 :: 0x59bbc :: 0x59bd0 :: 0x59be4 :: 0x5f574 :: 0x5f644 :: 0x6cb70 :: 0x6da7c :: 0x6dc0c :: 0x77964 :: nil)%list.
