(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v at 25e3d17bdb50, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build; the program's own function table, the .got end and the image bounds are fuzz_grant.asan's, the bounds from the unit's Reusable/YImgTop.v; six function ends that the move left at cgif_file's are the next function's start or the end of .text, and nine rows of cgif_file's file-opening model (fopen, fclose and their wrappers, musl's fopen, fclose, fdopen, fmodeflags, __ofl_add), which fuzz_grant does not have and no proof reads, are dropped. *)
(* Modified by Theorem Labs, 2026-10 [image A's note, kept from grant A's header; its numbers are fuzz_grant.asan's]: the side-stack class rows are keyed by fuzz_grant.asan's own symbols: SetTLSFakeStack ends at its own end 0x3cda4, and cgif_file's two merged labels asan_stack_malloc_A / _B are replaced by the four ranges __asan_stack_malloc_0, _1, _2 and _4 that this image links, each from its symbol's address and size. No proof read the three replaced names (measured over every branch of the unit). Image B (fuzz_grant.asan-ubsan fde52226dc48, symbol table 5a5ee7c02b4e): SetTLSFakeStack ends at 0x3cf4c, and the side-stack rows are __asan_stack_malloc_0, _1, _2, _4, _6 and __asan_stack_free_6, each [st_value, st_value + st_size) of image B's symbol. *)
(* Modified by Theorem Labs, 2026-10: grant A's file relocated to image B (fuzz_grant.asan-ubsan fde52226dc48) by port_core 53ec3af2afc9, A -> B; the numbers below are image B's unless a comment says image A. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/B/YB1w.v at 4f87de75d67 (donor image sha256 fde52226dc48), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan+UBSan build; 189 of the donor's function rows (27 of them for functions fuzz_wire.asan-ubsan does not link: 22 of fuzz_grant's own program functions such as reac_ctrl_parse and reac_grant_allocate, __asan_memset, __asan_stack_malloc_2, _4 and _6 and __asan_stack_free_6), the asan_globals range, three data rows (the asan allocator instance, the Flags struct and musl's progname area) and the end addresses of _start, target_run and set_thread_area are removed, and 23 rows are added: 20 for fuzz_wire's own program (its check_, rp_ and reac_frame_ functions and is_tagged_reac) and those of StackStore::Store, StackStore::BlockInfo::Create and TwoLevelMap::Create. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102d0.  Definition tfib_rodata_hi : Z := 0x2258c.
Definition tfib_text_lo : Z := 0x2ff5c.  Definition tfib_text_hi : Z := 0x972e0.
Definition tfib_init_array_lo : Z := 0x982e0.  Definition tfib_init_array_hi : Z := 0x98300.
Definition tfib_fini_array_lo : Z := 0x98300.  Definition tfib_fini_array_hi : Z := 0x98310.
Definition tfib_preinit_array_lo : Z := 0x98310.  Definition tfib_preinit_array_hi : Z := 0x98318.
Definition tfib_data_rel_ro_lo : Z := 0x98318.  Definition tfib_data_rel_ro_hi : Z := 0x98818.
Definition tfib_got_lo : Z := 0x98818.  Definition tfib_got_hi : Z := 0x99570.
Definition tfib_data_lo : Z := 0x9a570.  Definition tfib_data_hi : Z := 0x9d128.
  
Definition tfib_bss_lo : Z := 0x9d140.  Definition tfib_bss_hi : Z := 0x5f5070.
Definition tfib_tbss_lo : Z := 0x972e0.  Definition tfib_tbss_hi : Z := 0x972f4.
Definition tfib_img_lo : Z := IMG_LO.  Definition tfib_img_hi : Z := IMG_TOP.
Definition tfib_entry : Z := 0x2ff5c.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x2ff5c.
Definition tfib_A_do_init : Z := 0x2ffa4.  Definition tfib_E_do_init : Z := 0x30018.
Definition tfib_A_do_fini : Z := 0x30018.  Definition tfib_E_do_fini : Z := 0x300a8.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x300a8.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x300e4.
Definition tfib_A_InitializeAllocator : Z := 0x30254.  Definition tfib_E_InitializeAllocator : Z := 0x3026c.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x3026c.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x303d8.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x30934.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x30a90.
Definition tfib_A_asan_free : Z := 0x30e64.  Definition tfib_E_asan_free : Z := 0x30e8c.
Definition tfib_A_Allocator_Deallocate : Z := 0x30e8c.  Definition tfib_E_Allocator_Deallocate : Z := 0x31144.
Definition tfib_A_asan_malloc : Z := 0x31144.  Definition tfib_E_asan_malloc : Z := 0x311a0.
Definition tfib_A_Allocator_Allocate : Z := 0x311a0.  Definition tfib_E_Allocator_Allocate : Z := 0x31b28.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x32490.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x324ec.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x324ec.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x3273c.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x3273c.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x32830.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x331ec.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x33470.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x33470.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x335f0.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x335f0.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x337b8.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x337b8.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x33984.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x33a24.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x33b28.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33e50.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33f98.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x35128.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x352a0.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x35450.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x35634.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x35634.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x3590c.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x3590c.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x35d84.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x35d84.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x35e84.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x35e84.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x3618c.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x3618c.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x364fc.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x36a18.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x36b00.
Definition tfib_A_AsanActivate : Z := 0x36b00.  Definition tfib_E_AsanActivate : Z := 0x36bdc.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3bc58.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3bd30.
Definition tfib_A_FakeStack_Create : Z := 0x3bd30.  Definition tfib_E_FakeStack_Create : Z := 0x3be1c.
Definition tfib_A_SetTLSFakeStack : Z := 0x3c4f4.  Definition tfib_E_SetTLSFakeStack : Z := 0x3c524.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3c524.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3c698.
Definition tfib_A_asan_stack_malloc_1 : Z := 0x3c698.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3c828.




Definition tfib_A_check_forward : Z := 0x7fda4.  Definition tfib_E_check_forward : Z := 0x7ff2c.  Definition tfib_A_check_ret : Z := 0x7ff2c.  Definition tfib_E_check_ret : Z := 0x7ffe8.  Definition tfib_A_check_downstream : Z := 0x7ffe8.  Definition tfib_E_check_downstream : Z := 0x8016c.  Definition tfib_A_check_meter : Z := 0x8016c.  Definition tfib_E_check_meter : Z := 0x804c0.  Definition tfib_A_check_counter : Z := 0x804c0.  Definition tfib_E_check_counter : Z := 0x8057c.  Definition tfib_A_check_width : Z := 0x8057c.  Definition tfib_E_check_width : Z := 0x805f4.  Definition tfib_A_check_read : Z := 0x805f4.  Definition tfib_E_check_read : Z := 0x80abc.  Definition tfib_A_check_copy : Z := 0x80abc.  Definition tfib_E_check_copy : Z := 0x80d64.  Definition tfib_A_rp_fwd_class : Z := 0x80d9c.  Definition tfib_E_rp_fwd_class : Z := 0x80ee0.  Definition tfib_A_rp_ret_accept : Z := 0x80ee0.  Definition tfib_E_rp_ret_accept : Z := 0x80f84.  Definition tfib_A_rp_ds_accept : Z := 0x80f84.  Definition tfib_E_rp_ds_accept : Z := 0x8103c.  Definition tfib_A_is_tagged_reac : Z := 0x8103c.  Definition tfib_E_is_tagged_reac : Z := 0x81144.  Definition tfib_A_rp_meter_counter : Z := 0x81144.  Definition tfib_E_rp_meter_counter : Z := 0x81314.  Definition tfib_A_rp_counter : Z := 0x81314.  Definition tfib_E_rp_counter : Z := 0x813a0.  Definition tfib_A_rp_frame_channels : Z := 0x813a0.  Definition tfib_E_rp_frame_channels : Z := 0x81414.  Definition tfib_A_rp_copy_untag : Z := 0x81414.  Definition tfib_E_rp_copy_untag : Z := 0x8151c.  Definition tfib_A_rp_slot_width : Z := 0x8151c.  Definition tfib_E_rp_slot_width : Z := 0x815ec.  Definition tfib_A_rp_slot_read : Z := 0x815ec.  Definition tfib_E_rp_slot_read : Z := 0x8183c.  Definition tfib_A_reac_frame_is_reac : Z := 0x8183c.  Definition tfib_E_reac_frame_is_reac : Z := 0x818e8.  Definition tfib_A_reac_frame_clean_len : Z := 0x818e8.  Definition tfib_E_reac_frame_clean_len : Z := 0x81928.
Definition tfib_A_asan_InitializeFlags : Z := 0x3c964.  Definition tfib_E_asan_InitializeFlags : Z := 0x3d990.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3e09c.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3eeb8.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3eeb8.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x3f484.
Definition tfib_A_icpt_strlen : Z := 0x415d8.  Definition tfib_E_icpt_strlen : Z := 0x4186c.
Definition tfib_A_icpt_strnlen : Z := 0x4186c.  Definition tfib_E_icpt_strnlen : Z := 0x41b00.
Definition tfib_A_icpt_strcmp : Z := 0x41b04.  Definition tfib_E_icpt_strcmp : Z := 0x42034.
Definition tfib_A_icpt_strchr : Z := 0x42034.  Definition tfib_E_icpt_strchr : Z := 0x42314.
Definition tfib_A_icpt_memcmp : Z := 0x42bac.  Definition tfib_E_icpt_memcmp : Z := 0x42c68.
Definition tfib_A_icpt_memchr : Z := 0x42d24.  Definition tfib_E_icpt_memchr : Z := 0x42ff4.
Definition tfib_A_icpt_frexpl : Z := 0x42ff4.  Definition tfib_E_icpt_frexpl : Z := 0x4326c.
Definition tfib_A_icpt_read : Z := 0x4326c.  Definition tfib_E_icpt_read : Z := 0x434dc.
Definition tfib_A_icpt_fwrite : Z := 0x434dc.  Definition tfib_E_icpt_fwrite : Z := 0x43750.
Definition tfib_A_icpt_time : Z := 0x43750.  Definition tfib_E_icpt_time : Z := 0x439ec.
Definition tfib_A_icpt_gmtime_r : Z := 0x43bf4.  Definition tfib_E_icpt_gmtime_r : Z := 0x43e34.
Definition tfib_A_icpt_vprintf : Z := 0x43e34.  Definition tfib_E_icpt_vprintf : Z := 0x43ed0.
Definition tfib_A_printf_common_format_interceptor : Z := 0x43ed0.  Definition tfib_E_printf_common_format_interceptor : Z := 0x44998.
Definition tfib_A_icpt_vfprintf : Z := 0x44998.  Definition tfib_E_icpt_vfprintf : Z := 0x44a4c.
Definition tfib_A_icpt_vsnprintf : Z := 0x44a4c.  Definition tfib_E_icpt_vsnprintf : Z := 0x44d64.
Definition tfib_A_icpt_clock_gettime : Z := 0x44ee0.  Definition tfib_E_icpt_clock_gettime : Z := 0x45138.
Definition tfib_A_icpt_wcrtomb : Z := 0x45138.  Definition tfib_E_icpt_wcrtomb : Z := 0x456a8.
Definition tfib_A_icpt_wctomb : Z := 0x456a8.  Definition tfib_E_icpt_wctomb : Z := 0x45a04.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x45ad0.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x45eb8.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x45ec4.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x45f40.
Definition tfib_A_icpt_sem_timedwait : Z := 0x4614c.  Definition tfib_E_icpt_sem_timedwait : Z := 0x463e4.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x46414.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x4663c.
Definition tfib_A_icpt_send : Z := 0x4663c.  Definition tfib_E_icpt_send : Z := 0x468f0.
Definition tfib_A_icpt_sendto : Z := 0x468f0.  Definition tfib_E_icpt_sendto : Z := 0x46bb4.
Definition tfib_A_icpt_sigaltstack : Z := 0x46bb4.  Definition tfib_E_icpt_sigaltstack : Z := 0x46e10.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x46ee4.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47094.
Definition tfib_A_asan_memcpy : Z := 0x50c14.  Definition tfib_E_asan_memcpy : Z := 0x510b0.

Definition tfib_A_icpt_memset : Z := 0x51420.  Definition tfib_E_icpt_memset : Z := 0x51710.
Definition tfib_A_icpt_memcpy : Z := 0x51710.  Definition tfib_E_icpt_memcpy : Z := 0x51d00.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x51d00.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x51d38.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x51d38.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x51d3c.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x51d3c.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x51d40.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x51dec.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x51f28.
Definition tfib_A_free : Z := 0x52094.  Definition tfib_E_free : Z := 0x52098.
Definition tfib_A_malloc : Z := 0x52098.  Definition tfib_E_malloc : Z := 0x5209c.
Definition tfib_A_icpt_free : Z := 0x5209c.  Definition tfib_E_icpt_free : Z := 0x5226c.
Definition tfib_A_icpt_malloc : Z := 0x5226c.  Definition tfib_E_icpt_malloc : Z := 0x523c8.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x52494.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x52498.
Definition tfib_A_SetCanPoisonMemory : Z := 0x52f14.  Definition tfib_E_SetCanPoisonMemory : Z := 0x52f24.
Definition tfib_A_CanPoisonMemory : Z := 0x52f24.  Definition tfib_E_CanPoisonMemory : Z := 0x52f38.
Definition tfib_A_PoisonShadow : Z := 0x52f38.  Definition tfib_E_PoisonShadow : Z := 0x53434.
Definition tfib_A_MemToShadow_checked : Z := 0x53434.  Definition tfib_E_MemToShadow_checked : Z := 0x53570.
Definition tfib_A_asan_region_is_poisoned : Z := 0x538c0.  Definition tfib_E_asan_region_is_poisoned : Z := 0x53c04.
Definition tfib_A_AsanTSDInit : Z := 0x54024.  Definition tfib_E_AsanTSDInit : Z := 0x540a0.
Definition tfib_A_AsanTSDGet : Z := 0x540a0.  Definition tfib_E_AsanTSDGet : Z := 0x540e0.
Definition tfib_A_AsanTSDSet : Z := 0x540e0.  Definition tfib_E_AsanTSDSet : Z := 0x54120.
Definition tfib_A_PlatformTSDDtor : Z := 0x54120.  Definition tfib_E_PlatformTSDDtor : Z := 0x541a4.
Definition tfib_A_InstallAtForkHandler : Z := 0x541a4.  Definition tfib_E_InstallAtForkHandler : Z := 0x541c0.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54220.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x54264.
Definition tfib_A_ReportDoubleFree : Z := 0x55290.  Definition tfib_E_ReportDoubleFree : Z := 0x55520.
Definition tfib_A_ReportGenericError : Z := 0x56dfc.  Definition tfib_E_ReportGenericError : Z := 0x576b8.
Definition tfib_A_AsanInited : Z := 0x57e44.  Definition tfib_E_AsanInited : Z := 0x57e5c.
Definition tfib_A_asan_report_load1 : Z := 0x57e5c.  Definition tfib_E_asan_report_load1 : Z := 0x57eac.
Definition tfib_A_asan_report_exp_load1 : Z := 0x57eac.  Definition tfib_E_asan_report_exp_load1 : Z := 0x57efc.
Definition tfib_A_asan_report_load2 : Z := 0x57efc.  Definition tfib_E_asan_report_load2 : Z := 0x57f4c.
Definition tfib_A_asan_report_exp_load2 : Z := 0x57f4c.  Definition tfib_E_asan_report_exp_load2 : Z := 0x57f9c.
Definition tfib_A_asan_report_load4 : Z := 0x57f9c.  Definition tfib_E_asan_report_load4 : Z := 0x57fec.
Definition tfib_A_asan_report_exp_load4 : Z := 0x57fec.  Definition tfib_E_asan_report_exp_load4 : Z := 0x5803c.
Definition tfib_A_asan_report_load8 : Z := 0x5803c.  Definition tfib_E_asan_report_load8 : Z := 0x5808c.
Definition tfib_A_asan_report_exp_load8 : Z := 0x5808c.  Definition tfib_E_asan_report_exp_load8 : Z := 0x580dc.
Definition tfib_A_asan_report_load16 : Z := 0x580dc.  Definition tfib_E_asan_report_load16 : Z := 0x5812c.
Definition tfib_A_asan_report_exp_load16 : Z := 0x5812c.  Definition tfib_E_asan_report_exp_load16 : Z := 0x5817c.
Definition tfib_A_asan_report_store1 : Z := 0x5817c.  Definition tfib_E_asan_report_store1 : Z := 0x581cc.
Definition tfib_A_asan_report_exp_store1 : Z := 0x581cc.  Definition tfib_E_asan_report_exp_store1 : Z := 0x5821c.
Definition tfib_A_asan_report_store2 : Z := 0x5821c.  Definition tfib_E_asan_report_store2 : Z := 0x5826c.
Definition tfib_A_asan_report_exp_store2 : Z := 0x5826c.  Definition tfib_E_asan_report_exp_store2 : Z := 0x582bc.
Definition tfib_A_asan_report_store4 : Z := 0x582bc.  Definition tfib_E_asan_report_store4 : Z := 0x5830c.
Definition tfib_A_asan_report_exp_store4 : Z := 0x5830c.  Definition tfib_E_asan_report_exp_store4 : Z := 0x5835c.
Definition tfib_A_asan_report_store8 : Z := 0x5835c.  Definition tfib_E_asan_report_store8 : Z := 0x583ac.
Definition tfib_A_asan_report_exp_store8 : Z := 0x583ac.  Definition tfib_E_asan_report_exp_store8 : Z := 0x583fc.
Definition tfib_A_asan_report_store16 : Z := 0x583fc.  Definition tfib_E_asan_report_store16 : Z := 0x5844c.
Definition tfib_A_asan_report_exp_store16 : Z := 0x5844c.  Definition tfib_E_asan_report_exp_store16 : Z := 0x5849c.
Definition tfib_A_asan_report_load_n : Z := 0x5849c.  Definition tfib_E_asan_report_load_n : Z := 0x584ec.
Definition tfib_A_asan_report_exp_load_n : Z := 0x584ec.  Definition tfib_E_asan_report_exp_load_n : Z := 0x5853c.
Definition tfib_A_asan_report_store_n : Z := 0x5853c.  Definition tfib_E_asan_report_store_n : Z := 0x5858c.
Definition tfib_A_asan_report_exp_store_n : Z := 0x5858c.  Definition tfib_E_asan_report_exp_store_n : Z := 0x585dc.
Definition tfib_A_InitializeHighMemEnd : Z := 0x585dc.  Definition tfib_E_InitializeHighMemEnd : Z := 0x5865c.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x5865c.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x58a10.
Definition tfib_A_AsanInitInternal : Z := 0x58aa0.  Definition tfib_E_AsanInitInternal : Z := 0x58d54.
Definition tfib_A_asan_init : Z := 0x58fc0.  Definition tfib_E_asan_init : Z := 0x59054.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x59054.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x59058.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x592bc.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x595e4.
Definition tfib_A_InitializeShadowMemory : Z := 0x597c4.  Definition tfib_E_InitializeShadowMemory : Z := 0x59acc.
Definition tfib_A_SetMallocContextSize : Z := 0x59acc.  Definition tfib_E_SetMallocContextSize : Z := 0x59adc.
Definition tfib_A_GetMallocContextSize : Z := 0x59adc.  Definition tfib_E_GetMallocContextSize : Z := 0x59aec.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x59aec.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x59c3c.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5a720.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5a758.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5aa0c.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5aa98.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5aa98.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5ab00.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5ab00.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5ab78.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5ab78.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5abe0.
Definition tfib_A_AsanThread_Create : Z := 0x5b144.  Definition tfib_E_AsanThread_Create : Z := 0x5b2e0.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5b33c.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5b554.
Definition tfib_A_GetCurrentThread : Z := 0x5b554.  Definition tfib_E_GetCurrentThread : Z := 0x5b574.
Definition tfib_A_AsanThread_stack_top : Z := 0x5b718.  Definition tfib_E_AsanThread_stack_top : Z := 0x5b770.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5b770.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5b7c8.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5b7c8.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5b9f8.
Definition tfib_A_AsanThread_Init : Z := 0x5b9f8.  Definition tfib_E_AsanThread_Init : Z := 0x5bdec.
Definition tfib_A_CreateMainThread : Z := 0x5bf2c.  Definition tfib_E_CreateMainThread : Z := 0x5c03c.
Definition tfib_A_SetCurrentThread : Z := 0x5c03c.  Definition tfib_E_SetCurrentThread : Z := 0x5c11c.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5c320.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5c45c.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5da6c.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5dab8.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5dab8.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5dac4.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5daf4.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5db00.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5db00.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5db0c.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5f11c.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5f1f4.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5f1f4.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5f290.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5f7b4.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5f7f8.
Definition tfib_A_RunMallocHooks : Z := 0x5fd28.  Definition tfib_E_RunMallocHooks : Z := 0x5fde0.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x5fde0.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x5fde4.
Definition tfib_A_RunFreeHooks : Z := 0x5fde4.  Definition tfib_E_RunFreeHooks : Z := 0x5fe90.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x601d4.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60414.
Definition tfib_A_sanitizer_set_report_path : Z := 0x60a10.  Definition tfib_E_sanitizer_set_report_path : Z := 0x60a28.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x62638.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x62948.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x62948.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x62a8c.
Definition tfib_A_FlagParser_ParseString : Z := 0x62a8c.  Definition tfib_E_FlagParser_ParseString : Z := 0x62b80.
Definition tfib_A_internal_atoll : Z := 0x62db4.  Definition tfib_E_internal_atoll : Z := 0x62ea0.
Definition tfib_A_internal_simple_strtoll : Z := 0x62ea0.  Definition tfib_E_internal_simple_strtoll : Z := 0x62ffc.
Definition tfib_A_internal_memchr : Z := 0x62ffc.  Definition tfib_E_internal_memchr : Z := 0x6301c.
Definition tfib_A_internal_memcmp : Z := 0x6301c.  Definition tfib_E_internal_memcmp : Z := 0x63054.
Definition tfib_A_internal_memcpy : Z := 0x63054.  Definition tfib_E_internal_memcpy : Z := 0x63078.
Definition tfib_A_internal_memmove : Z := 0x63078.  Definition tfib_E_internal_memmove : Z := 0x630d0.
Definition tfib_A_internal_memset : Z := 0x630d0.  Definition tfib_E_internal_memset : Z := 0x63130.
Definition tfib_A_internal_strcspn : Z := 0x63130.  Definition tfib_E_internal_strcspn : Z := 0x63184.
Definition tfib_A_internal_strdup : Z := 0x631b8.  Definition tfib_E_internal_strdup : Z := 0x63224.
Definition tfib_A_internal_strlen : Z := 0x63224.  Definition tfib_E_internal_strlen : Z := 0x63240.
Definition tfib_A_internal_strchrnul : Z := 0x632d0.  Definition tfib_E_internal_strchrnul : Z := 0x63318.
Definition tfib_A_internal_strrchr : Z := 0x63318.  Definition tfib_E_internal_strrchr : Z := 0x63358.
Definition tfib_A_internal_strnlen : Z := 0x63488.  Definition tfib_E_internal_strnlen : Z := 0x634b8.
Definition tfib_A_internal_strncpy : Z := 0x634fc.  Definition tfib_E_internal_strncpy : Z := 0x6356c.
Definition tfib_A_internal_strstr : Z := 0x6356c.  Definition tfib_E_internal_strstr : Z := 0x63600.
Definition tfib_A_mem_is_zero : Z := 0x63600.  Definition tfib_E_mem_is_zero : Z := 0x636b4.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x636b4.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x636c4.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x636c4.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x638a4.
Definition tfib_A_internal_iserror : Z := 0x638b0.  Definition tfib_E_internal_iserror : Z := 0x638d0.
Definition tfib_A_internal_mmap : Z := 0x638d0.  Definition tfib_E_internal_mmap : Z := 0x638dc.
Definition tfib_A_internal_munmap : Z := 0x638dc.  Definition tfib_E_internal_munmap : Z := 0x638e8.
Definition tfib_A_internal_mprotect : Z := 0x638e8.  Definition tfib_E_internal_mprotect : Z := 0x638f8.
Definition tfib_A_internal_madvise : Z := 0x638f8.  Definition tfib_E_internal_madvise : Z := 0x63924.
Definition tfib_A_internal_close : Z := 0x63924.  Definition tfib_E_internal_close : Z := 0x63930.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x63930.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x63954.
Definition tfib_A_internal_read : Z := 0x63954.  Definition tfib_E_internal_read : Z := 0x6398c.
Definition tfib_A_internal_write : Z := 0x6398c.  Definition tfib_E_internal_write : Z := 0x639c4.
Definition tfib_A_internal_ftruncate : Z := 0x639c4.  Definition tfib_E_internal_ftruncate : Z := 0x639fc.
Definition tfib_A_internal_dup : Z := 0x639fc.  Definition tfib_E_internal_dup : Z := 0x63a08.
Definition tfib_A_internal_dup2_dup3 : Z := 0x63a08.  Definition tfib_E_internal_dup2_dup3 : Z := 0x63a18.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x63a18.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x63a30.
Definition tfib_A_internal_sched_yield : Z := 0x63a30.  Definition tfib_E_internal_sched_yield : Z := 0x63a3c.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x63a3c.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x63a88.
Definition tfib_A_internal_execve : Z := 0x63a88.  Definition tfib_E_internal_execve : Z := 0x63a94.
Definition tfib_A_internal_exit_exit_group : Z := 0x63a94.  Definition tfib_E_internal_exit_exit_group : Z := 0x63aa8.
Definition tfib_A_FileExists_newfstatat : Z := 0x63aa8.  Definition tfib_E_FileExists_newfstatat : Z := 0x63b28.
Definition tfib_A_DirExists_newfstatat : Z := 0x63b28.  Definition tfib_E_DirExists_newfstatat : Z := 0x63b8c.
Definition tfib_A_GetTid_gettid : Z := 0x63b8c.  Definition tfib_E_GetTid_gettid : Z := 0x63b98.
Definition tfib_A_GetEnv : Z := 0x63b98.  Definition tfib_E_GetEnv : Z := 0x63cc8.
Definition tfib_A_FutexWait : Z := 0x63dcc.  Definition tfib_E_FutexWait : Z := 0x63df0.
Definition tfib_A_FutexWake : Z := 0x63df0.  Definition tfib_E_FutexWake : Z := 0x63e14.
Definition tfib_A_internal_ptrace : Z := 0x63e14.  Definition tfib_E_internal_ptrace : Z := 0x63e20.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x63e20.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x63e30.
Definition tfib_A_internal_getpid : Z := 0x63e30.  Definition tfib_E_internal_getpid : Z := 0x63e3c.
Definition tfib_A_internal_getppid : Z := 0x63e3c.  Definition tfib_E_internal_getppid : Z := 0x63e48.
Definition tfib_A_internal_prctl : Z := 0x63e48.  Definition tfib_E_internal_prctl : Z := 0x63e54.
Definition tfib_A_internal_sigaltstack : Z := 0x63e54.  Definition tfib_E_internal_sigaltstack : Z := 0x63e60.
Definition tfib_A_internal_fork_clone : Z := 0x63e60.  Definition tfib_E_internal_fork_clone : Z := 0x63e78.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x63e78.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x63fa4.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x646e4.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x647fc.
Definition tfib_A_GetPageSizeCached : Z := 0x647fc.  Definition tfib_E_GetPageSizeCached : Z := 0x64804.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64804.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x648b0.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x648b0.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x649d0.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x64a98.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x64b18.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64b74.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64c40.
Definition tfib_A_CheckASLR : Z := 0x64d40.  Definition tfib_E_CheckASLR : Z := 0x64d44.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x64f90.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x64f94.
Definition tfib_A_MmapOrDie : Z := 0x64fa0.  Definition tfib_E_MmapOrDie : Z := 0x650ac.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x650ac.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x65120.
Definition tfib_A_UnmapOrDie : Z := 0x65120.  Definition tfib_E_UnmapOrDie : Z := 0x6519c.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x6519c.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x652ac.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x654d8.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x655dc.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x65c7c.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x65e88.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x66440.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x6644c.
Definition tfib_A_Printf : Z := 0x66450.  Definition tfib_E_Printf : Z := 0x6649c.
Definition tfib_A_SharedPrintfCode : Z := 0x6649c.  Definition tfib_E_SharedPrintfCode : Z := 0x664f8.
Definition tfib_A_Report : Z := 0x664f8.  Definition tfib_E_Report : Z := 0x66544.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68098.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x682d4.
Definition tfib_A_SuppressionContext_Parse : Z := 0x682d4.  Definition tfib_E_SuppressionContext_Parse : Z := 0x685f8.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x692a8.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x69720.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x69fe0.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6a304.
Definition tfib_A_AddDieCallback : Z := 0x6abc0.  Definition tfib_E_AddDieCallback : Z := 0x6ac48.
Definition tfib_A_Die : Z := 0x6ad0c.  Definition tfib_E_Die : Z := 0x6adcc.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6adcc.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6add8.
Definition tfib_A_CheckFailed : Z := 0x6add8.  Definition tfib_E_CheckFailed : Z := 0x6ae90.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6b4e8.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6b5e0.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6b5e0.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6b70c.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6b9e4.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6bccc.
Definition tfib_A_AndroidLogInit : Z := 0x6c574.  Definition tfib_E_AndroidLogInit : Z := 0x6c578.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6c5a8.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6c5f0.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6c5f0.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6c83c.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6c94c.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6ca50.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6cd94.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6ce34.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6cec0.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6cf84.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6cf84.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6d00c.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6d00c.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6d084.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6d084.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6d168.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6d224.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6d358.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x6f61c.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x6f740.
Definition tfib_A_StackStore_Alloc : Z := 0x6f740.  Definition tfib_E_StackStore_Alloc : Z := 0x6f874.
Definition tfib_A_StackStore_Store : Z := 0x6f61c.  Definition tfib_E_StackStore_Store : Z := 0x6f740.
Definition tfib_A_StackStore_BlockInfo_Create : Z := 0x70128.  Definition tfib_E_StackStore_BlockInfo_Create : Z := 0x701dc.
Definition tfib_A_TwoLevelMap_Create_71714 : Z := 0x7243c.  Definition tfib_E_TwoLevelMap_Create_71714 : Z := 0x7253c.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x70128.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x701dc.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x71930.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x7198c.
Definition tfib_A_StackDepotPut : Z := 0x71c18.  Definition tfib_E_StackDepotPut : Z := 0x71c38.
Definition tfib_A_StackDepotBase_Put : Z := 0x71c38.  Definition tfib_E_StackDepotBase_Put : Z := 0x71ebc.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x7259c.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x725a4.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x72704.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x72778.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x72c00.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x72d18.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x78f68.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x79024.
Definition tfib_A_Unwind_Trace_callback : Z := 0x79024.  Definition tfib_E_Unwind_Trace_callback : Z := 0x790fc.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x796e0.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79ab0.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x79d80.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x79e38.
Definition tfib_A_lsan_register_root_region : Z := 0x7bd9c.  Definition tfib_E_lsan_register_root_region : Z := 0x7c0cc.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7c0cc.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7c554.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7f4b4.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7f530.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7f530.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x7f5e0.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7f5f8.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7f740.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x7f740.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x7f74c.
Definition tfib_A_asan_default_options_cli_c : Z := 0x7f74c.  Definition tfib_E_asan_default_options_cli_c : Z := 0x7f758.
Definition tfib_A_main : Z := 0x7f758.  Definition tfib_E_main : Z := 0x7fa1c.
Definition tfib_A_target_alloc_init : Z := 0x7fa1c.  Definition tfib_E_target_alloc_init : Z := 0x7fa20.
Definition tfib_A_target_alloc_count : Z := 0x7fa20.  Definition tfib_E_target_alloc_count : Z := 0x7fa28.
Definition tfib_A_target_run : Z := 0x7fa28.
Definition tfib_A_emit_printf : Z := 0x7fbb0.  Definition tfib_E_emit_printf : Z := 0x7fbf8.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x7fbf8.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x7fda4.

Definition tfib_A_asan_module_ctor : Z := 0x80d64.  Definition tfib_E_asan_module_ctor : Z := 0x80d9c.
Definition tfib_A_asan_module_dtor : Z := 0x81928.  Definition tfib_E_asan_module_dtor : Z := 0x81958.





















Definition tfib_A_extenddftf2 : Z := 0x81968.  Definition tfib_E_extenddftf2 : Z := 0x81af8.
Definition tfib_A_sysconf : Z := 0x87748.  Definition tfib_E_sysconf : Z := 0x87970.
Definition tfib_A_init : Z := 0x87970.  Definition tfib_E_init : Z := 0x87974.
Definition tfib_A_init_libc : Z := 0x87974.  Definition tfib_E_init_libc : Z := 0x87ba0.
Definition tfib_A_libc_start_init : Z := 0x87ba0.  Definition tfib_E_libc_start_init : Z := 0x87bec.
Definition tfib_A_libc_start_main : Z := 0x87bec.  Definition tfib_E_libc_start_main : Z := 0x87c4c.
Definition tfib_A_libc_start_main_stage2 : Z := 0x87c4c.  Definition tfib_E_libc_start_main_stage2 : Z := 0x87c94.
Definition tfib_A_init_tls : Z := 0x87d6c.  Definition tfib_E_init_tls : Z := 0x8801c.
Definition tfib_A_init_ssp : Z := 0x8801c.  Definition tfib_E_init_ssp : Z := 0x8807c.
Definition tfib_A_stack_chk_fail : Z := 0x8807c.  Definition tfib_E_stack_chk_fail : Z := 0x88084.
Definition tfib_A_Exit : Z := 0x88160.  Definition tfib_E_Exit : Z := 0x8817c.
Definition tfib_A_funcs_on_exit : Z := 0x881ac.  Definition tfib_E_funcs_on_exit : Z := 0x88274.
Definition tfib_A_libc_exit_fini : Z := 0x88344.  Definition tfib_E_libc_exit_fini : Z := 0x88390.
Definition tfib_A_exit : Z := 0x88390.  Definition tfib_E_exit : Z := 0x88404.
Definition tfib_A_open : Z := 0x88604.  Definition tfib_E_open : Z := 0x886e8.
Definition tfib_A_syscall_ret : Z := 0x886e8.  Definition tfib_E_syscall_ret : Z := 0x88720.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x88720.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x888c8.
Definition tfib_A_calloc : Z := 0x88e8c.  Definition tfib_E_calloc : Z := 0x88fc4.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x88fc4.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x88fc8.
Definition tfib_A_libc_free : Z := 0x88fc8.  Definition tfib_E_libc_free : Z := 0x89194.
Definition tfib_A_get_meta : Z := 0x89194.  Definition tfib_E_get_meta : Z := 0x892a4.
Definition tfib_A_alloc_meta : Z := 0x8967c.  Definition tfib_E_alloc_meta : Z := 0x89954.
Definition tfib_A_libc_malloc_impl : Z := 0x89954.  Definition tfib_E_libc_malloc_impl : Z := 0x89cc4.
Definition tfib_A_alloc_slot : Z := 0x89cc4.  Definition tfib_E_alloc_slot : Z := 0x8a568.
Definition tfib_A_enframe : Z := 0x8a568.  Definition tfib_E_enframe : Z := 0x8a6b8.
Definition tfib_A_malloc_allzerop : Z := 0x8a6b8.  Definition tfib_E_malloc_allzerop : Z := 0x8a830.
Definition tfib_A_getrlimit : Z := 0x8c4e0.  Definition tfib_E_getrlimit : Z := 0x8c5d8.
Definition tfib_A_getrusage : Z := 0x8c5d8.  Definition tfib_E_getrusage : Z := 0x8c600.
Definition tfib_A_setrlimit : Z := 0x8c600.  Definition tfib_E_setrlimit : Z := 0x8c6c8.
Definition tfib_A_mmap : Z := 0x8caf0.  Definition tfib_E_mmap : Z := 0x8cbdc.
Definition tfib_A_mprotect : Z := 0x8cbdc.  Definition tfib_E_mprotect : Z := 0x8cc24.
Definition tfib_A_munmap : Z := 0x8ccf8.  Definition tfib_E_munmap : Z := 0x8cd40.
Definition tfib_A_sched_yield : Z := 0x8d004.  Definition tfib_E_sched_yield : Z := 0x8d028.
Definition tfib_A_raise_tkill_path : Z := 0x8d084.  Definition tfib_E_raise_tkill_path : Z := 0x8d0fc.
Definition tfib_A_musl_sigaltstack : Z := 0x8d3c8.  Definition tfib_E_musl_sigaltstack : Z := 0x8d454.
Definition tfib_A_lockfile : Z := 0x8da94.  Definition tfib_E_lockfile : Z := 0x8db90.
Definition tfib_A_unlockfile : Z := 0x8db90.  Definition tfib_E_unlockfile : Z := 0x8dbf0.
Definition tfib_A_stdio_read : Z := 0x8d780.  Definition tfib_E_stdio_read : Z := 0x8d898.
Definition tfib_A_stdio_write : Z := 0x8d8a0.  Definition tfib_E_stdio_write : Z := 0x8da30.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8d750.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8d754.
Definition tfib_A_stdio_close : Z := 0x8d754.  Definition tfib_E_stdio_close : Z := 0x8d780.
Definition tfib_A_fwritex : Z := 0x8e024.  Definition tfib_E_fwritex : Z := 0x8e15c.
Definition tfib_A_musl_fwrite : Z := 0x8e15c.  Definition tfib_E_musl_fwrite : Z := 0x8e214.
Definition tfib_A_towrite : Z := 0x8e214.  Definition tfib_E_towrite : Z := 0x8e268.
Definition tfib_A_stdio_exit : Z := 0x8de80.  Definition tfib_E_stdio_exit : Z := 0x8e024.
Definition tfib_A_ofl_lock : Z := 0x8e268.  Definition tfib_E_ofl_lock : Z := 0x8e298.
Definition tfib_A_musl_vfprintf : Z := 0x8e3e4.  Definition tfib_E_musl_vfprintf : Z := 0x8e594.
Definition tfib_A_printf_core : Z := 0x8e594.  Definition tfib_E_printf_core : Z := 0x8f3c4.
Definition tfib_A_pop_arg : Z := 0x8f3c4.  Definition tfib_E_pop_arg : Z := 0x8f4f8.
Definition tfib_A_pad : Z := 0x8f4f8.  Definition tfib_E_pad : Z := 0x8f5cc.
Definition tfib_A_fmt_fp : Z := 0x8f5cc.  Definition tfib_E_fmt_fp : Z := 0x90c94.
Definition tfib_A_musl_wctomb : Z := 0x8ce6c.  Definition tfib_E_musl_wctomb : Z := 0x8ce90.
Definition tfib_A_musl_wcrtomb : Z := 0x8cd40.  Definition tfib_E_musl_wcrtomb : Z := 0x8ce6c.
Definition tfib_A_fpclassifyl : Z := 0x8b0d0.  Definition tfib_E_fpclassifyl : Z := 0x8b114.
Definition tfib_A_letf2 : Z := 0x8a908.  Definition tfib_E_letf2 : Z := 0x8a9d0.
Definition tfib_A_multf3 : Z := 0x8a9d0.  Definition tfib_E_multf3 : Z := 0x8b0d0.
Definition tfib_A_floatsitf : Z := 0x8b92c.  Definition tfib_E_floatsitf : Z := 0x8ba34.
Definition tfib_A_scalbn : Z := 0x8c338.  Definition tfib_E_scalbn : Z := 0x8c3d0.
Definition tfib_A_subtf3 : Z := 0x8b91c.  Definition tfib_E_subtf3 : Z := 0x8b92c.
Definition tfib_A_addtf3 : Z := 0x8b114.  Definition tfib_E_addtf3 : Z := 0x8b8e0.
Definition tfib_A_fe_getround : Z := 0x8b8e0.  Definition tfib_E_fe_getround : Z := 0x8b910.
Definition tfib_A_fixunstfsi : Z := 0x90c9c.  Definition tfib_E_fixunstfsi : Z := 0x90d30.
Definition tfib_A_floatunsitf : Z := 0x90d30.  Definition tfib_E_floatunsitf : Z := 0x90e1c.
Definition tfib_A_fixtfsi : Z := 0x8c3d0.  Definition tfib_E_fixtfsi : Z := 0x8c478.
Definition tfib_A_divtf3 : Z := 0x8ba34.  Definition tfib_E_divtf3 : Z := 0x8c338.
Definition tfib_A_musl_vprintf : Z := 0x914f4.  Definition tfib_E_musl_vprintf : Z := 0x91510.
Definition tfib_A_stdout_write : Z := 0x8e2a4.  Definition tfib_E_stdout_write : Z := 0x8e344.
Definition tfib_A_musl_memcmp : Z := 0x91b78.  Definition tfib_E_musl_memcmp : Z := 0x91ba8.
Definition tfib_A_musl_memcpy : Z := 0x91ba8.  Definition tfib_E_musl_memcpy : Z := 0x91fac.
Definition tfib_A_musl_memset : Z := 0x91fac.  Definition tfib_E_musl_memset : Z := 0x920a4.
Definition tfib_A_musl_strchr : Z := 0x920a4.  Definition tfib_E_musl_strchr : Z := 0x920e0.
Definition tfib_A_strchrnul : Z := 0x920e0.  Definition tfib_E_strchrnul : Z := 0x921c0.
Definition tfib_A_musl_strlen : Z := 0x921f8.  Definition tfib_E_musl_strlen : Z := 0x92288.
Definition tfib_A_musl_strnlen : Z := 0x92434.  Definition tfib_E_musl_strnlen : Z := 0x92478.
Definition tfib_A_musl_memchr : Z := 0x91aac.  Definition tfib_E_musl_memchr : Z := 0x91b78.
Definition tfib_A_lock : Z := 0x92478.  Definition tfib_E_lock : Z := 0x92700.
Definition tfib_A_unlock : Z := 0x92700.  Definition tfib_E_unlock : Z := 0x92774.
Definition tfib_A_syscall_cp_c : Z := 0x92774.  Definition tfib_E_syscall_cp_c : Z := 0x92798.
Definition tfib_A_syscall_cp_sccp : Z := 0x92798.  Definition tfib_E_syscall_cp_sccp : Z := 0x9279c.
Definition tfib_A_pthread_atfork : Z := 0x927d8.  Definition tfib_E_pthread_atfork : Z := 0x9287c.
Definition tfib_A_mremap : Z := 0x8cc24.  Definition tfib_E_mremap : Z := 0x8ccf8.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x93850.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x9386c.
Definition tfib_A_pthread_key_create : Z := 0x93bf8.  Definition tfib_E_pthread_key_create : Z := 0x93ccc.
Definition tfib_A_pthread_setspecific : Z := 0x94194.  Definition tfib_E_pthread_setspecific : Z := 0x941c8.
Definition tfib_A_set_thread_area : Z := 0x941d0.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x94afc.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x94bb4.
Definition tfib_A_close : Z := 0x971cc.  Definition tfib_E_close : Z := 0x97220.
Definition tfib_A_musl_read : Z := 0x972ac.  Definition tfib_E_musl_read : Z := 0x972e0.
Definition tfib_A_vm_wait : Z := 0x9480c.  Definition tfib_E_vm_wait : Z := 0x9485c.
Definition tfib_D_str_sealed : Z := 0x11806.
Definition tfib_D_init_array_0_3 : Z := 0x982e0.
Definition tfib_D_fini_array_0_1 : Z := 0x98300.
Definition tfib_D_GOT_common_flags : Z := 0x98868.
Definition tfib_D_GOT_flags : Z := 0x98870.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x98878.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x98880.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x98888.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x98890.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x993e0.
Definition tfib_D_environ_musl : Z := 0x99508.
Definition tfib_D_REAL_read : Z := 0x9a5b0.
Definition tfib_D_REAL_memcpy : Z := 0x9a6d8.
Definition tfib_D_REAL_memset : Z := 0x9a6e0.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa07f8.
Definition tfib_D_asan_inited : Z := 0xa14d8.
Definition tfib_D_replace_intrin_cached : Z := 0xa14d9.
Definition tfib_D_kHighMemEnd : Z := 0xa14e0.
Definition tfib_D_kMidMemBeg : Z := 0xa14e8.
Definition tfib_D_kMidMemEnd : Z := 0xa14f0.
Definition tfib_D_malloc_context_size : Z := 0xa14fc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x132328.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f6000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x2ff5c.
Definition tfib_at_rw_lo : Z := 0x9a000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x630d0.
Definition tfib_at_x_imemcpy : Z := 0x63054.
Definition tfib_at_x_memset : Z := 0x91fac.
Definition tfib_at_x_memcpy : Z := 0x91ba8.
Definition tfib_at_x_memiszero : Z := 0x63600.
Definition tfib_at_x_istrncpy : Z := 0x634fc.
Definition tfib_at_x_sealed : Z := 0x11806.
Definition tfib_at_x_popfree : Z := 0x36348.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x879ac.
Definition tfib_at_x_envscan_k : Z := 0x879b8.
Definition tfib_at_x_pnscan : Z := 0x87a70.
Definition tfib_at_x_pnscan_k : Z := 0x87a7c.
Definition tfib_at_stops_more : list Z := (0x33fbc :: 0x355e0 :: 0x533dc :: 0x59794 :: 0x597a8 :: 0x597bc :: 0x5f14c :: 0x5f21c :: 0x6c748 :: 0x6d654 :: 0x6d7e4 :: 0x7753c :: nil)%list.
