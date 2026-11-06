(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1w.v, with its module paths changed and its addresses moved to libreac/fuzz_grant's ASan build; the program's own function table, the .got end and the image bounds are fuzz_grant.asan's, the bounds from the unit's Reusable/YImgTop.v; six function ends that the move left at cgif_file's are the next function's start or the end of .text, and nine rows of cgif_file's file-opening model (fopen, fclose and their wrappers, musl's fopen, fclose, fdopen, fmodeflags, __ofl_add), which fuzz_grant does not have and no proof reads, are dropped. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/AB1w.v (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
(* Modified by Theorem Labs, 2026-10: every row is keyed by fuzz_decode.asan's own .symtab: E = st_value + st_size of the FUNC symbol at A (a Theorem Labs lane, owner ruling; was copied from fuzz_grant's table). Of the six rows that spanned their function plus its neighbour (cgif's span convention), target_run now ends at its own end, start keeps only its start cell (its end cell tfib_E_start is removed: _start has st_size 0 in the .symtab, so the cell cannot be checked, and nothing reads it), and the other four (thunk_417cc, MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser, pthread_key_create_body_tsd_init, thunk_96f9c) are removed as false by the name rule and read by nothing; the six neighbours get their own rows (start_c, wrap__exit, SealedRepairReservation, oft_exit_guard, pthread_rwlock_timedwrlock, dummy); SetTLSFakeStack ends at 0x3c6b0 and __asan_stack_malloc_0 (0x3c6b0..0x3c824) has its own row, as fuzz_grant e47e01e8e06; the two rows the release's tag always emits from the target's .symtab are added: LLVMFuzzerTestOneInput (0x80064..0x80bc8) and StackDepotNode_store_hash_helper = _ZN11__sanitizer14StackDepotNode5storeEjRKNS_10StackTraceEy (0x71d9c..0x71df8). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x226ac.
Definition tfib_text_lo : Z := 0x30008.  Definition tfib_text_hi : Z := 0x977a8.
Definition tfib_init_array_lo : Z := 0x987a8.  Definition tfib_init_array_hi : Z := 0x987c8.
Definition tfib_fini_array_lo : Z := 0x987c8.  Definition tfib_fini_array_hi : Z := 0x987d8.
Definition tfib_preinit_array_lo : Z := 0x987d8.  Definition tfib_preinit_array_hi : Z := 0x987e0.
Definition tfib_data_rel_ro_lo : Z := 0x987e0.  Definition tfib_data_rel_ro_hi : Z := 0x98ce0.
Definition tfib_got_lo : Z := 0x98ce0.  Definition tfib_got_hi : Z := 0x99a50.
Definition tfib_data_lo : Z := 0x9aa50.  Definition tfib_data_hi : Z := 0x9d608.
Definition tfib_asan_globals_lo : Z := 0x9d610.  Definition tfib_asan_globals_hi : Z := 0x9d6d0.
Definition tfib_bss_lo : Z := 0x9d700.  Definition tfib_bss_hi : Z := 0x5f5638.
Definition tfib_tbss_lo : Z := 0x977a8.  Definition tfib_tbss_hi : Z := 0x977bc.
(* decode: YImgTop COMPUTES IMG_LO / IMG_TOP (the donor states numerals); the body here is the numeral vm_compute
   gives for YImgTop's term (no numeral written), so the donor's `unfold ...; lia` proofs see a number. *)
Definition tfib_img_lo : Z := ltac:(let v := eval vm_compute in IMG_LO in exact v).  Definition tfib_img_hi : Z := ltac:(let v := eval vm_compute in IMG_TOP in exact v).
Definition tfib_entry : Z := 0x30008.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x30008.
Definition tfib_A_start_c : Z := 0x30024.  Definition tfib_E_start_c : Z := 0x30050.
Definition tfib_A_do_init : Z := 0x30050.  Definition tfib_E_do_init : Z := 0x300c4.
Definition tfib_A_do_fini : Z := 0x300c4.  Definition tfib_E_do_fini : Z := 0x30154.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x30154.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x30190.
Definition tfib_A_InitializeAllocator : Z := 0x30300.  Definition tfib_E_InitializeAllocator : Z := 0x30318.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x30318.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x30484.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x309e0.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x30b3c.
Definition tfib_A_asan_free : Z := 0x30f10.  Definition tfib_E_asan_free : Z := 0x30f38.
Definition tfib_A_Allocator_Deallocate : Z := 0x30f38.  Definition tfib_E_Allocator_Deallocate : Z := 0x311f0.
Definition tfib_A_asan_malloc : Z := 0x311f0.  Definition tfib_E_asan_malloc : Z := 0x3124c.
Definition tfib_A_Allocator_Allocate : Z := 0x3124c.  Definition tfib_E_Allocator_Allocate : Z := 0x31bd4.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x3261c.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x32678.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x32678.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x328c8.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x328c8.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x329bc.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x33378.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x335fc.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x335fc.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x3377c.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x3377c.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x33944.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x33944.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x33b10.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x33bb0.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x33cb4.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x33fdc.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x34124.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x352b4.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x3542c.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x355dc.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x357c0.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x357c0.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x35a98.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x35a98.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x35f10.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x35f10.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x36010.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x36010.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x36318.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x36318.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x36688.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x36ba4.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x36c8c.
Definition tfib_A_AsanActivate : Z := 0x36c8c.  Definition tfib_E_AsanActivate : Z := 0x36d68.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3bde4.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3bebc.
Definition tfib_A_FakeStack_Create : Z := 0x3bebc.  Definition tfib_E_FakeStack_Create : Z := 0x3bfa8.
Definition tfib_A_SetTLSFakeStack : Z := 0x3c680.  Definition tfib_E_SetTLSFakeStack : Z := 0x3c6b0.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3c6b0.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3c824.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x71d9c.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x71df8.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x80064.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x80bc8.
Definition tfib_A_check_round_trip : Z := 0x80bc8.  Definition tfib_E_check_round_trip : Z := 0x80e58.  Definition tfib_A_check_braid : Z := 0x80e58.  Definition tfib_E_check_braid : Z := 0x8111c.  Definition tfib_A_reac_frame_is_reac : Z := 0x81154.  Definition tfib_E_reac_frame_is_reac : Z := 0x811ec.  Definition tfib_A_reac_frame_counter : Z := 0x811ec.  Definition tfib_E_reac_frame_counter : Z := 0x8126c.  Definition tfib_A_reac_frame_clean_len : Z := 0x8126c.  Definition tfib_E_reac_frame_clean_len : Z := 0x812ac.  Definition tfib_A_reac_frame_inspect : Z := 0x812dc.  Definition tfib_E_reac_frame_inspect : Z := 0x81434.  Definition tfib_A_reac_decode : Z := 0x81434.  Definition tfib_E_reac_decode : Z := 0x816b0.  Definition tfib_A_reac_decode_plain_le : Z := 0x816b0.  Definition tfib_E_reac_decode_plain_le : Z := 0x818d4.  Definition tfib_A_reac_braid_encode : Z := 0x818d4.  Definition tfib_E_reac_braid_encode : Z := 0x81ad0.  Definition tfib_A_reac_upstream_channels : Z := 0x81ad0.  Definition tfib_E_reac_upstream_channels : Z := 0x81b20.  Definition tfib_A_reac_upstream_decode : Z := 0x81b20.  Definition tfib_E_reac_upstream_decode : Z := 0x81e20.

Definition tfib_A_asan_InitializeFlags : Z := 0x3c960.  Definition tfib_E_asan_InitializeFlags : Z := 0x3d98c.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3e098.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3eeb4.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x3eeb4.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x3f480.
Definition tfib_A_wrap__exit : Z := 0x41598.  Definition tfib_E_wrap__exit : Z := 0x4159c.
Definition tfib_A_icpt_strlen : Z := 0x415d4.  Definition tfib_E_icpt_strlen : Z := 0x41868.
Definition tfib_A_icpt_strnlen : Z := 0x41868.  Definition tfib_E_icpt_strnlen : Z := 0x41afc.
Definition tfib_A_icpt_strcmp : Z := 0x41b00.  Definition tfib_E_icpt_strcmp : Z := 0x42030.
Definition tfib_A_icpt_strchr : Z := 0x42030.  Definition tfib_E_icpt_strchr : Z := 0x42310.
Definition tfib_A_icpt_memcmp : Z := 0x42ba8.  Definition tfib_E_icpt_memcmp : Z := 0x42c64.
Definition tfib_A_icpt_memchr : Z := 0x42d20.  Definition tfib_E_icpt_memchr : Z := 0x42ff0.
Definition tfib_A_icpt_frexpl : Z := 0x42ff0.  Definition tfib_E_icpt_frexpl : Z := 0x43268.
Definition tfib_A_icpt_read : Z := 0x43268.  Definition tfib_E_icpt_read : Z := 0x434d8.
Definition tfib_A_icpt_fwrite : Z := 0x434d8.  Definition tfib_E_icpt_fwrite : Z := 0x4374c.
Definition tfib_A_icpt_time : Z := 0x4374c.  Definition tfib_E_icpt_time : Z := 0x439e8.
Definition tfib_A_icpt_gmtime_r : Z := 0x43bf0.  Definition tfib_E_icpt_gmtime_r : Z := 0x43e30.
Definition tfib_A_icpt_vprintf : Z := 0x43e30.  Definition tfib_E_icpt_vprintf : Z := 0x43ecc.
Definition tfib_A_printf_common_format_interceptor : Z := 0x43ecc.  Definition tfib_E_printf_common_format_interceptor : Z := 0x44994.
Definition tfib_A_icpt_vfprintf : Z := 0x44994.  Definition tfib_E_icpt_vfprintf : Z := 0x44a48.
Definition tfib_A_icpt_vsnprintf : Z := 0x44a48.  Definition tfib_E_icpt_vsnprintf : Z := 0x44d60.
Definition tfib_A_icpt_clock_gettime : Z := 0x44edc.  Definition tfib_E_icpt_clock_gettime : Z := 0x45134.
Definition tfib_A_icpt_wcrtomb : Z := 0x45134.  Definition tfib_E_icpt_wcrtomb : Z := 0x456a4.
Definition tfib_A_icpt_wctomb : Z := 0x456a4.  Definition tfib_E_icpt_wctomb : Z := 0x45a00.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x45acc.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x45eb4.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x45ec0.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x45f3c.
Definition tfib_A_icpt_sem_timedwait : Z := 0x46148.  Definition tfib_E_icpt_sem_timedwait : Z := 0x463e0.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x46410.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x46638.
Definition tfib_A_icpt_send : Z := 0x46638.  Definition tfib_E_icpt_send : Z := 0x468ec.
Definition tfib_A_icpt_sendto : Z := 0x468ec.  Definition tfib_E_icpt_sendto : Z := 0x46bb0.
Definition tfib_A_icpt_sigaltstack : Z := 0x46bb0.  Definition tfib_E_icpt_sigaltstack : Z := 0x46e0c.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x46ee0.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x47090.
Definition tfib_A_asan_memcpy : Z := 0x50c10.  Definition tfib_E_asan_memcpy : Z := 0x510ac.
Definition tfib_A_asan_memset : Z := 0x510ac.  Definition tfib_E_asan_memset : Z := 0x512ec.
Definition tfib_A_icpt_memset : Z := 0x512ec.  Definition tfib_E_icpt_memset : Z := 0x515dc.
Definition tfib_A_icpt_memcpy : Z := 0x515dc.  Definition tfib_E_icpt_memcpy : Z := 0x51bcc.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x51bcc.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x51c04.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x51c04.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x51c08.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x51c08.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x51c0c.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x51cb8.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x51df4.
Definition tfib_A_free : Z := 0x51f60.  Definition tfib_E_free : Z := 0x51f64.
Definition tfib_A_malloc : Z := 0x51f64.  Definition tfib_E_malloc : Z := 0x51f68.
Definition tfib_A_icpt_free : Z := 0x51f6c.  Definition tfib_E_icpt_free : Z := 0x5213c.
Definition tfib_A_icpt_malloc : Z := 0x5213c.  Definition tfib_E_icpt_malloc : Z := 0x52298.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x5259c.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x525a0.
Definition tfib_A_SetCanPoisonMemory : Z := 0x5301c.  Definition tfib_E_SetCanPoisonMemory : Z := 0x5302c.
Definition tfib_A_CanPoisonMemory : Z := 0x5302c.  Definition tfib_E_CanPoisonMemory : Z := 0x53040.
Definition tfib_A_PoisonShadow : Z := 0x53040.  Definition tfib_E_PoisonShadow : Z := 0x5353c.
Definition tfib_A_MemToShadow_checked : Z := 0x5353c.  Definition tfib_E_MemToShadow_checked : Z := 0x53678.
Definition tfib_A_asan_region_is_poisoned : Z := 0x539c8.  Definition tfib_E_asan_region_is_poisoned : Z := 0x53d0c.
Definition tfib_A_AsanTSDInit : Z := 0x5412c.  Definition tfib_E_AsanTSDInit : Z := 0x541a8.
Definition tfib_A_AsanTSDGet : Z := 0x541a8.  Definition tfib_E_AsanTSDGet : Z := 0x541e8.
Definition tfib_A_AsanTSDSet : Z := 0x541e8.  Definition tfib_E_AsanTSDSet : Z := 0x54228.
Definition tfib_A_PlatformTSDDtor : Z := 0x54228.  Definition tfib_E_PlatformTSDDtor : Z := 0x542ac.
Definition tfib_A_InstallAtForkHandler : Z := 0x542ac.  Definition tfib_E_InstallAtForkHandler : Z := 0x542c8.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x54328.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x5436c.
Definition tfib_A_ReportDoubleFree : Z := 0x55398.  Definition tfib_E_ReportDoubleFree : Z := 0x55628.
Definition tfib_A_ReportGenericError : Z := 0x57154.  Definition tfib_E_ReportGenericError : Z := 0x57a10.
Definition tfib_A_AsanInited : Z := 0x5819c.  Definition tfib_E_AsanInited : Z := 0x581b4.
Definition tfib_A_asan_report_load1 : Z := 0x581b4.  Definition tfib_E_asan_report_load1 : Z := 0x58204.
Definition tfib_A_asan_report_exp_load1 : Z := 0x58204.  Definition tfib_E_asan_report_exp_load1 : Z := 0x58254.
Definition tfib_A_asan_report_load2 : Z := 0x58254.  Definition tfib_E_asan_report_load2 : Z := 0x582a4.
Definition tfib_A_asan_report_exp_load2 : Z := 0x582a4.  Definition tfib_E_asan_report_exp_load2 : Z := 0x582f4.
Definition tfib_A_asan_report_load4 : Z := 0x582f4.  Definition tfib_E_asan_report_load4 : Z := 0x58344.
Definition tfib_A_asan_report_exp_load4 : Z := 0x58344.  Definition tfib_E_asan_report_exp_load4 : Z := 0x58394.
Definition tfib_A_asan_report_load8 : Z := 0x58394.  Definition tfib_E_asan_report_load8 : Z := 0x583e4.
Definition tfib_A_asan_report_exp_load8 : Z := 0x583e4.  Definition tfib_E_asan_report_exp_load8 : Z := 0x58434.
Definition tfib_A_asan_report_load16 : Z := 0x58434.  Definition tfib_E_asan_report_load16 : Z := 0x58484.
Definition tfib_A_asan_report_exp_load16 : Z := 0x58484.  Definition tfib_E_asan_report_exp_load16 : Z := 0x584d4.
Definition tfib_A_asan_report_store1 : Z := 0x584d4.  Definition tfib_E_asan_report_store1 : Z := 0x58524.
Definition tfib_A_asan_report_exp_store1 : Z := 0x58524.  Definition tfib_E_asan_report_exp_store1 : Z := 0x58574.
Definition tfib_A_asan_report_store2 : Z := 0x58574.  Definition tfib_E_asan_report_store2 : Z := 0x585c4.
Definition tfib_A_asan_report_exp_store2 : Z := 0x585c4.  Definition tfib_E_asan_report_exp_store2 : Z := 0x58614.
Definition tfib_A_asan_report_store4 : Z := 0x58614.  Definition tfib_E_asan_report_store4 : Z := 0x58664.
Definition tfib_A_asan_report_exp_store4 : Z := 0x58664.  Definition tfib_E_asan_report_exp_store4 : Z := 0x586b4.
Definition tfib_A_asan_report_store8 : Z := 0x586b4.  Definition tfib_E_asan_report_store8 : Z := 0x58704.
Definition tfib_A_asan_report_exp_store8 : Z := 0x58704.  Definition tfib_E_asan_report_exp_store8 : Z := 0x58754.
Definition tfib_A_asan_report_store16 : Z := 0x58754.  Definition tfib_E_asan_report_store16 : Z := 0x587a4.
Definition tfib_A_asan_report_exp_store16 : Z := 0x587a4.  Definition tfib_E_asan_report_exp_store16 : Z := 0x587f4.
Definition tfib_A_asan_report_load_n : Z := 0x587f4.  Definition tfib_E_asan_report_load_n : Z := 0x58844.
Definition tfib_A_asan_report_exp_load_n : Z := 0x58844.  Definition tfib_E_asan_report_exp_load_n : Z := 0x58894.
Definition tfib_A_asan_report_store_n : Z := 0x58894.  Definition tfib_E_asan_report_store_n : Z := 0x588e4.
Definition tfib_A_asan_report_exp_store_n : Z := 0x588e4.  Definition tfib_E_asan_report_exp_store_n : Z := 0x58934.
Definition tfib_A_InitializeHighMemEnd : Z := 0x58934.  Definition tfib_E_InitializeHighMemEnd : Z := 0x589b4.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x589b4.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x58d68.
Definition tfib_A_AsanInitInternal : Z := 0x58df8.  Definition tfib_E_AsanInitInternal : Z := 0x590ac.
Definition tfib_A_asan_init : Z := 0x59318.  Definition tfib_E_asan_init : Z := 0x593ac.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x593ac.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x593b0.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x59614.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5993c.
Definition tfib_A_InitializeShadowMemory : Z := 0x59b1c.  Definition tfib_E_InitializeShadowMemory : Z := 0x59e24.
Definition tfib_A_SetMallocContextSize : Z := 0x59e24.  Definition tfib_E_SetMallocContextSize : Z := 0x59e34.
Definition tfib_A_GetMallocContextSize : Z := 0x59e34.  Definition tfib_E_GetMallocContextSize : Z := 0x59e44.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x59e44.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x59f94.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5aa78.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5aab0.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5ad64.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5adf0.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5adf0.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5ae58.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5ae58.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5aed0.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5aed0.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5af38.
Definition tfib_A_AsanThread_Create : Z := 0x5b49c.  Definition tfib_E_AsanThread_Create : Z := 0x5b638.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5b694.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5b8ac.
Definition tfib_A_GetCurrentThread : Z := 0x5b8ac.  Definition tfib_E_GetCurrentThread : Z := 0x5b8cc.
Definition tfib_A_AsanThread_stack_top : Z := 0x5ba70.  Definition tfib_E_AsanThread_stack_top : Z := 0x5bac8.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5bac8.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5bb20.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5bb20.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5bd50.
Definition tfib_A_AsanThread_Init : Z := 0x5bd50.  Definition tfib_E_AsanThread_Init : Z := 0x5c144.
Definition tfib_A_CreateMainThread : Z := 0x5c284.  Definition tfib_E_CreateMainThread : Z := 0x5c394.
Definition tfib_A_SetCurrentThread : Z := 0x5c394.  Definition tfib_E_SetCurrentThread : Z := 0x5c474.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5c678.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5c7b4.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5ded8.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5df24.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5df24.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5df30.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5df60.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5df6c.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5df6c.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5df78.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x5f588.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x5f660.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x5f660.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x5f6fc.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fc20.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x5fc64.
Definition tfib_A_RunMallocHooks : Z := 0x60194.  Definition tfib_E_RunMallocHooks : Z := 0x6024c.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x6024c.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x60250.
Definition tfib_A_RunFreeHooks : Z := 0x60250.  Definition tfib_E_RunFreeHooks : Z := 0x602fc.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60640.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x60880.
Definition tfib_A_sanitizer_set_report_path : Z := 0x60e7c.  Definition tfib_E_sanitizer_set_report_path : Z := 0x60e94.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x62aa4.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x62db4.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x62db4.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x62ef8.
Definition tfib_A_FlagParser_ParseString : Z := 0x62ef8.  Definition tfib_E_FlagParser_ParseString : Z := 0x62fec.
Definition tfib_A_internal_atoll : Z := 0x63220.  Definition tfib_E_internal_atoll : Z := 0x6330c.
Definition tfib_A_internal_simple_strtoll : Z := 0x6330c.  Definition tfib_E_internal_simple_strtoll : Z := 0x63468.
Definition tfib_A_internal_memchr : Z := 0x63468.  Definition tfib_E_internal_memchr : Z := 0x63488.
Definition tfib_A_internal_memcmp : Z := 0x63488.  Definition tfib_E_internal_memcmp : Z := 0x634c0.
Definition tfib_A_internal_memcpy : Z := 0x634c0.  Definition tfib_E_internal_memcpy : Z := 0x634e4.
Definition tfib_A_internal_memmove : Z := 0x634e4.  Definition tfib_E_internal_memmove : Z := 0x6353c.
Definition tfib_A_internal_memset : Z := 0x6353c.  Definition tfib_E_internal_memset : Z := 0x6359c.
Definition tfib_A_internal_strcspn : Z := 0x6359c.  Definition tfib_E_internal_strcspn : Z := 0x635f0.
Definition tfib_A_internal_strdup : Z := 0x63624.  Definition tfib_E_internal_strdup : Z := 0x63690.
Definition tfib_A_internal_strlen : Z := 0x63690.  Definition tfib_E_internal_strlen : Z := 0x636ac.
Definition tfib_A_internal_strchrnul : Z := 0x6373c.  Definition tfib_E_internal_strchrnul : Z := 0x63784.
Definition tfib_A_internal_strrchr : Z := 0x63784.  Definition tfib_E_internal_strrchr : Z := 0x637c4.
Definition tfib_A_internal_strnlen : Z := 0x638f4.  Definition tfib_E_internal_strnlen : Z := 0x63924.
Definition tfib_A_internal_strncpy : Z := 0x63968.  Definition tfib_E_internal_strncpy : Z := 0x639d8.
Definition tfib_A_internal_strstr : Z := 0x639d8.  Definition tfib_E_internal_strstr : Z := 0x63a6c.
Definition tfib_A_mem_is_zero : Z := 0x63a6c.  Definition tfib_E_mem_is_zero : Z := 0x63b20.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63b20.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x63b30.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63b30.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x63d10.
Definition tfib_A_internal_iserror : Z := 0x63d1c.  Definition tfib_E_internal_iserror : Z := 0x63d3c.
Definition tfib_A_internal_mmap : Z := 0x63d3c.  Definition tfib_E_internal_mmap : Z := 0x63d48.
Definition tfib_A_internal_munmap : Z := 0x63d48.  Definition tfib_E_internal_munmap : Z := 0x63d54.
Definition tfib_A_internal_mprotect : Z := 0x63d54.  Definition tfib_E_internal_mprotect : Z := 0x63d64.
Definition tfib_A_internal_madvise : Z := 0x63d64.  Definition tfib_E_internal_madvise : Z := 0x63d90.
Definition tfib_A_internal_close : Z := 0x63d90.  Definition tfib_E_internal_close : Z := 0x63d9c.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x63d9c.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x63dc0.
Definition tfib_A_internal_read : Z := 0x63dc0.  Definition tfib_E_internal_read : Z := 0x63df8.
Definition tfib_A_internal_write : Z := 0x63df8.  Definition tfib_E_internal_write : Z := 0x63e30.
Definition tfib_A_internal_ftruncate : Z := 0x63e30.  Definition tfib_E_internal_ftruncate : Z := 0x63e68.
Definition tfib_A_internal_dup : Z := 0x63e68.  Definition tfib_E_internal_dup : Z := 0x63e74.
Definition tfib_A_internal_dup2_dup3 : Z := 0x63e74.  Definition tfib_E_internal_dup2_dup3 : Z := 0x63e84.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x63e84.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x63e9c.
Definition tfib_A_internal_sched_yield : Z := 0x63e9c.  Definition tfib_E_internal_sched_yield : Z := 0x63ea8.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x63ea8.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x63ef4.
Definition tfib_A_internal_execve : Z := 0x63ef4.  Definition tfib_E_internal_execve : Z := 0x63f00.
Definition tfib_A_internal_exit_exit_group : Z := 0x63f00.  Definition tfib_E_internal_exit_exit_group : Z := 0x63f14.
Definition tfib_A_FileExists_newfstatat : Z := 0x63f14.  Definition tfib_E_FileExists_newfstatat : Z := 0x63f94.
Definition tfib_A_DirExists_newfstatat : Z := 0x63f94.  Definition tfib_E_DirExists_newfstatat : Z := 0x63ff8.
Definition tfib_A_GetTid_gettid : Z := 0x63ff8.  Definition tfib_E_GetTid_gettid : Z := 0x64004.
Definition tfib_A_GetEnv : Z := 0x64004.  Definition tfib_E_GetEnv : Z := 0x64134.
Definition tfib_A_FutexWait : Z := 0x64238.  Definition tfib_E_FutexWait : Z := 0x6425c.
Definition tfib_A_FutexWake : Z := 0x6425c.  Definition tfib_E_FutexWake : Z := 0x64280.
Definition tfib_A_internal_ptrace : Z := 0x64280.  Definition tfib_E_internal_ptrace : Z := 0x6428c.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x6428c.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x6429c.
Definition tfib_A_internal_getpid : Z := 0x6429c.  Definition tfib_E_internal_getpid : Z := 0x642a8.
Definition tfib_A_internal_getppid : Z := 0x642a8.  Definition tfib_E_internal_getppid : Z := 0x642b4.
Definition tfib_A_internal_prctl : Z := 0x642b4.  Definition tfib_E_internal_prctl : Z := 0x642c0.
Definition tfib_A_internal_sigaltstack : Z := 0x642c0.  Definition tfib_E_internal_sigaltstack : Z := 0x642cc.
Definition tfib_A_internal_fork_clone : Z := 0x642cc.  Definition tfib_E_internal_fork_clone : Z := 0x642e4.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x642e4.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x64410.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64b50.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x64c68.
Definition tfib_A_GetPageSizeCached : Z := 0x64c68.  Definition tfib_E_GetPageSizeCached : Z := 0x64c70.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64c70.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x64d1c.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x64d1c.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x64e3c.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x64f04.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x64f84.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x64fe0.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x650ac.
Definition tfib_A_CheckASLR : Z := 0x651ac.  Definition tfib_E_CheckASLR : Z := 0x651b0.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x653fc.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x65400.
Definition tfib_A_MmapOrDie : Z := 0x6540c.  Definition tfib_E_MmapOrDie : Z := 0x65518.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x65518.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x6558c.
Definition tfib_A_UnmapOrDie : Z := 0x6558c.  Definition tfib_E_UnmapOrDie : Z := 0x65608.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x65608.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x65718.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x65944.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x65a48.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x660e8.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x662f4.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x668ac.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x668b8.
Definition tfib_A_Printf : Z := 0x668bc.  Definition tfib_E_Printf : Z := 0x66908.
Definition tfib_A_SharedPrintfCode : Z := 0x66908.  Definition tfib_E_SharedPrintfCode : Z := 0x66964.
Definition tfib_A_Report : Z := 0x66964.  Definition tfib_E_Report : Z := 0x669b0.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x68504.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x68740.
Definition tfib_A_SuppressionContext_Parse : Z := 0x68740.  Definition tfib_E_SuppressionContext_Parse : Z := 0x68a64.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x69714.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x69b8c.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6a44c.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6a770.
Definition tfib_A_AddDieCallback : Z := 0x6b02c.  Definition tfib_E_AddDieCallback : Z := 0x6b0b4.
Definition tfib_A_Die : Z := 0x6b178.  Definition tfib_E_Die : Z := 0x6b238.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6b238.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6b244.
Definition tfib_A_CheckFailed : Z := 0x6b244.  Definition tfib_E_CheckFailed : Z := 0x6b2fc.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6b954.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6ba4c.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6ba4c.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6bb78.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6be50.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6c138.
Definition tfib_A_AndroidLogInit : Z := 0x6c9e0.  Definition tfib_E_AndroidLogInit : Z := 0x6c9e4.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6ca14.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6ca5c.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6ca5c.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6cca8.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6cdb8.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6cebc.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6d200.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6d2a0.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6d32c.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6d3f0.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6d3f0.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6d478.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6d478.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6d4f0.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6d4f0.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6d5d4.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6d690.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6d7c4.
Definition tfib_A_SealedRepairReservation : Z := 0x6dd00.  Definition tfib_E_SealedRepairReservation : Z := 0x6ddd8.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x6fa88.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x6fbac.
Definition tfib_A_StackStore_Alloc : Z := 0x6fbac.  Definition tfib_E_StackStore_Alloc : Z := 0x6fce0.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x70594.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x70648.

Definition tfib_A_StackDepotPut : Z := 0x72084.  Definition tfib_E_StackDepotPut : Z := 0x720a4.
Definition tfib_A_StackDepotBase_Put : Z := 0x720a4.  Definition tfib_E_StackDepotBase_Put : Z := 0x72328.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x72a08.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x72a10.
Definition tfib_A_StackTrace_PopStackFrames : Z := 0x72b70.  Definition tfib_E_StackTrace_PopStackFrames : Z := 0x72be4.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x7306c.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x73184.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x793d4.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x79490.
Definition tfib_A_Unwind_Trace_callback : Z := 0x79490.  Definition tfib_E_Unwind_Trace_callback : Z := 0x79568.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79b4c.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x79f1c.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7a1ec.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7a2a4.
Definition tfib_A_lsan_register_root_region : Z := 0x7c208.  Definition tfib_E_lsan_register_root_region : Z := 0x7c538.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7c538.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7c9c0.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x7f920.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x7f99c.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x7f99c.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x7fa4c.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7fa64.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x7fbac.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x7fbac.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x7fbb8.
Definition tfib_A_asan_default_options_cli_c : Z := 0x7fbb8.  Definition tfib_E_asan_default_options_cli_c : Z := 0x7fbc4.
Definition tfib_A_main : Z := 0x7fbc4.  Definition tfib_E_main : Z := 0x7fe88.
Definition tfib_A_target_alloc_init : Z := 0x7fe88.  Definition tfib_E_target_alloc_init : Z := 0x7fe8c.
Definition tfib_A_target_alloc_count : Z := 0x7fe8c.  Definition tfib_E_target_alloc_count : Z := 0x7fe94.
Definition tfib_A_target_run : Z := 0x7fe94.  Definition tfib_E_target_run : Z := 0x7ffec.
Definition tfib_A_oft_exit_guard : Z := 0x7ffec.  Definition tfib_E_oft_exit_guard : Z := 0x8001c.
Definition tfib_A_emit_printf : Z := 0x8001c.  Definition tfib_E_emit_printf : Z := 0x80064.


Definition tfib_A_asan_module_ctor : Z := 0x8111c.  Definition tfib_E_asan_module_ctor : Z := 0x81154.
Definition tfib_A_asan_module_dtor : Z := 0x812ac.  Definition tfib_E_asan_module_dtor : Z := 0x812dc.





















Definition tfib_A_extenddftf2 : Z := 0x81e30.  Definition tfib_E_extenddftf2 : Z := 0x81fc0.
Definition tfib_A_sysconf : Z := 0x87c10.  Definition tfib_E_sysconf : Z := 0x87e38.
Definition tfib_A_init : Z := 0x87e38.  Definition tfib_E_init : Z := 0x87e3c.
Definition tfib_A_init_libc : Z := 0x87e3c.  Definition tfib_E_init_libc : Z := 0x88068.
Definition tfib_A_libc_start_init : Z := 0x88068.  Definition tfib_E_libc_start_init : Z := 0x880b4.
Definition tfib_A_libc_start_main : Z := 0x880b4.  Definition tfib_E_libc_start_main : Z := 0x88114.
Definition tfib_A_libc_start_main_stage2 : Z := 0x88114.  Definition tfib_E_libc_start_main_stage2 : Z := 0x8815c.
Definition tfib_A_init_tls : Z := 0x88234.  Definition tfib_E_init_tls : Z := 0x884e4.
Definition tfib_A_init_ssp : Z := 0x884e4.  Definition tfib_E_init_ssp : Z := 0x88544.
Definition tfib_A_stack_chk_fail : Z := 0x88544.  Definition tfib_E_stack_chk_fail : Z := 0x8854c.
Definition tfib_A_Exit : Z := 0x88628.  Definition tfib_E_Exit : Z := 0x88644.
Definition tfib_A_funcs_on_exit : Z := 0x88674.  Definition tfib_E_funcs_on_exit : Z := 0x8873c.
Definition tfib_A_libc_exit_fini : Z := 0x8880c.  Definition tfib_E_libc_exit_fini : Z := 0x88858.
Definition tfib_A_exit : Z := 0x88858.  Definition tfib_E_exit : Z := 0x888cc.
Definition tfib_A_open : Z := 0x88acc.  Definition tfib_E_open : Z := 0x88bb0.
Definition tfib_A_syscall_ret : Z := 0x88bb0.  Definition tfib_E_syscall_ret : Z := 0x88be8.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x88be8.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x88d90.
Definition tfib_A_calloc : Z := 0x89354.  Definition tfib_E_calloc : Z := 0x8948c.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x8948c.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x89490.
Definition tfib_A_libc_free : Z := 0x89490.  Definition tfib_E_libc_free : Z := 0x8965c.
Definition tfib_A_get_meta : Z := 0x8965c.  Definition tfib_E_get_meta : Z := 0x8976c.
Definition tfib_A_alloc_meta : Z := 0x89b44.  Definition tfib_E_alloc_meta : Z := 0x89e1c.
Definition tfib_A_libc_malloc_impl : Z := 0x89e1c.  Definition tfib_E_libc_malloc_impl : Z := 0x8a18c.
Definition tfib_A_alloc_slot : Z := 0x8a18c.  Definition tfib_E_alloc_slot : Z := 0x8aa30.
Definition tfib_A_enframe : Z := 0x8aa30.  Definition tfib_E_enframe : Z := 0x8ab80.
Definition tfib_A_malloc_allzerop : Z := 0x8ab80.  Definition tfib_E_malloc_allzerop : Z := 0x8acf8.
Definition tfib_A_getrlimit : Z := 0x8c9a8.  Definition tfib_E_getrlimit : Z := 0x8caa0.
Definition tfib_A_getrusage : Z := 0x8caa0.  Definition tfib_E_getrusage : Z := 0x8cac8.
Definition tfib_A_setrlimit : Z := 0x8cac8.  Definition tfib_E_setrlimit : Z := 0x8cb90.
Definition tfib_A_mmap : Z := 0x8cfb8.  Definition tfib_E_mmap : Z := 0x8d0a4.
Definition tfib_A_mprotect : Z := 0x8d0a4.  Definition tfib_E_mprotect : Z := 0x8d0ec.
Definition tfib_A_munmap : Z := 0x8d1c0.  Definition tfib_E_munmap : Z := 0x8d208.
Definition tfib_A_sched_yield : Z := 0x8d4cc.  Definition tfib_E_sched_yield : Z := 0x8d4f0.
Definition tfib_A_raise_tkill_path : Z := 0x8d54c.  Definition tfib_E_raise_tkill_path : Z := 0x8d5c4.
Definition tfib_A_musl_sigaltstack : Z := 0x8d890.  Definition tfib_E_musl_sigaltstack : Z := 0x8d91c.
Definition tfib_A_lockfile : Z := 0x8df5c.  Definition tfib_E_lockfile : Z := 0x8e058.
Definition tfib_A_unlockfile : Z := 0x8e058.  Definition tfib_E_unlockfile : Z := 0x8e0b8.
Definition tfib_A_stdio_read : Z := 0x8dc48.  Definition tfib_E_stdio_read : Z := 0x8dd60.
Definition tfib_A_stdio_write : Z := 0x8dd68.  Definition tfib_E_stdio_write : Z := 0x8def8.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8dc18.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x8dc1c.
Definition tfib_A_stdio_close : Z := 0x8dc1c.  Definition tfib_E_stdio_close : Z := 0x8dc48.
Definition tfib_A_fwritex : Z := 0x8e4ec.  Definition tfib_E_fwritex : Z := 0x8e624.
Definition tfib_A_musl_fwrite : Z := 0x8e624.  Definition tfib_E_musl_fwrite : Z := 0x8e6dc.
Definition tfib_A_towrite : Z := 0x8e6dc.  Definition tfib_E_towrite : Z := 0x8e730.
Definition tfib_A_stdio_exit : Z := 0x8e348.  Definition tfib_E_stdio_exit : Z := 0x8e4ec.
Definition tfib_A_ofl_lock : Z := 0x8e730.  Definition tfib_E_ofl_lock : Z := 0x8e760.
Definition tfib_A_musl_vfprintf : Z := 0x8e8ac.  Definition tfib_E_musl_vfprintf : Z := 0x8ea5c.
Definition tfib_A_printf_core : Z := 0x8ea5c.  Definition tfib_E_printf_core : Z := 0x8f88c.
Definition tfib_A_pop_arg : Z := 0x8f88c.  Definition tfib_E_pop_arg : Z := 0x8f9c0.
Definition tfib_A_pad : Z := 0x8f9c0.  Definition tfib_E_pad : Z := 0x8fa94.
Definition tfib_A_fmt_fp : Z := 0x8fa94.  Definition tfib_E_fmt_fp : Z := 0x9115c.
Definition tfib_A_musl_wctomb : Z := 0x8d334.  Definition tfib_E_musl_wctomb : Z := 0x8d358.
Definition tfib_A_musl_wcrtomb : Z := 0x8d208.  Definition tfib_E_musl_wcrtomb : Z := 0x8d334.
Definition tfib_A_fpclassifyl : Z := 0x8b598.  Definition tfib_E_fpclassifyl : Z := 0x8b5dc.
Definition tfib_A_letf2 : Z := 0x8add0.  Definition tfib_E_letf2 : Z := 0x8ae98.
Definition tfib_A_multf3 : Z := 0x8ae98.  Definition tfib_E_multf3 : Z := 0x8b598.
Definition tfib_A_floatsitf : Z := 0x8bdf4.  Definition tfib_E_floatsitf : Z := 0x8befc.
Definition tfib_A_scalbn : Z := 0x8c800.  Definition tfib_E_scalbn : Z := 0x8c898.
Definition tfib_A_subtf3 : Z := 0x8bde4.  Definition tfib_E_subtf3 : Z := 0x8bdf4.
Definition tfib_A_addtf3 : Z := 0x8b5dc.  Definition tfib_E_addtf3 : Z := 0x8bda8.
Definition tfib_A_fe_getround : Z := 0x8bda8.  Definition tfib_E_fe_getround : Z := 0x8bdd8.
Definition tfib_A_fixunstfsi : Z := 0x91164.  Definition tfib_E_fixunstfsi : Z := 0x911f8.
Definition tfib_A_floatunsitf : Z := 0x911f8.  Definition tfib_E_floatunsitf : Z := 0x912e4.
Definition tfib_A_fixtfsi : Z := 0x8c898.  Definition tfib_E_fixtfsi : Z := 0x8c940.
Definition tfib_A_divtf3 : Z := 0x8befc.  Definition tfib_E_divtf3 : Z := 0x8c800.
Definition tfib_A_musl_vprintf : Z := 0x919bc.  Definition tfib_E_musl_vprintf : Z := 0x919d8.
Definition tfib_A_stdout_write : Z := 0x8e76c.  Definition tfib_E_stdout_write : Z := 0x8e80c.
Definition tfib_A_musl_memcmp : Z := 0x92040.  Definition tfib_E_musl_memcmp : Z := 0x92070.
Definition tfib_A_musl_memcpy : Z := 0x92070.  Definition tfib_E_musl_memcpy : Z := 0x92474.
Definition tfib_A_musl_memset : Z := 0x92474.  Definition tfib_E_musl_memset : Z := 0x9256c.
Definition tfib_A_musl_strchr : Z := 0x9256c.  Definition tfib_E_musl_strchr : Z := 0x925a8.
Definition tfib_A_strchrnul : Z := 0x925a8.  Definition tfib_E_strchrnul : Z := 0x92688.
Definition tfib_A_musl_strlen : Z := 0x926c0.  Definition tfib_E_musl_strlen : Z := 0x92750.
Definition tfib_A_musl_strnlen : Z := 0x928fc.  Definition tfib_E_musl_strnlen : Z := 0x92940.
Definition tfib_A_musl_memchr : Z := 0x91f74.  Definition tfib_E_musl_memchr : Z := 0x92040.
Definition tfib_A_lock : Z := 0x92940.  Definition tfib_E_lock : Z := 0x92bc8.
Definition tfib_A_unlock : Z := 0x92bc8.  Definition tfib_E_unlock : Z := 0x92c3c.
Definition tfib_A_syscall_cp_c : Z := 0x92c3c.  Definition tfib_E_syscall_cp_c : Z := 0x92c60.
Definition tfib_A_syscall_cp_sccp : Z := 0x92c60.  Definition tfib_E_syscall_cp_sccp : Z := 0x92c64.
Definition tfib_A_pthread_atfork : Z := 0x92ca0.  Definition tfib_E_pthread_atfork : Z := 0x92d44.
Definition tfib_A_mremap : Z := 0x8d0ec.  Definition tfib_E_mremap : Z := 0x8d1c0.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x93d18.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x93d34.
Definition tfib_A_pthread_key_create : Z := 0x940c0.  Definition tfib_E_pthread_key_create : Z := 0x94194.
Definition tfib_A_pthread_rwlock_timedwrlock : Z := 0x944e4.  Definition tfib_E_pthread_rwlock_timedwrlock : Z := 0x945f8.
Definition tfib_A_pthread_setspecific : Z := 0x9465c.  Definition tfib_E_pthread_setspecific : Z := 0x94690.
Definition tfib_A_set_thread_area : Z := 0x94698.
Definition tfib_A_dummy : Z := 0x94694.  Definition tfib_E_dummy : Z := 0x94698.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x94fc4.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9507c.
Definition tfib_A_close : Z := 0x97694.  Definition tfib_E_close : Z := 0x976e8.
Definition tfib_A_musl_read : Z := 0x97774.  Definition tfib_E_musl_read : Z := 0x977a8.
Definition tfib_A_vm_wait : Z := 0x94cd4.  Definition tfib_E_vm_wait : Z := 0x94d24.
Definition tfib_D_str_sealed : Z := 0x11816.
Definition tfib_D_init_array_0_3 : Z := 0x987a8.
Definition tfib_D_fini_array_0_1 : Z := 0x987c8.
Definition tfib_D_GOT_common_flags : Z := 0x98d30.
Definition tfib_D_GOT_flags : Z := 0x98d38.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0x98d40.
Definition tfib_D_GOT_kMidMemBeg : Z := 0x98d48.
Definition tfib_D_GOT_kMidMemEnd : Z := 0x98d50.
Definition tfib_D_GOT_kHighMemEnd : Z := 0x98d58.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0x998a8.
Definition tfib_D_environ_musl : Z := 0x999e8.
Definition tfib_D_REAL_read : Z := 0x9aa90.
Definition tfib_D_REAL_memcpy : Z := 0x9abb8.
Definition tfib_D_REAL_memset : Z := 0x9abc0.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xa0db8.
Definition tfib_D_asan_inited : Z := 0xa1a98.
Definition tfib_D_replace_intrin_cached : Z := 0xa1a99.
Definition tfib_D_kHighMemEnd : Z := 0xa1aa0.
Definition tfib_D_kMidMemBeg : Z := 0xa1aa8.
Definition tfib_D_kMidMemEnd : Z := 0xa1ab0.
Definition tfib_D_malloc_context_size : Z := 0xa1abc.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x1328e8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x5f3fe8.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x5f6000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x30008.
Definition tfib_at_rw_lo : Z := 0x9a000.
Definition tfib_at_rw_len : Z := 0x55c000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x6353c.
Definition tfib_at_x_imemcpy : Z := 0x634c0.
Definition tfib_at_x_memset : Z := 0x92474.
Definition tfib_at_x_memcpy : Z := 0x92070.
Definition tfib_at_x_memiszero : Z := 0x63a6c.
Definition tfib_at_x_istrncpy : Z := 0x63968.
Definition tfib_at_x_sealed : Z := 0x11816.
Definition tfib_at_x_popfree : Z := 0x364d4.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x87e74.
Definition tfib_at_x_envscan_k : Z := 0x87e80.
Definition tfib_at_x_pnscan : Z := 0x87f38.
Definition tfib_at_x_pnscan_k : Z := 0x87f44.
Definition tfib_at_stops_more : list Z := (0x34148 :: 0x3576c :: 0x534e4 :: 0x59aec :: 0x59b00 :: 0x59b14 :: 0x5f5b8 :: 0x5f688 :: 0x6cbb4 :: 0x6dac0 :: 0x6dc50 :: 0x779a8 :: nil)%list.
