(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1w.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_decode's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the function rows are keyed by name to fuzz_decode.asan-ubsan's own FUNC symbols (unstripped .symtab) and each tfib_E_ is st_value + st_size (provenance/core-reloc/B/yb1w/yb1w_regen.py); six rows the relocation had moved with cgif's span no longer cover the next function (start, thunk_417cc, MmapFixedOrDieOnFatalError_MmapFixedSuperNoReser, target_run, pthread_key_create_body_tsd_init, thunk_96f9c); and the three rows the relocation dropped are back, read off the same symbols (asan_stack_malloc_0, StackDepotNode_store_hash_helper, LLVMFuzzerTestOneInput). *)
(* Modified by Theorem Labs, 2026-10: tfib_img_lo / tfib_img_hi are the numerals vm_compute gives for the unit's Reusable/YImgTop.v IMG_LO / IMG_TOP, as image A's A/AB1w.v does (RELOC-GATES G17). *)
(* Relocated from proofs/libreac/fuzz_decode/lib/YB1w.v at 88154566652a by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan-ubsan). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YImgTop.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_rodata_lo : Z := 0x102e0.  Definition tfib_rodata_hi : Z := 0x22aec.
Definition tfib_text_lo : Z := 0x3112c.  Definition tfib_text_hi : Z := 0xa25a4.
Definition tfib_init_array_lo : Z := 0xa35a8.  Definition tfib_init_array_hi : Z := 0xa35c8.
Definition tfib_fini_array_lo : Z := 0xa35c8.  Definition tfib_fini_array_hi : Z := 0xa35d8.
Definition tfib_preinit_array_lo : Z := 0xa35d8.  Definition tfib_preinit_array_hi : Z := 0xa35e0.
Definition tfib_data_rel_ro_lo : Z := 0xa35e0.  Definition tfib_data_rel_ro_hi : Z := 0xa3c90.
Definition tfib_got_lo : Z := 0xa3c90.  Definition tfib_got_hi : Z := 0xa49e8.
Definition tfib_data_lo : Z := 0xa59e8.  Definition tfib_data_hi : Z := 0xa85a0.
Definition tfib_asan_globals_lo : Z := 0xa85a0.  Definition tfib_asan_globals_hi : Z := 0xa8fa0.
Definition tfib_bss_lo : Z := 0xa8fc0.  Definition tfib_bss_hi : Z := 0x615050.
Definition tfib_tbss_lo : Z := 0xa25a8.  Definition tfib_tbss_hi : Z := 0xa25bc.
(* B/YImgTop.v (written by port_core) states IMG_LO / IMG_TOP as numerals for the pinned fuzz_transport.asan-ubsan
   image (sha256 41113a03c82f): 0x10000, its first PT_LOAD p_vaddr, and 0x616000, the .bss end (sh_addr 0xa8fc0 +
   sh_size 0x56c090 = 0x615050) rounded up to a page; the body here is the numeral vm_compute gives for that notation
   (no numeral written), so the donor's `unfold ...; lia` proofs see a number. *)
Definition tfib_img_lo : Z := ltac:(let v := eval vm_compute in IMG_LO in exact v).  Definition tfib_img_hi : Z := ltac:(let v := eval vm_compute in IMG_TOP in exact v).
Definition tfib_entry : Z := 0x3112c.  Definition tfib_gp : Z := 0x10800.
Definition tfib_A_start : Z := 0x3112c.  Definition tfib_E_start : Z := 0x31148.
Definition tfib_A_do_init : Z := 0x31174.  Definition tfib_E_do_init : Z := 0x311e8.
Definition tfib_A_do_fini : Z := 0x311e8.  Definition tfib_E_do_fini : Z := 0x31278.
Definition tfib_A_AllocatorOptions_SetFrom : Z := 0x31278.  Definition tfib_E_AllocatorOptions_SetFrom : Z := 0x312b4.
Definition tfib_A_InitializeAllocator : Z := 0x31424.  Definition tfib_E_InitializeAllocator : Z := 0x3143c.
Definition tfib_A_Allocator_InitLinkerInitialized : Z := 0x3143c.  Definition tfib_E_Allocator_InitLinkerInitialized : Z := 0x315a8.
Definition tfib_A_Allocator_FindHeapChunkByAddress_helper : Z := 0x31b04.  Definition tfib_E_Allocator_FindHeapChunkByAddress_helper : Z := 0x31c60.
Definition tfib_A_asan_free : Z := 0x32034.  Definition tfib_E_asan_free : Z := 0x3205c.
Definition tfib_A_Allocator_Deallocate : Z := 0x3205c.  Definition tfib_E_Allocator_Deallocate : Z := 0x32314.
Definition tfib_A_asan_malloc : Z := 0x32314.  Definition tfib_E_asan_malloc : Z := 0x32370.
Definition tfib_A_Allocator_Allocate : Z := 0x32370.  Definition tfib_E_Allocator_Allocate : Z := 0x32cf8.
Definition tfib_A_sanitizer_get_allocated_begin_size_style_query : Z := 0x33660.  Definition tfib_E_sanitizer_get_allocated_begin_size_style_query : Z := 0x336bc.
Definition tfib_A_SizeClassAllocator64_Init : Z := 0x336bc.  Definition tfib_E_SizeClassAllocator64_Init : Z := 0x3390c.
Definition tfib_A_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x3390c.  Definition tfib_E_SizeClassAllocator64_MapWithCallbackOrDie : Z := 0x33a00.
Definition tfib_A_QuarantineCallback_Recycle : Z := 0x343bc.  Definition tfib_E_QuarantineCallback_Recycle : Z := 0x34640.
Definition tfib_A_LargeMmapAllocator_GetBlockBegin : Z := 0x34640.  Definition tfib_E_LargeMmapAllocator_GetBlockBegin : Z := 0x347c0.
Definition tfib_A_SizeClassAllocator64LocalCache_Deallocate : Z := 0x347c0.  Definition tfib_E_SizeClassAllocator64LocalCache_Deallocate : Z := 0x34988.
Definition tfib_A_LargeMmapAllocator_Deallocate : Z := 0x34988.  Definition tfib_E_LargeMmapAllocator_Deallocate : Z := 0x34b54.
Definition tfib_A_InternalMmapVector_Realloc : Z := 0x34bf4.  Definition tfib_E_InternalMmapVector_Realloc : Z := 0x34cf8.
Definition tfib_A_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x35020.  Definition tfib_E_SizeClassAllocator64_EnsureFreeArraySpace : Z := 0x35168.
Definition tfib_A_DieOnMapFailure_sealed : Z := 0x35168.  Definition tfib_E_DieOnMapFailure_sealed : Z := 0x351a0.
Definition tfib_A_Allocator_QuarantineChunk : Z := 0x362f8.  Definition tfib_E_Allocator_QuarantineChunk : Z := 0x36470.
Definition tfib_A_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x36470.  Definition tfib_E_Allocator_QuarantineChunk_tail_quarantine_Put : Z := 0x36620.
Definition tfib_A_QuarantineCache_Enqueue : Z := 0x36620.  Definition tfib_E_QuarantineCache_Enqueue : Z := 0x36804.
Definition tfib_A_CombinedAllocator_Allocate : Z := 0x36804.  Definition tfib_E_CombinedAllocator_Allocate : Z := 0x36adc.
Definition tfib_A_LargeMmapAllocator_Allocate : Z := 0x36adc.  Definition tfib_E_LargeMmapAllocator_Allocate : Z := 0x36f54.
Definition tfib_A_SizeClassAllocator64LocalCache_Refill : Z := 0x36f54.  Definition tfib_E_SizeClassAllocator64LocalCache_Refill : Z := 0x37054.
Definition tfib_A_SizeClassAllocator64_GetFromAllocator : Z := 0x37054.  Definition tfib_E_SizeClassAllocator64_GetFromAllocator : Z := 0x3735c.
Definition tfib_A_SizeClassAllocator64_PopulateFreeArray : Z := 0x3735c.  Definition tfib_E_SizeClassAllocator64_PopulateFreeArray : Z := 0x376cc.
Definition tfib_A_AsanDeactivate_activation_CHECK_helper : Z := 0x37be8.  Definition tfib_E_AsanDeactivate_activation_CHECK_helper : Z := 0x37cd0.
Definition tfib_A_AsanActivate : Z := 0x37cd0.  Definition tfib_E_AsanActivate : Z := 0x37dac.
Definition tfib_A_asan_activation_flag_parse_helper_0_no : Z := 0x38288.  Definition tfib_E_asan_activation_flag_parse_helper_0_no : Z := 0x38370.
Definition tfib_A_FakeStack_AddrIsInFakeStack : Z := 0x3ce28.  Definition tfib_E_FakeStack_AddrIsInFakeStack : Z := 0x3cf00.
Definition tfib_A_FakeStack_Create : Z := 0x3cf00.  Definition tfib_E_FakeStack_Create : Z := 0x3cfec.
Definition tfib_A_SetTLSFakeStack : Z := 0x3d6c4.  Definition tfib_E_SetTLSFakeStack : Z := 0x3d6f4.
Definition tfib_A_io_send : Z := 0x82ffc.  Definition tfib_E_io_send : Z := 0x83368.  Definition tfib_A_io_recv : Z := 0x83368.  Definition tfib_E_io_recv : Z := 0x83410.  Definition tfib_A_io_now : Z := 0x83410.  Definition tfib_E_io_now : Z := 0x8341c.  Definition tfib_A_notice : Z := 0x8341c.  Definition tfib_E_notice : Z := 0x836a8.  Definition tfib_A_receive : Z := 0x836a8.  Definition tfib_E_receive : Z := 0x8383c.  Definition tfib_A_m_tick : Z := 0x8383c.  Definition tfib_E_m_tick : Z := 0x838c0.  Definition tfib_A_settle : Z := 0x838c0.  Definition tfib_E_settle : Z := 0x83914.  Definition tfib_A_m_wake : Z := 0x83914.  Definition tfib_E_m_wake : Z := 0x8399c.  Definition tfib_A_check_state_wake_code : Z := 0x8399c.  Definition tfib_E_check_state_wake_code : Z := 0x839c0.  Definition tfib_A_spec_read_frame : Z := 0x839c0.  Definition tfib_E_spec_read_frame : Z := 0x84080.  Definition tfib_A_check_sent_frame : Z := 0x84080.  Definition tfib_E_check_sent_frame : Z := 0x843d4.  Definition tfib_A_check_ack_frame : Z := 0x843d4.  Definition tfib_E_check_ack_frame : Z := 0x84490.  Definition tfib_A_check_latest_control : Z := 0x84490.  Definition tfib_E_check_latest_control : Z := 0x844fc.  Definition tfib_A_check_inflight_retry : Z := 0x844fc.  Definition tfib_E_check_inflight_retry : Z := 0x84628.  Definition tfib_A_check_state_wake : Z := 0x84628.  Definition tfib_E_check_state_wake : Z := 0x84654.  Definition tfib_A_check_inflight_new : Z := 0x84654.  Definition tfib_E_check_inflight_new : Z := 0x846a0.  Definition tfib_A_tagged_of : Z := 0x846a0.  Definition tfib_E_tagged_of : Z := 0x8478c.  Definition tfib_A_check_latest_frame : Z := 0x8478c.  Definition tfib_E_check_latest_frame : Z := 0x84868.  Definition tfib_A_check_keepalive_due : Z := 0x84868.  Definition tfib_E_check_keepalive_due : Z := 0x848bc.  Definition tfib_A_check_latest_sent : Z := 0x848bc.  Definition tfib_E_check_latest_sent : Z := 0x84bd0.  Definition tfib_A_check_latest_display : Z := 0x84bd0.  Definition tfib_E_check_latest_display : Z := 0x84c1c.  Definition tfib_A_m_rx : Z := 0x84c1c.  Definition tfib_E_m_rx : Z := 0x85040.  Definition tfib_A_host_offset : Z := 0x85040.  Definition tfib_E_host_offset : Z := 0x85100.  Definition tfib_A_desk_named : Z := 0x85100.  Definition tfib_E_desk_named : Z := 0x851d4.  Definition tfib_A_m_maybe_online : Z := 0x851d4.  Definition tfib_E_m_maybe_online : Z := 0x85224.  Definition tfib_A_m_set : Z := 0x85224.  Definition tfib_E_m_set : Z := 0x85320.  Definition tfib_A_check_state_online : Z := 0x85320.  Definition tfib_E_check_state_online : Z := 0x85358.  Definition tfib_A_check_inflight_acked : Z := 0x85358.  Definition tfib_E_check_inflight_acked : Z := 0x85408.  Definition tfib_A_check_inflight_lost : Z := 0x85408.  Definition tfib_E_check_inflight_lost : Z := 0x854bc.  Definition tfib_A_check_state_desk : Z := 0x854bc.  Definition tfib_E_check_state_desk : Z := 0x857cc.  Definition tfib_A_check_state_data : Z := 0x857cc.  Definition tfib_E_check_state_data : Z := 0x85998.  Definition tfib_A_build_and_receive : Z := 0x85998.  Definition tfib_E_build_and_receive : Z := 0x85d88.  Definition tfib_A_check_ack_settle : Z := 0x85d88.  Definition tfib_E_check_ack_settle : Z := 0x85dbc.  Definition tfib_A_check_state_settle : Z := 0x85dbc.  Definition tfib_E_check_state_settle : Z := 0x85fdc.  Definition tfib_A_check_inflight_settle : Z := 0x85fdc.  Definition tfib_E_check_inflight_settle : Z := 0x860a4.  Definition tfib_A_check_keepalive_settle : Z := 0x860a4.  Definition tfib_E_check_keepalive_settle : Z := 0x86104.  Definition tfib_A_check_latest_queue : Z := 0x86104.  Definition tfib_E_check_latest_queue : Z := 0x862b8.  Definition tfib_A_check_latest_drain : Z := 0x862b8.  Definition tfib_E_check_latest_drain : Z := 0x8640c.  Definition tfib_A_check_refusal_submit : Z := 0x8640c.  Definition tfib_E_check_refusal_submit : Z := 0x86568.  Definition tfib_A_check_latest_submit : Z := 0x86568.  Definition tfib_E_check_latest_submit : Z := 0x8658c.  Definition tfib_A_diginet_session_config_default : Z := 0x865f4.  Definition tfib_E_diginet_session_config_default : Z := 0x8680c.  Definition tfib_A_diginet_session_init : Z := 0x8680c.  Definition tfib_E_diginet_session_init : Z := 0x86a38.  Definition tfib_A_diginet_session_wake : Z := 0x86a38.  Definition tfib_E_diginet_session_wake : Z := 0x86ed4.  Definition tfib_A_send_control : Z := 0x86ed4.  Definition tfib_E_send_control : Z := 0x872cc.  Definition tfib_A_set_state : Z := 0x872cc.  Definition tfib_E_set_state : Z := 0x87648.  Definition tfib_A_diginet_session_close : Z := 0x87648.  Definition tfib_E_diginet_session_close : Z := 0x87784.  Definition tfib_A_diginet_session_rx : Z := 0x87784.  Definition tfib_E_diginet_session_rx : Z := 0x87cc8.  Definition tfib_A_on_announce : Z := 0x87cc8.  Definition tfib_E_on_announce : Z := 0x8858c.  Definition tfib_A_on_ack : Z := 0x8858c.  Definition tfib_E_on_ack : Z := 0x88a48.  Definition tfib_A_on_data : Z := 0x88a48.  Definition tfib_E_on_data : Z := 0x8909c.  Definition tfib_A_diginet_session_tick : Z := 0x8909c.  Definition tfib_E_diginet_session_tick : Z := 0x89aec.  Definition tfib_A_diginet_session_submit : Z := 0x89aec.  Definition tfib_E_diginet_session_submit : Z := 0x89d78.  Definition tfib_A_send_data : Z := 0x89d78.  Definition tfib_E_send_data : Z := 0x8a160.  Definition tfib_A_take : Z := 0x8a160.  Definition tfib_E_take : Z := 0x8a6c0.  Definition tfib_A_diginet_session_deadline : Z := 0x8a6c0.  Definition tfib_E_diginet_session_deadline : Z := 0x8aa98.  Definition tfib_A_diginet_session_poll : Z := 0x8aa98.  Definition tfib_E_diginet_session_poll : Z := 0x8ae8c.  Definition tfib_A_maybe_online : Z := 0x8ae8c.  Definition tfib_E_maybe_online : Z := 0x8afd8.  Definition tfib_A_diginet_sum16 : Z := 0x8afd8.  Definition tfib_E_diginet_sum16 : Z := 0x8b068.  Definition tfib_A_diginet_mac_is_digidesign : Z := 0x8b068.  Definition tfib_E_diginet_mac_is_digidesign : Z := 0x8b128.  Definition tfib_A_diginet_frame_is_keepalive : Z := 0x8b128.  Definition tfib_E_diginet_frame_is_keepalive : Z := 0x8b1f8.  Definition tfib_A_diginet_frame_parse : Z := 0x8b1f8.  Definition tfib_E_diginet_frame_parse : Z := 0x8b734.  Definition tfib_A_rd32 : Z := 0x8b734.  Definition tfib_E_rd32 : Z := 0x8b818.  Definition tfib_A_diginet_frame_build : Z := 0x8b818.  Definition tfib_E_diginet_frame_build : Z := 0x8bdec.  Definition tfib_A_diginet_announce_parse : Z := 0x8bdec.  Definition tfib_E_diginet_announce_parse : Z := 0x8bf5c.  Definition tfib_A_copy_strz : Z := 0x8bf5c.  Definition tfib_E_copy_strz : Z := 0x8c050.  Definition tfib_A_diginet_personality_from_name : Z := 0x8c050.  Definition tfib_E_diginet_personality_from_name : Z := 0x8c0fc.  Definition tfib_A_diginet_body_check : Z := 0x8c0fc.  Definition tfib_E_diginet_body_check : Z := 0x8c554.  Definition tfib_A_diginet_cursor_init : Z := 0x8c554.  Definition tfib_E_diginet_cursor_init : Z := 0x8c60c.  Definition tfib_A_diginet_msg_next : Z := 0x8c60c.  Definition tfib_E_diginet_msg_next : Z := 0x8cc1c.
Definition tfib_A_asan_stack_malloc_0 : Z := 0x3d6f4.  Definition tfib_E_asan_stack_malloc_0 : Z := 0x3d868.  Definition tfib_A_asan_stack_malloc_1 : Z := 0x3d868.  Definition tfib_E_asan_stack_malloc_1 : Z := 0x3d9f8.  Definition tfib_A_asan_stack_malloc_2 : Z := 0x3d9f8.  Definition tfib_E_asan_stack_malloc_2 : Z := 0x3db94.  Definition tfib_A_asan_stack_malloc_3 : Z := 0x3db94.  Definition tfib_E_asan_stack_malloc_3 : Z := 0x3dd40.  Definition tfib_A_asan_stack_malloc_5 : Z := 0x3dd40.  Definition tfib_E_asan_stack_malloc_5 : Z := 0x3df4c.

Definition tfib_A_asan_InitializeFlags : Z := 0x3e13c.  Definition tfib_E_asan_InitializeFlags : Z := 0x3f168.
Definition tfib_A_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x3f874.  Definition tfib_E_asan_register_globals_impl_RegisterGlobal_loop : Z := 0x40690.
Definition tfib_A_asan_unregister_globals_impl : Z := 0x40690.  Definition tfib_E_asan_unregister_globals_impl : Z := 0x40c5c.
Definition tfib_A_asan_UnpoisonBeforeMain_ctor : Z := 0x413b0.  Definition tfib_E_asan_UnpoisonBeforeMain_ctor : Z := 0x41620.
Definition tfib_A_strlen : Z := 0x42d20.  Definition tfib_E_strlen : Z := 0x42d24.
Definition tfib_A_strnlen : Z := 0x42d24.  Definition tfib_E_strnlen : Z := 0x42d28.
Definition tfib_A_strcmp : Z := 0x42d28.  Definition tfib_E_strcmp : Z := 0x42d2c.
Definition tfib_A_strchr : Z := 0x42d2c.  Definition tfib_E_strchr : Z := 0x42d30.
Definition tfib_A_memcmp : Z := 0x42d30.  Definition tfib_E_memcmp : Z := 0x42d34.
Definition tfib_A_memchr : Z := 0x42d38.  Definition tfib_E_memchr : Z := 0x42d3c.
Definition tfib_A_frexpl : Z := 0x42d3c.  Definition tfib_E_frexpl : Z := 0x42d40.
Definition tfib_A_read : Z := 0x42d40.  Definition tfib_E_read : Z := 0x42d44.
Definition tfib_A_fwrite : Z := 0x42d44.  Definition tfib_E_fwrite : Z := 0x42d48.
Definition tfib_A_time : Z := 0x42d48.  Definition tfib_E_time : Z := 0x42d4c.
Definition tfib_A_gmtime_r : Z := 0x42d4c.  Definition tfib_E_gmtime_r : Z := 0x42d50.
Definition tfib_A_vprintf : Z := 0x42d50.  Definition tfib_E_vprintf : Z := 0x42d54.
Definition tfib_A_vfprintf : Z := 0x42d54.  Definition tfib_E_vfprintf : Z := 0x42d58.
Definition tfib_A_vsnprintf : Z := 0x42d58.  Definition tfib_E_vsnprintf : Z := 0x42d5c.
Definition tfib_A_thunk_417bc : Z := 0x42d60.  Definition tfib_E_thunk_417bc : Z := 0x42d64.
Definition tfib_A_clock_gettime : Z := 0x42d64.  Definition tfib_E_clock_gettime : Z := 0x42d68.
Definition tfib_A_wcrtomb : Z := 0x42d68.  Definition tfib_E_wcrtomb : Z := 0x42d6c.
Definition tfib_A_wctomb : Z := 0x42d6c.  Definition tfib_E_wctomb : Z := 0x42d70.
Definition tfib_A_thunk_417cc : Z := 0x42d70.  Definition tfib_E_thunk_417cc : Z := 0x42d74.
Definition tfib_A_pthread_attr_getstack : Z := 0x42d78.  Definition tfib_E_pthread_attr_getstack : Z := 0x42d7c.
Definition tfib_A_tls_get_addr_thunk : Z := 0x42d7c.  Definition tfib_E_tls_get_addr_thunk : Z := 0x42d80.

Definition tfib_A_thunk_417dc : Z := 0x42d80.  Definition tfib_E_thunk_417dc : Z := 0x42d84.

Definition tfib_A_thunk_417e4 : Z := 0x42d84.  Definition tfib_E_thunk_417e4 : Z := 0x42d88.
Definition tfib_A_thunk_417e8 : Z := 0x42d88.  Definition tfib_E_thunk_417e8 : Z := 0x42d8c.
Definition tfib_A_thunk_417ec : Z := 0x42d8c.  Definition tfib_E_thunk_417ec : Z := 0x42d90.
Definition tfib_A_thunk_417f0 : Z := 0x42d90.  Definition tfib_E_thunk_417f0 : Z := 0x42d94.
Definition tfib_A_sem_timedwait : Z := 0x42d94.  Definition tfib_E_sem_timedwait : Z := 0x42d98.
Definition tfib_A_thunk_417f8 : Z := 0x42d98.  Definition tfib_E_thunk_417f8 : Z := 0x42d9c.
Definition tfib_A_pthread_setcancelstate : Z := 0x42d9c.  Definition tfib_E_pthread_setcancelstate : Z := 0x42da0.
Definition tfib_A_send : Z := 0x42da0.  Definition tfib_E_send : Z := 0x42da4.
Definition tfib_A_sendto : Z := 0x42da4.  Definition tfib_E_sendto : Z := 0x42da8.
Definition tfib_A_sigaltstack : Z := 0x42da8.  Definition tfib_E_sigaltstack : Z := 0x42dac.
Definition tfib_A_thunk_4180c : Z := 0x42dac.  Definition tfib_E_thunk_4180c : Z := 0x42db0.
Definition tfib_A_icpt_strlen : Z := 0x42db0.  Definition tfib_E_icpt_strlen : Z := 0x43044.
Definition tfib_A_icpt_strnlen : Z := 0x43044.  Definition tfib_E_icpt_strnlen : Z := 0x432d8.
Definition tfib_A_icpt_strcmp : Z := 0x432dc.  Definition tfib_E_icpt_strcmp : Z := 0x4380c.
Definition tfib_A_icpt_strchr : Z := 0x4380c.  Definition tfib_E_icpt_strchr : Z := 0x43aec.
Definition tfib_A_icpt_memcmp : Z := 0x44384.  Definition tfib_E_icpt_memcmp : Z := 0x44440.
Definition tfib_A_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x44440.  Definition tfib_E_icpt_memcmp_MemcmpInterceptorCommon_entry_bcmp_m : Z := 0x444fc.
Definition tfib_A_icpt_memchr : Z := 0x444fc.  Definition tfib_E_icpt_memchr : Z := 0x447cc.
Definition tfib_A_icpt_frexpl : Z := 0x447cc.  Definition tfib_E_icpt_frexpl : Z := 0x44a44.
Definition tfib_A_icpt_read : Z := 0x44a44.  Definition tfib_E_icpt_read : Z := 0x44cb4.
Definition tfib_A_icpt_fwrite : Z := 0x44cb4.  Definition tfib_E_icpt_fwrite : Z := 0x44f28.
Definition tfib_A_icpt_time : Z := 0x44f28.  Definition tfib_E_icpt_time : Z := 0x451c4.
Definition tfib_A_icpt_gmtime_r : Z := 0x453cc.  Definition tfib_E_icpt_gmtime_r : Z := 0x4560c.
Definition tfib_A_icpt_vprintf : Z := 0x4560c.  Definition tfib_E_icpt_vprintf : Z := 0x456a8.
Definition tfib_A_printf_common_format_interceptor : Z := 0x456a8.  Definition tfib_E_printf_common_format_interceptor : Z := 0x46170.
Definition tfib_A_icpt_vfprintf : Z := 0x46170.  Definition tfib_E_icpt_vfprintf : Z := 0x46224.
Definition tfib_A_icpt_vsnprintf : Z := 0x46224.  Definition tfib_E_icpt_vsnprintf : Z := 0x4653c.
Definition tfib_A_icpt_clock_gettime : Z := 0x466b8.  Definition tfib_E_icpt_clock_gettime : Z := 0x46910.
Definition tfib_A_icpt_wcrtomb : Z := 0x46910.  Definition tfib_E_icpt_wcrtomb : Z := 0x46e80.
Definition tfib_A_icpt_wctomb : Z := 0x46e80.  Definition tfib_E_icpt_wctomb : Z := 0x471dc.
Definition tfib_A_icpt_pthread_attr_getstack : Z := 0x472a8.  Definition tfib_E_icpt_pthread_attr_getstack : Z := 0x47690.
Definition tfib_A_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x4769c.  Definition tfib_E_icpt_tls_get_addr_DTLS_on_tls_get_addr_hook : Z := 0x47718.


Definition tfib_A_icpt_sem_timedwait : Z := 0x47924.  Definition tfib_E_icpt_sem_timedwait : Z := 0x47bbc.
Definition tfib_A_icpt_pthread_setcancelstate : Z := 0x47bec.  Definition tfib_E_icpt_pthread_setcancelstate : Z := 0x47e14.
Definition tfib_A_icpt_send : Z := 0x47e14.  Definition tfib_E_icpt_send : Z := 0x480c8.
Definition tfib_A_icpt_sendto : Z := 0x480c8.  Definition tfib_E_icpt_sendto : Z := 0x4838c.
Definition tfib_A_icpt_sigaltstack : Z := 0x4838c.  Definition tfib_E_icpt_sigaltstack : Z := 0x485e8.
Definition tfib_A_InitializeAsanInterceptors : Z := 0x486bc.  Definition tfib_E_InitializeAsanInterceptors : Z := 0x4886c.
Definition tfib_A_memset : Z := 0x523e4.  Definition tfib_E_memset : Z := 0x523e8.
Definition tfib_A_memcpy : Z := 0x523e8.  Definition tfib_E_memcpy : Z := 0x523ec.
Definition tfib_A_asan_memcpy : Z := 0x523ec.  Definition tfib_E_asan_memcpy : Z := 0x52888.
Definition tfib_A_asan_memset : Z := 0x52888.  Definition tfib_E_asan_memset : Z := 0x52ac8.
Definition tfib_A_icpt_memset : Z := 0x52ac8.  Definition tfib_E_icpt_memset : Z := 0x52db8.
Definition tfib_A_icpt_memcpy : Z := 0x52db8.  Definition tfib_E_icpt_memcpy : Z := 0x533a8.
Definition tfib_A_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x533a8.  Definition tfib_E_InitializeMemintrinsicInterceptors_tail_CHECK : Z := 0x533e0.
Definition tfib_A_InitializePlatformInterceptors : Z := 0x533e0.  Definition tfib_E_InitializePlatformInterceptors : Z := 0x533e4.
Definition tfib_A_InitializePlatformExceptionHandlers : Z := 0x533e4.  Definition tfib_E_InitializePlatformExceptionHandlers : Z := 0x533e8.
Definition tfib_A_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x533e8.  Definition tfib_E_asan_linux_PlatformShadowSetup_helper_CheckForEx : Z := 0x53448.
Definition tfib_A_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x53494.  Definition tfib_E_MemToShadow_CHECK_AddrIsInMem_instance : Z := 0x535d0.
Definition tfib_A_free : Z := 0x5373c.  Definition tfib_E_free : Z := 0x53740.
Definition tfib_A_malloc : Z := 0x53740.  Definition tfib_E_malloc : Z := 0x53744.
Definition tfib_A_icpt_free : Z := 0x53744.  Definition tfib_E_icpt_free : Z := 0x53914.
Definition tfib_A_icpt_malloc : Z := 0x53914.  Definition tfib_E_icpt_malloc : Z := 0x53a70.
Definition tfib_A_ReplaceSystemMalloc : Z := 0x53b3c.  Definition tfib_E_ReplaceSystemMalloc : Z := 0x53b40.
Definition tfib_A_SetCanPoisonMemory : Z := 0x545bc.  Definition tfib_E_SetCanPoisonMemory : Z := 0x545cc.
Definition tfib_A_CanPoisonMemory : Z := 0x545cc.  Definition tfib_E_CanPoisonMemory : Z := 0x545e0.
Definition tfib_A_PoisonShadow : Z := 0x545e0.  Definition tfib_E_PoisonShadow : Z := 0x54adc.
Definition tfib_A_MemToShadow_checked : Z := 0x54adc.  Definition tfib_E_MemToShadow_checked : Z := 0x54c18.
Definition tfib_A_asan_region_is_poisoned : Z := 0x54f68.  Definition tfib_E_asan_region_is_poisoned : Z := 0x552ac.
Definition tfib_A_AsanTSDInit : Z := 0x556cc.  Definition tfib_E_AsanTSDInit : Z := 0x55748.
Definition tfib_A_AsanTSDGet : Z := 0x55748.  Definition tfib_E_AsanTSDGet : Z := 0x55788.
Definition tfib_A_AsanTSDSet : Z := 0x55788.  Definition tfib_E_AsanTSDSet : Z := 0x557c8.
Definition tfib_A_PlatformTSDDtor : Z := 0x557c8.  Definition tfib_E_PlatformTSDDtor : Z := 0x5584c.
Definition tfib_A_InstallAtForkHandler : Z := 0x5584c.  Definition tfib_E_InstallAtForkHandler : Z := 0x55868.
Definition tfib_A_InstallAtExitCheckLeaks : Z := 0x558c8.  Definition tfib_E_InstallAtExitCheckLeaks : Z := 0x5590c.
Definition tfib_A_ReportDoubleFree : Z := 0x56938.  Definition tfib_E_ReportDoubleFree : Z := 0x56bc8.
Definition tfib_A_ReportGenericError : Z := 0x584a4.  Definition tfib_E_ReportGenericError : Z := 0x58d60.
Definition tfib_A_AsanInited : Z := 0x594ec.  Definition tfib_E_AsanInited : Z := 0x59504.
Definition tfib_A_asan_report_load1 : Z := 0x59504.  Definition tfib_E_asan_report_load1 : Z := 0x59554.
Definition tfib_A_asan_report_exp_load1 : Z := 0x59554.  Definition tfib_E_asan_report_exp_load1 : Z := 0x595a4.
Definition tfib_A_asan_report_load2 : Z := 0x595a4.  Definition tfib_E_asan_report_load2 : Z := 0x595f4.
Definition tfib_A_asan_report_exp_load2 : Z := 0x595f4.  Definition tfib_E_asan_report_exp_load2 : Z := 0x59644.
Definition tfib_A_asan_report_load4 : Z := 0x59644.  Definition tfib_E_asan_report_load4 : Z := 0x59694.
Definition tfib_A_asan_report_exp_load4 : Z := 0x59694.  Definition tfib_E_asan_report_exp_load4 : Z := 0x596e4.
Definition tfib_A_asan_report_load8 : Z := 0x596e4.  Definition tfib_E_asan_report_load8 : Z := 0x59734.
Definition tfib_A_asan_report_exp_load8 : Z := 0x59734.  Definition tfib_E_asan_report_exp_load8 : Z := 0x59784.
Definition tfib_A_asan_report_load16 : Z := 0x59784.  Definition tfib_E_asan_report_load16 : Z := 0x597d4.
Definition tfib_A_asan_report_exp_load16 : Z := 0x597d4.  Definition tfib_E_asan_report_exp_load16 : Z := 0x59824.
Definition tfib_A_asan_report_store1 : Z := 0x59824.  Definition tfib_E_asan_report_store1 : Z := 0x59874.
Definition tfib_A_asan_report_exp_store1 : Z := 0x59874.  Definition tfib_E_asan_report_exp_store1 : Z := 0x598c4.
Definition tfib_A_asan_report_store2 : Z := 0x598c4.  Definition tfib_E_asan_report_store2 : Z := 0x59914.
Definition tfib_A_asan_report_exp_store2 : Z := 0x59914.  Definition tfib_E_asan_report_exp_store2 : Z := 0x59964.
Definition tfib_A_asan_report_store4 : Z := 0x59964.  Definition tfib_E_asan_report_store4 : Z := 0x599b4.
Definition tfib_A_asan_report_exp_store4 : Z := 0x599b4.  Definition tfib_E_asan_report_exp_store4 : Z := 0x59a04.
Definition tfib_A_asan_report_store8 : Z := 0x59a04.  Definition tfib_E_asan_report_store8 : Z := 0x59a54.
Definition tfib_A_asan_report_exp_store8 : Z := 0x59a54.  Definition tfib_E_asan_report_exp_store8 : Z := 0x59aa4.
Definition tfib_A_asan_report_store16 : Z := 0x59aa4.  Definition tfib_E_asan_report_store16 : Z := 0x59af4.
Definition tfib_A_asan_report_exp_store16 : Z := 0x59af4.  Definition tfib_E_asan_report_exp_store16 : Z := 0x59b44.
Definition tfib_A_asan_report_load_n : Z := 0x59b44.  Definition tfib_E_asan_report_load_n : Z := 0x59b94.
Definition tfib_A_asan_report_exp_load_n : Z := 0x59b94.  Definition tfib_E_asan_report_exp_load_n : Z := 0x59be4.
Definition tfib_A_asan_report_store_n : Z := 0x59be4.  Definition tfib_E_asan_report_store_n : Z := 0x59c34.
Definition tfib_A_asan_report_exp_store_n : Z := 0x59c34.  Definition tfib_E_asan_report_exp_store_n : Z := 0x59c84.
Definition tfib_A_InitializeHighMemEnd : Z := 0x59c84.  Definition tfib_E_InitializeHighMemEnd : Z := 0x59d04.
Definition tfib_A_PrintAddressSpaceLayout : Z := 0x59d04.  Definition tfib_E_PrintAddressSpaceLayout : Z := 0x5a0b8.
Definition tfib_A_AsanInitInternal : Z := 0x5a148.  Definition tfib_E_AsanInitInternal : Z := 0x5a3fc.
Definition tfib_A_thunk_59674 : Z := 0x5a664.  Definition tfib_E_thunk_59674 : Z := 0x5a668.
Definition tfib_A_asan_init : Z := 0x5a668.  Definition tfib_E_asan_init : Z := 0x5a6fc.
Definition tfib_A_asan_version_mismatch_check_v8 : Z := 0x5a6fc.  Definition tfib_E_asan_version_mismatch_check_v8 : Z := 0x5a700.
Definition tfib_A_SealedTopOfMemory_check : Z := 0x5a700.  Definition tfib_E_SealedTopOfMemory_check : Z := 0x5a764.
Definition tfib_A_force_interface_symbols_dead_volatile_switch : Z := 0x5a964.  Definition tfib_E_force_interface_symbols_dead_volatile_switch : Z := 0x5ac8c.
Definition tfib_A_InitializeShadowMemory : Z := 0x5ae6c.  Definition tfib_E_InitializeShadowMemory : Z := 0x5b174.
Definition tfib_A_SetMallocContextSize : Z := 0x5b174.  Definition tfib_E_SetMallocContextSize : Z := 0x5b184.
Definition tfib_A_GetMallocContextSize : Z := 0x5b184.  Definition tfib_E_GetMallocContextSize : Z := 0x5b194.
Definition tfib_A_BufferedStackTrace_UnwindImpl_asan : Z := 0x5b194.  Definition tfib_E_BufferedStackTrace_UnwindImpl_asan : Z := 0x5b2e4.
Definition tfib_A_GetCurrentThreadStats : Z := 0x5bdc8.  Definition tfib_E_GetCurrentThreadStats : Z := 0x5be00.
Definition tfib_A_asan_suppression_kinds_getter_3_insns : Z := 0x5c0a8.  Definition tfib_E_asan_suppression_kinds_getter_3_insns : Z := 0x5c0b4.
Definition tfib_A_asan_InitializeSuppressions : Z := 0x5c0b4.  Definition tfib_E_asan_InitializeSuppressions : Z := 0x5c140.
Definition tfib_A_IsInterceptorSuppressed : Z := 0x5c140.  Definition tfib_E_IsInterceptorSuppressed : Z := 0x5c1a8.
Definition tfib_A_HaveStackTraceBasedSuppressions : Z := 0x5c1a8.  Definition tfib_E_HaveStackTraceBasedSuppressions : Z := 0x5c220.
Definition tfib_A_IsODRViolationSuppressed : Z := 0x5c220.  Definition tfib_E_IsODRViolationSuppressed : Z := 0x5c288.
Definition tfib_A_asan_thread_tiny_getter_3_insns : Z := 0x5c660.  Definition tfib_E_asan_thread_tiny_getter_3_insns : Z := 0x5c66c.
Definition tfib_A_AsanThread_Create : Z := 0x5c7ec.  Definition tfib_E_AsanThread_Create : Z := 0x5c988.
Definition tfib_A_AsanThread_Destroy_TSDDtor : Z := 0x5c9e4.  Definition tfib_E_AsanThread_Destroy_TSDDtor : Z := 0x5cbfc.
Definition tfib_A_GetCurrentThread : Z := 0x5cbfc.  Definition tfib_E_GetCurrentThread : Z := 0x5cc1c.
Definition tfib_A_AsanThread_stack_top : Z := 0x5cdc0.  Definition tfib_E_AsanThread_stack_top : Z := 0x5ce18.
Definition tfib_A_AsanThread_stack_bottom : Z := 0x5ce18.  Definition tfib_E_AsanThread_stack_bottom : Z := 0x5ce70.
Definition tfib_A_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5ce70.  Definition tfib_E_AsanThread_AsyncSignalSafeLazyInitFakeStack : Z := 0x5d0a0.
Definition tfib_A_AsanThread_Init : Z := 0x5d0a0.  Definition tfib_E_AsanThread_Init : Z := 0x5d494.
Definition tfib_A_CreateMainThread : Z := 0x5d5d4.  Definition tfib_E_CreateMainThread : Z := 0x5d6e4.
Definition tfib_A_SetCurrentThread : Z := 0x5d6e4.  Definition tfib_E_SetCurrentThread : Z := 0x5d7c4.
Definition tfib_A_MemToShadow_checked_instance_3 : Z := 0x5d9c8.  Definition tfib_E_MemToShadow_checked_instance_3 : Z := 0x5db04.
Definition tfib_A_weak_default_hook_ret : Z := 0x5e7d8.  Definition tfib_E_weak_default_hook_ret : Z := 0x5e7dc.
Definition tfib_A_SetLowLevelAllocateMinAlignment : Z := 0x5f114.  Definition tfib_E_SetLowLevelAllocateMinAlignment : Z := 0x5f160.
Definition tfib_A_SetLowLevelAllocateCallback : Z := 0x5f160.  Definition tfib_E_SetLowLevelAllocateCallback : Z := 0x5f16c.
Definition tfib_A_SetAllocatorMayReturnNull : Z := 0x5f19c.  Definition tfib_E_SetAllocatorMayReturnNull : Z := 0x5f1a8.
Definition tfib_A_PrintHintAllocatorCannotReturnNull : Z := 0x5f1a8.  Definition tfib_E_PrintHintAllocatorCannotReturnNull : Z := 0x5f1b4.
Definition tfib_A_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5f1d0.  Definition tfib_E_InternalAllocator_CombinedAllocator_Allocate_int : Z := 0x5f49c.
Definition tfib_A_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f49c.  Definition tfib_E_InternalAllocator_LargeMmapAllocator_Allocate : Z := 0x5f85c.
Definition tfib_A_SetSealedStartFrame_sealed_patch : Z := 0x607b8.  Definition tfib_E_SetSealedStartFrame_sealed_patch : Z := 0x607c4.
Definition tfib_A_ReportMmapFailureAndDie : Z := 0x607c4.  Definition tfib_E_ReportMmapFailureAndDie : Z := 0x6089c.
Definition tfib_A_ReportMunmapFailureAndDie : Z := 0x6089c.  Definition tfib_E_ReportMunmapFailureAndDie : Z := 0x60938.
Definition tfib_A_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60e5c.  Definition tfib_E_IncreaseTotalMmap_CHECK_part_mmap_limit_mb_check : Z := 0x60ea0.
Definition tfib_A_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x61118.  Definition tfib_E_ReadBinaryNameCached_CacheBinaryName_body : Z := 0x6122c.
Definition tfib_A_RunMallocHooks : Z := 0x613d0.  Definition tfib_E_RunMallocHooks : Z := 0x61488.
Definition tfib_A_sanitizer_malloc_hook_weak_default_ret : Z := 0x61488.  Definition tfib_E_sanitizer_malloc_hook_weak_default_ret : Z := 0x6148c.
Definition tfib_A_RunFreeHooks : Z := 0x6148c.  Definition tfib_E_RunFreeHooks : Z := 0x61538.
Definition tfib_A_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x6187c.  Definition tfib_E_ReportFile_SetReportPath_body_stderr_stdout_keyw : Z := 0x61abc.
Definition tfib_A_sanitizer_set_report_path : Z := 0x620b8.  Definition tfib_E_sanitizer_set_report_path : Z := 0x620d0.
Definition tfib_A_FlagParser_parse_flag_ParseString_core : Z := 0x63ce0.  Definition tfib_E_FlagParser_parse_flag_ParseString_core : Z := 0x63ff0.
Definition tfib_A_FlagParser_ParseStringFromEnv : Z := 0x63ff0.  Definition tfib_E_FlagParser_ParseStringFromEnv : Z := 0x64134.
Definition tfib_A_FlagParser_ParseString : Z := 0x64134.  Definition tfib_E_FlagParser_ParseString : Z := 0x64228.
Definition tfib_A_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x6441c.  Definition tfib_E_FlagParser_alloc_helper_LowLevelAlloc : Z := 0x6445c.
Definition tfib_A_internal_atoll : Z := 0x6445c.  Definition tfib_E_internal_atoll : Z := 0x64548.
Definition tfib_A_internal_simple_strtoll : Z := 0x64548.  Definition tfib_E_internal_simple_strtoll : Z := 0x646a4.
Definition tfib_A_internal_memchr : Z := 0x646a4.  Definition tfib_E_internal_memchr : Z := 0x646c4.
Definition tfib_A_internal_memcmp : Z := 0x646c4.  Definition tfib_E_internal_memcmp : Z := 0x646fc.
Definition tfib_A_internal_memcpy : Z := 0x646fc.  Definition tfib_E_internal_memcpy : Z := 0x64720.
Definition tfib_A_internal_memmove : Z := 0x64720.  Definition tfib_E_internal_memmove : Z := 0x64778.
Definition tfib_A_internal_memset : Z := 0x64778.  Definition tfib_E_internal_memset : Z := 0x647d8.
Definition tfib_A_internal_strcspn : Z := 0x647d8.  Definition tfib_E_internal_strcspn : Z := 0x6482c.
Definition tfib_A_internal_strdup : Z := 0x64860.  Definition tfib_E_internal_strdup : Z := 0x648cc.
Definition tfib_A_internal_strlen : Z := 0x648cc.  Definition tfib_E_internal_strlen : Z := 0x648e8.
Definition tfib_A_internal_strchrnul : Z := 0x64978.  Definition tfib_E_internal_strchrnul : Z := 0x649c0.
Definition tfib_A_internal_strrchr : Z := 0x649c0.  Definition tfib_E_internal_strrchr : Z := 0x64a00.
Definition tfib_A_internal_strnlen : Z := 0x64b30.  Definition tfib_E_internal_strnlen : Z := 0x64b60.
Definition tfib_A_internal_strncpy : Z := 0x64ba4.  Definition tfib_E_internal_strncpy : Z := 0x64c14.
Definition tfib_A_internal_strstr : Z := 0x64c14.  Definition tfib_E_internal_strstr : Z := 0x64ca8.
Definition tfib_A_mem_is_zero : Z := 0x64ca8.  Definition tfib_E_mem_is_zero : Z := 0x64d5c.
Definition tfib_A_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64d5c.  Definition tfib_E_internal_sigprocmask_raw_rt_sigprocmask : Z := 0x64d6c.
Definition tfib_A_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64d6c.  Definition tfib_E_BlockSignals_ScopedBlockSignals_ctor_CHECK_inter : Z := 0x64f4c.
Definition tfib_A_internal_iserror : Z := 0x64f58.  Definition tfib_E_internal_iserror : Z := 0x64f78.
Definition tfib_A_internal_mmap : Z := 0x64f78.  Definition tfib_E_internal_mmap : Z := 0x64f84.
Definition tfib_A_internal_munmap : Z := 0x64f84.  Definition tfib_E_internal_munmap : Z := 0x64f90.
Definition tfib_A_internal_mprotect : Z := 0x64f90.  Definition tfib_E_internal_mprotect : Z := 0x64fa0.
Definition tfib_A_internal_madvise : Z := 0x64fa0.  Definition tfib_E_internal_madvise : Z := 0x64fcc.
Definition tfib_A_internal_close : Z := 0x64fcc.  Definition tfib_E_internal_close : Z := 0x64fd8.
Definition tfib_A_internal_open_openat_AT_FDCWD : Z := 0x64fd8.  Definition tfib_E_internal_open_openat_AT_FDCWD : Z := 0x64ffc.
Definition tfib_A_internal_read : Z := 0x64ffc.  Definition tfib_E_internal_read : Z := 0x65034.
Definition tfib_A_internal_write : Z := 0x65034.  Definition tfib_E_internal_write : Z := 0x6506c.
Definition tfib_A_internal_ftruncate : Z := 0x6506c.  Definition tfib_E_internal_ftruncate : Z := 0x650a4.
Definition tfib_A_internal_dup : Z := 0x650a4.  Definition tfib_E_internal_dup : Z := 0x650b0.
Definition tfib_A_internal_dup2_dup3 : Z := 0x650b0.  Definition tfib_E_internal_dup2_dup3 : Z := 0x650c0.
Definition tfib_A_internal_unlink_unlinkat : Z := 0x650c0.  Definition tfib_E_internal_unlink_unlinkat : Z := 0x650d8.
Definition tfib_A_internal_sched_yield : Z := 0x650d8.  Definition tfib_E_internal_sched_yield : Z := 0x650e4.
Definition tfib_A_internal_usleep_internal_sleep_nanosleep : Z := 0x650e4.  Definition tfib_E_internal_usleep_internal_sleep_nanosleep : Z := 0x65130.
Definition tfib_A_internal_execve : Z := 0x65130.  Definition tfib_E_internal_execve : Z := 0x6513c.
Definition tfib_A_internal_exit_exit_group : Z := 0x6513c.  Definition tfib_E_internal_exit_exit_group : Z := 0x65150.
Definition tfib_A_FileExists_newfstatat : Z := 0x65150.  Definition tfib_E_FileExists_newfstatat : Z := 0x651d0.
Definition tfib_A_DirExists_newfstatat : Z := 0x651d0.  Definition tfib_E_DirExists_newfstatat : Z := 0x65234.
Definition tfib_A_GetTid_gettid : Z := 0x65234.  Definition tfib_E_GetTid_gettid : Z := 0x65240.
Definition tfib_A_GetEnv : Z := 0x65240.  Definition tfib_E_GetEnv : Z := 0x65370.
Definition tfib_A_FutexWait : Z := 0x65474.  Definition tfib_E_FutexWait : Z := 0x65498.
Definition tfib_A_FutexWake : Z := 0x65498.  Definition tfib_E_FutexWake : Z := 0x654bc.
Definition tfib_A_internal_ptrace : Z := 0x654bc.  Definition tfib_E_internal_ptrace : Z := 0x654c8.
Definition tfib_A_internal_waitpid_wait4 : Z := 0x654c8.  Definition tfib_E_internal_waitpid_wait4 : Z := 0x654d8.
Definition tfib_A_internal_getpid : Z := 0x654d8.  Definition tfib_E_internal_getpid : Z := 0x654e4.
Definition tfib_A_internal_getppid : Z := 0x654e4.  Definition tfib_E_internal_getppid : Z := 0x654f0.
Definition tfib_A_internal_prctl : Z := 0x654f0.  Definition tfib_E_internal_prctl : Z := 0x654fc.
Definition tfib_A_internal_sigaltstack : Z := 0x654fc.  Definition tfib_E_internal_sigaltstack : Z := 0x65508.
Definition tfib_A_internal_fork_clone : Z := 0x65508.  Definition tfib_E_internal_fork_clone : Z := 0x65520.
Definition tfib_A_internal_sigaction_norestorer_rt_sigaction : Z := 0x65520.  Definition tfib_E_internal_sigaction_norestorer_rt_sigaction : Z := 0x6564c.
Definition tfib_A_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65d8c.  Definition tfib_E_GetMaxUserVirtualAddress_sealed_from_the_start_f : Z := 0x65ea4.
Definition tfib_A_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65eac.  Definition tfib_E_ReadBinaryName_readlinkat_proc_self_exe : Z := 0x65f58.
Definition tfib_A_ReadLongProcessName_proc_self_cmdline : Z := 0x65f58.  Definition tfib_E_ReadLongProcessName_proc_self_cmdline : Z := 0x66078.
Definition tfib_A_internal_clone_CHECK_child_stack_16 : Z := 0x66140.  Definition tfib_E_internal_clone_CHECK_child_stack_16 : Z := 0x661c0.
Definition tfib_A_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x6621c.  Definition tfib_E_internal_start_thread_BlockSignals_variant_rt_si : Z := 0x662e8.
Definition tfib_A_thunk_653ec : Z := 0x663e4.  Definition tfib_E_thunk_653ec : Z := 0x663e8.
Definition tfib_A_CheckASLR : Z := 0x663e8.  Definition tfib_E_CheckASLR : Z := 0x663ec.
Definition tfib_A_GetMmapGranularity_thunk : Z := 0x66638.  Definition tfib_E_GetMmapGranularity_thunk : Z := 0x6663c.
Definition tfib_A_internal_errno_mapping_helper : Z := 0x6663c.  Definition tfib_E_internal_errno_mapping_helper : Z := 0x66648.
Definition tfib_A_MmapOrDie : Z := 0x66648.  Definition tfib_E_MmapOrDie : Z := 0x66754.
Definition tfib_A_MmapNamed_internal_mmap_name_helper : Z := 0x66754.  Definition tfib_E_MmapNamed_internal_mmap_name_helper : Z := 0x667c8.
Definition tfib_A_UnmapOrDie : Z := 0x667c8.  Definition tfib_E_UnmapOrDie : Z := 0x66844.
Definition tfib_A_MmapOrDieOnFatalError : Z := 0x66844.  Definition tfib_E_MmapOrDieOnFatalError : Z := 0x66954.
Definition tfib_A_MmapNoReserveOrDie : Z := 0x66b80.  Definition tfib_E_MmapNoReserveOrDie : Z := 0x66c84.
Definition tfib_A_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x66c90.  Definition tfib_E_MmapFixed_named_may_die_core_MmapNamed_IncreaseT : Z := 0x66e08.
Definition tfib_A_thunk_66008 : Z := 0x67000.  Definition tfib_E_thunk_66008 : Z := 0x67004.
Definition tfib_A_GetNamedMappingFd_MmapNamed : Z := 0x67324.  Definition tfib_E_GetNamedMappingFd_MmapNamed : Z := 0x67530.
Definition tfib_A_SetPrintfAndReportCallback : Z := 0x67ae8.  Definition tfib_E_SetPrintfAndReportCallback : Z := 0x67af4.
Definition tfib_A_Printf : Z := 0x67af8.  Definition tfib_E_Printf : Z := 0x67b44.
Definition tfib_A_SharedPrintfCode : Z := 0x67b44.  Definition tfib_E_SharedPrintfCode : Z := 0x67ba0.
Definition tfib_A_Report : Z := 0x67ba0.  Definition tfib_E_Report : Z := 0x67bec.
Definition tfib_A_SuppressionContext_ctor : Z := 0x696e4.  Definition tfib_E_SuppressionContext_ctor : Z := 0x69740.
Definition tfib_A_SuppressionContext_ParseFromFile : Z := 0x69740.  Definition tfib_E_SuppressionContext_ParseFromFile : Z := 0x6997c.
Definition tfib_A_SuppressionContext_Parse : Z := 0x6997c.  Definition tfib_E_SuppressionContext_Parse : Z := 0x69ca0.
Definition tfib_A_ThreadRegistry_CreateThread : Z := 0x6a950.  Definition tfib_E_ThreadRegistry_CreateThread : Z := 0x6adc8.
Definition tfib_A_ThreadRegistry_StartThread : Z := 0x6b688.  Definition tfib_E_ThreadRegistry_StartThread : Z := 0x6b9ac.
Definition tfib_A_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6b9b4.  Definition tfib_E_ThreadRegistry_ThreadArgRetval_vector_growth : Z := 0x6bab8.
Definition tfib_A_AddDieCallback : Z := 0x6c268.  Definition tfib_E_AddDieCallback : Z := 0x6c2f0.
Definition tfib_A_Die : Z := 0x6c3b4.  Definition tfib_E_Die : Z := 0x6c474.
Definition tfib_A_SetCheckUnwindCallback : Z := 0x6c474.  Definition tfib_E_SetCheckUnwindCallback : Z := 0x6c480.
Definition tfib_A_CheckFailed : Z := 0x6c480.  Definition tfib_E_CheckFailed : Z := 0x6c538.
Definition tfib_A_ReservedAddressRange_InitAligned : Z := 0x6cb90.  Definition tfib_E_ReservedAddressRange_InitAligned : Z := 0x6cc88.
Definition tfib_A_ReserveShadowMemoryRange : Z := 0x6cc88.  Definition tfib_E_ReserveShadowMemoryRange : Z := 0x6cdb4.
Definition tfib_A_sanitizer_common_libcdep_static_ctor_background : Z := 0x6cfdc.  Definition tfib_E_sanitizer_common_libcdep_static_ctor_background : Z := 0x6d058.
Definition tfib_A_GetThreadStackTopAndBottom : Z := 0x6d08c.  Definition tfib_E_GetThreadStackTopAndBottom : Z := 0x6d374.
Definition tfib_A_weak_default_hook_ret_2 : Z := 0x6d374.  Definition tfib_E_weak_default_hook_ret_2 : Z := 0x6d378.
Definition tfib_A_AndroidLogInit : Z := 0x6dc1c.  Definition tfib_E_AndroidLogInit : Z := 0x6dc20.
Definition tfib_A_MonotonicNanoTime_NanoTime : Z := 0x6dc50.  Definition tfib_E_MonotonicNanoTime_NanoTime : Z := 0x6dc98.
Definition tfib_A_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6dc98.  Definition tfib_E_MapDynamicShadow_MmapAlignedOrDieOnFatalError : Z := 0x6dee4.
Definition tfib_A_weak_default_hook_ret_3 : Z := 0x6dee4.  Definition tfib_E_weak_default_hook_ret_3 : Z := 0x6dee8.
Definition tfib_A_InternalMmapVector_Realloc_2 : Z := 0x6dff4.  Definition tfib_E_InternalMmapVector_Realloc_2 : Z := 0x6e0f8.
Definition tfib_A_thunk_6d37c : Z := 0x6e374.  Definition tfib_E_thunk_6d37c : Z := 0x6e378.
Definition tfib_A_DisableCoreDumperIfNecessary : Z := 0x6e43c.  Definition tfib_E_DisableCoreDumperIfNecessary : Z := 0x6e4dc.
Definition tfib_A_internal_pthread_weak_stub_ret : Z := 0x6e528.  Definition tfib_E_internal_pthread_weak_stub_ret : Z := 0x6e52c.
Definition tfib_A_SetAlternateSignalStack : Z := 0x6e568.  Definition tfib_E_SetAlternateSignalStack : Z := 0x6e62c.
Definition tfib_A_UnsetAlternateSignalStack : Z := 0x6e62c.  Definition tfib_E_UnsetAlternateSignalStack : Z := 0x6e6b4.
Definition tfib_A_InstallDeadlySignalHandlers : Z := 0x6e6b4.  Definition tfib_E_InstallDeadlySignalHandlers : Z := 0x6e72c.
Definition tfib_A_MaybeInstallSigaction : Z := 0x6e72c.  Definition tfib_E_MaybeInstallSigaction : Z := 0x6e810.
Definition tfib_A_IsAccessibleMemoryRange : Z := 0x6e8cc.  Definition tfib_E_IsAccessibleMemoryRange : Z := 0x6ea00.
Definition tfib_A_StackStore_Store_BlockInfo_helper : Z := 0x70cc4.  Definition tfib_E_StackStore_Store_BlockInfo_helper : Z := 0x70de8.
Definition tfib_A_StackStore_Alloc : Z := 0x70de8.  Definition tfib_E_StackStore_Alloc : Z := 0x70f1c.
Definition tfib_A_StackStore_BlockInfo_Create_Map : Z := 0x717d0.  Definition tfib_E_StackStore_BlockInfo_Create_Map : Z := 0x71884.
Definition tfib_A_StackDepotNode_store_hash_helper : Z := 0x72fd8.  Definition tfib_E_StackDepotNode_store_hash_helper : Z := 0x73034.
Definition tfib_A_StackDepotPut : Z := 0x732c0.  Definition tfib_E_StackDepotPut : Z := 0x732e0.
Definition tfib_A_StackDepotBase_Put : Z := 0x732e0.  Definition tfib_E_StackDepotBase_Put : Z := 0x73564.
Definition tfib_A_StackTrace_GetCurrentPc : Z := 0x73c44.  Definition tfib_E_StackTrace_GetCurrentPc : Z := 0x73c4c.
Definition tfib_A_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73c4c.  Definition tfib_E_BufferedStackTrace_Init_UnwindFast_frame_pointer : Z := 0x73dac.
Definition tfib_A_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x742a8.  Definition tfib_E_BufferedStackTrace_Unwind_FAST_frame_pointer_wal : Z := 0x743c0.
Definition tfib_A_thunk_762d8 : Z := 0x7740c.  Definition tfib_E_thunk_762d8 : Z := 0x77410.
Definition tfib_A_thunk_77ab0 : Z := 0x78be4.  Definition tfib_E_thunk_77ab0 : Z := 0x78be8.
Definition tfib_A_BufferedStackTrace_UnwindSlow : Z := 0x7a610.  Definition tfib_E_BufferedStackTrace_UnwindSlow : Z := 0x7a6cc.
Definition tfib_A_Unwind_Trace_callback : Z := 0x7a6cc.  Definition tfib_E_Unwind_Trace_callback : Z := 0x7a7a4.
Definition tfib_A_lsan_flags_init_helper : Z := 0x7ad44.  Definition tfib_E_lsan_flags_init_helper : Z := 0x7ad88.
Definition tfib_A_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7ad88.  Definition tfib_E_lsan_RegisterLsanFlags_lsan_Flags_SetDefaults_Re : Z := 0x7b158.
Definition tfib_A_lsan_InitCommonLsan : Z := 0x7b428.  Definition tfib_E_lsan_InitCommonLsan : Z := 0x7b4e0.
Definition tfib_A_thunk_7b6f8 : Z := 0x7c838.  Definition tfib_E_thunk_7b6f8 : Z := 0x7c83c.
Definition tfib_A_lsan_register_root_region : Z := 0x7d444.  Definition tfib_E_lsan_register_root_region : Z := 0x7d774.
Definition tfib_A_lsan_unregister_root_region : Z := 0x7d774.  Definition tfib_E_lsan_unregister_root_region : Z := 0x7dbfc.
Definition tfib_A_lsan_ubsan_default_options_weak_stub : Z := 0x7dbfc.  Definition tfib_E_lsan_ubsan_default_options_weak_stub : Z := 0x7dc08.
Definition tfib_A_ubsan_InitializeSuppressions : Z := 0x80b5c.  Definition tfib_E_ubsan_InitializeSuppressions : Z := 0x80bd8.
Definition tfib_A_ubsan_InitAsPlugin : Z := 0x80bd8.  Definition tfib_E_ubsan_InitAsPlugin : Z := 0x80c88.
Definition tfib_A_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80ca0.  Definition tfib_E_ubsan_RegisterUbsanFlags_InitializeFlags_part : Z := 0x80de8.
Definition tfib_A_ubsan_default_options_weak_returns : Z := 0x80de8.  Definition tfib_E_ubsan_default_options_weak_returns : Z := 0x80df4.
Definition tfib_A_asan_default_options_cli_c : Z := 0x80df4.  Definition tfib_E_asan_default_options_cli_c : Z := 0x80e00.
Definition tfib_A_main : Z := 0x80e00.  Definition tfib_E_main : Z := 0x810c4.
Definition tfib_A_target_alloc_init : Z := 0x810c4.  Definition tfib_E_target_alloc_init : Z := 0x810c8.
Definition tfib_A_target_alloc_count : Z := 0x810c8.  Definition tfib_E_target_alloc_count : Z := 0x810d0.
Definition tfib_A_target_run : Z := 0x810d0.  Definition tfib_E_target_run : Z := 0x81228.
Definition tfib_A_emit_printf : Z := 0x81258.  Definition tfib_E_emit_printf : Z := 0x812a0.
Definition tfib_A_LLVMFuzzerTestOneInput : Z := 0x812a0.  Definition tfib_E_LLVMFuzzerTestOneInput : Z := 0x82ffc.

Definition tfib_A_asan_module_ctor : Z := 0x8658c.  Definition tfib_E_asan_module_ctor : Z := 0x865c4.








Definition tfib_A_asan_module_dtor : Z := 0x865c4.  Definition tfib_E_asan_module_dtor : Z := 0x865f4.






Definition tfib_A_extenddftf2 : Z := 0x8cc2c.  Definition tfib_E_extenddftf2 : Z := 0x8cdbc.
Definition tfib_A_sysconf : Z := 0x92a0c.  Definition tfib_E_sysconf : Z := 0x92c34.
Definition tfib_A_init : Z := 0x92c34.  Definition tfib_E_init : Z := 0x92c38.
Definition tfib_A_init_libc : Z := 0x92c38.  Definition tfib_E_init_libc : Z := 0x92e64.
Definition tfib_A_libc_start_init : Z := 0x92e64.  Definition tfib_E_libc_start_init : Z := 0x92eb0.
Definition tfib_A_libc_start_main : Z := 0x92eb0.  Definition tfib_E_libc_start_main : Z := 0x92f10.
Definition tfib_A_libc_start_main_stage2 : Z := 0x92f10.  Definition tfib_E_libc_start_main_stage2 : Z := 0x92f58.
Definition tfib_A_init_tls : Z := 0x93030.  Definition tfib_E_init_tls : Z := 0x932e0.
Definition tfib_A_init_ssp : Z := 0x932e0.  Definition tfib_E_init_ssp : Z := 0x93340.
Definition tfib_A_stack_chk_fail : Z := 0x93340.  Definition tfib_E_stack_chk_fail : Z := 0x93348.
Definition tfib_A_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x93390.  Definition tfib_E_musl_sigaction_abort_area_fn_rt_sigaction_tkill : Z := 0x93424.
Definition tfib_A_Exit : Z := 0x93424.  Definition tfib_E_Exit : Z := 0x93440.
Definition tfib_A_funcs_on_exit : Z := 0x93470.  Definition tfib_E_funcs_on_exit : Z := 0x93538.
Definition tfib_A_libc_exit_fini : Z := 0x93608.  Definition tfib_E_libc_exit_fini : Z := 0x93654.
Definition tfib_A_exit : Z := 0x93654.  Definition tfib_E_exit : Z := 0x936c8.
Definition tfib_A_open : Z := 0x938c8.  Definition tfib_E_open : Z := 0x939ac.
Definition tfib_A_syscall_ret : Z := 0x939ac.  Definition tfib_E_syscall_ret : Z := 0x939e4.
Definition tfib_A_musl_dl_iterate_phdr_static : Z := 0x939e4.  Definition tfib_E_musl_dl_iterate_phdr_static : Z := 0x93b8c.
Definition tfib_A_calloc : Z := 0x94150.  Definition tfib_E_calloc : Z := 0x94288.
Definition tfib_A_libc_malloc_j_libc_malloc_impl : Z := 0x94288.  Definition tfib_E_libc_malloc_j_libc_malloc_impl : Z := 0x9428c.
Definition tfib_A_libc_free : Z := 0x9428c.  Definition tfib_E_libc_free : Z := 0x94458.
Definition tfib_A_get_meta : Z := 0x94458.  Definition tfib_E_get_meta : Z := 0x94568.
Definition tfib_A_alloc_meta : Z := 0x94940.  Definition tfib_E_alloc_meta : Z := 0x94c18.
Definition tfib_A_libc_malloc_impl : Z := 0x94c18.  Definition tfib_E_libc_malloc_impl : Z := 0x94f88.
Definition tfib_A_alloc_slot : Z := 0x94f88.  Definition tfib_E_alloc_slot : Z := 0x9582c.
Definition tfib_A_enframe : Z := 0x9582c.  Definition tfib_E_enframe : Z := 0x9597c.
Definition tfib_A_malloc_allzerop : Z := 0x9597c.  Definition tfib_E_malloc_allzerop : Z := 0x95af4.
Definition tfib_A_getrlimit : Z := 0x977a4.  Definition tfib_E_getrlimit : Z := 0x9789c.
Definition tfib_A_getrusage : Z := 0x9789c.  Definition tfib_E_getrusage : Z := 0x978c4.
Definition tfib_A_setrlimit : Z := 0x978c4.  Definition tfib_E_setrlimit : Z := 0x9798c.
Definition tfib_A_mmap : Z := 0x97db4.  Definition tfib_E_mmap : Z := 0x97ea0.
Definition tfib_A_mprotect : Z := 0x97ea0.  Definition tfib_E_mprotect : Z := 0x97ee8.
Definition tfib_A_munmap : Z := 0x97fbc.  Definition tfib_E_munmap : Z := 0x98004.
Definition tfib_A_sched_yield : Z := 0x982c8.  Definition tfib_E_sched_yield : Z := 0x982ec.
Definition tfib_A_raise_tkill_path : Z := 0x98348.  Definition tfib_E_raise_tkill_path : Z := 0x983c0.
Definition tfib_A_musl_sigaltstack : Z := 0x9868c.  Definition tfib_E_musl_sigaltstack : Z := 0x98718.

Definition tfib_A_lockfile : Z := 0x98d58.  Definition tfib_E_lockfile : Z := 0x98e54.
Definition tfib_A_unlockfile : Z := 0x98e54.  Definition tfib_E_unlockfile : Z := 0x98eb4.



Definition tfib_A_stdio_read : Z := 0x98a44.  Definition tfib_E_stdio_read : Z := 0x98b5c.
Definition tfib_A_stdio_write : Z := 0x98b64.  Definition tfib_E_stdio_write : Z := 0x98cf4.
Definition tfib_A_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x98a14.  Definition tfib_E_aio_close_stub_j_ret_used_by_close_stdio_close : Z := 0x98a18.
Definition tfib_A_stdio_close : Z := 0x98a18.  Definition tfib_E_stdio_close : Z := 0x98a44.
Definition tfib_A_fwritex : Z := 0x992e8.  Definition tfib_E_fwritex : Z := 0x99420.
Definition tfib_A_musl_fwrite : Z := 0x99420.  Definition tfib_E_musl_fwrite : Z := 0x994d8.
Definition tfib_A_towrite : Z := 0x994d8.  Definition tfib_E_towrite : Z := 0x9952c.
Definition tfib_A_stdio_exit : Z := 0x99144.  Definition tfib_E_stdio_exit : Z := 0x992e8.
Definition tfib_A_ofl_lock : Z := 0x9952c.  Definition tfib_E_ofl_lock : Z := 0x9955c.

Definition tfib_A_musl_vfprintf : Z := 0x996a8.  Definition tfib_E_musl_vfprintf : Z := 0x99858.
Definition tfib_A_printf_core : Z := 0x99858.  Definition tfib_E_printf_core : Z := 0x9a688.
Definition tfib_A_pop_arg : Z := 0x9a688.  Definition tfib_E_pop_arg : Z := 0x9a7bc.
Definition tfib_A_pad : Z := 0x9a7bc.  Definition tfib_E_pad : Z := 0x9a890.
Definition tfib_A_fmt_fp : Z := 0x9a890.  Definition tfib_E_fmt_fp : Z := 0x9bf58.
Definition tfib_A_thunk_931e0 : Z := 0x93da4.  Definition tfib_E_thunk_931e0 : Z := 0x93da8.
Definition tfib_A_musl_wctomb : Z := 0x98130.  Definition tfib_E_musl_wctomb : Z := 0x98154.
Definition tfib_A_musl_wcrtomb : Z := 0x98004.  Definition tfib_E_musl_wcrtomb : Z := 0x98130.
Definition tfib_A_fpclassifyl : Z := 0x96394.  Definition tfib_E_fpclassifyl : Z := 0x963d8.
Definition tfib_A_letf2 : Z := 0x95bcc.  Definition tfib_E_letf2 : Z := 0x95c94.
Definition tfib_A_multf3 : Z := 0x95c94.  Definition tfib_E_multf3 : Z := 0x96394.
Definition tfib_A_floatsitf : Z := 0x96bf0.  Definition tfib_E_floatsitf : Z := 0x96cf8.
Definition tfib_A_scalbn : Z := 0x975fc.  Definition tfib_E_scalbn : Z := 0x97694.
Definition tfib_A_subtf3 : Z := 0x96be0.  Definition tfib_E_subtf3 : Z := 0x96bf0.
Definition tfib_A_addtf3 : Z := 0x963d8.  Definition tfib_E_addtf3 : Z := 0x96ba4.
Definition tfib_A_fe_getround : Z := 0x96ba4.  Definition tfib_E_fe_getround : Z := 0x96bd4.
Definition tfib_A_fixunstfsi : Z := 0x9bf60.  Definition tfib_E_fixunstfsi : Z := 0x9bff4.
Definition tfib_A_floatunsitf : Z := 0x9bff4.  Definition tfib_E_floatunsitf : Z := 0x9c0e0.
Definition tfib_A_fixtfsi : Z := 0x97694.  Definition tfib_E_fixtfsi : Z := 0x9773c.
Definition tfib_A_divtf3 : Z := 0x96cf8.  Definition tfib_E_divtf3 : Z := 0x975fc.
Definition tfib_A_musl_vprintf : Z := 0x9c7b8.  Definition tfib_E_musl_vprintf : Z := 0x9c7d4.
Definition tfib_A_stdout_write : Z := 0x99568.  Definition tfib_E_stdout_write : Z := 0x99608.
Definition tfib_A_thunk_95368 : Z := 0x9cd6c.  Definition tfib_E_thunk_95368 : Z := 0x9cd70.
Definition tfib_A_musl_memcmp : Z := 0x9ce3c.  Definition tfib_E_musl_memcmp : Z := 0x9ce6c.
Definition tfib_A_musl_memcpy : Z := 0x9ce6c.  Definition tfib_E_musl_memcpy : Z := 0x9d270.
Definition tfib_A_musl_memset : Z := 0x9d270.  Definition tfib_E_musl_memset : Z := 0x9d368.
Definition tfib_A_musl_strchr : Z := 0x9d368.  Definition tfib_E_musl_strchr : Z := 0x9d3a4.
Definition tfib_A_strchrnul : Z := 0x9d3a4.  Definition tfib_E_strchrnul : Z := 0x9d484.
Definition tfib_A_musl_strlen : Z := 0x9d4bc.  Definition tfib_E_musl_strlen : Z := 0x9d54c.
Definition tfib_A_musl_strnlen : Z := 0x9d6f8.  Definition tfib_E_musl_strnlen : Z := 0x9d73c.
Definition tfib_A_musl_memchr : Z := 0x9cd70.  Definition tfib_E_musl_memchr : Z := 0x9ce3c.
Definition tfib_A_lock : Z := 0x9d73c.  Definition tfib_E_lock : Z := 0x9d9c4.
Definition tfib_A_unlock : Z := 0x9d9c4.  Definition tfib_E_unlock : Z := 0x9da38.
Definition tfib_A_syscall_cp_c : Z := 0x9da38.  Definition tfib_E_syscall_cp_c : Z := 0x9da5c.
Definition tfib_A_syscall_cp_sccp : Z := 0x9da5c.  Definition tfib_E_syscall_cp_sccp : Z := 0x9da60.
Definition tfib_A_pthread_atfork : Z := 0x9da9c.  Definition tfib_E_pthread_atfork : Z := 0x9db40.
Definition tfib_A_mremap : Z := 0x97ee8.  Definition tfib_E_mremap : Z := 0x97fbc.
Definition tfib_A_pthread_getspecific_tss_get : Z := 0x9eb14.  Definition tfib_E_pthread_getspecific_tss_get : Z := 0x9eb30.
Definition tfib_A_pthread_key_create : Z := 0x9eebc.  Definition tfib_E_pthread_key_create : Z := 0x9ef90.
Definition tfib_A_pthread_setspecific : Z := 0x9f458.  Definition tfib_E_pthread_setspecific : Z := 0x9f48c.
Definition tfib_A_set_thread_area : Z := 0x9f494.  Definition tfib_E_set_thread_area : Z := 0x9f4a0.
Definition tfib_A_thunk_96f9c : Z := 0x9f48c.  Definition tfib_E_thunk_96f9c : Z := 0x9f490.
Definition tfib_A_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9fdc0.  Definition tfib_E_clock_gettime_113_vdso_fallback_169_gettimeofday : Z := 0x9fe78.
Definition tfib_A_close : Z := 0xa2490.  Definition tfib_E_close : Z := 0xa24e4.
Definition tfib_A_musl_read : Z := 0xa2570.  Definition tfib_E_musl_read : Z := 0xa25a4.
Definition tfib_A_vm_wait : Z := 0x9fad0.  Definition tfib_E_vm_wait : Z := 0x9fb20.
Definition tfib_D_str_sealed : Z := 0x1184c.
Definition tfib_D_init_array_0_3 : Z := 0xa35a8.
Definition tfib_D_fini_array_0_1 : Z := 0xa35c8.
Definition tfib_D_GOT_common_flags : Z := 0xa3ce0.
Definition tfib_D_GOT_flags : Z := 0xa3ce8.
Definition tfib_D_GOT_asan_shadow_memory_dynamic_address : Z := 0xa3cf0.
Definition tfib_D_GOT_kMidMemBeg : Z := 0xa3cf8.
Definition tfib_D_GOT_kMidMemEnd : Z := 0xa3d00.
Definition tfib_D_GOT_kHighMemEnd : Z := 0xa3d08.
Definition tfib_D_GOT_replace_intrin_cached : Z := 0xa4858.
Definition tfib_D_environ_musl : Z := 0xa4980.
Definition tfib_D_REAL_read : Z := 0xa5a28.
Definition tfib_D_REAL_memcpy : Z := 0xa5b50.
Definition tfib_D_REAL_memset : Z := 0xa5b58.
Definition tfib_D_asan_allocator_instance_asan_allocator_cpp_insta : Z := 0xa9018.
Definition tfib_D_asan_flags_Flags_struct_flags : Z := 0xa9e78.
Definition tfib_D_asan_shadow_memory_dynamic_address : Z := 0xac678.
Definition tfib_D_asan_inited : Z := 0xad358.
Definition tfib_D_replace_intrin_cached : Z := 0xad359.
Definition tfib_D_kHighMemEnd : Z := 0xad360.
Definition tfib_D_kMidMemBeg : Z := 0xad368.
Definition tfib_D_kMidMemEnd : Z := 0xad370.
Definition tfib_D_malloc_context_size : Z := 0xad37c.
Definition tfib_D_common_flags_dont_use_CommonFlags_struct_common : Z := 0x13e1a8.
Definition tfib_D_libc_progname_area_musl_bss : Z := 0x613a00.
Definition tfib_at_img_lo : Z := 0x10000.
Definition tfib_at_img_hi : Z := 0x616000.
Definition tfib_at_n_res : nat := 4%nat.
Definition tfib_at_shadow_off : Z := 0x7fff8000.
Definition tfib_at_a_entry : Z := 0x3112c.
Definition tfib_at_rw_lo : Z := 0xa5000.
Definition tfib_at_rw_len : Z := 0x571000.
Definition tfib_at_ph_addr_z : Z := 0x10040.
Definition tfib_at_ph_ent_z : Z := 56.
Definition tfib_at_ph_num_z : Z := 11.
Definition tfib_at_x_imemset : Z := 0x64778.
Definition tfib_at_x_imemcpy : Z := 0x646fc.
Definition tfib_at_x_memset : Z := 0x9d270.
Definition tfib_at_x_memcpy : Z := 0x9ce6c.
Definition tfib_at_x_memiszero : Z := 0x64ca8.
Definition tfib_at_x_istrncpy : Z := 0x64ba4.
Definition tfib_at_x_sealed : Z := 0x1184c.
Definition tfib_at_x_popfree : Z := 0x37518.
Definition tfib_at_x_sniff : Z := 0.
Definition tfib_at_sniff_tab : Z := 0.
Definition tfib_at_sniff_cell : Z := 0.
Definition tfib_at_x_envscan : Z := 0x92c70.
Definition tfib_at_x_envscan_k : Z := 0x92c7c.
Definition tfib_at_x_pnscan : Z := 0x92d34.
Definition tfib_at_x_pnscan_k : Z := 0x92d40.
Definition tfib_at_stops_more : list Z := (0x3518c :: 0x367b0 :: 0x54a84 :: 0x5ae3c :: 0x5ae50 :: 0x5ae64 :: 0x607f4 :: 0x608c4 :: 0x6ddf0 :: 0x6ecfc :: 0x6ee8c :: 0x78be4 :: 0x6effc :: nil)%list.
