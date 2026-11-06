(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The names the listing of fuzz_wire.asan's program code calls: the memory-checking
   runtime's entries, the wrappers' trampolines, and the program functions that
   have their own contract. *)
From Stdlib Require Import ZArith.
Inductive wsym : Type :=
| WS___interceptor_trampoline_malloc
| WS___asan_memcpy
| WS_check_forward
| WS_check_ret
| WS_check_downstream
| WS_check_meter
| WS_check_counter
| WS_check_width
| WS_check_read
| WS_check_copy
| WS___interceptor_trampoline_free
| WS___asan_handle_no_return
| WS_abort
| WS___asan_report_load1
| WS_rp_fwd_class
| WS_rp_ret_accept
| WS_rp_ds_accept
| WS___asan_stack_malloc_0
| WS_rp_meter_counter
| WS_rp_counter
| WS_rp_frame_channels
| WS___asan_stack_malloc_1
| WS___asan_memset
| WS_rp_slot_read
| WS_rp_copy_untag
| WS___interceptor_trampoline_bcmp
| WS___asan_init
| WS___asan_version_mismatch_check_v8
| WS___asan_register_elf_globals
| WS___asan_report_store2
| WS_reac_frame_clean_len
| WS___asan_memmove
| WS_reac_frame_is_reac
| WS_rp_slot_width
| WS___asan_report_store4
| WS___asan_unregister_elf_globals.
