(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The names the listing of fuzz_decode.asan's program code calls: the memory-checking
   runtime's entries, the wrappers' trampolines, and the program functions that
   have their own contract. *)
From Stdlib Require Import ZArith.
Inductive dsym : Type :=
| DS___asan_stack_malloc_0
| DS___interceptor_trampoline_malloc
| DS___asan_memcpy
| DS_reac_frame_is_reac
| DS_reac_frame_clean_len
| DS_reac_frame_inspect
| DS_reac_frame_counter
| DS___asan_memset
| DS_reac_decode
| DS___asan_report_load1
| DS_check_round_trip
| DS_check_braid
| DS_reac_decode_plain_le
| DS___interceptor_trampoline_bcmp
| DS___interceptor_trampoline_free
| DS_reac_upstream_channels
| DS_reac_upstream_decode
| DS___asan_handle_no_return
| DS_abort
| DS___asan_report_load4
| DS___interceptor_trampoline_calloc
| DS_reac_braid_encode
| DS___asan_report_store4
| DS___asan_report_store8
| DS___asan_init
| DS___asan_version_mismatch_check_v8
| DS___asan_register_elf_globals
| DS___asan_unregister_elf_globals
| DS___asan_report_store1
| DS___asan_report_load8.
