(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The names the listing of fuzz_decode.asan-ubsan's program code calls: the memory-checking
   runtime's entries, the wrappers' trampolines, and the program functions that
   have their own contract. *)
From Stdlib Require Import ZArith.
Inductive dbsym : Type :=
| DB___asan_stack_malloc_0
| DB___interceptor_trampoline_malloc
| DB___asan_memcpy
| DB_reac_frame_is_reac
| DB_reac_frame_clean_len
| DB_reac_frame_inspect
| DB_reac_frame_counter
| DB___asan_memset
| DB_reac_decode
| DB___asan_report_load1
| DB_check_round_trip
| DB_check_braid
| DB_reac_decode_plain_le
| DB___interceptor_trampoline_bcmp
| DB___interceptor_trampoline_free
| DB_reac_upstream_channels
| DB_reac_upstream_decode
| DB___asan_handle_no_return
| DB_abort
| DB___asan_report_load4
| DB___interceptor_trampoline_calloc
| DB_reac_braid_encode
| DB___asan_report_store4
| DB___asan_report_store8
| DB___asan_init
| DB___asan_version_mismatch_check_v8
| DB___asan_register_elf_globals
| DB___asan_unregister_elf_globals
| DB___asan_report_store1
| DB___asan_report_load8.
