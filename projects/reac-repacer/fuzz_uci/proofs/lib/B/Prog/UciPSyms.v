(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The names the listing of fuzz_uci.asan-ubsan's program code calls: the memory-checking
   runtime's entries, the wrappers' trampolines, and the program functions that
   have their own contract. *)
From Stdlib Require Import ZArith.
Inductive usym : Type :=
| US_check_no_overread
| US_check_value
| US___asan_report_load1
| US_check_clamp
| US___asan_report_load4
| US___interceptor_trampoline_malloc
| US___asan_memcpy
| US_rp_uci_int
| US___interceptor_trampoline_free
| US___asan_handle_no_return
| US_abort
| US___asan_report_store1
| US___asan_stack_malloc_1
| US_rp_hot_clamp
| US___asan_init
| US___asan_version_mismatch_check_v8
| US___asan_register_elf_globals
| US___asan_unregister_elf_globals
| US___asan_report_store4
| US___interceptor_trampoline_memchr.
