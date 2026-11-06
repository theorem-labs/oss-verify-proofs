(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The names the listing of fuzz_boxreg.asan-ubsan's program code calls: the memory-checking
   runtime's entries, the wrappers' trampolines, and the program functions that
   have their own contract. *)
From Stdlib Require Import ZArith.
Inductive bbsym : Type :=
| BB___asan_stack_malloc_3
| BB___interceptor_trampoline_malloc
| BB_reac_boxreg_init
| BB_check
| BB___asan_memcpy
| BB_read_mac
| BB_reac_boxreg_find
| BB___interceptor_trampoline_bcmp
| BB_read_name
| BB_range_free
| BB_reac_boxreg_declare
| BB___interceptor_trampoline_strncmp
| BB_reac_boxreg_set_name
| BB___interceptor_trampoline_free
| BB_reac_boxreg_add
| BB___asan_report_load4
| BB___asan_set_shadow_f5
| BB___asan_handle_no_return
| BB_abort
| BB___asan_report_load1
| BB___interceptor_trampoline_memchr
| BB___asan_report_store1
| BB___asan_report_load8
| BB___asan_report_store8
| BB___asan_init
| BB___asan_version_mismatch_check_v8
| BB___asan_register_elf_globals
| BB___asan_unregister_elf_globals
| BB___asan_memset
| BB___asan_report_store4
| BB_mac_is_zero
| BB_range_taken
| BB_lowest_free_base
| BB___interceptor_trampoline_snprintf.
