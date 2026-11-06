(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The names the listing of fuzz_boxreg's program code calls: the memory-checking
   runtime's entries, the wrappers' trampolines, and the program functions that
   have their own contract. *)
From Stdlib Require Import ZArith.
Inductive bsym : Type :=
| BS___asan_stack_malloc_3
| BS___interceptor_trampoline_malloc
| BS_reac_boxreg_init
| BS_check
| BS___asan_memcpy
| BS_read_name
| BS_range_free
| BS_reac_boxreg_set_name
| BS___interceptor_trampoline_strncmp
| BS___interceptor_trampoline_free
| BS_reac_boxreg_find
| BS___interceptor_trampoline_bcmp
| BS_reac_boxreg_add
| BS_lowest_free
| BS_reac_boxreg_declare
| BS___asan_report_load4
| BS___asan_set_shadow_f5
| BS___asan_handle_no_return
| BS_abort
| BS___asan_report_load1
| BS___interceptor_trampoline_memchr
| BS___asan_report_store1
| BS___asan_report_load8
| BS___asan_report_store8
| BS___asan_init
| BS___asan_version_mismatch_check_v8
| BS___asan_register_elf_globals
| BS___asan_unregister_elf_globals
| BS___asan_memset
| BS___asan_report_store4
| BS_lowest_free_base
| BS___interceptor_trampoline_snprintf.
