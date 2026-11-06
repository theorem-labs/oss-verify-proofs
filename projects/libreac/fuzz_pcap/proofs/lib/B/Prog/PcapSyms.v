(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The names the listing of fuzz_pcap.asan-ubsan's program code calls (v1.9.0, pin
   sha256 9e66f771f22af67aadc8b8ddcd7ee91f46c4c63442c694faaf2375f9c5b79321): the
   memory-checking runtime's entries, the wrappers' trampolines, and the program
   functions that have their own contract. *)
From Stdlib Require Import ZArith.
Inductive psym : Type :=
| PS___interceptor_trampoline_strcmp
| PS___interceptor_trampoline_fopen
| PS___interceptor_trampoline_fmemopen
| PS___asan_stack_malloc_1
| PS___interceptor_trampoline_malloc
| PS___asan_memcpy
| PS___asan_memset
| PS_pcap_source_open
| PS_rd32
| PS___interceptor_trampoline_free
| PS_pcap_source_next
| PS___interceptor_trampoline_bcmp
| PS___asan_report_load1
| PS_pcap_source_close
| PS___asan_handle_no_return
| PS_abort
| PS___asan_init
| PS___asan_version_mismatch_check_v8
| PS___asan_register_elf_globals
| PS___asan_unregister_elf_globals
| PS_libreac_fuzz_fopen
| PS___interceptor_trampoline_fread
| PS___interceptor_trampoline_fclose
| PS___asan_report_store8
| PS___asan_report_store4
| PS___asan_report_store2
| PS___asan_report_load8
| PS___asan_stack_malloc_0
| PS_rd_u32
| PS___asan_memmove
| PS___asan_report_load4.
