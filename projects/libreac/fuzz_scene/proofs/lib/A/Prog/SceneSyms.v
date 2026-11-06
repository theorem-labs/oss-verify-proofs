(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Generated from fuzz_scene.asan (sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026) by mklisting.py, sha256 b39bde09dd82c7145e8d7f6d64672434e9e1bae7a8bd14a241d13a4ed7d7d950 (with the --pin aliasing fix, a Theorem Labs lane 20:43Z), run with fuzz_grant's own flags and no --pin, and by emit_rocq.py, sha256 34955550906406a211aeadad3b715013a584b480d96e1ba64c3180e51c8d5b1b, a copy of emit_rocq.py kept as emit_rocq.py (sha256 349555509064; internal record), that writes this target's names. *)
(* The names the listing of fuzz_scene.asan's program code calls: the memory-checking
   runtime's entries, the wrappers' trampolines, and the program functions that
   have their own contract. The names are the symbol names of fuzz_scene.asan (sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026);
   their addresses are in SceneAddr.v. *)
From Stdlib Require Import ZArith.
Inductive ssym : Type :=
| SS___asan_stack_malloc_8
| SS___asan_set_shadow_f8
| SS___asan_report_load1
| SS___interceptor_trampoline_malloc
| SS___asan_memset
| SS_reac_ctrl_build_scene_step
| SS_check_step
| SS___asan_memcpy
| SS___interceptor_trampoline_bcmp
| SS___interceptor_trampoline_free
| SS_reac_ctrl_scene_set_mac
| SS_reac_ctrl_scene_build
| SS___asan_set_shadow_00
| SS___asan_stack_free_8
| SS___asan_handle_no_return
| SS_abort
| SS___asan_report_store1
| SS___asan_stack_malloc_2
| SS_reac_ctrl_parse
| SS_reac_ctrl_checksum_verify
| SS___asan_init
| SS___asan_version_mismatch_check_v8
| SS___asan_register_elf_globals
| SS___asan_unregister_elf_globals
| SS___asan_report_store_n
| SS___asan_stack_malloc_1
| SS_kind_of_link1
| SS___asan_report_store4
| SS___asan_report_store2
| SS___asan_report_load4.
