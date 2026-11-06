(* The names the listing of fuzz_identity's program code calls: the memory-checking
   runtime's entries, the wrappers' trampolines, and the program functions that
   have their own contract. *)
From Stdlib Require Import ZArith.
(* Removes the plain sink instances from resolution; see that file's header. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentSkGuard.
Inductive isym : Type :=
| IS___asan_stack_malloc_4
| IS_reac_identity_init
| IS_reac_identity_ingest
| IS_reac_identity_fw_str
| IS_reac_identity_reac_ver_str
| IS_reac_box_catalogue_defect
| IS_reac_box_family_of
| IS___asan_memset
| IS___interceptor_trampoline_malloc
| IS___asan_memcpy
| IS___interceptor_trampoline_free
| IS___interceptor_trampoline_bcmp
| IS_put_dec
| IS___interceptor_trampoline_memchr
| IS_check_str
| IS___asan_report_load1
| IS_reac_box_family_stem
| IS_reac_box_name
| IS___interceptor_trampoline_strlen
| IS___interceptor_trampoline_strcmp
| IS_reac_box_catalogue
| IS___asan_set_shadow_f5
| IS___asan_set_shadow_00
| IS___asan_handle_no_return
| IS_abort
| IS___asan_report_store1
| IS___asan_report_load4
| IS___asan_report_load_n
| IS___asan_report_load8
| IS___asan_stack_malloc_0
| IS___asan_init
| IS___asan_version_mismatch_check_v8
| IS___asan_register_elf_globals
| IS___asan_unregister_elf_globals
| IS___asan_stack_malloc_3
| IS_sb_dec
| IS___asan_report_store8
| IS___asan_report_store4
| IS___asan_report_store_n
| IS___asan_report_store2
| IS_write_uint.
