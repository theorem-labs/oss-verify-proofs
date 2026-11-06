(* The names the listing of fuzz_identity.asan-ubsan's program code calls: the memory-checking
   runtime's entries, the wrappers' trampolines, and the program functions that
   have their own contract. *)
From Stdlib Require Import ZArith.
(* Removes the plain sink instances from resolution; see that file's header. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import IdentBSkGuard.
Inductive ibsym : Type :=
| IB___asan_stack_malloc_4
| IB_reac_identity_init
| IB_reac_identity_ingest
| IB_reac_identity_fw_str
| IB_reac_identity_reac_ver_str
| IB_reac_box_catalogue_defect
| IB_reac_box_family_of
| IB___asan_memset
| IB___interceptor_trampoline_malloc
| IB___asan_memcpy
| IB_buf_of
| IB___interceptor_trampoline_free
| IB___interceptor_trampoline_bcmp
| IB_put_dec
| IB___interceptor_trampoline_memchr
| IB_check_str
| IB___asan_report_load1
| IB_reac_box_family_stem
| IB_reac_box_name
| IB___interceptor_trampoline_strlen
| IB___interceptor_trampoline_strcmp
| IB_reac_box_catalogue
| IB___asan_set_shadow_f5
| IB___asan_set_shadow_00
| IB___asan_handle_no_return
| IB_abort
| IB___asan_report_store1
| IB___asan_report_load4
| IB___asan_report_load_n
| IB___asan_report_load8
| IB___asan_stack_malloc_0
| IB___asan_init
| IB___asan_version_mismatch_check_v8
| IB___asan_register_elf_globals
| IB___asan_unregister_elf_globals
| IB___asan_stack_malloc_3
| IB_sb_dec
| IB_sb_ch
| IB___asan_report_store4
| IB___asan_report_store8
| IB___asan_report_store_n
| IB___asan_report_store2
| IB_write_uint.
