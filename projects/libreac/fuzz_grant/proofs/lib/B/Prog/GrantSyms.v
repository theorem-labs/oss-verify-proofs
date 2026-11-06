(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The names the listing of fuzz_grant's program code calls: the memory-checking
   runtime's entries, the wrappers' trampolines, and the program functions that
   have their own contract. *)
From Stdlib Require Import ZArith.
Inductive gsym : Type :=
| GS___asan_stack_malloc_4
| GS___asan_set_shadow_f5
| GS___asan_set_shadow_00
| GS___interceptor_trampoline_malloc
| GS_reac_headamp_tx_init
| GS___asan_memset
| GS_reac_headamp_tx_set
| GS_reac_headamp_tx_effective
| GS_reac_headamp_default
| GS___asan_report_load1
| GS_reac_grant_alloc_fits
| GS_reac_grant_allocate
| GS_reac_grant_build_sweep
| GS___interceptor_trampoline_bcmp
| GS_want_of
| GS_check_groupa
| GS_reac_ctrl_identity_poll_block
| GS___interceptor_trampoline_free
| GS_reac_headamp_tx_arm_scene
| GS_reac_headamp_tx_set_resweep
| GS_reac_headamp_tx_next
| GS___asan_handle_no_return
| GS_abort
| GS___asan_report_store1
| GS___asan_stack_malloc_2
| GS___asan_memcpy
| GS_reac_ctrl_parse
| GS_reac_ctrl_headamp_record_verify
| GS_reac_ctrl_checksum_verify
| GS___asan_init
| GS___asan_version_mismatch_check_v8
| GS___asan_register_elf_globals
| GS___asan_unregister_elf_globals
| GS___asan_stack_malloc_1
| GS_kind_of_link1
| GS___asan_report_store4
| GS___asan_report_store2
| GS___asan_report_load4
| GS___asan_stack_malloc_0
| GS_ctrl_lay_block
| GS_ctrl_finish
| GS___asan_stack_malloc_6
| GS___asan_set_shadow_f8
| GS_reac_ctrl_stamp_headamp
| GS___asan_stack_free_6
| GS_reac_box_model_block
| GS___asan_report_load8
| GS_reac_ctrl_record_cksum_stamp
| GS_reac_ctrl_block_cksum_stamp
| GS_build_dt1_single
| GS_name_field
| GS_dt1_head
| GS___asan_report_load2
| GS_reac_ctrl_build_grant_sweep.
