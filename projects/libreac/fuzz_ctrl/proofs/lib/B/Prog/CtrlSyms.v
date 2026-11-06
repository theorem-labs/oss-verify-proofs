(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The names the listing of fuzz_ctrl's program code calls: the memory-checking
   runtime's entries, the wrappers' trampolines, and the program functions that
   have their own contract. *)
From Stdlib Require Import ZArith.
Inductive gsym : Type :=
| GS___asan_stack_malloc_6
| GS___asan_set_shadow_f8
| GS___asan_report_load1
| GS_reac_box_catalogue
| GS___asan_set_shadow_00
| GS_reac_identity_init
| GS___asan_memset
| GS_reac_ctrl_build_as
| GS___interceptor_trampoline_malloc
| GS___asan_memcpy
| GS_reac_ctrl_parse
| GS_reac_ctrl_identity_reply
| GS_reac_ctrl_identity_fragment
| GS_reac_identity_ingest
| GS_reac_box_catalogue_match
| GS_reac_ports_parse
| GS_declaration_of
| GS___interceptor_trampoline_bcmp
| GS___interceptor_trampoline_free
| GS___asan_report_load4
| GS___interceptor_trampoline_strcmp
| GS_reac_ports_unknown
| GS_reac_ctrl_kind_name
| GS_record_sum_closes
| GS_joined_byte
| GS_reac_ctrl_checksum_verify
| GS_reac_ctrl_headamp_record_verify
| GS_reac_ctrl_classify_box_frame
| GS___interceptor_trampoline_memchr
| GS___asan_stack_free_6
| GS___asan_handle_no_return
| GS_abort
| GS___asan_report_load2
| GS___asan_report_load8
| GS___asan_report_store1
| GS___asan_report_store_n
| GS___asan_init
| GS___asan_version_mismatch_check_v8
| GS___asan_register_elf_globals
| GS___asan_unregister_elf_globals
| GS___asan_report_store4
| GS___asan_stack_malloc_1
| GS_kind_of_link1
| GS___asan_report_store2
| GS_reac_ctrl_record_cksum_verify
| GS___asan_report_store8
| GS___asan_stack_malloc_2
| GS_reac_box_model_block
| GS_reac_box_model_upstream_width
| GS_ctrl_emit_as
| GS_ctrl_lay_block
| GS_reac_braid_encode
| GS_ctrl_finish
| GS_reac_ctrl_record_cksum_stamp
| GS_reac_ctrl_block_cksum_stamp
| GS___asan_stack_malloc_0
| GS_build_dt1_single
| GS_name_field
| GS_dt1_head
| GS___asan_report_load_n.
