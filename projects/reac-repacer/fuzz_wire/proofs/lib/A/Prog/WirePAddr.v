(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The addresses fuzz_wire.asan gives the listing's names, objects and auipc values.
   The PAImg instance of this image checks them against the image. The objects
   past the ones the slots build are the cells the walks read through a GOT
   word: __asan_shadow_memory_dynamic_address (the shadow base) and
   __asan_option_detect_stack_use_after_return. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition wire_text : Z := 0x7fe58.
Definition wire_sigma (s : wsym) : Z :=
match s with
| WS___interceptor_trampoline_malloc => 0x522f8
| WS___asan_memcpy => 0x50c34
| WS_check_forward => 0x7fff0
| WS_check_ret => 0x80154
| WS_check_downstream => 0x801fc
| WS_check_meter => 0x80340
| WS_check_counter => 0x80660
| WS_check_width => 0x80708
| WS_check_read => 0x8077c
| WS_check_copy => 0x80c38
| WS___interceptor_trampoline_free => 0x522f4
| WS___asan_handle_no_return => 0x590b8
| WS_abort => 0x88038
| WS___asan_report_load1 => 0x580bc
| WS_rp_fwd_class => 0x80ec4
| WS_rp_ret_accept => 0x80fe0
| WS_rp_ds_accept => 0x8106c
| WS___asan_stack_malloc_0 => 0x3c544
| WS_rp_meter_counter => 0x81168
| WS_rp_counter => 0x812f4
| WS_rp_frame_channels => 0x8136c
| WS___asan_stack_malloc_1 => 0x3c6b8
| WS___asan_memset => 0x510d0
| WS_rp_slot_read => 0x8160c
| WS_rp_copy_untag => 0x813e0
| WS___interceptor_trampoline_bcmp => 0x4157c
| WS___asan_init => 0x59220
| WS___asan_version_mismatch_check_v8 => 0x592b4
| WS___asan_register_elf_globals => 0x3f4a4
| WS___asan_report_store2 => 0x5847c
| WS_reac_frame_clean_len => 0x81854
| WS___asan_memmove => 0x51310
| WS_reac_frame_is_reac => 0x817bc
| WS_rp_slot_width => 0x81554
| WS___asan_report_store4 => 0x5851c
| WS___asan_unregister_elf_globals => 0x3f510
end.
Definition wire_obj (i : nat) : Z :=
match i with
| 0%nat => 0x987e8
| 1%nat => 0x98840
| 2%nat => 0x18cc3
| 3%nat => 0x80340
| 4%nat => 0x16e29
| 5%nat => 0x8077c
| 6%nat => 0x99460
| 7%nat => 0x99468
| 8%nat => 0x9d0c0
| 9%nat => 0x10328
| 10%nat => 0x10300
| 11%nat => 0x103b0
| 12%nat => 0xa0778
| 13%nat => 0xa0780
| _ => 0
end.
Definition wire_hi (j : nat) : Z :=
match j with
| 0%nat => 0x98e90
| 1%nat => 0x98010
| 2%nat => 0x98168
| 3%nat => 0x98210
| 4%nat => 0x98388
| 5%nat => 0x9838c
| 6%nat => 0x193e4
| 7%nat => 0x803e8
| 8%nat => 0x9867c
| 9%nat => 0x987cc
| 10%nat => 0x987d0
| 11%nat => 0x16830
| 12%nat => 0x80834
| 13%nat => 0x98c60
| 14%nat => 0x98e9c
| 15%nat => 0x98ea0
| 16%nat => 0x9ceac
| 17%nat => 0x98ed4
| 18%nat => 0x97ff0
| 19%nat => 0x9807c
| 20%nat => 0x98178
| 21%nat => 0x982fc
| 22%nat => 0x1038c
| 23%nat => 0x98404
| 24%nat => 0x98574
| 25%nat => 0x98630
| 26%nat => 0x987d4
| 27%nat => 0x1085c
| 28%nat => 0x10864
| 29%nat => 0x9989c
| 30%nat => 0x998a0
| 31%nat => 0x9d8ac
| _ => 0
end.
Definition wire_nobj : nat := 14%nat.
Definition wire_nhi : nat := 32%nat.
