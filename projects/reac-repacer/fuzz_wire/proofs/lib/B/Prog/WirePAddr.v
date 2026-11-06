(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The addresses fuzz_wire.asan-ubsan gives the listing's names, objects and auipc values.
   The PAImg instance of this image checks them against the image. The objects
   past the ones the slots build are the cells the walks read through a GOT
   word: __asan_shadow_memory_dynamic_address (the shadow base) and
   __asan_option_detect_stack_use_after_return. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import WirePSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition wire_text : Z := 0x7fbf8.
Definition wire_sigma (s : wsym) : Z :=
match s with
| WS___interceptor_trampoline_malloc => 0x52098
| WS___asan_memcpy => 0x50c14
| WS_check_forward => 0x7fda4
| WS_check_ret => 0x7ff2c
| WS_check_downstream => 0x7ffe8
| WS_check_meter => 0x8016c
| WS_check_counter => 0x804c0
| WS_check_width => 0x8057c
| WS_check_read => 0x805f4
| WS_check_copy => 0x80abc
| WS___interceptor_trampoline_free => 0x52094
| WS___asan_handle_no_return => 0x58e58
| WS_abort => 0x880cc
| WS___asan_report_load1 => 0x57e5c
| WS_rp_fwd_class => 0x80d9c
| WS_rp_ret_accept => 0x80ee0
| WS_rp_ds_accept => 0x80f84
| WS___asan_stack_malloc_0 => 0x3c524
| WS_rp_meter_counter => 0x81144
| WS_rp_counter => 0x81314
| WS_rp_frame_channels => 0x813a0
| WS___asan_stack_malloc_1 => 0x3c698
| WS_rp_slot_read => 0x815ec
| WS_rp_copy_untag => 0x81414
| WS___interceptor_trampoline_bcmp => 0x4155c
| WS___asan_init => 0x58fc0
| WS___asan_version_mismatch_check_v8 => 0x59054
| WS___asan_register_elf_globals => 0x3f484
| WS_is_tagged_reac => 0x8103c
| WS___asan_report_store2 => 0x5821c
| WS_reac_frame_clean_len => 0x818e8
| WS___asan_memmove => 0x510b0
| WS_reac_frame_is_reac => 0x8183c
| WS_rp_slot_width => 0x8151c
| WS___asan_report_store4 => 0x582bc
| WS___asan_unregister_elf_globals => 0x3f4f0
end.
Definition wire_obj (i : nat) : Z :=
match i with
| 0%nat => 0x98878
| 1%nat => 0x988d0
| 2%nat => 0x18cc3
| 3%nat => 0x8016c
| 4%nat => 0x16e29
| 5%nat => 0x805f4
| 6%nat => 0x994f0
| 7%nat => 0x994f8
| 8%nat => 0x9d140
| 9%nat => 0x10328
| 10%nat => 0x10300
| 11%nat => 0x103b0
| 12%nat => 0xa07f8
| 13%nat => 0xa0800
| _ => 0
end.
Definition wire_hi (j : nat) : Z :=
match j with
| 0%nat => 0x98c34
| 1%nat => 0x98dc4
| 2%nat => 0x98f48
| 3%nat => 0x99004
| 4%nat => 0x981b4
| 5%nat => 0x981b8
| 6%nat => 0x19210
| 7%nat => 0x80214
| 8%nat => 0x984dc
| 9%nat => 0x98644
| 10%nat => 0x98648
| 11%nat => 0x166a8
| 12%nat => 0x806ac
| 13%nat => 0x98ae4
| 14%nat => 0x98d74
| 15%nat => 0x98d78
| 16%nat => 0x9cd84
| 17%nat => 0x98db8
| 18%nat => 0x98efc
| 19%nat => 0x98fb0
| 20%nat => 0x99050
| 21%nat => 0x98160
| 22%nat => 0x9832c
| 23%nat => 0x103c0
| 24%nat => 0x9843c
| 25%nat => 0x98548
| 26%nat => 0x9861c
| 27%nat => 0x9885c
| 28%nat => 0x108f0
| 29%nat => 0x108f8
| 30%nat => 0x99930
| 31%nat => 0x99934
| 32%nat => 0x9d940
| _ => 0
end.
Definition wire_nobj : nat := 14%nat.
Definition wire_nhi : nat := 33%nat.
