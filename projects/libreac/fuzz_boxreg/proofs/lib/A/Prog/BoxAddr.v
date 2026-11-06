(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The addresses fuzz_boxreg.asan gives the listing's names, objects and
   auipc values. BoxImg.v checks them against the image. The objects past the
   ones the slots build are the cells the walks read through a GOT word:
   __asan_shadow_memory_dynamic_address (the shadow base) and
   __asan_option_detect_stack_use_after_return. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition box_text : Z := 0x7ff4c.
Definition box_sigma (s : bsym) : Z :=
match s with
| BS___asan_stack_malloc_3 => 0x3c520
| BS___interceptor_trampoline_malloc => 0x523ec
| BS_reac_boxreg_init => 0x8161c
| BS_check => 0x80ff0
| BS___asan_memcpy => 0x51098
| BS_read_name => 0x812b0
| BS_range_free => 0x81430
| BS_reac_boxreg_set_name => 0x81ea4
| BS___interceptor_trampoline_strncmp => 0x413f8
| BS___interceptor_trampoline_free => 0x523e8
| BS_reac_boxreg_find => 0x816a0
| BS___interceptor_trampoline_bcmp => 0x41404
| BS_reac_boxreg_add => 0x81ba8
| BS_lowest_free => 0x81524
| BS_reac_boxreg_declare => 0x817a0
| BS___asan_report_load4 => 0x582f0
| BS___asan_set_shadow_f5 => 0x54060
| BS___asan_handle_no_return => 0x591ac
| BS_abort => 0x886a8
| BS___asan_report_load1 => 0x581b0
| BS___interceptor_trampoline_memchr => 0x41408
| BS___asan_report_store1 => 0x584d0
| BS___asan_report_load8 => 0x58390
| BS___asan_report_store8 => 0x586b0
| BS___asan_init => 0x59314
| BS___asan_version_mismatch_check_v8 => 0x593a8
| BS___asan_register_elf_globals => 0x3f328
| BS___asan_unregister_elf_globals => 0x3f394
| BS___asan_memset => 0x51534
| BS___asan_report_store4 => 0x58610
| BS_lowest_free_base => 0x81a54
| BS___interceptor_trampoline_snprintf => 0x41430
end.
Definition box_obj (i : nat) : Z :=
match i with
| 0%nat => 0x98f10
| 1%nat => 0x98eb8
| 2%nat => 0x16e2e
| 3%nat => 0x7ff4c
| 4%nat => 0x20d00
| 5%nat => 0x20ce0
| 6%nat => 0x20cc0
| 7%nat => 0x99b30
| 8%nat => 0x99b38
| 9%nat => 0x9d8c0
| 10%nat => 0x20d40
| 11%nat => 0x20d60
| 12%nat => 0xa0f78
| 13%nat => 0xa0f80
| _ => 0
end.
Definition box_hi (j : nat) : Z :=
match j with
| 0%nat => 0x98f98
| 1%nat => 0x98f9c
| 2%nat => 0x16ff8
| 3%nat => 0x7fffc
| 4%nat => 0x2135c
| 5%nat => 0x213b0
| 6%nat => 0x205d0
| 7%nat => 0x20668
| 8%nat => 0x206cc
| 9%nat => 0x20740
| 10%nat => 0x209c4
| 11%nat => 0x20a28
| 12%nat => 0x20b88
| 13%nat => 0x99028
| 14%nat => 0x210a8
| 15%nat => 0x992c8
| 16%nat => 0x9944c
| 17%nat => 0x995c4
| 18%nat => 0x995c8
| 19%nat => 0x9d5d4
| 20%nat => 0x995f4
| 21%nat => 0x995f8
| 22%nat => 0x9d604
| 23%nat => 0x99634
| 24%nat => 0x986c4
| 25%nat => 0x987f8
| 26%nat => 0x20974
| 27%nat => 0x98a64
| 28%nat => 0x98bf4
| 29%nat => 0x98eb4
| 30%nat => 0x20ef4
| 31%nat => 0x20efc
| _ => 0
end.
Definition box_nobj : nat := 14%nat.
Definition box_nhi : nat := 32%nat.
