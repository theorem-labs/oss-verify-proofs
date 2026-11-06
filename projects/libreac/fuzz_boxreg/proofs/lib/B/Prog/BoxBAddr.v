(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The addresses fuzz_boxreg.asan-ubsan gives the listing's names, objects and
   auipc values. BoxBImg.v checks them against the image. The objects past the
   ones the slots build are the cells the walks read through a GOT word:
   __asan_shadow_memory_dynamic_address (the shadow base) and
   __asan_option_detect_stack_use_after_return. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition boxb_text : Z := 0x7ffac.
Definition boxb_sigma (s : bbsym) : Z :=
match s with
| BB___asan_stack_malloc_3 => 0x3c580
| BB___interceptor_trampoline_malloc => 0x5244c
| BB_reac_boxreg_init => 0x81894
| BB_check => 0x81034
| BB___asan_memcpy => 0x510f8
| BB_read_mac => 0x81618
| BB_reac_boxreg_find => 0x81928
| BB___interceptor_trampoline_bcmp => 0x41464
| BB_read_name => 0x81318
| BB_range_free => 0x814e8
| BB_reac_boxreg_declare => 0x81ad0
| BB___interceptor_trampoline_strncmp => 0x41458
| BB_reac_boxreg_set_name => 0x8229c
| BB___interceptor_trampoline_free => 0x52448
| BB_reac_boxreg_add => 0x81f68
| BB___asan_report_load4 => 0x58350
| BB___asan_set_shadow_f5 => 0x540c0
| BB___asan_handle_no_return => 0x5920c
| BB_abort => 0x88acc
| BB___asan_report_load1 => 0x58210
| BB___interceptor_trampoline_memchr => 0x41468
| BB___asan_report_store1 => 0x58530
| BB___asan_report_load8 => 0x583f0
| BB___asan_report_store8 => 0x58710
| BB___asan_init => 0x59374
| BB___asan_version_mismatch_check_v8 => 0x59408
| BB___asan_register_elf_globals => 0x3f388
| BB___asan_unregister_elf_globals => 0x3f3f4
| BB___asan_memset => 0x51594
| BB___asan_report_store4 => 0x58670
| BB_mac_is_zero => 0x81a38
| BB_range_taken => 0x81d6c
| BB_lowest_free_base => 0x81e94
| BB___interceptor_trampoline_snprintf => 0x41490
end.
Definition boxb_obj (i : nat) : Z :=
match i with
| 0%nat => 0x99330
| 1%nat => 0x992d8
| 2%nat => 0x16e2e
| 3%nat => 0x7ffac
| 4%nat => 0x20cc0
| 5%nat => 0x20ce0
| 6%nat => 0x20d00
| 7%nat => 0x99f50
| 8%nat => 0x99f58
| 9%nat => 0x9dd00
| 10%nat => 0x20d40
| 11%nat => 0x20d60
| 12%nat => 0xa13b8
| 13%nat => 0xa13c0
| _ => 0
end.
Definition boxb_hi (j : nat) : Z :=
match j with
| 0%nat => 0x98ff8
| 1%nat => 0x98ffc
| 2%nat => 0x17058
| 3%nat => 0x8005c
| 4%nat => 0x2145c
| 5%nat => 0x2061c
| 6%nat => 0x20688
| 7%nat => 0x206d4
| 8%nat => 0x20778
| 9%nat => 0x20890
| 10%nat => 0x20c00
| 11%nat => 0x9907c
| 12%nat => 0x21204
| 13%nat => 0x99338
| 14%nat => 0x99508
| 15%nat => 0x99630
| 16%nat => 0x20710
| 17%nat => 0x9983c
| 18%nat => 0x99840
| 19%nat => 0x9d84c
| 20%nat => 0x9986c
| 21%nat => 0x99870
| 22%nat => 0x9d87c
| 23%nat => 0x998ac
| 24%nat => 0x99954
| 25%nat => 0x99a40
| 26%nat => 0x98b30
| 27%nat => 0x20c60
| 28%nat => 0x98d7c
| 29%nat => 0x98ec8
| 30%nat => 0x98fc0
| 31%nat => 0x992b8
| 32%nat => 0x21314
| 33%nat => 0x2131c
| _ => 0
end.
Definition boxb_nobj : nat := 14%nat.
Definition boxb_nhi : nat := 34%nat.
