(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The addresses fuzz_uci.asan-ubsan gives the listing's names, objects and auipc values.
   The PAImg instance of this image checks them against the image. The objects
   past the ones the slots build are the cells the walks read through a GOT
   word: __asan_shadow_memory_dynamic_address (the shadow base) and
   __asan_option_detect_stack_use_after_return. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import UciPSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition uci_text : Z := 0x7f2e8.
Definition uci_sigma (s : usym) : Z :=
match s with
| US_check_no_overread => 0x7f56c
| US_check_value => 0x7f6b0
| US___asan_report_load1 => 0x5754c
| US_check_clamp => 0x7f950
| US___asan_report_load4 => 0x5768c
| US___interceptor_trampoline_malloc => 0x51788
| US___asan_memcpy => 0x50674
| US_rp_uci_int => 0x7ffd4
| US___interceptor_trampoline_free => 0x51784
| US___asan_handle_no_return => 0x58548
| US_abort => 0x86980
| US___asan_report_store1 => 0x5786c
| US___asan_stack_malloc_1 => 0x3c1b8
| US_rp_hot_clamp => 0x7fd38
| US___asan_init => 0x586b0
| US___asan_version_mismatch_check_v8 => 0x58744
| US___asan_register_elf_globals => 0x3efa4
| US___asan_unregister_elf_globals => 0x3f010
| US___asan_report_store4 => 0x579ac
| US___interceptor_trampoline_memchr => 0x4107c
end.
Definition uci_obj (i : nat) : Z :=
match i with
| 0%nat => 0x97128
| 1%nat => 0x20ca0
| 2%nat => 0x97180
| 3%nat => 0x18ca6
| 4%nat => 0x7f950
| 5%nat => 0x97da0
| 6%nat => 0x97da8
| 7%nat => 0x9ba40
| 8%nat => 0x9f0f8
| 9%nat => 0x9f100
| _ => 0
end.
Definition uci_hi (j : nat) : Z :=
match j with
| 0%nat => 0x9732c
| 1%nat => 0x21354
| 2%nat => 0x21374
| 3%nat => 0x97598
| 4%nat => 0x976dc
| 5%nat => 0x96990
| 6%nat => 0x96994
| 7%nat => 0x189f4
| 8%nat => 0x7f9f8
| 9%nat => 0x97ce0
| 10%nat => 0x97ce4
| 11%nat => 0x9bcf0
| 12%nat => 0x97d10
| 13%nat => 0x97d14
| 14%nat => 0x9bd20
| 15%nat => 0x96d4c
| 16%nat => 0x9700c
| _ => 0
end.
Definition uci_nobj : nat := 10%nat.
Definition uci_nhi : nat := 17%nat.
