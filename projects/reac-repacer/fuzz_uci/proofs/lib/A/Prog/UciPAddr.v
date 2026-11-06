(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The addresses fuzz_uci.asan gives the listing's names, objects and auipc values.
   The PAImg instance of this image checks them against the image. The objects
   past the ones the slots build are the cells the walks read through a GOT
   word: __asan_shadow_memory_dynamic_address (the shadow base) and
   __asan_option_detect_stack_use_after_return. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import UciPSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition uci_text : Z := 0x7f2e8.
Definition uci_sigma (s : usym) : Z :=
match s with
| US_check_no_overread => 0x7f4fc
| US_check_value => 0x7f62c
| US___asan_report_load1 => 0x5754c
| US_check_clamp => 0x7f888
| US___asan_report_load4 => 0x5768c
| US___interceptor_trampoline_malloc => 0x51788
| US___asan_memcpy => 0x50674
| US_rp_uci_int => 0x7fef0
| US___interceptor_trampoline_free => 0x51784
| US___asan_handle_no_return => 0x58548
| US_abort => 0x86878
| US___asan_report_store1 => 0x5786c
| US___asan_stack_malloc_1 => 0x3c1b8
| US_rp_hot_clamp => 0x7fc64
| US___asan_init => 0x586b0
| US___asan_version_mismatch_check_v8 => 0x58744
| US___asan_register_elf_globals => 0x3efa4
| US___asan_unregister_elf_globals => 0x3f010
| US___asan_report_store4 => 0x579ac
| US___interceptor_trampoline_memchr => 0x4107c
end.
Definition uci_obj (i : nat) : Z :=
match i with
| 0%nat => 0x97020
| 1%nat => 0x20ca0
| 2%nat => 0x97078
| 3%nat => 0x18ca6
| 4%nat => 0x7f888
| 5%nat => 0x97c98
| 6%nat => 0x97ca0
| 7%nat => 0x9b940
| 8%nat => 0x9eff8
| 9%nat => 0x9f000
| _ => 0
end.
Definition uci_hi (j : nat) : Z :=
match j with
| 0%nat => 0x9732c
| 1%nat => 0x21360
| 2%nat => 0x97528
| 3%nat => 0x97658
| 4%nat => 0x968c8
| 5%nat => 0x968cc
| 6%nat => 0x1892c
| 7%nat => 0x7f930
| 8%nat => 0x97c0c
| 9%nat => 0x97c10
| 10%nat => 0x9bc1c
| 11%nat => 0x97c3c
| 12%nat => 0x97c40
| 13%nat => 0x9bc4c
| 14%nat => 0x96c6c
| 15%nat => 0x96f18
| _ => 0
end.
Definition uci_nobj : nat := 10%nat.
Definition uci_nhi : nat := 16%nat.
