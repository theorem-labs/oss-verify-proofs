(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The addresses fuzz_decode.asan gives the listing's names, objects and auipc values.
   The PAImg instance of this image checks them against the image. The objects
   past the ones the slots build are the cells the walks read through a GOT
   word: __asan_shadow_memory_dynamic_address (the shadow base) and
   __asan_option_detect_stack_use_after_return. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition decode_text : Z := 0x80064.
Definition decode_sigma (s : dsym) : Z :=
match s with
| DS___asan_stack_malloc_0 => 0x3c6b0
| DS___interceptor_trampoline_malloc => 0x51f64
| DS___asan_memcpy => 0x50c10
| DS_reac_frame_is_reac => 0x81154
| DS_reac_frame_clean_len => 0x8126c
| DS_reac_frame_inspect => 0x812dc
| DS_reac_frame_counter => 0x811ec
| DS___asan_memset => 0x510ac
| DS_reac_decode => 0x81434
| DS___asan_report_load1 => 0x581b4
| DS_check_round_trip => 0x80bc8
| DS_check_braid => 0x80e58
| DS_reac_decode_plain_le => 0x816b0
| DS___interceptor_trampoline_bcmp => 0x41558
| DS___interceptor_trampoline_free => 0x51f60
| DS_reac_upstream_channels => 0x81ad0
| DS_reac_upstream_decode => 0x81b20
| DS___asan_handle_no_return => 0x591b0
| DS_abort => 0x88594
| DS___asan_report_load4 => 0x582f4
| DS___interceptor_trampoline_calloc => 0x51f68
| DS_reac_braid_encode => 0x818d4
| DS___asan_report_store4 => 0x58614
| DS___asan_report_store8 => 0x586b4
| DS___asan_init => 0x59318
| DS___asan_version_mismatch_check_v8 => 0x593ac
| DS___asan_register_elf_globals => 0x3f480
| DS___asan_unregister_elf_globals => 0x3f4ec
| DS___asan_report_store1 => 0x584d4
| DS___asan_report_load8 => 0x58394
end.
Definition decode_obj (i : nat) : Z :=
match i with
| 0%nat => 0x98d98
| 1%nat => 0x98d40
| 2%nat => 0x1ffda
| 3%nat => 0x80064
| 4%nat => 0x999b8
| 5%nat => 0x999c0
| 6%nat => 0x999c8
| 7%nat => 0x10310
| 8%nat => 0x103c0
| 9%nat => 0x10338
| 10%nat => 0x999d0
| 11%nat => 0x999d8
| 12%nat => 0x9d700
| 13%nat => 0xa0db8
| 14%nat => 0xa0dc0
| _ => 0
end.
Definition decode_hi (j : nat) : Z :=
match j with
| 0%nat => 0x990b0
| 1%nat => 0x990b4
| 2%nat => 0x2010c
| 3%nat => 0x80110
| 4%nat => 0x9a1b4
| 5%nat => 0x9924c
| 6%nat => 0x99260
| 7%nat => 0x9926c
| 8%nat => 0x1033c
| 9%nat => 0x10348
| 10%nat => 0x107bc
| 11%nat => 0x98c0c
| 12%nat => 0x98e94
| 13%nat => 0x9a12c
| 14%nat => 0x9a130
| 15%nat => 0x9d13c
| 16%nat => 0x9916c
| 17%nat => 0x991f4
| 18%nat => 0x10274
| 19%nat => 0x1027c
| 20%nat => 0x992b4
| 21%nat => 0x992b8
| 22%nat => 0x9d2c4
| 23%nat => 0x992ec
| 24%nat => 0x99460
| 25%nat => 0x986d0
| 26%nat => 0x988f4
| 27%nat => 0x20920
| 28%nat => 0x10adc
| 29%nat => 0xfb50
| 30%nat => 0x98bac
| _ => 0
end.
Definition decode_nobj : nat := 15%nat.
Definition decode_nhi : nat := 31%nat.
