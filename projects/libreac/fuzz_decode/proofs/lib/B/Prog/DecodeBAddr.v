(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The addresses fuzz_decode.asan-ubsan gives the listing's names, objects and auipc values.
   The PAImg instance of this image checks them against the image. The objects
   past the ones the slots build are the cells the walks read through a GOT
   word: __asan_shadow_memory_dynamic_address (the shadow base) and
   __asan_option_detect_stack_use_after_return. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition decodeb_text : Z := 0x800b0.
Definition decodeb_sigma (s : dbsym) : Z :=
match s with
| DB___asan_stack_malloc_0 => 0x3c6fc
| DB___interceptor_trampoline_malloc => 0x51fb0
| DB___asan_memcpy => 0x50c5c
| DB_reac_frame_is_reac => 0x8144c
| DB_reac_frame_clean_len => 0x8158c
| DB_reac_frame_inspect => 0x815fc
| DB_reac_frame_counter => 0x814f8
| DB___asan_memset => 0x510f8
| DB_reac_decode => 0x81788
| DB___asan_report_load1 => 0x58200
| DB_check_round_trip => 0x80d54
| DB_check_braid => 0x81070
| DB_reac_decode_plain_le => 0x81a8c
| DB___interceptor_trampoline_bcmp => 0x415a4
| DB___interceptor_trampoline_free => 0x51fac
| DB_reac_upstream_channels => 0x81fe8
| DB_reac_upstream_decode => 0x82038
| DB___asan_handle_no_return => 0x591fc
| DB_abort => 0x88b3c
| DB___asan_report_load4 => 0x58340
| DB___interceptor_trampoline_calloc => 0x51fb4
| DB_reac_braid_encode => 0x81cfc
| DB___asan_report_store4 => 0x58660
| DB___asan_report_store8 => 0x58700
| DB___asan_init => 0x59364
| DB___asan_version_mismatch_check_v8 => 0x593f8
| DB___asan_register_elf_globals => 0x3f4cc
| DB___asan_unregister_elf_globals => 0x3f538
| DB___asan_report_store1 => 0x58520
| DB___asan_report_load8 => 0x583e0
end.
Definition decodeb_obj (i : nat) : Z :=
match i with
| 0%nat => 0x99340
| 1%nat => 0x992e8
| 2%nat => 0x1ffe2
| 3%nat => 0x800b0
| 4%nat => 0x99f60
| 5%nat => 0x99f68
| 6%nat => 0x99f70
| 7%nat => 0x10310
| 8%nat => 0x10360
| 9%nat => 0x10338
| 10%nat => 0x99f78
| 11%nat => 0x99f80
| 12%nat => 0x9dc80
| 13%nat => 0x103c8
| 14%nat => 0xa1338
| 15%nat => 0xa1340
| _ => 0
end.
Definition decodeb_hi (j : nat) : Z :=
match j with
| 0%nat => 0x990fc
| 1%nat => 0x99100
| 2%nat => 0x20158
| 3%nat => 0x8015c
| 4%nat => 0x9a23c
| 5%nat => 0x9a2c8
| 6%nat => 0x9a2dc
| 7%nat => 0x9a2e8
| 8%nat => 0x103e4
| 9%nat => 0x103f0
| 10%nat => 0x10900
| 11%nat => 0x98d9c
| 12%nat => 0x990bc
| 13%nat => 0x9a424
| 14%nat => 0x9a428
| 15%nat => 0x9e434
| 16%nat => 0x9946c
| 17%nat => 0x99510
| 18%nat => 0x10594
| 19%nat => 0x1059c
| 20%nat => 0x9a5d4
| 21%nat => 0x9a5d8
| 22%nat => 0x9d5e4
| 23%nat => 0x99618
| 24%nat => 0x997b8
| 25%nat => 0x99aac
| 26%nat => 0x98d38
| 27%nat => 0x20d68
| 28%nat => 0xfff4
| 29%nat => 0x10074
| 30%nat => 0x990dc
| _ => 0
end.
Definition decodeb_nobj : nat := 16%nat.
Definition decodeb_nhi : nat := 31%nat.
