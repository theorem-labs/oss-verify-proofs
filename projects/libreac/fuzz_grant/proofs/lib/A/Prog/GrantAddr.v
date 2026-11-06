(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* The addresses fuzz_grant.asan gives the listing's names, objects and
   auipc values. GrantImg.v checks them against the image. The objects past the
   ones the slots build are the cells the walks read through a GOT word:
   __asan_shadow_memory_dynamic_address (the shadow base) and
   __asan_option_detect_stack_use_after_return. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable GrantSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition grant_text : Z := 0x806b0.
Definition grant_sigma (s : gsym) : Z :=
match s with
| GS___asan_stack_malloc_4 => 0x3d244
| GS___interceptor_trampoline_malloc => 0x52b50
| GS_reac_headamp_tx_init => 0x84d1c
| GS___asan_memset => 0x51c98
| GS_reac_headamp_tx_set => 0x84d3c
| GS_reac_headamp_tx_effective => 0x84e64
| GS_reac_headamp_default => 0x84e54
| GS___asan_report_load1 => 0x58914
| GS_reac_grant_alloc_fits => 0x8483c
| GS_reac_grant_allocate => 0x84860
| GS_reac_grant_build_sweep => 0x848f0
| GS___interceptor_trampoline_bcmp => 0x42144
| GS_check_groupa => 0x81b70
| GS_reac_ctrl_identity_poll_block => 0x82d3c
| GS___interceptor_trampoline_free => 0x52b4c
| GS_reac_headamp_tx_arm_scene => 0x84f1c
| GS_reac_headamp_tx_set_resweep => 0x85058
| GS_reac_headamp_tx_next => 0x850cc
| GS___asan_set_shadow_f5 => 0x547c4
| GS___asan_set_shadow_00 => 0x546bc
| GS___asan_handle_no_return => 0x59910
| GS_abort => 0x8bf50
| GS___asan_report_store1 => 0x58c34
| GS___asan_stack_malloc_2 => 0x3d0a8
| GS___asan_memcpy => 0x517fc
| GS_reac_ctrl_parse => 0x82000
| GS_reac_ctrl_headamp_record_verify => 0x82c60
| GS_reac_ctrl_checksum_verify => 0x81f8c
| GS___asan_init => 0x59a78
| GS___asan_version_mismatch_check_v8 => 0x59b0c
| GS___asan_register_elf_globals => 0x4006c
| GS___asan_unregister_elf_globals => 0x400d8
| GS___asan_stack_malloc_1 => 0x3cf18
| GS_kind_of_link1 => 0x829a0
| GS___asan_report_store4 => 0x58d74
| GS___asan_report_store2 => 0x58cd4
| GS___asan_report_load4 => 0x58a54
| GS___asan_stack_malloc_0 => 0x3cda4
| GS_ctrl_lay_block => 0x82ffc
| GS_ctrl_finish => 0x8339c
| GS_reac_ctrl_stamp_headamp => 0x82a14
| GS_reac_box_model_block => 0x8354c
| GS___asan_report_load8 => 0x58af4
| GS_build_dt1_single => 0x843cc
| GS___asan_report_load2 => 0x589b4
| GS_reac_ctrl_build_grant_sweep => 0x82d8c
end.
Definition grant_obj (i : nat) : Z :=
match i with
| 0%nat => 0x9c8c8
| 1%nat => 0x9c870
| 2%nat => 0x12d76
| 3%nat => 0x806b0
| 4%nat => 0x20ec0
| 5%nat => 0x20f20
| 6%nat => 0x20e80
| 7%nat => 0x14ff0
| 8%nat => 0x81b70
| 9%nat => 0x20f80
| 10%nat => 0x9d4e8
| 11%nat => 0x9d4f0
| 12%nat => 0xa1480
| 13%nat => 0x17669
| 14%nat => 0x82000
| 15%nat => 0x21020
| 16%nat => 0x1ca62
| 17%nat => 0x82a14
| 18%nat => 0x9c670
| 19%nat => 0x21040
| 20%nat => 0x211c0
| 21%nat => 0x21220
| 22%nat => 0x19ecc
| 23%nat => 0x82ffc
| 24%nat => 0x20ff4
| 25%nat => 0x12e47
| 26%nat => 0x8354c
| 27%nat => 0x21294
| 28%nat => 0x212c0
| 29%nat => 0x21300
| 30%nat => 0x1af4f
| 31%nat => 0x848f0
| 32%nat => 0xa4b38
| 33%nat => 0xa4b40
| _ => 0
end.
Definition grant_hi (j : nat) : Z :=
match j with
| 0%nat => 0x9c6fc
| 1%nat => 0x9c700
| 2%nat => 0x1275c
| 3%nat => 0x80760
| 4%nat => 0x21000
| 5%nat => 0x2101c
| 6%nat => 0x211d8
| 7%nat => 0x9cbc8
| 8%nat => 0x9cbcc
| 9%nat => 0x14c30
| 10%nat => 0x81c34
| 11%nat => 0x20cdc
| 12%nat => 0x9cf34
| 13%nat => 0x9cf38
| 14%nat => 0xa0f44
| 15%nat => 0x9cf64
| 16%nat => 0x9cf68
| 17%nat => 0xa0f74
| 18%nat => 0x9cf98
| 19%nat => 0x9d04c
| 20%nat => 0x9d050
| 21%nat => 0x170b0
| 22%nat => 0x820b4
| 23%nat => 0x211b4
| 24%nat => 0x9ca60
| 25%nat => 0x9ca64
| 26%nat => 0x1cac0
| 27%nat => 0x82ac4
| 28%nat => 0x9cb80
| 29%nat => 0x9cc68
| 30%nat => 0x20d60
| 31%nat => 0x9ce00
| 32%nat => 0x20e0c
| 33%nat => 0x20eb0
| 34%nat => 0x20ec8
| 35%nat => 0x1a0ac
| 36%nat => 0x830b0
| 37%nat => 0x21144
| 38%nat => 0x9c3a4
| 39%nat => 0x9c59c
| 40%nat => 0x9c5a0
| 41%nat => 0x135fc
| 42%nat => 0x83600
| 43%nat => 0x21678
| 44%nat => 0x218b4
| 45%nat => 0x218f4
| 46%nat => 0x9c3e8
| 47%nat => 0x9c88c
| 48%nat => 0x9c944
| 49%nat => 0x9c948
| 50%nat => 0x1a9a4
| 51%nat => 0x849a8
| 52%nat => 0x9cd50
| 53%nat => 0x9ce88
| 54%nat => 0x9cf50
| 55%nat => 0x9d060
| 56%nat => 0x9c0f8
| _ => 0
end.
Definition grant_nobj : nat := 34%nat.
Definition grant_nhi : nat := 57%nat.
