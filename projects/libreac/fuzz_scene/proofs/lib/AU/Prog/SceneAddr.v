(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Generated from fuzz_scene.asan-ubsan (sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f) by mklisting.py, sha256 b39bde09dd82c7145e8d7f6d64672434e9e1bae7a8bd14a241d13a4ed7d7d950 (with the --pin aliasing fix, a Theorem Labs lane 20:43Z), run with fuzz_grant's own flags and no --pin, and by emit_rocq_au.py, sha256 1085eb2ae647583d23a0f6aafe23c1e7a6d719568d4be1cf0fbf73d66675df1a, the copy of emit_rocq.py (sha256 349555509064; internal record) that writes the files of this build under lib/AU/Prog. *)
(* The addresses fuzz_scene.asan-ubsan (sha256 e98b1ed286c1aa5c3d558cb2069011d2413d58b2122f741531364382a528833f) gives the listing's
   names, objects and auipc values. SceneImg.v checks them against the image.
   Every symbol address comes from the .symtab of the unstripped twin unstripped/fuzz_scene/fuzz_scene.asan-ubsan (its loaded bytes are the pinned image's apart from the ELF header's section-table fields and the build-id note);
   each object and auipc value is the address the image's own auipc pair builds.
   Object 16 is built by no slot: it is __asan_shadow_memory_dynamic_address,
   at 0xa3af8, which a GOT word of the image holds and the walks read.
   Object 17 is built by no slot: it is __asan_option_detect_stack_use_after_return,
   at 0xa3b00, which a GOT word of the image holds and the walks read.
   *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable SceneSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition scene_text : Z := 0x828a4.
Definition scene_sigma (s : ssym) : Z :=
match s with
| SS___asan_stack_malloc_8 => 0x3f438
| SS___asan_set_shadow_f8 => 0x569d0
| SS___asan_report_load1 => 0x5ab08
| SS___interceptor_trampoline_malloc => 0x54d44
| SS___asan_memset => 0x53e8c
| SS_reac_ctrl_build_scene_step => 0x83a70
| SS_check_step => 0x83294
| SS___asan_memcpy => 0x539f0
| SS___interceptor_trampoline_bcmp => 0x44338
| SS___interceptor_trampoline_free => 0x54d40
| SS_reac_ctrl_scene_set_mac => 0x83e04
| SS_reac_ctrl_scene_build => 0x83e58
| SS___asan_set_shadow_00 => 0x568b0
| SS___asan_stack_free_8 => 0x3f5b4
| SS___asan_handle_no_return => 0x5bb04
| SS_abort => 0x8b294
| SS___asan_report_store1 => 0x5ae28
| SS___asan_stack_malloc_2 => 0x3f29c
| SS_reac_ctrl_parse => 0x84028
| SS_reac_ctrl_checksum_verify => 0x839e8
| SS___asan_init => 0x5bc6c
| SS___asan_version_mismatch_check_v8 => 0x5bd00
| SS___asan_register_elf_globals => 0x42260
| SS___asan_unregister_elf_globals => 0x422cc
| SS_reac_ctrl_block_cksum_stamp => 0x83930
| SS___asan_report_store_n => 0x5b1e8
| SS___asan_stack_malloc_1 => 0x3f10c
| SS_kind_of_link1 => 0x84aac
| SS___asan_report_store4 => 0x5af68
| SS___asan_report_store2 => 0x5aec8
| SS___asan_report_load4 => 0x5ac48
end.
Definition scene_obj (i : nat) : Z :=
match i with
| 0%nat => 0x9ba98
| 1%nat => 0x9ba40
| 2%nat => 0x196aa
| 3%nat => 0x828a4
| 4%nat => 0x9c6b8
| 5%nat => 0x14ef7
| 6%nat => 0x83294
| 7%nat => 0x20d80
| 8%nat => 0x20da0
| 9%nat => 0x9c6c0
| 10%nat => 0x9c6c8
| 11%nat => 0xa0440
| 12%nat => 0x20e20
| 13%nat => 0x17552
| 14%nat => 0x84028
| 15%nat => 0x20e40
| 16%nat => 0xa3af8
| 17%nat => 0xa3b00
| _ => 0
end.
Definition scene_hi (j : nat) : Z :=
match j with
| 0%nat => 0x9b8f0
| 1%nat => 0x9b8f4
| 2%nat => 0x1995c
| 3%nat => 0x82960
| 4%nat => 0x9cc64
| 5%nat => 0x9b2e4
| 6%nat => 0x9b2e8
| 7%nat => 0x15348
| 8%nat => 0x8334c
| 9%nat => 0x20618
| 10%nat => 0x2064c
| 11%nat => 0x9c8d8
| 12%nat => 0x9c8dc
| 13%nat => 0xa08e8
| 14%nat => 0x9c908
| 15%nat => 0x9c90c
| 16%nat => 0xa0918
| 17%nat => 0x9b93c
| 18%nat => 0x9b9f8
| 19%nat => 0x9bab8
| 20%nat => 0x20ca4
| 21%nat => 0x9be8c
| 22%nat => 0x9c074
| 23%nat => 0x9c078
| 24%nat => 0x170d8
| 25%nat => 0x840dc
| 26%nat => 0x21210
| _ => 0
end.
Definition scene_nobj : nat := 18%nat.
Definition scene_nhi : nat := 27%nat.
