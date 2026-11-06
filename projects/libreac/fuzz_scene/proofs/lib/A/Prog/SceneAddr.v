(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Generated from fuzz_scene.asan (sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026) by mklisting.py, sha256 b39bde09dd82c7145e8d7f6d64672434e9e1bae7a8bd14a241d13a4ed7d7d950 (with the --pin aliasing fix, a Theorem Labs lane 20:43Z), run with fuzz_grant's own flags and no --pin, and by emit_rocq.py, sha256 34955550906406a211aeadad3b715013a584b480d96e1ba64c3180e51c8d5b1b, a copy of emit_rocq.py kept as emit_rocq.py (sha256 349555509064; internal record), that writes this target's names. *)
(* The addresses fuzz_scene.asan (sha256 43654a025fd02e1f248bcaf6b8ac44f9e5dbded7f2fc1d9a1e90f9d74feb3026) gives the listing's
   names, objects and auipc values. SceneImg.v checks them against the image.
   Every symbol address comes from the .symtab of the unstripped twin unstripped/fuzz_scene/fuzz_scene.asan (its loaded bytes are the pinned image's apart from the ELF header's section-table fields and the build-id note; no code, rodata, relro or data byte differs);
   each object and auipc value is the address the image's own auipc pair builds.
   Object 16 is built by no slot: it is __asan_shadow_memory_dynamic_address,
   at 0xa37f8, which a GOT word of the image holds and the walks read.
   Object 17 is built by no slot: it is __asan_option_detect_stack_use_after_return,
   at 0xa3800, which a GOT word of the image holds and the walks read.
   *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import PaTable SceneSyms.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.
Definition scene_text : Z := 0x82878.
Definition scene_sigma (s : ssym) : Z :=
match s with
| SS___asan_stack_malloc_8 => 0x3f40c
| SS___asan_set_shadow_f8 => 0x569a4
| SS___asan_report_load1 => 0x5aadc
| SS___interceptor_trampoline_malloc => 0x54d18
| SS___asan_memset => 0x53e60
| SS_reac_ctrl_build_scene_step => 0x83834
| SS_check_step => 0x8319c
| SS___asan_memcpy => 0x539c4
| SS___interceptor_trampoline_bcmp => 0x4430c
| SS___interceptor_trampoline_free => 0x54d14
| SS_reac_ctrl_scene_set_mac => 0x83bdc
| SS_reac_ctrl_scene_build => 0x83c24
| SS___asan_set_shadow_00 => 0x56884
| SS___asan_stack_free_8 => 0x3f588
| SS___asan_handle_no_return => 0x5bad8
| SS_abort => 0x8af60
| SS___asan_report_store1 => 0x5adfc
| SS___asan_stack_malloc_2 => 0x3f270
| SS_reac_ctrl_parse => 0x83dd8
| SS_reac_ctrl_checksum_verify => 0x837c0
| SS___asan_init => 0x5bc40
| SS___asan_version_mismatch_check_v8 => 0x5bcd4
| SS___asan_register_elf_globals => 0x42234
| SS___asan_unregister_elf_globals => 0x422a0
| SS___asan_report_store_n => 0x5b1bc
| SS___asan_stack_malloc_1 => 0x3f0e0
| SS_kind_of_link1 => 0x84778
| SS___asan_report_store4 => 0x5af3c
| SS___asan_report_store2 => 0x5ae9c
| SS___asan_report_load4 => 0x5ac1c
end.
Definition scene_obj (i : nat) : Z :=
match i with
| 0%nat => 0x9b768
| 1%nat => 0x9b710
| 2%nat => 0x196aa
| 3%nat => 0x82878
| 4%nat => 0x9c388
| 5%nat => 0x14ef7
| 6%nat => 0x8319c
| 7%nat => 0x20d80
| 8%nat => 0x20da0
| 9%nat => 0x9c390
| 10%nat => 0x9c398
| 11%nat => 0xa0140
| 12%nat => 0x20e20
| 13%nat => 0x17552
| 14%nat => 0x83dd8
| 15%nat => 0x20e40
| 16%nat => 0xa37f8
| 17%nat => 0xa3800
| _ => 0
end.
Definition scene_hi (j : nat) : Z :=
match j with
| 0%nat => 0x9b8c4
| 1%nat => 0x9b8c8
| 2%nat => 0x19930
| 3%nat => 0x82934
| 4%nat => 0x9bbb0
| 5%nat => 0x9b1ec
| 6%nat => 0x9b1f0
| 7%nat => 0x15250
| 8%nat => 0x83254
| 9%nat => 0x214bc
| 10%nat => 0x214f0
| 11%nat => 0x9c768
| 12%nat => 0x9c76c
| 13%nat => 0xa0778
| 14%nat => 0x9c798
| 15%nat => 0x9c79c
| 16%nat => 0xa07a8
| 17%nat => 0x9b7cc
| 18%nat => 0x9b87c
| 19%nat => 0x20a10
| 20%nat => 0x9bc58
| 21%nat => 0x9be24
| 22%nat => 0x9be28
| 23%nat => 0x16e88
| 24%nat => 0x83e8c
| 25%nat => 0x20f8c
| _ => 0
end.
Definition scene_nobj : nat := 18%nat.
Definition scene_nhi : nat := 26%nat.
