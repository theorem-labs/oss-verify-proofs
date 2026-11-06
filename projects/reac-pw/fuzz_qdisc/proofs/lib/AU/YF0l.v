(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0l.v at c8557374ad2e, with its module paths changed and every address relocated to libreac/fuzz_knock's asan image (sha256 61768cf4739b...): each value is the same function + offset in knock's symbol table (port_addr_check.py MAPS rows; h-rw-kno-2 knock-reloc/literals.tsv name-pair rows, masked instructions equal). Three cgif entries have no knock counterpart and are 0 (no code is at 0 in knock's image, which starts at 0x10000): __asan_stack_malloc_2 (cgif 0x3ca34; knock uses class 1 only), __asan_memcpy (cgif 0x515dc) and the bcmp trampoline (cgif 0x41904); knock's image has none of these symbols. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AF0l.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_qdisc's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AF0l.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_qdisc's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AF0l.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YG0f.
Local Open Scope Z_scope.
Definition Tfib_code : acode := {|
pc_malloc := 0x50d08;        pc_wrap_malloc := 0x50b34;   pc_malloc_ra0 := 0x50dd0;
pc_free := 0x50b38;          pc_wrap_free := 0x50b30;     pc_free_ra0 := 0x50c70;
pc_stack_malloc := fun cid => 0;
pc_asan_memcpy := 0;         pc_asan_memset := 0;
pc_wrap_memcpy := 0x4feb8;   pc_wrap_memset := 0x4feb4;   pc_wrap_memcmp := 0x408c0;  pc_wrap_bcmp := 0;
pc_wrap_read := 0x408cc;     pc_wrap_fwrite := 0x408d0;   pc_wrap_vprintf := 0x408dc; pc_wrap_vfprintf := 0x408e0;
pc_wrap_fprintf := 0x408e8;  pc_wrap_memchr := 0x408c4;   pc_wrap_strnlen := 0x408b4;
pc_region_is_poisoned := 0x5235c;
pc_spin_mmapdie := 0x5dbe8;  pc_spin_batch := 0x35070;    pc_spin_freearray := 0x33a4c; pc_spin_shadow := 0x6c0f0
|}.
