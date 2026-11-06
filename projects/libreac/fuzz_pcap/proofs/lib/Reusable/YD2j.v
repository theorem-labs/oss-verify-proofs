(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/YD2i.v and lib/YD2j.v (origin/ossv/recipes c8557374ad2e) for libreac/fuzz_pcap's asan-ubsan image (sha256 9e66f771f22a...) by a Theorem Labs lane's gen_ad2.py, with its module paths changed: sregs_main, TIDV, CANV and TFIB_MAIN from the 50 hand-off states of lib/Reusable/YB01.v, the image bounds from lib/Reusable/YB12.v and lib/Reusable/YB1h.v; IMG_REGIONS below .data from the image and the owned static cells of lib/Reusable/YF0m.v, from .data on cgif's regions at the same offsets from their section anchors (checked against the unstripped twin's symbols, c969d83cdd59...), every CVal value read from the hand-off states *)
(* Modified by Theorem Labs, 2026-10-29: the cut set the generator was given is Tfib_owned_static of lib/Reusable/YF0m.v UNION the BODIES of the harness globals registered in the image's asan_globals table whose body lies in .bss -- g_file_len [0x5d3e40, 0x5d3e48) and g_file [0x5d3e60, 0x5d3e68) (the asan twins at +0x100).  No at-main state writes the harness-global hull (only the writable hull KWr), so IMG_REGIONS carries NO region over [0x5d3e40, 0x5d3e80): R_A5a is cut into R_A5a_1 [0x5d3e10, 0x5d3e40) and R_A5a_2 [0x5d3e80, 0x5d46ec), 33 regions.  YF0m.v itself is unchanged (the harness-globals ruling keeps the bodies out of owned_static); the widening is in the generator INPUT, prep_owned.py (sha256 9d548aaca227; internal record) --globals-bss. *)
(* gated: a Theorem Labs lane PASS A+B at c061542723f / 731386609e0.  Read independently by gate_check.py (sha256 b1cf8cb7ca98; internal record): GATE ok, 33 regions, 4 with gaps, 0 NEW gaps, 0 failures; kimg_overlap 0 conflicts; codeptr c0ce606ed1fa (startup-set 2026-10-29): 0 findings / 0 stale on every file, with 20 declarations carrying their measured reasons in declarations-20.sh (sha256 880286aef98b; internal record); AB1m / YB1m UNMEASURED (no address literal; BFUEL is %nat); logs final20.txt (sha256 b2b70d12a063; internal record) / final20.no-b1m.txt (sha256 be056cbfc3b7; internal record) (a Theorem Labs lane); an independent run by a second lane agrees (asan-ubsan.declared.out (sha256 9949145995f3; internal record)) *)
(* Before commit 5098883da0b3 (2026-10-29) brought YF0l and YB13 into this tree, the asan-ubsan files built ONLY in a union that also included a working branch 27d40cfe97f76cd158308a2aef684e7e509db360: lib/Reusable/YF0m.v Requires YF0l and lib/Reusable/YD2i.v Requires YB13, both of them core files of that branch. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP09.
Import ListNotations.
Open Scope Z_scope.
Definition R_A1a : region :=
mkRegion None 65536 (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x8)%Z) 0 0
[ mkChunk 65536 (CImg (symaddr ((Symbols.AsanUbsan.Sec.s_rodata + 0x8) - (65536))%Z)) ].
Definition R_A1b : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x10)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x28)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x10)%Z) (CImg 24) ].
Definition R_A1c : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x30)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x48)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x30)%Z) (CImg 24) ].
Definition R_A1d : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x50)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xb8)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x50)%Z) (CImg 104) ].
Definition R_A1e : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc8)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd0)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc8)%Z) (CImg 8) ].
Definition R_A1f : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd8)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x140)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xd8)%Z) (CImg 104) ].
Definition R_A1g : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x180)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x240)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x180)%Z) (CImg 192) ].
Definition R_A1h : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x280)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc978)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0x280)%Z) (CImg 50936) ].
Definition R_A1i : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc98d)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67488)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 0xc98d)%Z) (CImg 15891) ].
Definition R_A1j : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67492)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68141)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 67492)%Z) (CImg 649) ].
Definition R_A1k : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68160)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68195)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68160)%Z) (CImg 35) ].
Definition R_A1l : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68224)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 69636)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 68224)%Z) (CImg 1412) ].
Definition R_A1m : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 69640)%Z) (symaddr (Symbols.AsanUbsan.s_sysconf_values + 0x3c)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_rodata + 69640)%Z) (CImg 96) ].
Definition R_A1n : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.s_sysconf_values + 0x3e)%Z) (symaddr ImgPages.AsanUbsan.relro_lo) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.s_sysconf_values + 0x3e)%Z) (CImg (symaddr ((626688) - (Symbols.AsanUbsan.s_sysconf_values + 0x3e))%Z)) ].
Definition R_A2a : region :=
mkRegion None (symaddr ImgPages.AsanUbsan.relro_lo) (symaddr (Symbols.AsanUbsan.Sec.s_got + 0x40)%Z) 0 0
[ mkChunk (symaddr ImgPages.AsanUbsan.relro_lo) (CImg (symaddr ((Symbols.AsanUbsan.Sec.s_got + 0x40) - (626688))%Z)) ].
Definition R_A2b : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xc0)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xbc8)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xc0)%Z) (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xbd0)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xcb8)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xbd0)%Z) (CImg 232) ].
Definition R_A2d : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xcc0)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xcd8)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xcc0)%Z) (CImg 24) ].
Definition R_A2e : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xce8)%Z) (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xd40)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xce8)%Z) (CImg 8);
mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_got + 0xcf0)%Z) (CImg 80) ].
Definition R_A2f : region :=
mkRegion None (symaddr Symbols.AsanUbsan.Sec.s_relro_padding) (symaddr Symbols.AsanUbsan.s___dso_handle) 0 0
[ mkChunk (symaddr Symbols.AsanUbsan.Sec.s_relro_padding) (CImg (symaddr ((Symbols.AsanUbsan.s___dso_handle) - (Symbols.AsanUbsan.Sec.s_relro_padding))%Z)) ].
Definition R_A3 : region :=
mkRegion None (symaddr Symbols.AsanUbsan.s_oft_arg0) (symaddr Symbols.AsanUbsan.Sec.s_asan_globals) (symaddr Symbols.AsanUbsan.s_oft_arg0) (symaddr Symbols.AsanUbsan.Sec.s_asan_globals)
[ mkChunk (symaddr Symbols.AsanUbsan.s_oft_arg0) (CImg (symaddr ((Symbols.AsanUbsan.Sec.s_asan_globals) - (Symbols.AsanUbsan.s_oft_arg0))%Z)) ].
Definition R_A4 : region :=
mkRegion None (symaddr Symbols.AsanUbsan.s___do_init___initialized) (symaddr Symbols.AsanUbsan.s___do_fini___finalized) (symaddr Symbols.AsanUbsan.s___do_init___initialized) (symaddr Symbols.AsanUbsan.s___do_fini___finalized)
[ mkChunk (symaddr Symbols.AsanUbsan.s___do_init___initialized) (CVal 1 (SLit 1));
mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_bss + 0x9)%Z) (CImg 71) ].
Definition R_RS : region :=
mkRegion None (symaddr Symbols.AsanUbsan.s_read_stage) (symaddr Symbols.AsanUbsan.s_target_run_initialized) 0 0
[  ].
Definition R_A5a_1 : region :=
mkRegion None (symaddr Symbols.AsanUbsan.s_target_run_initialized) (symaddr Symbols.AsanUbsan.s_g_file_len) (symaddr Symbols.AsanUbsan.s_target_run_initialized) (symaddr Symbols.AsanUbsan.s_g_file_len)
[ mkChunk (symaddr Symbols.AsanUbsan.s_target_run_initialized) (CImg 4);
mkChunk (symaddr Symbols.AsanUbsan.s_oft_in_callback) (CVal 1 (SLit 0));
mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_bss + 5463317)%Z) (CImg 43) ].
Definition R_A5a_2 : region :=
mkRegion None (symaddr Symbols.AsanUbsan.s__ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE5_lockE) (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x24)%Z) (symaddr Symbols.AsanUbsan.s__ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE5_lockE) (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x24)%Z)
[ mkChunk (symaddr Symbols.AsanUbsan.s__ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE5_lockE) (CImg 2112);
mkChunk (symaddr Symbols.AsanUbsan.s_builtin_tls) (CVal 8 (SLit (symaddr Symbols.AsanUbsan.s_builtin_tls)));
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x8)%Z) (CVal 8 (SLit (symaddr Symbols.AsanUbsan.s_builtin_tls)));
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x10)%Z) (CVal 8 (SLit (symaddr Symbols.AsanUbsan.s_builtin_tls)));
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x18)%Z) (CVal 8 (SLit 0));
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x20)%Z) (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x28)%Z) (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x70)%Z) (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x28)%Z) (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x70)%Z)
[ mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x28)%Z) (CVal 4 (SLit 2));
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x2c)%Z) (CImg 6);
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x32)%Z) (CVal 1 (SLit 1));
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x33)%Z) (CImg 61) ].
Definition R_A6 : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x78)%Z) (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0xc0)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x78)%Z) (CVal 8 (SLit (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x78)%Z)));
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x80)%Z) (CImg 24);
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x98)%Z) (CVal 8 (SLit (symaddr (Symbols.AsanUbsan.s___libc + 0x38)%Z)));
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0xa0)%Z) (CImg 24);
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0xb8)%Z) (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x104)%Z) (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x110)%Z) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.s_builtin_tls + 0x104)%Z) (CImg 12) ].
Definition R_A7b : region :=
mkRegion None (symaddr Symbols.AsanUbsan.s___thread_list_lock) (symaddr (Symbols.AsanUbsan.s___libc + 0x30)%Z) (symaddr Symbols.AsanUbsan.s_finished_atexit) (symaddr Symbols.AsanUbsan.s_exit_exit_lock)
[ mkChunk (symaddr Symbols.AsanUbsan.s___thread_list_lock) (CImg 16);
mkChunk (symaddr (Symbols.AsanUbsan.s_main_tls + 0x8)%Z) (CVal 8 (SLit (symaddr Symbols.AsanUbsan.Sec.s_tbss)));
mkChunk (symaddr (Symbols.AsanUbsan.s_main_tls + 0x10)%Z) (CVal 8 (SLit 0));
mkChunk (symaddr (Symbols.AsanUbsan.s_main_tls + 0x18)%Z) (CVal 8 (SLit 24));
mkChunk (symaddr (Symbols.AsanUbsan.s_main_tls + 0x20)%Z) (CVal 8 (SLit 8));
mkChunk (symaddr (Symbols.AsanUbsan.s_main_tls + 0x28)%Z) (CVal 8 (SLit 0));
mkChunk (symaddr Symbols.AsanUbsan.s___stack_chk_guard) (CVal 8 (SOff 41 0));
mkChunk (symaddr Symbols.AsanUbsan.s___abort_lock) (CImg 16);
mkChunk (symaddr Symbols.AsanUbsan.s_slot) (CVal 4 (SLit 1));
mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_bss + 5596908)%Z) (CImg 4);
mkChunk (symaddr Symbols.AsanUbsan.s_head) (CVal 8 (SLit (symaddr Symbols.AsanUbsan.s_builtin)));
mkChunk (symaddr Symbols.AsanUbsan.s_builtin) (CImg 8);
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin + 0x8)%Z) (CVal 8 (SLit (symaddr Symbols.AsanUbsan.s_call)));
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin + 0x10)%Z) (CImg 248);
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin + 0x108)%Z) (CVal 8 (SLit (symaddr Symbols.AsanUbsan.s___sanitizer_cov_dump)));
mkChunk (symaddr (Symbols.AsanUbsan.s_builtin + 0x110)%Z) (CImg 264);
mkChunk (symaddr Symbols.AsanUbsan.s_program_invocation_name) (CVal 8 (SOff 1 0));
mkChunk (symaddr Symbols.AsanUbsan.s___libc) (CVal 1 (SLit 1));
mkChunk (symaddr (Symbols.AsanUbsan.s___libc + 0x1)%Z) (CImg 7);
mkChunk (symaddr (Symbols.AsanUbsan.s___libc + 0x8)%Z) (CVal 8 (SOff 5 0));
mkChunk (symaddr (Symbols.AsanUbsan.s___libc + 0x10)%Z) (CVal 8 (SLit (symaddr Symbols.AsanUbsan.s_main_tls)));
mkChunk (symaddr (Symbols.AsanUbsan.s___libc + 0x18)%Z) (CVal 8 (SLit 248));
mkChunk (symaddr (Symbols.AsanUbsan.s___libc + 0x20)%Z) (CVal 8 (SLit 8));
mkChunk (symaddr (Symbols.AsanUbsan.s___libc + 0x28)%Z) (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.s___libc + 0x38)%Z) (symaddr Symbols.AsanUbsan.s___malloc_context) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.s___libc + 0x38)%Z) (CImg 48);
mkChunk (symaddr Symbols.AsanUbsan.s_freebuf_queue) (CImg 16) ].
Definition R_A8 : region :=
mkRegion None (symaddr Symbols.AsanUbsan.s___malloc_replaced) (symaddr Symbols.AsanUbsan.s_funcs) 0 0
[ mkChunk (symaddr Symbols.AsanUbsan.s___malloc_replaced) (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None (symaddr Symbols.AsanUbsan.s_tl_lock_count) (symaddr Symbols.AsanUbsan.s___pthread_tsd_main) 0 0
[ mkChunk (symaddr Symbols.AsanUbsan.s_tl_lock_count) (CImg 8);
mkChunk (symaddr Symbols.AsanUbsan.s_keys) (CVal 8 (SLit (symaddr Symbols.AsanUbsan.s__ZN6__asan15PlatformTSDDtorEPv)));
mkChunk (symaddr (Symbols.AsanUbsan.s_keys + 0x8)%Z) (CImg 1016);
mkChunk (symaddr Symbols.AsanUbsan.s_next_key) (CVal 4 (SLit 0));
mkChunk (symaddr (Symbols.AsanUbsan.Sec.s_bss + 5601788)%Z) (CImg 4);
mkChunk (symaddr Symbols.AsanUbsan.s_key_lock) (CVal 4 (SLit 0));
mkChunk (symaddr (Symbols.AsanUbsan.s_key_lock + 0x4)%Z) (CImg 52) ].
Definition R_A9b : region :=
mkRegion None (symaddr (Symbols.AsanUbsan.s___pthread_tsd_main + 0x8)%Z) (symaddr ImgPages.AsanUbsan.top) 0 0
[ mkChunk (symaddr (Symbols.AsanUbsan.s___pthread_tsd_main + 0x8)%Z) (CImg (symaddr ((6254592) - (Symbols.AsanUbsan.s___pthread_tsd_main + 0x8))%Z)) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a_1; R_A5a_2; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
