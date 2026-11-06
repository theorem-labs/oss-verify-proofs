(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/A/AD2i.v and lib/A/AD2j.v (origin/ossv/recipes c8557374ad2e) for libreac/fuzz_pcap's asan image (sha256 b7a91d9b1fb0...) by a Theorem Labs lane's gen_ad2.py, with its module paths changed: sregs_main, TIDV, CANV and TFIB_MAIN from the 50 hand-off states of lib/A/AB01.v, the image bounds from lib/A/AB12.v and lib/A/AB1h.v; IMG_REGIONS below .data from the image and the owned static cells of lib/A/AF0m.v, from .data on cgif's regions at the same offsets from their section anchors (checked against the unstripped twin's symbols, 36da3052c383...), every CVal value read from the hand-off states *)
(* Modified by Theorem Labs, 2026-10-29: the cut set the generator was given is Tfib_owned_static of lib/A/AF0m.v UNION the BODIES of the harness globals registered in the image's asan_globals table whose body lies in .bss -- g_file_len [0x5d3f40, 0x5d3f48) and g_file [0x5d3f60, 0x5d3f68).  No at-main state writes the harness-global hull (only the writable hull KWr), so IMG_REGIONS carries NO region over [0x5d3f40, 0x5d3f80): R_A5a is cut into R_A5a_1 [0x5d3f10, 0x5d3f40) and R_A5a_2 [0x5d3f80, 0x5d47ec), 33 regions.  AF0m.v itself is unchanged (the harness-globals ruling keeps the bodies out of owned_static); the widening is in the generator INPUT, prep_owned.py (sha256 9d548aaca227; internal record) --globals-bss. *)
(* gated: a Theorem Labs lane PASS A+B at c061542723f / 731386609e0.  Read independently by gate_check.py (sha256 b1cf8cb7ca98; internal record): GATE ok, 33 regions, 4 with gaps, 0 NEW gaps, 0 failures; kimg_overlap 0 conflicts; codeptr c0ce606ed1fa (startup-set 2026-10-29): 0 findings / 0 stale on every file, with 20 declarations carrying their measured reasons in declarations-20.sh (sha256 880286aef98b; internal record); AB1m / YB1m UNMEASURED (no address literal; BFUEL is %nat); logs final20.txt (sha256 b2b70d12a063; internal record) / final20.no-b1m.txt (sha256 be056cbfc3b7; internal record) (a Theorem Labs lane); independent run by a Theorem Labs lane agrees *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP0m YP09.
Import ListNotations.
Open Scope Z_scope.
Definition R_A1a : region :=
mkRegion None 65536 (symaddr (Symbols.Asan.Sec.s_rodata + 0x8)%Z) 0 0
[ mkChunk 65536 (CImg (symaddr ((Symbols.Asan.Sec.s_rodata + 0x8) - (65536))%Z)) ].
Definition R_A1b : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_rodata + 0x10)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 0x28)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_rodata + 0x10)%Z) (CImg 24) ].
Definition R_A1c : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_rodata + 0x30)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 0x48)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_rodata + 0x30)%Z) (CImg 24) ].
Definition R_A1d : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_rodata + 0x50)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 0xb8)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_rodata + 0x50)%Z) (CImg 104) ].
Definition R_A1e : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_rodata + 0xc8)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 0xd0)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_rodata + 0xc8)%Z) (CImg 8) ].
Definition R_A1f : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_rodata + 0xd8)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 0x140)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_rodata + 0xd8)%Z) (CImg 104) ].
Definition R_A1g : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_rodata + 0x180)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 0x240)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_rodata + 0x180)%Z) (CImg 192) ].
Definition R_A1h : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_rodata + 0x280)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 0xc978)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_rodata + 0x280)%Z) (CImg 50936) ].
Definition R_A1i : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_rodata + 0xc98d)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 67488)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_rodata + 0xc98d)%Z) (CImg 15891) ].
Definition R_A1j : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_rodata + 67492)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 68141)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_rodata + 67492)%Z) (CImg 649) ].
Definition R_A1k : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_rodata + 68160)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 68195)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_rodata + 68160)%Z) (CImg 35) ].
Definition R_A1l : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_rodata + 68224)%Z) (symaddr (Symbols.Asan.Sec.s_rodata + 69636)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_rodata + 68224)%Z) (CImg 1412) ].
Definition R_A1m : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_rodata + 69640)%Z) (symaddr (Symbols.Asan.s_sysconf_values + 0x3c)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_rodata + 69640)%Z) (CImg 96) ].
Definition R_A1n : region :=
mkRegion None (symaddr (Symbols.Asan.s_sysconf_values + 0x3e)%Z) (symaddr ImgPages.Asan.relro_lo) 0 0
[ mkChunk (symaddr (Symbols.Asan.s_sysconf_values + 0x3e)%Z) (CImg (symaddr ((626688) - (Symbols.Asan.s_sysconf_values + 0x3e))%Z)) ].
Definition R_A2a : region :=
mkRegion None (symaddr ImgPages.Asan.relro_lo) (symaddr (Symbols.Asan.Sec.s_got + 0x40)%Z) 0 0
[ mkChunk (symaddr ImgPages.Asan.relro_lo) (CImg (symaddr ((Symbols.Asan.Sec.s_got + 0x40) - (626688))%Z)) ].
Definition R_A2b : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_got + 0xc0)%Z) (symaddr (Symbols.Asan.Sec.s_got + 0xbc8)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_got + 0xc0)%Z) (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_got + 0xbd0)%Z) (symaddr (Symbols.Asan.Sec.s_got + 0xcb8)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_got + 0xbd0)%Z) (CImg 232) ].
Definition R_A2d : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_got + 0xcc0)%Z) (symaddr (Symbols.Asan.Sec.s_got + 0xcd8)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_got + 0xcc0)%Z) (CImg 24) ].
Definition R_A2e : region :=
mkRegion None (symaddr (Symbols.Asan.Sec.s_got + 0xce8)%Z) (symaddr (Symbols.Asan.Sec.s_got + 0xd40)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.Sec.s_got + 0xce8)%Z) (CImg 8);
mkChunk (symaddr (Symbols.Asan.Sec.s_got + 0xcf0)%Z) (CImg 80) ].
Definition R_A2f : region :=
mkRegion None (symaddr Symbols.Asan.Sec.s_relro_padding) (symaddr Symbols.Asan.s___dso_handle) 0 0
[ mkChunk (symaddr Symbols.Asan.Sec.s_relro_padding) (CImg (symaddr ((Symbols.Asan.s___dso_handle) - (Symbols.Asan.Sec.s_relro_padding))%Z)) ].
Definition R_A3 : region :=
mkRegion None (symaddr Symbols.Asan.s_oft_arg0) (symaddr Symbols.Asan.Sec.s_asan_globals) (symaddr Symbols.Asan.s_oft_arg0) (symaddr Symbols.Asan.Sec.s_asan_globals)
[ mkChunk (symaddr Symbols.Asan.s_oft_arg0) (CImg 832) ].
Definition R_A4 : region :=
mkRegion None (symaddr Symbols.Asan.s___do_init___initialized) (symaddr Symbols.Asan.s___do_fini___finalized) (symaddr Symbols.Asan.s___do_init___initialized) (symaddr Symbols.Asan.s___do_fini___finalized)
[ mkChunk (symaddr Symbols.Asan.s___do_init___initialized) (CVal 1 (SLit 1));
mkChunk (symaddr (Symbols.Asan.Sec.s_bss + 0x9)%Z) (CImg 71) ].
Definition R_RS : region :=
mkRegion None (symaddr Symbols.Asan.s_read_stage) (symaddr Symbols.Asan.s_target_run_initialized) 0 0
[  ].
Definition R_A5a_1 : region :=
mkRegion None (symaddr Symbols.Asan.s_target_run_initialized) (symaddr Symbols.Asan.s_g_file_len) (symaddr Symbols.Asan.s_target_run_initialized) (symaddr Symbols.Asan.s_g_file_len)
[ mkChunk (symaddr Symbols.Asan.s_target_run_initialized) (CImg 4);
mkChunk (symaddr Symbols.Asan.s_oft_in_callback) (CVal 1 (SLit 0));
mkChunk (symaddr (Symbols.Asan.Sec.s_bss + 5463317)%Z) (CImg 43) ].
Definition R_A5a_2 : region :=
mkRegion None (symaddr Symbols.Asan.s__ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE5_lockE) (symaddr (Symbols.Asan.s_builtin_tls + 0x24)%Z) (symaddr Symbols.Asan.s__ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE5_lockE) (symaddr (Symbols.Asan.s_builtin_tls + 0x24)%Z)
[ mkChunk (symaddr Symbols.Asan.s__ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE5_lockE) (CImg 2112);
mkChunk (symaddr Symbols.Asan.s_builtin_tls) (CVal 8 (SLit (symaddr Symbols.Asan.s_builtin_tls)));
mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0x8)%Z) (CVal 8 (SLit (symaddr Symbols.Asan.s_builtin_tls)));
mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0x10)%Z) (CVal 8 (SLit (symaddr Symbols.Asan.s_builtin_tls)));
mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0x18)%Z) (CVal 8 (SLit 0));
mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0x20)%Z) (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None (symaddr (Symbols.Asan.s_builtin_tls + 0x28)%Z) (symaddr (Symbols.Asan.s_builtin_tls + 0x70)%Z) (symaddr (Symbols.Asan.s_builtin_tls + 0x28)%Z) (symaddr (Symbols.Asan.s_builtin_tls + 0x70)%Z)
[ mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0x28)%Z) (CVal 4 (SLit 2));
mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0x2c)%Z) (CImg 6);
mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0x32)%Z) (CVal 1 (SLit 1));
mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0x33)%Z) (CImg 61) ].
Definition R_A6 : region :=
mkRegion None (symaddr (Symbols.Asan.s_builtin_tls + 0x78)%Z) (symaddr (Symbols.Asan.s_builtin_tls + 0xc0)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0x78)%Z) (CVal 8 (SLit (symaddr (Symbols.Asan.s_builtin_tls + 0x78)%Z)));
mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0x80)%Z) (CImg 24);
mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0x98)%Z) (CVal 8 (SLit (symaddr (Symbols.Asan.s___libc + 0x38)%Z)));
mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0xa0)%Z) (CImg 24);
mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0xb8)%Z) (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None (symaddr (Symbols.Asan.s_builtin_tls + 0x104)%Z) (symaddr (Symbols.Asan.s_builtin_tls + 0x110)%Z) 0 0
[ mkChunk (symaddr (Symbols.Asan.s_builtin_tls + 0x104)%Z) (CImg 12) ].
Definition R_A7b : region :=
mkRegion None (symaddr Symbols.Asan.s___thread_list_lock) (symaddr (Symbols.Asan.s___libc + 0x30)%Z) (symaddr Symbols.Asan.s_finished_atexit) (symaddr Symbols.Asan.s_exit_exit_lock)
[ mkChunk (symaddr Symbols.Asan.s___thread_list_lock) (CImg 16);
mkChunk (symaddr (Symbols.Asan.s_main_tls + 0x8)%Z) (CVal 8 (SLit (symaddr Symbols.Asan.Sec.s_tbss)));
mkChunk (symaddr (Symbols.Asan.s_main_tls + 0x10)%Z) (CVal 8 (SLit 0));
mkChunk (symaddr (Symbols.Asan.s_main_tls + 0x18)%Z) (CVal 8 (SLit 24));
mkChunk (symaddr (Symbols.Asan.s_main_tls + 0x20)%Z) (CVal 8 (SLit 8));
mkChunk (symaddr (Symbols.Asan.s_main_tls + 0x28)%Z) (CVal 8 (SLit 0));
mkChunk (symaddr Symbols.Asan.s___stack_chk_guard) (CVal 8 (SOff 41 0));
mkChunk (symaddr Symbols.Asan.s___abort_lock) (CImg 16);
mkChunk (symaddr Symbols.Asan.s_slot) (CVal 4 (SLit 1));
mkChunk (symaddr (Symbols.Asan.Sec.s_bss + 5596908)%Z) (CImg 4);
mkChunk (symaddr Symbols.Asan.s_head) (CVal 8 (SLit (symaddr Symbols.Asan.s_builtin)));
mkChunk (symaddr Symbols.Asan.s_builtin) (CImg 8);
mkChunk (symaddr (Symbols.Asan.s_builtin + 0x8)%Z) (CVal 8 (SLit (symaddr Symbols.Asan.s_call)));
mkChunk (symaddr (Symbols.Asan.s_builtin + 0x10)%Z) (CImg 248);
mkChunk (symaddr (Symbols.Asan.s_builtin + 0x108)%Z) (CVal 8 (SLit (symaddr Symbols.Asan.s___sanitizer_cov_dump)));
mkChunk (symaddr (Symbols.Asan.s_builtin + 0x110)%Z) (CImg 264);
mkChunk (symaddr Symbols.Asan.s_program_invocation_name) (CVal 8 (SOff 1 0));
mkChunk (symaddr Symbols.Asan.s___libc) (CVal 1 (SLit 1));
mkChunk (symaddr (Symbols.Asan.s___libc + 0x1)%Z) (CImg 7);
mkChunk (symaddr (Symbols.Asan.s___libc + 0x8)%Z) (CVal 8 (SOff 5 0));
mkChunk (symaddr (Symbols.Asan.s___libc + 0x10)%Z) (CVal 8 (SLit (symaddr Symbols.Asan.s_main_tls)));
mkChunk (symaddr (Symbols.Asan.s___libc + 0x18)%Z) (CVal 8 (SLit 248));
mkChunk (symaddr (Symbols.Asan.s___libc + 0x20)%Z) (CVal 8 (SLit 8));
mkChunk (symaddr (Symbols.Asan.s___libc + 0x28)%Z) (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None (symaddr (Symbols.Asan.s___libc + 0x38)%Z) (symaddr Symbols.Asan.s___malloc_context) 0 0
[ mkChunk (symaddr (Symbols.Asan.s___libc + 0x38)%Z) (CImg 48);
mkChunk (symaddr Symbols.Asan.s_freebuf_queue) (CImg 16) ].
Definition R_A8 : region :=
mkRegion None (symaddr Symbols.Asan.s___malloc_replaced) (symaddr Symbols.Asan.s_funcs) 0 0
[ mkChunk (symaddr Symbols.Asan.s___malloc_replaced) (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None (symaddr Symbols.Asan.s_tl_lock_count) (symaddr Symbols.Asan.s___pthread_tsd_main) 0 0
[ mkChunk (symaddr Symbols.Asan.s_tl_lock_count) (CImg 8);
mkChunk (symaddr Symbols.Asan.s_keys) (CVal 8 (SLit (symaddr Symbols.Asan.s__ZN6__asan15PlatformTSDDtorEPv)));
mkChunk (symaddr (Symbols.Asan.s_keys + 0x8)%Z) (CImg 1016);
mkChunk (symaddr Symbols.Asan.s_next_key) (CVal 4 (SLit 0));
mkChunk (symaddr (Symbols.Asan.Sec.s_bss + 5601788)%Z) (CImg 4);
mkChunk (symaddr Symbols.Asan.s_key_lock) (CVal 4 (SLit 0));
mkChunk (symaddr (Symbols.Asan.s_key_lock + 0x4)%Z) (CImg 52) ].
Definition R_A9b : region :=
mkRegion None (symaddr (Symbols.Asan.s___pthread_tsd_main + 0x8)%Z) (symaddr ImgPages.Asan.top) 0 0
[ mkChunk (symaddr (Symbols.Asan.s___pthread_tsd_main + 0x8)%Z) (CImg (symaddr ((6254592) - (Symbols.Asan.s___pthread_tsd_main + 0x8))%Z)) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a_1; R_A5a_2; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
