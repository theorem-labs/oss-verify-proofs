(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA LibIface LibIfaceAJ.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMTAL.
Section LAYOUT.
Variables (STK : Z) (FRAMES LEAK : Z -> Z) (CREDIT : Z -> credit).
Definition ATEXIT_a : Z := 0x68edd0.
Definition foot_a : list (Z * Z) :=
[(0x66d380, 0x66d382); (0x66d5b0, 0x66d5b2)]
++ [(0x66d5b2, 0x66dcf0); (0x66e418, 0x66e470)]
++ [(ATEXIT_a, ATEXIT_a + 544)].
Definition init_cells_a : list (Z * Z * Z) :=
[(ATEXIT_a, 1, 0); (ATEXIT_a + 4, 4, 0); (ATEXIT_a + 8, 4, 2); (ATEXIT_a + 16, 8, ATEXIT_a + 24); (ATEXIT_a + 24, 8, 0);
(ATEXIT_a + 32, 8, 0x1138d0); (ATEXIT_a + 288, 8, 0x96c0c);
(ATEXIT_a + 40, 8, 0x1138d0); (ATEXIT_a + 296, 8, 0xa75d4);
(0x68f013, 1, 0); (0x68f0f0, 4, 0)].
Definition TopLayA_a (L : asan_layout) : lib_layoutA := {|
lla_L := L;
lla_entry := 0xa764c;
lla_gp := 0x10800;
lla_empty := 0x66d360;
lla_initc := [(0x66ecb8, 0x66ed80); (0x68edc0, 0x68edc8); (0x68f018, 0x68f020); (0x68f048, 0x68f078); (0x68f013, 0x68f014); (0x68f0f0, 0x68f0f4)];
lla_init_img := [(0x10000, 0x134000); (0x136d70, 0x136e18); (0x66d351, 0x66d354); (0x66d355, 0x66ecb0)];
lla_td_self := 0x66ecb8; lla_td_tid := 0x66ecd8; lla_td_locale := 0x66ed50; lla_locale := 0x68f048; lla_td_canary := 0x66ed70;
lla_guard := 0x68edc0; lla_auxvp := 0x68f018;
lla_phdr := 0x10040; lla_phent := 56; lla_phnum := 11;
lla_rw_lo := 0x134000;
lla_stack := STK;
lla_frames := FRAMES;
lla_leak := LEAK;
lla_credit := CREDIT;
lla_foot := foot_a;
lla_junk := [];
lla_init_cells := init_cells_a |}.
Definition ATEXIT_b : Z := 0x690b10.
Definition foot_b : list (Z * Z) :=
[(0x66f0c0, 0x66f0c2); (0x66f2f0, 0x66f2f2)]
++ [(0x66f2f2, 0x66fa30); (0x670158, 0x6701b0)]
++ [(ATEXIT_b, ATEXIT_b + 544)].
Definition init_cells_b : list (Z * Z * Z) :=
[(ATEXIT_b, 1, 0); (ATEXIT_b + 4, 4, 0); (ATEXIT_b + 8, 4, 2); (ATEXIT_b + 16, 8, ATEXIT_b + 24); (ATEXIT_b + 24, 8, 0);
(ATEXIT_b + 32, 8, 0x115708); (ATEXIT_b + 288, 8, 0x96edc);
(ATEXIT_b + 40, 8, 0x115708); (ATEXIT_b + 296, 8, 0xa78a4);
(0x690d53, 1, 0); (0x690e30, 4, 0)].
Definition TopLayA_b (L : asan_layout) : lib_layoutA := {|
lla_L := L;
lla_entry := 0xa791c;
lla_gp := 0x10800;
lla_empty := 0x66f0a0;
lla_initc := [(0x6709f8, 0x670ac0); (0x690b00, 0x690b08); (0x690d58, 0x690d60); (0x690d88, 0x690db8); (0x690d53, 0x690d54); (0x690e30, 0x690e34)];
lla_init_img := [(0x10000, 0x136000); (0x138ad8, 0x138b80); (0x66f091, 0x66f094); (0x66f095, 0x6709f0)];
lla_td_self := 0x6709f8; lla_td_tid := 0x670a18; lla_td_locale := 0x670a90; lla_locale := 0x690d88; lla_td_canary := 0x670ab0;
lla_guard := 0x690b00; lla_auxvp := 0x690d58;
lla_phdr := 0x10040; lla_phent := 56; lla_phnum := 11;
lla_rw_lo := 0x136000;
lla_stack := STK;
lla_frames := FRAMES;
lla_leak := LEAK;
lla_credit := CREDIT;
lla_foot := foot_b;
lla_junk := [];
lla_init_cells := init_cells_b |}.
End LAYOUT.
End PMTAL.
