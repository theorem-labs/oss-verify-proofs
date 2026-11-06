(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7k.v for libreac/fuzz_disco's asan-ubsan program walk, with its module paths changed; the atom fact of atom 43 cites YImgTop.IMG_LO / IMG_TOP (was cgif_file's image bounds as decimals, 65536 / 6270976 = 0x5fb000; fuzz_disco's images end at 0x5fd930 and 0x5fdcf0). *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11 YP0m YP0e YP09 YP02 YP0l YM05.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_BX : sstate :=
(mkSS 380
[SLit 0; SOff 546 0; SOff 2 (-192); SOff 3 0; SOff 4 0; SOff 547 0; SOff 548 0; SOff 549 0; SOff 2 0; SOff 2 (-192); SOff 550 0; SOff 551 0; SOff 552 0; SOff 553 0; SOff 554 0; SOff 555 0; SOff 556 0; SOff 557 0; SOff 516 0; SOff 19 0;
SOff 10 0; SOff 21 0; SOff 22 0; SOff 10 32; SOff 35 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 32) (SLit 3)) (SOff 35 0); SOff 529 0; SOff 516 0; SOff 558 0; SOff 559 0; SOff 560 0; SOff 561 0]
[{|
r_base := Some 534%nat;
r_lo := 0;
r_hi := 48;
r_wlo := 40;
r_whi := 48;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 36 0) |}; {| c_off := 30; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 32; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 34; YP09.c_val := CVal 2 (SOff 39 0) |}]
|};
{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 32;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |}; {| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 8; YP09.c_val := CVal 1 (SLit 3) |}; {| c_off := 17; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 16; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 5) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 19; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 18; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 24; YP09.c_val := CVal 8 (SLit 0) |}]
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 256;
r_wlo := 0;
r_whi := 256;
r_chunks := [{| c_off := 16; YP09.c_val := CVal 8 (SOff 240 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 247 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}; {| c_off := 248; YP09.c_val := CVal 8 (SOff 528 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -192;
r_hi := 0;
r_wlo := -192;
r_whi := 0;
r_chunks :=
[{| c_off := -152; YP09.c_val := CVal 8 (SOff 534 0) |}; {| c_off := -112; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
{| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
{| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
{| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}; {| c_off := -192; YP09.c_val := CVal 8 (SLit 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 35 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 43 0) |}] |};
{| r_base := Some 43%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 248%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 0) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 36 0) |}; {| c_off := 30; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 32; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 34; YP09.c_val := CVal 2 (SOff 39 0) |}]
|};
{|
r_base := Some 32%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 64; YP09.c_val := CVal 8 (SOff 40 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 44 0) |}]
|}]
None
{|
f_atoms :=
[(534%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
(516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
(32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(35%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (40%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 1 |}); (42%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 1 |});
(43%nat, {| af_lo := YImgTop.IMG_LO; af_hi := YImgTop.IMG_TOP; af_al2 := 2 |}); (44%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_GEU; ac_a := SLit 256; ac_b := SOff 38 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 35 0), SOff 529 0)]
|}).
Definition rn_deads_C_X_unused : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 21; 28; 29; 30; 31]%bv.
Definition ss_CX : sstate :=
(mkSS 600
[SLit 0; SOff 631 0; SOff 2 (-192); SOff 3 0; SOff 4 0; SOff 632 0; SOff 633 0; SOff 634 0; SOff 2 0; SOff 2 (-192); SOff 635 0; SOff 636 0; SOff 637 0; SOff 638 0; SOff 639 0; SOff 640 0; SOff 641 0; SOff 642 0; SOff 516 0; SOff 643 0; SOff 10 0; SOff 644 0; SOff 516 112; SOff 10 32; SOff 35 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 32) (SLit 3)) (SOff 35 0); SOff 529 0; SOff 516 0; SOff 645 0; SOff 646 0; SOff 647 0; SOff 648 0]
[{| r_base := Some 516%nat; r_lo := 122; r_hi := 125; r_wlo := 122; r_whi := 125; r_chunks := [{| c_off := 122; YP09.c_val := CVal 1 (SOff 45 0) |}; {| c_off := 123; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 124; YP09.c_val := CVal 1 (SLit 0) |}] |};
{| r_base := Some 516%nat; r_lo := 0; r_hi := 122; r_wlo := 0; r_whi := 122; r_chunks := [{| c_off := 121; YP09.c_val := CVal 1 (SAlu ALU_SRL (SExt true 16 (SOff 37 0)) (SLit 8)) |}; {| c_off := 120; YP09.c_val := CVal 1 (SExt true 16 (SOff 37 0)) |}; {| c_off := 119; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 36 0) (SLit 8)) |}; {| c_off := 118; YP09.c_val := CVal 1 (SOff 36 0) |}; {| c_off := 117; YP09.c_val := CVal 1 (SLit 97) |}; {| c_off := 116; YP09.c_val := CVal 1 (SLit 57) |}; {| c_off := 115; YP09.c_val := CVal 1 (SLit 56) |}; {| c_off := 114; YP09.c_val := CVal 1 (SLit 70) |}; {| c_off := 113; YP09.c_val := CVal 1 (SLit 73) |}; {| c_off := 112; YP09.c_val := CVal 1 (SLit 71) |}] |};
{| r_base := Some 534%nat; r_lo := 0; r_hi := 48; r_wlo := 40; r_whi := 48; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 37 0) |};
{| c_off := 32; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 34; YP09.c_val := CVal 2 (SOff 39 0) |}] |};
{| r_base := Some 529%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 3) |};
{| c_off := 17; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 16; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 15; YP09.c_val := CVal 1 (SLit 5) |};
{| c_off := 14; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 19; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 18; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 24; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 516%nat; r_lo := 125; r_hi := 256; r_wlo := 125; r_whi := 256; r_chunks := [{| c_off := 248; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{| r_base := Some 2%nat; r_lo := -192; r_hi := 0; r_wlo := -192; r_whi := 0; r_chunks := [{| c_off := -160; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := -152; YP09.c_val := CVal 8 (SOff 534 0) |};
{| c_off := -112; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
{| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
{| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |};
{| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
{| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |};
{| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
{| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |};
{| c_off := -192; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 35 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 43 0) |}] |};
{| r_base := Some 43%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 248%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 0) |}] |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 40; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 37 0) |};
{| c_off := 32; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 34; YP09.c_val := CVal 2 (SOff 39 0) |}] |};
{| r_base := Some 32%nat; r_lo := 0; r_hi := 96; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 42 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 40 0) |};
{| c_off := 80; YP09.c_val := CVal 8 (SOff 44 0) |}] |}]
None
{| f_atoms := [(534%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
(516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
(10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
(32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(35%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(37%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(40%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 1 |}); (42%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 1 |});
(43%nat, {| af_lo := YImgTop.IMG_LO; af_hi := YImgTop.IMG_TOP; af_al2 := 2 |}); (44%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 35 0), SOff 529 0)] |}).
Definition rn_deads_G_X_unused : list (bv 5) := [1; 5; 6; 7; 11; 14; 16; 17; 25; 28; 29; 30; 31]%bv.
Definition ss_GX : sstate :=
(mkSS 780
[SLit 0; SOff 691 0; SOff 2 (-192); SOff 3 0; SOff 4 0; SOff 692 0; SOff 693 0; SOff 694 0; SOff 2 0; SOff 2 (-192); SLit 0; SOff 695 0; SLit 0; SLit 1; SOff 696 0; SOff 38 0; SOff 697 0; SOff 698 0; SOff 516 0; SOff 10 8; SOff 10 0; SLit 0; SOff 516 112; SOff 516 32; SOff 35 0; SOff 699 0; SOff 529 0; SOff 516 0; SOff 700 0; SOff 701 0; SOff 702 0; SOff 703 0]
[{| r_base := Some 516%nat; r_lo := 122; r_hi := 125; r_wlo := 122; r_whi := 125; r_chunks := [] |};
{| r_base := Some 516%nat; r_lo := 0; r_hi := 122; r_wlo := 0; r_whi := 122; r_chunks := [] |};
{| r_base := Some 534%nat; r_lo := 0; r_hi := 48; r_wlo := 40; r_whi := 48; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 37 0) |};
{| c_off := 32; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 34; YP09.c_val := CVal 2 (SOff 39 0) |}] |};
{| r_base := Some 529%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 3) |};
{| c_off := 17; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 16; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 15; YP09.c_val := CVal 1 (SLit 5) |};
{| c_off := 14; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 19; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 18; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 24; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 516%nat; r_lo := 125; r_hi := 256; r_wlo := 125; r_whi := 256; r_chunks := [{| c_off := 248; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{| r_base := Some 2%nat; r_lo := -192; r_hi := 0; r_wlo := -192; r_whi := 0; r_chunks := [{| c_off := -168; YP09.c_val := CVal 8 (SOff 10 8) |};
{| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 35 0)) |};
{| c_off := -136; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 35 0)) |};
{| c_off := -160; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := -152; YP09.c_val := CVal 8 (SOff 534 0) |};
{| c_off := -112; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
{| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
{| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |};
{| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
{| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |};
{| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
{| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |};
{| c_off := -192; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 35 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 43 0) |}] |};
{| r_base := Some 43%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 248%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 0) |}] |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 40; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 37 0) |};
{| c_off := 32; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 34; YP09.c_val := CVal 2 (SOff 39 0) |}] |};
{| r_base := Some 32%nat; r_lo := 0; r_hi := 96; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 42 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 40 0) |};
{| c_off := 80; YP09.c_val := CVal 8 (SOff 44 0) |}] |}]
None
{| f_atoms := [(534%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
(516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
(10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
(32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(35%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(37%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(40%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 1 |}); (42%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 1 |});
(43%nat, {| af_lo := YImgTop.IMG_LO; af_hi := YImgTop.IMG_TOP; af_al2 := 2 |}); (44%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_NE; ac_a := SOff 38 0; ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 35 0), SOff 529 0)] |}).
Definition rn_deads_D_X_unused : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 22; 23; 25; 28; 29; 30; 31]%bv.
Definition ss_DX : sstate :=
(mkSS 960
[SLit 0; SOff 771 0; SOff 2 (-192); SOff 3 0; SOff 4 0; SOff 772 0; SOff 773 0; SOff 774 0; SOff 2 0; SOff 2 (-192); SOff 775 0; SOff 776 0; SOff 777 0; SOff 778 0; SOff 779 0; SOff 780 0; SOff 781 0; SOff 782 0; SOff 516 0; SOff 783 0; SOff 10 0; SLit 0; SOff 784 0; SOff 785 0; SOff 35 0; SOff 786 0; SOff 529 0; SOff 516 0; SOff 787 0; SOff 788 0; SOff 789 0; SOff 790 0]
[{| r_base := Some 516%nat; r_lo := 122; r_hi := 125; r_wlo := 122; r_whi := 125; r_chunks := [] |};
{| r_base := Some 516%nat; r_lo := 0; r_hi := 122; r_wlo := 0; r_whi := 122; r_chunks := [] |};
{| r_base := Some 534%nat; r_lo := 0; r_hi := 48; r_wlo := 40; r_whi := 48; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 37 0) |};
{| c_off := 32; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 34; YP09.c_val := CVal 2 (SOff 39 0) |}] |};
{| r_base := Some 529%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 3) |};
{| c_off := 17; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 16; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 15; YP09.c_val := CVal 1 (SLit 5) |};
{| c_off := 14; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 19; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 18; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 24; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 516%nat; r_lo := 125; r_hi := 256; r_wlo := 125; r_whi := 256; r_chunks := [{| c_off := 248; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{| r_base := Some 2%nat; r_lo := -192; r_hi := 0; r_wlo := -192; r_whi := 0; r_chunks := [{| c_off := -168; YP09.c_val := CVal 8 (SOff 10 8) |};
{| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 35 0)) |};
{| c_off := -136; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 35 0)) |};
{| c_off := -160; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := -152; YP09.c_val := CVal 8 (SOff 534 0) |};
{| c_off := -112; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
{| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
{| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |};
{| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
{| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |};
{| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
{| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |};
{| c_off := -192; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 35 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 43 0) |}] |};
{| r_base := Some 43%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 248%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 0) |}] |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 40; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 37 0) |};
{| c_off := 32; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 34; YP09.c_val := CVal 2 (SOff 39 0) |}] |};
{| r_base := Some 32%nat; r_lo := 0; r_hi := 96; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 42 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 40 0) |};
{| c_off := 80; YP09.c_val := CVal 8 (SOff 44 0) |}] |}]
None
{| f_atoms := [(534%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
(516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
(10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
(32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(35%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(37%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(40%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 1 |}); (42%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 1 |});
(43%nat, {| af_lo := YImgTop.IMG_LO; af_hi := YImgTop.IMG_TOP; af_al2 := 2 |}); (44%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 35 0), SOff 529 0)] |}).
Definition rn_deads_X_X_unused : list (bv 5) := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31]%bv.
Definition ss_XX : sstate :=
(mkSS 1232
[SLit 0; SOff 871 0; SOff 2 (-192); SOff 3 0; SOff 4 0; SOff 872 0; SOff 873 0; SOff 874 0; SOff 2 0; SOff 2 (-192); SOff 534 0; SOff 875 0; SOff 876 0; SOff 877 0; SOff 878 0; SOff 879 0; SOff 880 0; SOff 881 0; SOff 516 0; SOff 882 0; SOff 883 0; SOff 884 0; SOff 885 0; SOff 886 0; SOff 887 0; SOff 888 0; SOff 529 0; SOff 516 0; SOff 889 0; SOff 890 0; SOff 891 0; SOff 892 0]
[{| r_base := Some 516%nat; r_lo := 122; r_hi := 125; r_wlo := 122; r_whi := 125; r_chunks := [] |};
{| r_base := Some 516%nat; r_lo := 0; r_hi := 122; r_wlo := 0; r_whi := 122; r_chunks := [] |};
{| r_base := Some 534%nat; r_lo := 0; r_hi := 48; r_wlo := 40; r_whi := 48; r_chunks := [{| c_off := 40; YP09.c_val := CVal 4 (SLit 6) |};
{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 37 0) |};
{| c_off := 32; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 34; YP09.c_val := CVal 2 (SOff 39 0) |}] |};
{| r_base := Some 529%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 3) |};
{| c_off := 17; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 16; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 15; YP09.c_val := CVal 1 (SLit 5) |};
{| c_off := 14; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 19; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 18; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 24; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 516%nat; r_lo := 125; r_hi := 256; r_wlo := 125; r_whi := 256; r_chunks := [{| c_off := 248; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{| r_base := Some 2%nat; r_lo := -192; r_hi := 0; r_wlo := -192; r_whi := 0; r_chunks := [{| c_off := -168; YP09.c_val := CVal 8 (SOff 10 8) |};
{| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 35 0)) |};
{| c_off := -136; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 35 0)) |};
{| c_off := -160; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := -152; YP09.c_val := CVal 8 (SOff 534 0) |};
{| c_off := -112; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
{| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |};
{| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |};
{| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |};
{| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |};
{| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |};
{| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |};
{| c_off := -192; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 35 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 43 0) |}] |};
{| r_base := Some 43%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 248%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 0) |}] |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 40; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 37 0) |};
{| c_off := 32; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 34; YP09.c_val := CVal 2 (SOff 39 0) |}] |};
{| r_base := Some 32%nat; r_lo := 0; r_hi := 96; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 42 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 40 0) |};
{| c_off := 80; YP09.c_val := CVal 8 (SOff 44 0) |}] |}]
None
{| f_atoms := [(534%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
(516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
(10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
(32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(35%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(37%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(40%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 1 |}); (42%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 1 |});
(43%nat, {| af_lo := YImgTop.IMG_LO; af_hi := YImgTop.IMG_TOP; af_al2 := 2 |}); (44%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 35 0), SOff 529 0)] |}).
End a.
