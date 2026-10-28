(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC20 YC44 YC45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h ACk4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YC5d YC7z YC7x YC21.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI17 YE02 YC5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {NP : ng_params}.
#[local] Notation hw := (@ngp_hw NP).
#[local] Notation CTX := (@ngp_ctx NP).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition ss_NBX : sstate :=
(mkSS 300
[SLit 0; SOff 530 0; SOff 2 (-192); SOff 3 0; SOff 4 0; SOff 531 0; SOff 532 0; SOff 533 0; SOff 2 0; SOff 2 (-192); SOff 534 0; SOff 535 0; SOff 536 0; SOff 537 0; SOff 538 0; SOff 539 0; SOff 540 0; SOff 541 0; SOff 516 0; SOff 19 0;
SOff 10 0; SOff 516 32; SOff 22 0; SOff 23 0; SOff 529 0; SOff 35 0; SOff 26 0; SOff 516 0; SOff 542 0; SOff 543 0; SOff 544 0; SOff 545 0]
[{| r_base := Some 516%nat; r_lo := 32; r_hi := 72; r_wlo := 32; r_whi := 72; r_chunks := [] |}; {| r_base := Some 516%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [] |};
{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 16;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
|}; {| r_base := Some 516%nat; r_lo := 72; r_hi := 128; r_wlo := 72; r_whi := 128; r_chunks := [{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{|
r_base := Some 2%nat;
r_lo := -192;
r_hi := 0;
r_wlo := -192;
r_whi := 0;
r_chunks :=
[{| c_off := -112; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}; {| c_off := -192; YP09.c_val := CVal 8 (SLit 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 35 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |}] |};
{| r_base := Some 41%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 244%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 0) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 48;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 36 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 28; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 30; YP09.c_val := CVal 2 (SOff 39 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SLit hw) |}; {| c_off := 40; YP09.c_val := CVal 8 (SLit 0) |}]
|}]
None
{|
f_atoms :=
[(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |}); (32%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(33%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (35%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(40%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (42%nat, {| af_lo := 65536; af_hi := 6270976; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 35 0), SOff 529 0)]
|}).
Definition ss_NMX : sstate :=
(mkSS 416 [SLit 0; SOff 546 0; SOff 2 (-192); SOff 3 0; SOff 4 0; SOff 547 0; SOff 548 0; SOff 549 0; SOff 2 0; SOff 2 (-192); SOff 550 0; SOff 551 0; SOff 552 0; SOff 553 0; SOff 554 0; SOff 555 0; SOff 556 0; SOff 557 0; SOff 516 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 26) (SLit 3)) (SOff 35 0); SOff 10 0; SOff 516 32; SOff 10 24; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 35 0); SOff 529 0; SOff 35 0; SOff 10 26; SOff 516 0; SOff 558 0; SOff 559 0; SOff 560 0; SOff 561 0]
[{| r_base := Some 550%nat; r_lo := 0; r_hi := 96; r_wlo := 0; r_whi := 96; r_chunks := [] |};
{| r_base := Some 516%nat; r_lo := 32; r_hi := 72; r_wlo := 32; r_whi := 72; r_chunks := [] |};
{| r_base := Some 516%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [] |};
{| r_base := Some 529%nat; r_lo := 0; r_hi := 16; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}] |};
{| r_base := Some 516%nat; r_lo := 72; r_hi := 128; r_wlo := 72; r_whi := 128; r_chunks := [{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{| r_base := Some 2%nat; r_lo := -192; r_hi := 0; r_wlo := -192; r_whi := 0; r_chunks := [{| c_off := -136; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 26) (SLit 3)) (SOff 35 0)) |}; {| c_off := -112; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}; {| c_off := -192; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 35 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |}] |};
{| r_base := Some 41%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 244%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 0) |}] |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 48; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 34 0) |}; {| c_off := 24; YP09.c_val := CVal 2 (SOff 36 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 28; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 30; YP09.c_val := CVal 2 (SOff 39 0) |}; {| c_off := 32; YP09.c_val := CVal 8 (SLit hw) |}; {| c_off := 40; YP09.c_val := CVal 8 (SLit 0) |}] |}]
None
{| f_atoms := [(550%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |}); (32%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (33%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (35%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (40%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (42%nat, {| af_lo := 65536; af_hi := 6270976; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_NE; ac_a := SOff 37 0; ac_b := SLit 0 |}; {| ac_c := BC_NE; ac_a := SOff 36 0; ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 35 0), SOff 529 0)] |}).
Definition ss_NKX : sstate :=
(mkSS 552
[SLit 0; SOff 578 0; SOff 2 (-192); SOff 3 0; SOff 4 0; SOff 579 0; SOff 580 0; SOff 581 0; SOff 2 0; SOff 2 (-192); SOff 582 0; SOff 583 0; SOff 584 0; SOff 585 0; SOff 586 0; SOff 587 0; SOff 588 0; SOff 589 0; SOff 516 0;
SOff 550 0; SOff 10 0; SOff 516 32; SOff 10 24; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 35 0); SOff 529 0; SOff 35 0; SOff 550 24; SOff 516 0; SOff 590 0; SOff 591 0; SOff 592 0; SOff 593 0]
[{|
r_base := Some 550%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 96;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 34 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 39 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SLit hw) |};
{| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SLit 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SLit 1) |}]
|}; {| r_base := Some 516%nat; r_lo := 32; r_hi := 72; r_wlo := 32; r_whi := 72; r_chunks := [] |}; {| r_base := Some 516%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [] |};
{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 16;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
|}; {| r_base := Some 516%nat; r_lo := 72; r_hi := 128; r_wlo := 72; r_whi := 128; r_chunks := [{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{|
r_base := Some 2%nat;
r_lo := -192;
r_hi := 0;
r_wlo := -192;
r_whi := 0;
r_chunks :=
[{| c_off := -160; YP09.c_val := CVal 8 (SOff 10 26) |}; {| c_off := -136; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 26) (SLit 3)) (SOff 35 0)) |};
{| c_off := -112; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}; {| c_off := -192; YP09.c_val := CVal 8 (SLit 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 35 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |}] |};
{| r_base := Some 41%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 244%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 0) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 48;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 36 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 28; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 30; YP09.c_val := CVal 2 (SOff 39 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SLit hw) |}; {| c_off := 40; YP09.c_val := CVal 8 (SLit 0) |}]
|}]
None
{|
f_atoms :=
[(550%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
(516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
(32%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (33%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(35%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (40%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (42%nat, {| af_lo := 65536; af_hi := 6270976; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_NE; ac_a := SOff 37 0; ac_b := SLit 0 |}; {| ac_c := BC_NE; ac_a := SOff 36 0; ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 35 0), SOff 529 0)]
|}).
Definition ss_NP0X : sstate :=
(mkSS 804
[SLit 0; SOff 578 0; SOff 2 (-192); SOff 3 0; SOff 4 0; SOff 579 0; SOff 580 0; SOff 581 0; SOff 2 0; SOff 2 (-192); SLit 0; SOff 33 0; SOff 595 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 16) (SLit 3)) (SOff 35 0); SOff 586 0;
SOff 587 0; SOff 588 0; SOff 589 0; SOff 516 0; SOff 550 0; SOff 10 0; SOff 516 32; SOff 10 24; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 35 0); SOff 529 0; SOff 35 0; SOff 550 24; SOff 516 0; SOff 590 0; SOff 591 0;
SOff 592 0; SOff 593 0]
[{|
r_base := Some 550%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 96;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 34 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 39 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SLit hw) |};
{| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SLit 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SLit 1) |}]
|}; {| r_base := Some 516%nat; r_lo := 32; r_hi := 72; r_wlo := 32; r_whi := 72; r_chunks := [{| c_off := 48; YP09.c_val := CVal 8 (SOff 32 0) |}] |}; {| r_base := Some 516%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [] |};
{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 16;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
|}; {| r_base := Some 516%nat; r_lo := 72; r_hi := 128; r_wlo := 72; r_whi := 128; r_chunks := [{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{|
r_base := Some 2%nat;
r_lo := -192;
r_hi := 0;
r_wlo := -192;
r_whi := 0;
r_chunks :=
[{| c_off := -160; YP09.c_val := CVal 8 (SOff 10 26) |}; {| c_off := -136; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 26) (SLit 3)) (SOff 35 0)) |};
{| c_off := -112; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}; {| c_off := -192; YP09.c_val := CVal 8 (SLit 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 35 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |}] |};
{| r_base := Some 41%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 244%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 0) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 48;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 36 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 28; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 30; YP09.c_val := CVal 2 (SOff 39 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SLit hw) |}; {| c_off := 40; YP09.c_val := CVal 8 (SLit 0) |}]
|}]
None
{|
f_atoms :=
[(550%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
(516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
(32%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (33%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(35%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (40%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (42%nat, {| af_lo := 65536; af_hi := 6270976; af_al2 := 0 |})];
f_conds :=
[{| ac_c := BC_NE; ac_a := SAlu ALU_AND (SOff 33 0) (SLit 4); ac_b := SLit 0 |}; {| ac_c := BC_NE; ac_a := SAlu ALU_AND (SExt false 8 (SOff 33 0)) (SLit 4); ac_b := SLit 0 |}; {| ac_c := BC_NE; ac_a := SOff 37 0; ac_b := SLit 0 |};
{| ac_c := BC_NE; ac_a := SOff 36 0; ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 35 0), SOff 529 0)]
|}).
Definition ss_NG1X : sstate :=
(mkSS 644
[SLit 0; SOff 595 0; SOff 2 (-192); SOff 3 0; SOff 4 0; SOff 596 0; SOff 597 0; SOff 598 0; SOff 2 0; SOff 2 (-192); SOff 599 0; SOff 600 0; SOff 601 0; SOff 602 0; SOff 603 0; SOff 604 0; SOff 605 0; SOff 606 0; SOff 516 0;
SOff 550 0; SOff 10 0; SOff 516 32; SOff 10 24; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 35 0); SOff 529 0; SOff 35 0; SOff 550 24; SOff 516 0; SOff 607 0; SOff 608 0; SOff 609 0; SOff 610 0]
[{|
r_base := Some 550%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 96;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 34 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 39 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SLit hw) |};
{| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SLit 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SLit 1) |}]
|}; {| r_base := Some 516%nat; r_lo := 32; r_hi := 72; r_wlo := 32; r_whi := 72; r_chunks := [] |}; {| r_base := Some 516%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [] |};
{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 16;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
|}; {| r_base := Some 516%nat; r_lo := 72; r_hi := 128; r_wlo := 72; r_whi := 128; r_chunks := [{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{|
r_base := Some 2%nat;
r_lo := -192;
r_hi := 0;
r_wlo := -192;
r_whi := 0;
r_chunks :=
[{| c_off := -184; YP09.c_val := CVal 8 (SOff 10 28) |}; {| c_off := -192; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 28) (SLit 3)) (SOff 35 0)) |}; {| c_off := -168; YP09.c_val := CVal 8 (SOff 10 16) |};
{| c_off := -176; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 16) (SLit 3)) (SOff 35 0)) |}; {| c_off := -152; YP09.c_val := CVal 8 (SAlu ALU_SRL (SOff 10 0) (SLit 3)) |};
{| c_off := -160; YP09.c_val := CVal 8 (SOff 10 26) |}; {| c_off := -136; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 26) (SLit 3)) (SOff 35 0)) |};
{| c_off := -112; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 35 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |}] |};
{| r_base := Some 41%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 244%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 0) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 48;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 36 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 28; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 30; YP09.c_val := CVal 2 (SOff 39 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SLit hw) |}; {| c_off := 40; YP09.c_val := CVal 8 (SLit 0) |}]
|}]
None
{|
f_atoms :=
[(599%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (550%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
(10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |}); (32%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (33%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (35%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(37%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (40%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (42%nat, {| af_lo := 65536; af_hi := 6270976; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_EQ; ac_a := SAlu ALU_AND (SExt false 8 (SOff 33 0)) (SLit 4); ac_b := SLit 0 |}; {| ac_c := BC_NE; ac_a := SOff 37 0; ac_b := SLit 0 |}; {| ac_c := BC_NE; ac_a := SOff 36 0; ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 35 0), SOff 529 0)]
|}).
Definition ss_NP1X : sstate :=
(mkSS 804
[SLit 0; SOff 611 0; SOff 2 (-192); SOff 3 0; SOff 4 0; SOff 612 0; SOff 613 0; SOff 614 0; SOff 2 0; SOff 2 (-192); SOff 38 0; SOff 33 0; SOff 629 0; SOff 630 0; SOff 619 0; SOff 620 0; SOff 621 0; SOff 622 0; SOff 516 0;
SOff 550 0; SOff 10 0; SOff 516 32; SOff 10 24; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 35 0); SOff 529 0; SOff 35 0; SOff 550 24; SOff 516 0; SOff 623 0; SOff 624 0; SOff 625 0; SOff 626 0]
[{|
r_base := Some 550%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 96;
r_chunks :=
[{| c_off := 24; YP09.c_val := CVal 8 (SOff 599 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SLit 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 34 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 39 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SLit hw) |};
{| c_off := 64; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SLit 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SLit 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SLit 1) |}]
|}; {| r_base := Some 516%nat; r_lo := 32; r_hi := 72; r_wlo := 32; r_whi := 72; r_chunks := [{| c_off := 48; YP09.c_val := CVal 8 (SOff 32 0) |}] |}; {| r_base := Some 516%nat; r_lo := 0; r_hi := 32; r_wlo := 0; r_whi := 32; r_chunks := [] |};
{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 16;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 7; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 14; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
|}; {| r_base := Some 516%nat; r_lo := 72; r_hi := 128; r_wlo := 72; r_whi := 128; r_chunks := [{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{|
r_base := Some 2%nat;
r_lo := -192;
r_hi := 0;
r_wlo := -192;
r_whi := 0;
r_chunks :=
[{| c_off := -184; YP09.c_val := CVal 8 (SOff 10 28) |}; {| c_off := -192; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 28) (SLit 3)) (SOff 35 0)) |}; {| c_off := -168; YP09.c_val := CVal 8 (SOff 10 16) |};
{| c_off := -176; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 16) (SLit 3)) (SOff 35 0)) |}; {| c_off := -152; YP09.c_val := CVal 8 (SAlu ALU_SRL (SOff 10 0) (SLit 3)) |};
{| c_off := -160; YP09.c_val := CVal 8 (SOff 10 26) |}; {| c_off := -136; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 26) (SLit 3)) (SOff 35 0)) |};
{| c_off := -112; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |};
{| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |};
{| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |};
{| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 35 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |}] |};
{| r_base := Some 41%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 244%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 0) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 48;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 33 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 36 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 28; YP09.c_val := CVal 2 (SOff 38 0) |}; {| c_off := 30; YP09.c_val := CVal 2 (SOff 39 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SLit hw) |}; {| c_off := 40; YP09.c_val := CVal 8 (SLit 0) |}]
|}]
None
{|
f_atoms :=
[(599%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (550%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
(10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |}); (32%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (33%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (35%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(37%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (40%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (42%nat, {| af_lo := 65536; af_hi := 6270976; af_al2 := 0 |})];
f_conds :=
[{| ac_c := BC_EQ; ac_a := SAlu ALU_AND (SOff 33 0) (SLit 4); ac_b := SLit 0 |}; {| ac_c := BC_EQ; ac_a := SAlu ALU_AND (SExt false 8 (SOff 33 0)) (SLit 4); ac_b := SLit 0 |}; {| ac_c := BC_NE; ac_a := SOff 37 0; ac_b := SLit 0 |};
{| ac_c := BC_NE; ac_a := SOff 36 0; ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 35 0), SOff 529 0)]
|}).
Definition NGX_PATH : nat := 42.
Definition NGX_PF : nat := 52.
Definition NGX_BAND : nat := 48.
Definition ng_extraX (pal0 attr gen Wd Hd ngp loops uar path : Z) : list word :=
ng_extra pal0 attr gen Wd Hd ngp loops uar ++ [Z_to_bv 64 path].
Definition ncfg_regionX : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 48 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 42 0)); YP09.mkChunk 16 (CVal 4 (SOff 33 0));
YP09.mkChunk 20 (CVal 4 (SOff 34 0)); YP09.mkChunk 24 (CVal 2 (SOff 36 0)); YP09.mkChunk 26 (CVal 2 (SOff 37 0));
YP09.mkChunk 28 (CVal 2 (SOff 38 0)); YP09.mkChunk 30 (CVal 2 (SOff 39 0));
YP09.mkChunk 32 (CVal 8 (SLit hw)); YP09.mkChunk 40 (CVal 8 (SLit 0))].
Definition ng_regions0X : smem :=
[ stack_region 192; got_regionP; bcell_regionP 35; uar_got_regionP 41; uar_cell_regionP 41; obj8_region 3 (SOff A_TEXT 0);
ncfg_regionX ].
Definition ng_atoms0X : list (nat * afact) := ng_atoms0 ++ [ (42%nat, mkAF 0x10000 0x5fb000 0) ].
Definition ss_ng0X : sstate := mkSS AF_asan3_cgif_newgif sr_atoms ng_regions0X None (mkFacts ng_atoms0X [] []).
Definition ng_EX (E0 E : env) (attr gen Wd Hd ngp loops F FL uar path : Z) : Prop :=
ng_E E0 E attr gen Wd Hd ngp loops F FL uar /\ ew E 42 = Z_to_bv 64 path.
Definition ng_ctxX (B : asyms) ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (cfgp pal0 pala attr gen Wd Hd ngp loops path : Z) (rest : list (Z * Z)) : Prop :=
afn_pre SEGS B TNEWGIFX_STK ly S W regs mem md ch /\ spZ regs mod 32 = 0 /\
In (raZ regs :: spine ch) CTX /\ Z.of_nat (length (frames S)) <= 7 /\ spZ regs + 32 <= ly_top ly /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) /\
obj_at SEGS (mrestrict (w_H W) mem) cfgp LAY_Config [pal0; path; attr; gen; Wd; Hd; ngp; loops; hw; 0] /\
Wd * Hd <= 100000000 /\ Z_to_bv 64 pala = Z_to_bv 64 pal0 /\
Permutation (ablocks B ly S) ((if Z.land attr 4 =? 0 then [(pala, 3 * ngp)] else []) ++ rest) /\
st_nev S + EV_NEWGIF <= EV_MAX /\ blocks_bytes S + LIVE_NEWGIF <= LIVE_MAX.
Definition ng_xent (B : asyms) (K : asink_syms) (MT : ameter_ops) (XN : xnums) ly S (W : world SEGS) mem md (pala attr ngp aM : Z) (GPAL : list Z) : Prop :=
(Z.land attr 4 = 0 -> garr8 SEGS (mrestrict (w_H W) mem) pala GPAL /\ Z.of_nat (length GPAL) = 3 * ngp) /\
asink_none SEGS K (mrestrict (w_H W) mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
ameta_inv SEGS K ly (mrestrict (w_H W) mem) aM /\
mo_ok MT S (xm_newgif XN ngp).
Definition ng_macc1 (MT : ameter_ops) : Z := mo_malloc MT FILE_BLOCK.
Definition ng_macc2 (MT : ameter_ops) : Z := ng_macc1 MT + mo_malloc MT 96.
Definition ng_macc3 (MT : ameter_ops) (ngp : Z) : Z := ng_macc2 MT + mo_malloc MT (3 * ngp).
Definition ng_msum (MT : ameter_ops) (ngp : Z) : Z := ng_macc3 MT ngp + mo_malloc MT RAW_SIZE + 4 * mo_free MT.
Definition ng_nowBX (B : asyms) (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) (k : Z) : Prop :=
ajournal SEGS B TNEWGIFX_STK (spZ regs) [] ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem ms3) md3 k /\ k <= 0 /\
frames S3 = (1, fpos) :: frames S /\ ablocks B ly3 S3 = ablocks B ly S.
Definition ng_nowMX (B : asyms) (K : asink_syms) (MT : ameter_ops) (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model) (fpos pf g : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) (k : Z) : Prop :=
ajournal SEGS B TNEWGIFX_STK (spZ regs) [sink_token] ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem ms3) md3 k /\ k <= 2 /\
frames S3 = (1, fpos) :: frames S /\ ablocks B ly3 S3 = (ablocks B ly S ++ [(pf, FILE_BLOCK)]) ++ [(g, 96)] /\ 4096 <= g /\ 4096 <= pf /\
aftok [sink_token] (ablocks B ly S) (g, 96) /\
(forall blc lyq ownq i, In (g, 96) blc -> 0 <= i < 96 -> awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc lyq ownq (g + i)) /\
aftok [sink_token] (ablocks B ly S) (pf, FILE_BLOCK) /\
(forall blc lyq ownq i, In (pf, FILE_BLOCK) blc -> 0 <= i < req_size FILE_BLOCK -> awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc lyq ownq (pf + i)) /\
asink_at SEGS K (mrestrict (w_H W3) (ms_mem ms3)) md3 pf [] /\
mo_le MT S S3 (ng_macc2 MT).
Definition ng_nowGX (B : asyms) (K : asink_syms) (MT : ameter_ops) (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model) (fpos pf g pal n ngp : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) (k : Z) : Prop :=
ajournal SEGS B TNEWGIFX_STK (spZ regs) [sink_token] ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem ms3) md3 k /\ k <= 3 /\
frames S3 = (1, fpos) :: frames S /\ ablocks B ly3 S3 = ((ablocks B ly S ++ [(pf, FILE_BLOCK)]) ++ [(g, 96)]) ++ [(pal, n)] /\ 4096 <= g /\ 4096 <= pal /\ 4096 <= pf /\
aftok [sink_token] (ablocks B ly S) (g, 96) /\
(forall blc lyq ownq i, In (g, 96) blc -> 0 <= i < 96 -> awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc lyq ownq (g + i)) /\
aftok [sink_token] (ablocks B ly S) (pal, n) /\
(forall blc lyq ownq i, In (pal, n) blc -> 0 <= i < req_size n -> awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc lyq ownq (pal + i)) /\
aftok [sink_token] (ablocks B ly S) (pf, FILE_BLOCK) /\
(forall blc lyq ownq i, In (pf, FILE_BLOCK) blc -> 0 <= i < req_size FILE_BLOCK -> awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc lyq ownq (pf + i)) /\
asink_at SEGS K (mrestrict (w_H W3) (ms_mem ms3)) md3 pf [] /\
mo_le MT S S3 (ng_macc3 MT ngp).
Definition ng_postXB (B : asyms) (K : asink_syms) (MT : ameter_ops) (XN : xnums) (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS)
(mem : word -> option byte) (md : Model) (attr gen Wd Hd ngp loops aM : Z) (GPAL : list Z) : world SEGS -> config -> Prop :=
apost_base SEGS B TNEWGIFX_STK [sink_token] regs ly S W mem md EV_NEWGIF
(fun ly' S' W' regs' mem' md' => exists res : Z, getr regs' 10 = w64 res /\
ameta_ok SEGS K (mrestrict (w_H W') mem') aM /\ mo_le MT S S' (xn_newgif XN ngp) /\
((res = 0 /\ g_sgct_ok (newgif_cfg Wd Hd attr gen ngp GPAL) = false /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\ asink_none SEGS K (mrestrict (w_H W') mem') md' /\
Fs.fs_lookup (m_fs md') sink_path = Some (bytes []))
\/
(res <> 0 /\ g_sgct_ok (newgif_cfg Wd Hd attr gen ngp GPAL) = true /\
exists (s : cgif_st) (f : Z),
xcgif_at SEGS (BASE + 0x614) (ak_path K) hw f (mrestrict (w_H W') mem') res s /\ cgif_wf s (Wd * Hd) /\ f <> 0 /\
cg_frames s = [None; None; None] /\ cg_W s = Wd /\ cg_H s = Hd /\ cg_attr s = attr /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\ cg_gen s = gen /\ cg_ngp s = ngp /\
Permutation (ablocks B ly' S') (cgif_blocks res s (Wd * Hd) ++ (f, FILE_BLOCK) :: ablocks B ly S) /\
(forall b, In b (cgif_blocks res s (Wd * Hd) ++ [(f, FILE_BLOCK)]) ->
aftok [sink_token] (ablocks B ly S) b /\
forall blc i, In b blc -> 0 <= i < req_size (snd b) ->
awr_byte TNEWGIFX_STK (spZ regs) [sink_token] (ablocks B ly S) blc ly' [] (fst b + i)) /\
cgif_relA SEGS K (mrestrict (w_H W') mem') md' s f (Wd * Hd) GPAL (gs_new Wd Hd attr ngp loops GPAL) /\
Z.of_nat (length (concat (YO07.s_out (gs_new Wd Hd attr ngp loops GPAL)))) <= HDR_OUT))).
Definition NG_M_stmtX (B : asyms) (K : asink_syms) (MT : ameter_ops) (XN : xnums) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp pal0 pala attr gen Wd Hd ngp loops aM : Z) rest (GPAL : list Z) (cid pos : Z)
(E0 E : env) W3 ly3 S3 (ms3 : machine_state) md3 (k fpos pf g : Z),
ng_ctxX B ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops (ak_path K) rest ->
ng_xent B K MT XN ly S W mem md pala attr ngp aM GPAL ->
ng_cfg B ly S W mem cid pos cfgp ->
ng_E0 regs cfgp pal0 E0 -> ng_EX E0 E attr gen Wd Hd ngp loops (frame_addr ly 1 fpos) (flag_addr ly 1 fpos) (as_uar_cell B) (ak_path K) ->
ew E 52 = Z_to_bv 64 pf -> ew E 550 = Z_to_bv 64 g ->
ng_nowMX B K MT regs ly S W mem md fpos pf g ly3 S3 W3 ms3 md3 k ->
Wd <> 0 -> Hd <> 0 ->
st_ok_pi SEGS VAL E ss_NMX (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (ng_postXB B K MT XN regs ly S W mem md attr gen Wd Hd ngp loops aM GPAL).
Definition NG_K_stmtX (B : asyms) (K : asink_syms) (MT : ameter_ops) (XN : xnums) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp pal0 pala attr gen Wd Hd ngp loops aM : Z) rest (GPAL : list Z) (cid pos : Z)
(E0 E : env) W3 ly3 S3 (ms3 : machine_state) md3 (k fpos pf g : Z),
ng_ctxX B ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops (ak_path K) rest ->
ng_xent B K MT XN ly S W mem md pala attr ngp aM GPAL ->
ng_cfg B ly S W mem cid pos cfgp ->
ng_E0 regs cfgp pal0 E0 -> ng_EX E0 E attr gen Wd Hd ngp loops (frame_addr ly 1 fpos) (flag_addr ly 1 fpos) (as_uar_cell B) (ak_path K) ->
ew E 52 = Z_to_bv 64 pf -> ew E 550 = Z_to_bv 64 g ->
ng_nowMX B K MT regs ly S W mem md fpos pf g ly3 S3 W3 ms3 md3 k ->
Wd <> 0 -> Hd <> 0 ->
st_ok_pi SEGS VAL E ss_NKX (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (ng_postXB B K MT XN regs ly S W mem md attr gen Wd Hd ngp loops aM GPAL).
Definition NG_P0_stmtX (B : asyms) (K : asink_syms) (MT : ameter_ops) (XN : xnums) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp pal0 pala attr gen Wd Hd ngp loops aM : Z) rest (GPAL : list Z) (cid pos : Z)
(E0 E : env) W3 ly3 S3 (ms3 : machine_state) md3 (k fpos pf g : Z),
ng_ctxX B ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops (ak_path K) rest ->
ng_xent B K MT XN ly S W mem md pala attr ngp aM GPAL ->
ng_cfg B ly S W mem cid pos cfgp ->
ng_E0 regs cfgp pal0 E0 -> ng_EX E0 E attr gen Wd Hd ngp loops (frame_addr ly 1 fpos) (flag_addr ly 1 fpos) (as_uar_cell B) (ak_path K) ->
ew E 52 = Z_to_bv 64 pf -> ew E 550 = Z_to_bv 64 g ->
ng_nowMX B K MT regs ly S W mem md fpos pf g ly3 S3 W3 ms3 md3 k ->
Wd <> 0 -> Hd <> 0 -> Z.land attr 4 <> 0 ->
st_ok_pi SEGS VAL E ss_NP0X (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (ng_postXB B K MT XN regs ly S W mem md attr gen Wd Hd ngp loops aM GPAL).
Definition NG_G_stmtX (B : asyms) (K : asink_syms) (MT : ameter_ops) (XN : xnums) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp pal0 pala attr gen Wd Hd ngp loops aM : Z) rest (GPAL : list Z) (cid pos : Z)
(E0 E : env) W3 ly3 S3 (ms3 : machine_state) md3 (k fpos pf g pal : Z),
ng_ctxX B ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops (ak_path K) rest ->
ng_xent B K MT XN ly S W mem md pala attr ngp aM GPAL ->
ng_cfg B ly S W mem cid pos cfgp ->
ng_E0 regs cfgp pal0 E0 -> ng_EX E0 E attr gen Wd Hd ngp loops (frame_addr ly 1 fpos) (flag_addr ly 1 fpos) (as_uar_cell B) (ak_path K) ->
ew E 52 = Z_to_bv 64 pf -> ew E 550 = Z_to_bv 64 g -> ew E 599 = Z_to_bv 64 pal ->
ng_nowGX B K MT regs ly S W mem md fpos pf g pal (3 * ngp) ngp ly3 S3 W3 ms3 md3 k ->
Wd <> 0 -> Hd <> 0 -> Z.land attr 4 = 0 -> pala = pal0 ->
st_ok_pi SEGS VAL E ss_NG1X (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (ng_postXB B K MT XN regs ly S W mem md attr gen Wd Hd ngp loops aM GPAL).
Definition NG_P1_stmtX (B : asyms) (K : asink_syms) (MT : ameter_ops) (XN : xnums) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp pal0 pala attr gen Wd Hd ngp loops aM : Z) rest (GPAL : list Z) (cid pos : Z)
(E0 E : env) W3 ly3 S3 (ms3 : machine_state) md3 (k fpos pf g pal : Z),
ng_ctxX B ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops (ak_path K) rest ->
ng_xent B K MT XN ly S W mem md pala attr ngp aM GPAL ->
ng_cfg B ly S W mem cid pos cfgp ->
ng_E0 regs cfgp pal0 E0 -> ng_EX E0 E attr gen Wd Hd ngp loops (frame_addr ly 1 fpos) (flag_addr ly 1 fpos) (as_uar_cell B) (ak_path K) ->
ew E 52 = Z_to_bv 64 pf -> ew E 550 = Z_to_bv 64 g -> ew E 599 = Z_to_bv 64 pal ->
ng_nowGX B K MT regs ly S W mem md fpos pf g pal (3 * ngp) ngp ly3 S3 W3 ms3 md3 k ->
Wd <> 0 -> Hd <> 0 -> Z.land attr 4 = 0 -> pala = pal0 ->
garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) pal GPAL ->
st_ok_pi SEGS VAL E ss_NP1X (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (ng_postXB B K MT XN regs ly S W mem md attr gen Wd Hd ngp loops aM GPAL).
Definition ng_treeX (md : Model) (attr gen Wd Hd ngp : Z) (GPAL : list Z) (TA TB : TSet) : TSet :=
if g_opens (newgif_cfg Wd Hd attr gen ngp GPAL) then openat_shape (m_fs md) TA TB else TA.
Definition ng_contX (B : asyms) (K : asink_syms) (MT : ameter_ops) (XN : xnums) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
(attr gen Wd Hd ngp loops aM : Z) (GPAL : list Z) (TA TB : TSet) : Prop :=
(forall W' c', wle W W' -> AI SEGS (w_H W') (w_A W') (cfg_model c') ->
tnewgif_postA SEGS K B MT XN regs ly S W mem md Wd Hd attr gen ngp GPAL aM W' c' -> srealizes SEGS c' TA) /\
(g_opens (newgif_cfg Wd Hd attr gen ngp GPAL) = true -> g_sgct_ok (newgif_cfg Wd Hd attr gen ngp GPAL) = false ->
forall W' c', wle W W' -> AI SEGS (w_H W') (w_A W') (cfg_model c') ->
tnewgif_postB0 SEGS K B MT XN regs ly S W mem md Wd Hd attr gen ngp GPAL aM W' c' -> srealizes SEGS c' TB) /\
(g_opens (newgif_cfg Wd Hd attr gen ngp GPAL) = true -> g_sgct_ok (newgif_cfg Wd Hd attr gen ngp GPAL) = true ->
forall W' c', wle W W' -> AI SEGS (w_H W') (w_A W') (cfg_model c') ->
tnewgif_postB1 SEGS K B MT XN (BASE + 0x614) regs ly S W mem md Wd Hd attr gen ngp loops GPAL aM W' c' -> srealizes SEGS c' TB).
Definition NG_B_stmtX (B : asyms) (K : asink_syms) (MT : ameter_ops) (XN : xnums) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp pal0 pala attr gen Wd Hd ngp loops aM : Z) rest (GPAL : list Z) (cid pos : Z)
(E0 E : env) W3 ly3 S3 (ms3 : machine_state) md3 (k fpos : Z) (TA TB : TSet),
ng_ctxX B ly S W regs mem md ch cfgp pal0 pala attr gen Wd Hd ngp loops (ak_path K) rest ->
ng_xent B K MT XN ly S W mem md pala attr ngp aM GPAL ->
ng_contX B K MT XN regs ly S W mem md attr gen Wd Hd ngp loops aM GPAL TA TB ->
ng_cfg B ly S W mem cid pos cfgp ->
ng_E0 regs cfgp pal0 E0 -> ng_EX E0 E attr gen Wd Hd ngp loops (frame_addr ly 1 fpos) (flag_addr ly 1 fpos) (as_uar_cell B) (ak_path K) ->
ng_nowBX B regs ly S W mem md fpos ly3 S3 W3 ms3 md3 k ->
st_ok_pi SEGS VAL E ss_NBX (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3)
(fun W' c' => AI SEGS (w_H W') (w_A W') (cfg_model c') -> srealizes SEGS c' (ng_treeX md attr gen Wd Hd ngp GPAL TA TB)).
Lemma ng_postXB_arms : forall (B : asyms) (K : asink_syms) (MT : ameter_ops) (XN : xnums) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
(attr gen Wd Hd ngp loops aM : Z) (GPAL : list Z) W' c',
hw = 0 ->
ng_postXB B K MT XN regs ly S W mem md attr gen Wd Hd ngp loops aM GPAL W' c' ->
(g_sgct_ok (newgif_cfg Wd Hd attr gen ngp GPAL) = false /\ tnewgif_postB0 SEGS K B MT XN regs ly S W mem md Wd Hd attr gen ngp GPAL aM W' c') \/
(g_sgct_ok (newgif_cfg Wd Hd attr gen ngp GPAL) = true /\ tnewgif_postB1 SEGS K B MT XN (BASE + 0x614) regs ly S W mem md Wd Hd attr gen ngp loops GPAL aM W' c').
Proof.
intros B K MT XN regs ly S W mem md attr gen Wd Hd ngp loops aM GPAL W' c' Hhw
(ly' & S' & regs' & mem' & md' & -> & HJ & HP & res & Ha0 & HAM & MLE & [(-> & Hsg & HPerm & HSN & Hlk) | (Hres & Hsg & s & f & HX)]).
- left. split; [exact Hsg|]. exists ly', S', regs', mem', md'. split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|].
split; [exact Ha0|]. split; [exact HAM|]. split; [exact MLE|]. split; [exact HPerm|]. split; [exact HSN | exact Hlk].
- right. split; [exact Hsg|]. exists ly', S', regs', mem', md'. split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|].
exists res. split; [exact Ha0|]. split; [exact HAM|]. split; [exact MLE|]. split; [exact Hres|]. exists s, f. rewrite Hhw in HX. exact HX.
Qed.
Section d.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis Rhw : 0 <= hw < 2 ^ 64.
Variable path : Z.
Hypothesis Rpath : 0x10000 <= path < 0x5fb000.
Hypothesis HGOT3 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 3)) 8 (BASE + 0).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Lemma ng_entryX : forall W ly S regs mem md ch cfgp pal0 attr gen Wd Hd ngp loops,
afn_pre SEGS B TNEWGIFX_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj SEGS B ly S W mem cfgp 48 ->
obj_at SEGS (mrestrict (w_H W) mem) cfgp LAY_Config [pal0; path; attr; gen; Wd; Hd; ngp; loops; hw; 0] ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ng_extraX pal0 attr gen Wd Hd ngp loops (as_uar_cell B) path))) ss_ng0X (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_asan3_cgif_newgif)) mem (seg_rom SEGS))).
Proof.
intros W ly S regs mem md ch cfgp pal0 attr gen Wd Hd ngp loops HPRE Hal32 HROD H10 HFO Hcfg.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : TNEWGIFX_STK = 18816) by reflexivity.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
pose proof Hcfg as Hcfg'. cbn [obj_at LAY_Config] in Hcfg'.
destruct Hcfg' as ([V0 R0] & [V8 _] & [V16 R16] & [V20 R20] & [V24 R24] & [V26 R26] & [V28 R28] & [V30 R30] & [V32 _] & [V40 _] & _).
cbn [fst snd N.to_nat Z.of_N] in V0, V8, V16, V20, V24, V26, V28, V30, V32, V40, R0, R16, R20, R24, R26, R28, R30.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with (2 ^ 32) in *. change (2 ^ (8 * 2)) with 65536 in *.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (ng_extraX pal0 attr gen Wd Hd ngp loops (as_uar_cell B) path))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 cfgp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, (j < 11)%nat -> ew E (32 + j) = nth j (ng_extraX pal0 attr gen Wd Hd ngp loops (as_uar_cell B) path) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37. pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41. pose proof (EX 10%nat ltac:(lia)) as E42.
cbn [Nat.add nth ng_extraX ng_extra map app] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42. clear EX.
assert (E240 : ew E A_TEXT = Z_to_bv 64 BASE) by (subst E; apply Eimg_img; unfold A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E244 : ew E (A_OBJ 3) = Z_to_bv 64 (VAL (A_OBJ 3))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 3 ltac:(lia)) as Hob3.
pose proof (pa_obj_img 12 ltac:(lia)) as Hob12. pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
Local Ltac ck HE M := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | first [exact M | rewrite Z.add_0_r; exact M] ].
unfold ss_ng0X. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold ng_regions0X, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, obj8_region, ncfg_regionX.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 35 0) SB);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 41 0) (as_uar_cell B));
[cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite (VB 41%nat (as_uar_cell B) E41) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
+ rewrite (VB (A_OBJ 3) (VAL (A_OBJ 3)) E244) by (pose proof (pa_val_range (A_OBJ 3)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 3)) 0 8 (SOff A_TEXT 0) (BASE + 0));
[cbn [sv_denot]; rewrite E240, unsigned_lit_small by lia; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (HGOT3 (w_H W) mem HROD).
+ rewrite (VB 10%nat cfgp E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [ck E32 V0|].
constructor; [apply (chunk_ok_val SEGS E _ cfgp 8 8 _ path); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rpath; zside | zside | exact V8]|].
constructor; [ck E33 V16|]. constructor; [ck E34 V20|]. constructor; [ck E36 V24|].
constructor; [ck E37 V26|]. constructor; [ck E38 V28|]. constructor; [ck E39 V30|].
constructor; [apply (chunk_ok_val SEGS E _ cfgp 32 8 _ hw); [reflexivity | clear - Rhw; zside | zside | exact V32]|].
constructor; [apply (chunk_ok_val SEGS E _ cfgp 40 8 _ 0); [reflexivity | zside | zside | exact V40]|]. constructor.
- apply pairwise_disjoint_of_extents.
unfold ng_regions0X, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, obj8_region, ncfg_regionX, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat cfgp E10), (VB 41%nat (as_uar_cell B) E41) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 3) (VAL (A_OBJ 3)) E244) by (pose proof (pa_val_range (A_OBJ 3)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hfceil Hfhigh Hfhigh_img Hflo Hfhi C1 C3 FFS Hstk0 Hob0 Hob1 Hob3 Hob12 Huar Hsep. clear. unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
repeat split; first [ assumption | (apply or_comm; assumption)
| (repeat match goal with H : pa_val (A_OBJ _) + 8 <= _ \/ _ |- _ => clear H | H : as_uar_cell _ + 4 <= _ \/ _ |- _ => clear H end; lia) ].
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok ng_atoms0X ng_atoms0 app]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hc8 : cfgp mod 8 = 0) by exact Hcal.
revert Hslo Hshi H47 Hceil Hfceil Hfhigh Hfhigh_img Hflo Hfhi Hal32 Hc8 R0 R16 R20 R24 R26 R28 R30 C1 C3 FFS Hstk0 Huar Huar4 Rhw Rpath. clear. unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
End d.
End c.
End a.
