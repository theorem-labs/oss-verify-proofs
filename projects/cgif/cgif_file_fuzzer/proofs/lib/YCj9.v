(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkd.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkc YCj4 YCj0 YCj6 YCj7 YC8g YCjr.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition ss_R2_0 : sstate :=
(mkSS 10800
[SLit 0; SOff 847 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 57 0; SOff 841 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0); SOff 2 0; SOff 60 0; SOff 51 0; SLit 0; SOff 850 0; SOff 851 0; SOff 852 0; SOff 10 0;
SOff 11 0; SOff 12 0; SOff 516 0; SOff 853 0; SOff 856 0; SOff 844 0; SOff 846 0; SOff 845 0; SLit 0; SOff 516 32; SOff 854 0; SOff 855 0; SOff 11 20; SOff 32 0;
SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))); SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)]
[{|
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
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 128;
r_wlo := 0;
r_whi := 128;
r_chunks :=
[{| c_off := 32; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 240 6660) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 246 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |};
{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
|};
{|
r_base := Some 60%nat;
r_lo := 0;
r_hi := 248;
r_wlo := 0;
r_whi := 248;
r_chunks :=
[{| c_off := 64; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)) |}; {| c_off := 56; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 4)) |};
{| c_off := 72; YP09.c_val := CVal 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2)))) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 11 20) |};
{| c_off := 88; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0)) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 11 16) |}; {| c_off := 96; YP09.c_val := CVal 8 (SOff 57 0) |};
{| c_off := 120; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 1)) |}; {| c_off := 184; YP09.c_val := CVal 8 (SOff 842 0) |}; {| c_off := 176; YP09.c_val := CVal 8 (SOff 40 0) |};
{| c_off := 104; YP09.c_val := CVal 8 (SOff 529 0) |}; {| c_off := 128; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 240; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 112; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := 192; YP09.c_val := CVal 8 (SOff 12 0) |}; {| c_off := 208; YP09.c_val := CVal 8 (SOff 11 0) |}; {| c_off := 200; YP09.c_val := CVal 8 (SOff 10 0) |}; {| c_off := 216; YP09.c_val := CVal 8 (SOff 32 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 59 0) |}] |};
{| r_base := Some 59%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 37 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 38 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 39 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 40 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 41 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 42 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 43 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SOff 44 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 45 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SOff 46 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 47 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 48 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SOff 49 0) |}]
|};
{|
r_base := Some 11%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 20;
r_whi := 24;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 51 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 52 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 621 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 54 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 55 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 56 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 57 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 58 0) |}]
|}]
None
{|
f_atoms :=
[(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(60%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (40%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(42%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(51%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (53%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(54%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (55%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (621%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (625%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (841%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(844%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (845%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (846%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_EQ; ac_a := SOff 843 0; ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)]
|}).
Definition ss_R2 : sstate := Eval vm_compute in ss_clear_conds (ss_havoc_regs ss_R2_0 891 fl_R2_deads).
Definition ss_R3_0 : sstate :=
(mkSS 10848
[SLit 0; SOff 847 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 57 0; SOff 841 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0); SOff 2 0; SOff 60 0; SLit 1; SOff 893 0; SOff 850 0; SOff 851 0; SOff 852 0; SOff 10 0;
SOff 11 0; SOff 12 0; SOff 516 0; SOff 853 0; SOff 856 0; SOff 844 0; SOff 846 0; SOff 845 0; SOff 892 0; SOff 516 32; SOff 854 0; SOff 855 0; SOff 11 20; SOff 32 0;
SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))); SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)]
[{|
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
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 128;
r_wlo := 0;
r_whi := 128;
r_chunks :=
[{| c_off := 48; YP09.c_val := CVal 4 (SOff 901 0) |}; {| c_off := 40; YP09.c_val := CVal 8 (SOff 891 0) |}; {| c_off := 32; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 240 6660) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 246 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
|};
{|
r_base := Some 60%nat;
r_lo := 0;
r_hi := 248;
r_wlo := 0;
r_whi := 248;
r_chunks :=
[{| c_off := 64; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)) |}; {| c_off := 56; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 4)) |};
{| c_off := 72; YP09.c_val := CVal 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2)))) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 11 20) |};
{| c_off := 88; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0)) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 11 16) |}; {| c_off := 96; YP09.c_val := CVal 8 (SOff 57 0) |};
{| c_off := 120; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 1)) |}; {| c_off := 184; YP09.c_val := CVal 8 (SOff 842 0) |}; {| c_off := 176; YP09.c_val := CVal 8 (SOff 40 0) |};
{| c_off := 104; YP09.c_val := CVal 8 (SOff 529 0) |}; {| c_off := 128; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 240; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 112; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := 192; YP09.c_val := CVal 8 (SOff 12 0) |}; {| c_off := 208; YP09.c_val := CVal 8 (SOff 11 0) |}; {| c_off := 200; YP09.c_val := CVal 8 (SOff 10 0) |}; {| c_off := 216; YP09.c_val := CVal 8 (SOff 32 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 59 0) |}] |};
{| r_base := Some 59%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 37 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 38 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 39 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 40 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 41 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 42 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 43 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SOff 44 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 45 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SOff 46 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 47 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 48 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SOff 49 0) |}]
|};
{|
r_base := Some 11%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 20;
r_whi := 24;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 51 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 52 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 621 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 54 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 55 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 56 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 57 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 58 0) |}]
|}]
None
{|
f_atoms :=
[(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(60%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (40%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(42%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(51%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (53%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(54%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (55%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (621%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (625%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (841%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(844%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (845%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (846%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_NE; ac_a := SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))); ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)]
|}).
Definition ss_R3 : sstate := Eval vm_compute in
ss_clear_conds (ss_set_facts (ss_havoc_regs (ss_rechunk_off ss_R3_0 516 48 (SOff 901 0)) 902 fl_R3_deads)
(f_atoms (ss_facts ss_R3_0) ++ [(901%nat, mkAF 0 1 0)])).
Definition ss_R4_0 : sstate :=
(mkSS 10960
[SLit 0; SOff 847 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 57 0; SOff 841 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0); SOff 2 0; SOff 60 0; SLit 0; SOff 905 0; SOff 906 0; SOff 851 0; SOff 852 0; SOff 10 0;
SOff 11 0; SOff 12 0; SOff 516 0; SOff 853 0; SOff 856 0; SOff 844 0; SOff 846 0; SOff 845 0; SOff 892 0; SOff 516 32; SOff 854 0; SOff 855 0; SOff 11 20; SOff 32 0;
SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))); SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)]
[{|
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
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 128;
r_wlo := 0;
r_whi := 128;
r_chunks :=
[{| c_off := 62; YP09.c_val := CVal 2 (SOff 911 0) |}; {| c_off := 60; YP09.c_val := CVal 2 (SExt true 16 (SOff 54 0)) |}; {| c_off := 56; YP09.c_val := CVal 2 (SOff 841 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 845 0) |};
{| c_off := 52; YP09.c_val := CVal 2 (SOff 844 0) |}; {| c_off := 48; YP09.c_val := CVal 4 (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_SRL (SExt true 32 (SOff 52 0)) (SLit 2)) (SLit 2)) (SOff 901 0)) |};
{| c_off := 58; YP09.c_val := CVal 2 (SOff 846 0) |}; {| c_off := 40; YP09.c_val := CVal 8 (SOff 891 0) |}; {| c_off := 32; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 240 6660) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 246 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
|};
{|
r_base := Some 60%nat;
r_lo := 0;
r_hi := 248;
r_wlo := 0;
r_whi := 248;
r_chunks :=
[{| c_off := 64; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)) |}; {| c_off := 56; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 4)) |};
{| c_off := 72; YP09.c_val := CVal 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2)))) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 11 20) |};
{| c_off := 88; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0)) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 11 16) |}; {| c_off := 96; YP09.c_val := CVal 8 (SOff 57 0) |};
{| c_off := 120; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 1)) |}; {| c_off := 184; YP09.c_val := CVal 8 (SOff 842 0) |}; {| c_off := 176; YP09.c_val := CVal 8 (SOff 40 0) |};
{| c_off := 104; YP09.c_val := CVal 8 (SOff 529 0) |}; {| c_off := 128; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 240; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 112; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := 192; YP09.c_val := CVal 8 (SOff 12 0) |}; {| c_off := 208; YP09.c_val := CVal 8 (SOff 11 0) |}; {| c_off := 200; YP09.c_val := CVal 8 (SOff 10 0) |}; {| c_off := 216; YP09.c_val := CVal 8 (SOff 32 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 59 0) |}] |};
{| r_base := Some 59%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 37 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 38 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 39 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 40 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 41 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 42 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 43 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SOff 44 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 45 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SOff 46 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 47 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 48 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SOff 49 0) |}]
|};
{|
r_base := Some 11%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 20;
r_whi := 24;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 51 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 52 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 621 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 54 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 55 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 56 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 57 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 58 0) |}]
|}]
None
{|
f_atoms :=
[(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(60%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (40%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(42%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(51%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (53%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(54%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (55%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (621%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (625%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (841%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(844%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (845%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (846%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (901%nat, {| af_lo := 0; af_hi := 1; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_EQ; ac_a := SAlu ALU_AND (SOff 52 0) (SLit 1); ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)]
|}).
Definition ss_R4 : sstate := Eval vm_compute in
ss_clear_conds (ss_set_facts (ss_havoc_regs (ss_rechunk_off ss_R4_0 516 62 (SOff 911 0)) 912 fl_R4_deads)
(f_atoms (ss_facts ss_R4_0) ++ [(911%nat, mkAF 0 65535 0)])).
Definition ss_R5_0 : sstate :=
(mkSS 11004
[SLit 0; SOff 916 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 917 0; SOff 918 0; SOff 919 0; SOff 2 0; SOff 60 0; SOff 920 0; SOff 921 0; SOff 922 0; SOff 923 0; SOff 924 0; SOff 925 0; SOff 926 0; SOff 927 0; SOff 516 0; SOff 853 0;
SOff 856 0; SOff 844 0; SOff 846 0; SOff 845 0; SOff 892 0; SOff 516 32; SOff 854 0; SOff 855 0; SOff 928 0; SOff 929 0; SOff 930 0; SOff 931 0]
[{|
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
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 128;
r_wlo := 0;
r_whi := 128;
r_chunks :=
[{| c_off := 65; YP09.c_val := CVal 1 (SOff 842 0) |}; {| c_off := 64; YP09.c_val := CVal 1 (SOff 57 0) |}; {| c_off := 62; YP09.c_val := CVal 2 (SOff 911 0) |}; {| c_off := 60; YP09.c_val := CVal 2 (SExt true 16 (SOff 54 0)) |};
{| c_off := 56; YP09.c_val := CVal 2 (SOff 841 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 845 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 844 0) |};
{| c_off := 48; YP09.c_val := CVal 4 (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_SRL (SExt true 32 (SOff 52 0)) (SLit 2)) (SLit 2)) (SOff 901 0)) |}; {| c_off := 58; YP09.c_val := CVal 2 (SOff 846 0) |};
{| c_off := 40; YP09.c_val := CVal 8 (SOff 891 0) |}; {| c_off := 32; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 240 6660) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 246 0) |};
{| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
|};
{|
r_base := Some 60%nat;
r_lo := 0;
r_hi := 248;
r_wlo := 0;
r_whi := 248;
r_chunks :=
[{| c_off := 64; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)) |}; {| c_off := 56; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 4)) |};
{| c_off := 72; YP09.c_val := CVal 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2)))) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 11 20) |};
{| c_off := 88; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0)) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 11 16) |}; {| c_off := 96; YP09.c_val := CVal 8 (SOff 57 0) |};
{| c_off := 120; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 1)) |}; {| c_off := 184; YP09.c_val := CVal 8 (SOff 842 0) |}; {| c_off := 176; YP09.c_val := CVal 8 (SOff 40 0) |};
{| c_off := 104; YP09.c_val := CVal 8 (SOff 529 0) |}; {| c_off := 128; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 240; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 112; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := 192; YP09.c_val := CVal 8 (SOff 12 0) |}; {| c_off := 208; YP09.c_val := CVal 8 (SOff 11 0) |}; {| c_off := 200; YP09.c_val := CVal 8 (SOff 10 0) |}; {| c_off := 216; YP09.c_val := CVal 8 (SOff 32 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 59 0) |}] |};
{| r_base := Some 59%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 37 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 38 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 39 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 40 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 41 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 42 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 43 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SOff 44 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 45 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SOff 46 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 47 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 48 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SOff 49 0) |}]
|};
{|
r_base := Some 11%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 20;
r_whi := 24;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 51 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 52 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 621 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 54 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 55 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 56 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 57 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 58 0) |}]
|}]
None
{|
f_atoms :=
[(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(60%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (40%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(42%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(51%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (53%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(54%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (55%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (621%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (625%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (841%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(844%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (845%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (846%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (901%nat, {| af_lo := 0; af_hi := 1; af_al2 := 0 |});
(911%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)]
|}).
Definition ss_R5 : sstate := Eval vm_compute in ss_clear_conds ss_R5_0.
Definition ss_X : sstate := Eval vm_compute in
ss_clear_conds (ss_set_facts
(ss_havoc_regs (ss_set_reg (ss_set_reg (ss_set_pc (ss_set_mem ss_R4 (fl_X_mem (ss_mem ss_R4))) 11024) 11 (SOff 516 0)) 12 (SOff 529 0)) 961 fl_X_deads)
(f_atoms (ss_facts ss_B3))).
Definition fl_T1x_deads : list nat := [10; 11; 12; 13]%nat.
Definition fl_T1x_deads_bv : list (bv 5) := [10; 11; 12; 13]%bv.
Definition ss_T1x_0 : sstate :=
(mkSS 10120
[SLit 0; SOff 686 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 57 0; SOff 681 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0); SOff 2 0; SOff 60 0; SOff 695 0;
SAlu ALU_AND (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff 695 0)) (SLit (-1))) (SLit 255); SLit 2; SLit 64; SOff 697 0; SOff 10 0; SOff 11 0; SOff 12 0; SOff 516 0; SOff 41 0; SOff 625 0; SOff 683 0;
SOff 685 0; SOff 684 0; SOff 682 0; SOff 516 32; SOff 694 0; SOff 40 0; SOff 11 20; SOff 32 0; SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2)));
SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)]
[{|
r_base := Some 12%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 651 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 652 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 653 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 654 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 655 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 656 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 657 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 658 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 659 0) |}]
|};
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
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 128;
r_wlo := 0;
r_whi := 128;
r_chunks := [{| c_off := 16; YP09.c_val := CVal 8 (SOff 240 6660) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 246 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
|};
{|
r_base := Some 60%nat;
r_lo := 0;
r_hi := 248;
r_wlo := 0;
r_whi := 248;
r_chunks :=
[{| c_off := 152; YP09.c_val := CVal 8 (SOff 681 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 516 32) |}; {| c_off := 184; YP09.c_val := CVal 8 (SOff 741 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)) |}; {| c_off := 56; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 4)) |};
{| c_off := 72; YP09.c_val := CVal 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2)))) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 11 20) |};
{| c_off := 88; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0)) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 11 16) |}; {| c_off := 96; YP09.c_val := CVal 8 (SOff 57 0) |};
{| c_off := 120; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 1)) |}; {| c_off := 176; YP09.c_val := CVal 8 (SOff 40 0) |}; {| c_off := 104; YP09.c_val := CVal 8 (SOff 529 0) |};
{| c_off := 128; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 240; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 112; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 192; YP09.c_val := CVal 8 (SOff 12 0) |};
{| c_off := 208; YP09.c_val := CVal 8 (SOff 11 0) |}; {| c_off := 200; YP09.c_val := CVal 8 (SOff 10 0) |}; {| c_off := 216; YP09.c_val := CVal 8 (SOff 32 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 59 0) |}] |};
{| r_base := Some 59%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 37 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 38 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 39 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 40 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 41 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 42 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 43 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SOff 44 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 45 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SOff 46 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 47 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 48 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SOff 49 0) |}]
|};
{|
r_base := Some 11%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 20;
r_whi := 24;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 51 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 52 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 621 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 54 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 55 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 56 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 57 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 58 0) |}]
|}]
None
{|
f_atoms :=
[(697%nat, {| af_lo := 1; af_hi := 65536; af_al2 := 0 |}); (696%nat, {| af_lo := 0; af_hi := 16; af_al2 := 0 |}); (695%nat, {| af_lo := 0; af_hi := 16; af_al2 := 0 |}); (12%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(651%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (652%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (653%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(654%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (655%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (656%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (657%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(658%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (659%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (60%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (40%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (42%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(43%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(49%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (51%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(52%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (53%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (54%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (55%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (621%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(625%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (681%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (683%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (684%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(685%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |})];
f_conds :=
[{| ac_c := BC_GEU; ac_a := SAlu ALU_AND (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff 695 0)) (SLit (-1))) (SLit 255); ac_b := SOff 625 0 |}; {| ac_c := BC_GEU; ac_a := SOff 696 0; ac_b := SLit 2 |};
{| ac_c := BC_NE; ac_a := SAlu ALU_AND (SExt false 8 (SOff 621 0)) (SLit 1); ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)]
|}).
Definition ss_T1x : sstate := Eval vm_compute in
ss_clear_conds (ss_havoc_regs (ss_rechunk_off ss_T1x_0 60 184 (SOff 741 0)) 742 fl_T1x_deads).
Definition fl_T3_deads : list nat := [24; 1; 5; 6; 7; 10; 11; 12; 13; 14; 18; 19; 20; 25; 26; 27; 28; 30; 31]%nat.
Definition fl_T3_deads_bv : list (bv 5) := [24; 1; 5; 6; 7; 10; 11; 12; 13; 14; 18; 19; 20; 25; 26; 27; 28; 30; 31]%bv.
Definition ss_T3_0 : sstate :=
(mkSS 10204
[SLit 0; SOff 686 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 57 0; SOff 681 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0); SOff 2 0; SOff 60 0; SOff 742 0; SOff 743 0; SOff 744 0; SOff 745 0; SOff 697 0;
SOff 10 0; SOff 11 0; SOff 12 0; SOff 516 0; SOff 41 0; SOff 625 0; SOff 683 0; SOff 685 0; SOff 684 0; SOff 682 0; SOff 516 32; SOff 694 0; SOff 40 0; SOff 11 20; SOff 32 0;
SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))); SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)]
[{|
r_base := Some 12%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 651 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 652 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 653 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 654 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 655 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 656 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 657 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 658 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 659 0) |}]
|};
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
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 128;
r_wlo := 0;
r_whi := 128;
r_chunks := [{| c_off := 16; YP09.c_val := CVal 8 (SOff 240 6660) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 246 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
|};
{|
r_base := Some 60%nat;
r_lo := 0;
r_hi := 248;
r_wlo := 0;
r_whi := 248;
r_chunks :=
[{| c_off := 152; YP09.c_val := CVal 8 (SOff 681 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 516 32) |}; {| c_off := 184; YP09.c_val := CVal 8 (SOff 741 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)) |}; {| c_off := 56; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 4)) |};
{| c_off := 72; YP09.c_val := CVal 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2)))) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 11 20) |};
{| c_off := 88; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0)) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 11 16) |}; {| c_off := 96; YP09.c_val := CVal 8 (SOff 57 0) |};
{| c_off := 120; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 1)) |}; {| c_off := 176; YP09.c_val := CVal 8 (SOff 40 0) |}; {| c_off := 104; YP09.c_val := CVal 8 (SOff 529 0) |};
{| c_off := 128; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 240; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 112; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := 192; YP09.c_val := CVal 8 (SOff 12 0) |};
{| c_off := 208; YP09.c_val := CVal 8 (SOff 11 0) |}; {| c_off := 200; YP09.c_val := CVal 8 (SOff 10 0) |}; {| c_off := 216; YP09.c_val := CVal 8 (SOff 32 0) |}]
|};
{|
r_base := Some 2%nat;
r_lo := -104;
r_hi := 0;
r_wlo := -104;
r_whi := 0;
r_chunks :=
[{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |};
{| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |};
{| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |};
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 32 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 59 0) |}] |};
{| r_base := Some 59%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 34 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 35 0) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 8 (SOff 37 0) |}; {| c_off := 40; YP09.c_val := CVal 4 (SOff 38 0) |}; {| c_off := 44; YP09.c_val := CVal 4 (SOff 39 0) |}; {| c_off := 48; YP09.c_val := CVal 2 (SOff 40 0) |};
{| c_off := 50; YP09.c_val := CVal 2 (SOff 41 0) |}; {| c_off := 52; YP09.c_val := CVal 2 (SOff 42 0) |}; {| c_off := 54; YP09.c_val := CVal 2 (SOff 43 0) |}; {| c_off := 56; YP09.c_val := CVal 8 (SOff 44 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 45 0) |}; {| c_off := 72; YP09.c_val := CVal 8 (SOff 46 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 47 0) |}; {| c_off := 88; YP09.c_val := CVal 4 (SOff 48 0) |};
{| c_off := 92; YP09.c_val := CVal 4 (SOff 49 0) |}]
|};
{|
r_base := Some 11%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 20;
r_whi := 24;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 50 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 51 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 52 0) |}; {| c_off := 20; YP09.c_val := CVal 4 (SOff 621 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 54 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 55 0) |}; {| c_off := 28; YP09.c_val := CVal 1 (SOff 56 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 57 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 58 0) |}]
|}]
None
{|
f_atoms :=
[(697%nat, {| af_lo := 1; af_hi := 65536; af_al2 := 0 |}); (696%nat, {| af_lo := 0; af_hi := 16; af_al2 := 0 |}); (695%nat, {| af_lo := 0; af_hi := 16; af_al2 := 0 |}); (12%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(651%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (652%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (653%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(654%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (655%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (656%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (657%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(658%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (659%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (60%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (40%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (42%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(43%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(49%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (51%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(52%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (53%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (54%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (55%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (621%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(625%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (681%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (683%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (684%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(685%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_NE; ac_a := SOff 682 0; ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)]
|}).
Definition ss_T3 : sstate := Eval vm_compute in
ss_clear_conds (ss_set_facts (ss_havoc_regs ss_T3_0 801 fl_T3_deads) (f_atoms (ss_facts ss_T3_0) ++ [(801%nat, HPTR 4)])).
Definition INV_T3 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (fl_npal cx) /\
(exists fb, fl_bef cx fb E) /\
exists pt w h top left,
ew E 801 = Z_to_bv 64 pt /\ ew E 683 = Z_to_bv 64 w /\ ew E 684 = Z_to_bv 64 h /\ ew E 681 = Z_to_bv 64 top /\ ew E 685 = Z_to_bv 64 left /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\
k <= 2 /\ fl_tmpblk B cx pt (w * h) ly3 S3.
End b.
End a.
