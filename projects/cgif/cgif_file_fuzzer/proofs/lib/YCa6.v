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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI10 YC4a YC8i YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbk YC9g YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8h YC8j YCab YCai YCaj.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCai YCaj YCak YCal.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YCbh YC85 YCa3 YCa4 YCa5.
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
Context {PI : PAImg lib_both3_1_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_1_listing PI) (@pa_relro_lo _ lib_both3_1_listing PI) (@pa_relro_hi _ lib_both3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition ss_L0X : sstate :=
(mkSS 3300
[SLit 0; SOff 816 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 817 0; SOff 818 0; SOff 819 0; SOff 2 0; SOff 2 (-320); SOff 859 0; SLit 7; SLit 5; SOff 823 0; SOff 824 0; SOff 825 0; SOff 826 0; SOff 827 0; SOff 529 0; SLit 0;
SOff 43 0; SOff 11 20; SOff 11 22; SOff 11 8; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 22) (SLit 3)) (SOff 40 0); SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 40 0); SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 8) (SLit 3)) (SOff 40 0);
SOff 859 0; SOff 828 0; SOff 829 0; SOff 830 0; SOff 831 0]
[{|
r_base := Some 516%nat;
r_lo := 49;
r_hi := 58;
r_wlo := 49;
r_whi := 58;
r_chunks :=
[{| c_off := 50; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 47 0) (SLit 8)) |}; {| c_off := 49; YP09.c_val := CVal 1 (SOff 47 0) |}; {| c_off := 52; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 46 0) (SLit 8)) |};
{| c_off := 51; YP09.c_val := CVal 1 (SOff 46 0) |}; {| c_off := 56; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 45 0) (SLit 8)) |}; {| c_off := 55; YP09.c_val := CVal 1 (SOff 45 0) |};
{| c_off := 54; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 44 0) (SLit 8)) |}; {| c_off := 53; YP09.c_val := CVal 1 (SOff 44 0) |};
{| c_off := 57; YP09.c_val := CVal 1 (SAlu ALU_OR (SOff 661 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 43 0) (SLit 2)) (SLit 5))) |}]
|};
{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 16;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 14; YP09.c_val := CVal 1 (SLit 1) |}; {| c_off := 7; YP09.c_val := CVal 1 (SLit 2) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |}; {| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 8; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 49;
r_wlo := 0;
r_whi := 49;
r_chunks := [{| c_off := 48; YP09.c_val := CVal 1 (SLit 44) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 240 2060) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 249 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}]
|}; {| r_base := Some 516%nat; r_lo := 58; r_hi := 128; r_wlo := 58; r_whi := 128; r_chunks := [{| c_off := 112; YP09.c_val := CVal 1 (SOff 759 (-1)) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{|
r_base := Some 2%nat;
r_lo := -320;
r_hi := 0;
r_wlo := -320;
r_whi := 0;
r_chunks :=
[{| c_off := -320; YP09.c_val := CVal 8 (SLit 7) |}; {| c_off := -312; YP09.c_val := CVal 8 (SLit 5) |}; {| c_off := -304; YP09.c_val := CVal 8 (SOff 859 0) |}; {| c_off := -296; YP09.c_val := CVal 8 (SOff 814 0) |};
{| c_off := -288; YP09.c_val := CVal 8 (SOff 516 112) |}; {| c_off := -240; YP09.c_val := CVal 8 (SOff 516 80) |}; {| c_off := -272; YP09.c_val := CVal 8 (SOff 10 24) |};
{| c_off := -280; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 40 0)) |}; {| c_off := -248; YP09.c_val := CVal 8 (SOff 815 0) |}; {| c_off := -152; YP09.c_val := CVal 8 (SOff 516 32) |};
{| c_off := -264; YP09.c_val := CVal 8 (SOff 658 0) |}; {| c_off := -216; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 40) (SLit 3)) (SOff 40 0)) |}; {| c_off := -208; YP09.c_val := CVal 8 (SOff 10 40) |};
{| c_off := -192; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -144; YP09.c_val := CVal 8 (SOff 40 0) |}; {| c_off := -160; YP09.c_val := CVal 8 (SOff 11 0) |}; {| c_off := -176; YP09.c_val := CVal 8 (SOff 10 0) |};
{| c_off := -168; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -136; YP09.c_val := CVal 8 (SOff 516 48) |}; {| c_off := -184; YP09.c_val := CVal 8 (SOff 49 0) |}; {| c_off := -200; YP09.c_val := CVal 8 (SOff 11 30) |};
{| c_off := -256; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 30) (SLit 3)) (SOff 40 0)) |}; {| c_off := -224; YP09.c_val := CVal 8 (SOff 11 16) |};
{| c_off := -232; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 40 0)) |}; {| c_off := -128; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
{| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |};
{| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |};
{| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}]
|}; {| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 40 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 55 0) |}] |};
{| r_base := Some 55%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 250%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 2060) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 48;
r_wlo := 40;
r_whi := 44;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 53 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 35 0) |}; {| c_off := 30; YP09.c_val := CVal 2 (SOff 36 0) |}; {| c_off := 32; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 34; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 39 0) |}]
|};
{|
r_base := Some 11%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 43 0) |}; {| c_off := 20; YP09.c_val := CVal 2 (SOff 44 0) |};
{| c_off := 22; YP09.c_val := CVal 2 (SOff 45 0) |}; {| c_off := 24; YP09.c_val := CVal 2 (SOff 46 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 47 0) |}; {| c_off := 28; YP09.c_val := CVal 2 (SOff 48 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 49 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 50 0) |}; {| c_off := 33; YP09.c_val := CVal 1 (SOff 51 0) |}]
|};
{|
r_base := Some 32%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 54 0) |}; {| c_off := 64; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 56 0) |}]
|}]
None
{|
f_atoms :=
[(859%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (711%nat, {| af_lo := 0; af_hi := 8; af_al2 := 0 |}); (529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
(10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |}); (32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (35%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(40%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (42%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(43%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (44%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (45%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(47%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (48%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(51%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (52%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (658%nat, {| af_lo := 0; af_hi := 8; af_al2 := 0 |}); (660%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(710%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |}); (759%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |}); (814%nat, {| af_lo := 4; af_hi := 256; af_al2 := 0 |}); (815%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 40 0), SOff 529 0)]
|}).
Definition ss_LX : sstate := Eval vm_compute in ss_havoc_regs ss_L0X 861 [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition ss_M0X : sstate :=
(mkSS 4108
[SLit 0; SOff 896 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 897 0; SOff 898 0; SOff 899 0; SOff 2 0; SOff 2 (-320); SOff 900 0; SOff 901 0; SOff 902 0; SOff 903 0; SOff 904 0; SOff 905 0; SOff 906 0; SOff 907 0; SOff 529 0;
SOff 859 0; SOff 890 0; SOff 11 20; SOff 11 22; SOff 11 8; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 22) (SLit 3)) (SOff 40 0); SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 40 0);
SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 8) (SLit 3)) (SOff 40 0); SOff 40 0; SOff 908 0; SOff 909 0; SOff 910 0; SOff 911 0]
[{|
r_base := Some 2%nat;
r_lo := -320;
r_hi := -120;
r_wlo := -320;
r_whi := -120;
r_chunks :=
[{| c_off := -320; YP09.c_val := CVal 8 (SLit 7) |}; {| c_off := -312; YP09.c_val := CVal 8 (SLit 5) |}; {| c_off := -304; YP09.c_val := CVal 8 (SOff 859 0) |}; {| c_off := -296; YP09.c_val := CVal 8 (SOff 814 0) |};
{| c_off := -288; YP09.c_val := CVal 8 (SOff 516 112) |}; {| c_off := -240; YP09.c_val := CVal 8 (SOff 516 80) |}; {| c_off := -272; YP09.c_val := CVal 8 (SOff 10 24) |};
{| c_off := -280; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 40 0)) |}; {| c_off := -248; YP09.c_val := CVal 8 (SOff 815 0) |}; {| c_off := -152; YP09.c_val := CVal 8 (SOff 516 32) |};
{| c_off := -264; YP09.c_val := CVal 8 (SOff 658 0) |}; {| c_off := -216; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 40) (SLit 3)) (SOff 40 0)) |}; {| c_off := -208; YP09.c_val := CVal 8 (SOff 10 40) |};
{| c_off := -192; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -144; YP09.c_val := CVal 8 (SOff 40 0) |}; {| c_off := -160; YP09.c_val := CVal 8 (SOff 11 0) |}; {| c_off := -176; YP09.c_val := CVal 8 (SOff 10 0) |};
{| c_off := -168; YP09.c_val := CVal 8 (SOff 516 0) |}; {| c_off := -136; YP09.c_val := CVal 8 (SOff 516 48) |}; {| c_off := -184; YP09.c_val := CVal 8 (SOff 49 0) |}; {| c_off := -200; YP09.c_val := CVal 8 (SOff 11 30) |};
{| c_off := -256; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 30) (SLit 3)) (SOff 40 0)) |}; {| c_off := -224; YP09.c_val := CVal 8 (SOff 11 16) |};
{| c_off := -232; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 40 0)) |}; {| c_off := -128; YP09.c_val := CVal 8 (SOff 516 0) |}]
|};
{|
r_base := Some 516%nat;
r_lo := 49;
r_hi := 58;
r_wlo := 49;
r_whi := 58;
r_chunks :=
[{| c_off := 50; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 47 0) (SLit 8)) |}; {| c_off := 49; YP09.c_val := CVal 1 (SOff 47 0) |}; {| c_off := 52; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 46 0) (SLit 8)) |};
{| c_off := 51; YP09.c_val := CVal 1 (SOff 46 0) |}; {| c_off := 56; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 45 0) (SLit 8)) |}; {| c_off := 55; YP09.c_val := CVal 1 (SOff 45 0) |};
{| c_off := 54; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 44 0) (SLit 8)) |}; {| c_off := 53; YP09.c_val := CVal 1 (SOff 44 0) |};
{| c_off := 57; YP09.c_val := CVal 1 (SAlu ALU_OR (SOff 661 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 43 0) (SLit 2)) (SLit 5))) |}]
|};
{|
r_base := Some 529%nat;
r_lo := 0;
r_hi := 16;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 14; YP09.c_val := CVal 1 (SLit 1) |}; {| c_off := 7; YP09.c_val := CVal 1 (SLit 2) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |}; {| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 8; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}]
|};
{|
r_base := Some 516%nat;
r_lo := 0;
r_hi := 49;
r_wlo := 0;
r_whi := 49;
r_chunks := [{| c_off := 48; YP09.c_val := CVal 1 (SLit 44) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 240 2060) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 249 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}]
|}; {| r_base := Some 516%nat; r_lo := 58; r_hi := 128; r_wlo := 58; r_whi := 128; r_chunks := [{| c_off := 112; YP09.c_val := CVal 1 (SOff 759 (-1)) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
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
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 40 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 55 0) |}] |};
{| r_base := Some 55%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 250%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 2060) |}] |};
{|
r_base := Some 10%nat;
r_lo := 0;
r_hi := 48;
r_wlo := 40;
r_whi := 44;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 53 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |}; {| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |}; {| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 35 0) |}; {| c_off := 30; YP09.c_val := CVal 2 (SOff 36 0) |}; {| c_off := 32; YP09.c_val := CVal 2 (SOff 37 0) |}; {| c_off := 34; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 39 0) |}]
|};
{|
r_base := Some 11%nat;
r_lo := 0;
r_hi := 40;
r_wlo := 0;
r_whi := 0;
r_chunks :=
[{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 16; YP09.c_val := CVal 4 (SOff 43 0) |}; {| c_off := 20; YP09.c_val := CVal 2 (SOff 44 0) |};
{| c_off := 22; YP09.c_val := CVal 2 (SOff 45 0) |}; {| c_off := 24; YP09.c_val := CVal 2 (SOff 46 0) |}; {| c_off := 26; YP09.c_val := CVal 2 (SOff 47 0) |}; {| c_off := 28; YP09.c_val := CVal 2 (SOff 48 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 49 0) |}; {| c_off := 32; YP09.c_val := CVal 1 (SOff 50 0) |}; {| c_off := 33; YP09.c_val := CVal 1 (SOff 51 0) |}]
|};
{|
r_base := Some 32%nat;
r_lo := 0;
r_hi := 96;
r_wlo := 0;
r_whi := 0;
r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 54 0) |}; {| c_off := 64; YP09.c_val := CVal 8 (SOff 52 0) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 56 0) |}]
|}]
None
{|
f_atoms :=
[(859%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (711%nat, {| af_lo := 0; af_hi := 8; af_al2 := 0 |}); (529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
(10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |}); (32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (35%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (37%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |}); (38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(40%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (42%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(43%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (44%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (45%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(47%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (48%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(51%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (52%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (658%nat, {| af_lo := 0; af_hi := 8; af_al2 := 0 |}); (660%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(710%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |}); (759%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |}); (814%nat, {| af_lo := 4; af_hi := 256; af_al2 := 0 |}); (815%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 40 0), SOff 529 0)]
|}).
Definition ss_MX : sstate := Eval vm_compute in ss_havoc_regs ss_M0X 959 [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 28; 29; 30; 31]%nat.
Section c.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Definition INV_LX (B : asyms) : racx -> raxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_L B cx E k ly3 S3 W3 ms3 md3 /\ XC cx /\ XV_FI cx E /\ YO07.flag (c_fattr cx) 2 = true /\
XMET MT XN cx S3 (xm_lzw XN (c_w cx * c_h cx) (rx_idl cx) + 2 * mo_free MT) (xn_lzw XN (c_w cx * c_h cx) (rx_idl cx) + 2 * mo_free MT).
Definition XLZW_M (cx : racx) (xx : raxx) (E : env) (m : word -> option byte) : Prop :=
exists res, ew E 963 = Z_to_bv 64 res /\ (res = 0 \/ res = 5) /\
(res = 0 -> forall bb M, val_mem SEGS m (spZ (c_regs cx) - 120) 8 bb -> val_mem SEGS m (spZ (c_regs cx) - 120 + 8) 4 M ->
0 <= bb < 2 ^ 64 -> 0 <= M < 2 ^ 32 ->
lzw_vokA SEGS (rx_idl cx) (rx_iclen cx) (rx_pix cx (x_IMG xx)) m bb M /\ M <= 2 * (c_w cx * c_h cx) + 16) /\
(res = 5 -> lzw_vnone (rx_idl cx) (rx_iclen cx) (rx_pix cx (x_IMG xx))).
Definition INV_MX (B : asyms) : racx -> raxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_M B cx E k ly3 S3 W3 ms3 md3 /\ XC cx /\ XV_F cx E /\
XLZW_M cx xx E (mrestrict (w_H W3) (ms_mem ms3)) /\ XMET MT XN cx S3 (2 * mo_free MT) (2 * mo_free MT).
End c.
End b.
End a.
