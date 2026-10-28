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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACab ACai ACaj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition ra_deads_T0 : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition ra_deads_Tf : list (bv 5) := [1; 5; 6; 7; 19; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31; 21]%bv.
Definition ss_T0 : sstate :=
(mkSS 3512
[SLit 0; SOff 1061 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 1062 0; SOff 1063 0; SOff 1064 0; SOff 2 0; SOff 2 (-320); SOff 1065 0; SOff 1066 0; SOff 1067 0; SOff 1068 0; SOff 1069 0; SOff 1070 0; SOff 1071 0; SOff 1072 0; SOff 516 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 40 0); SOff 529 0; SLit 0; SOff 11 0; SOff 49 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 22) (SLit 3)) (SOff 40 0); SOff 10 40; SOff 516 0; SOff 10 0; SOff 1073 0; SOff 1074 0; SOff 1075 0; SOff 1076 0]
[{| r_base := Some 2%nat; r_lo := -120; r_hi := -104; r_wlo := -120; r_whi := -104; r_chunks := [{| c_off := -120; YP09.c_val := CVal 8 (SOff 1059 0) |};
{| c_off := -112; YP09.c_val := CVal 4 (SOff 1060 0) |}] |};
{| r_base := Some 2%nat; r_lo := -320; r_hi := -120; r_wlo := -320; r_whi := -120; r_chunks := [{| c_off := -176; YP09.c_val := CVal 8 (SOff 516 80) |};
{| c_off := -256; YP09.c_val := CVal 8 (SOff 516 32) |};
{| c_off := -224; YP09.c_val := CVal 8 (SOff 516 48) |};
{| c_off := -216; YP09.c_val := CVal 8 (SOff 516 112) |};
{| c_off := -192; YP09.c_val := CVal 8 (SOff 814 0) |};
{| c_off := -152; YP09.c_val := CVal 8 (SOff 11 0) |};
{| c_off := -184; YP09.c_val := CVal 8 (SOff 815 0) |};
{| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 40) (SLit 3)) (SOff 40 0)) |};
{| c_off := -208; YP09.c_val := CVal 8 (SOff 10 24) |};
{| c_off := -232; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 40 0)) |};
{| c_off := -264; YP09.c_val := CVal 8 (SOff 662 0) |};
{| c_off := -160; YP09.c_val := CVal 8 (SOff 11 30) |};
{| c_off := -248; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 30) (SLit 3)) (SOff 40 0)) |};
{| c_off := -200; YP09.c_val := CVal 8 (SOff 11 16) |};
{| c_off := -168; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 40 0)) |};
{| c_off := -136; YP09.c_val := CVal 8 (SOff 40 0) |};
{| c_off := -128; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := -320; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 516%nat; r_lo := 49; r_hi := 58; r_wlo := 49; r_whi := 58; r_chunks := [{| c_off := 52; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 46 0) (SLit 8)) |};
{| c_off := 51; YP09.c_val := CVal 1 (SOff 46 0) |};
{| c_off := 50; YP09.c_val := CVal 1 (SAlu ALU_SRL (SExt true 16 (SOff 47 0)) (SLit 8)) |};
{| c_off := 49; YP09.c_val := CVal 1 (SExt true 16 (SOff 47 0)) |};
{| c_off := 56; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 45 0) (SLit 8)) |};
{| c_off := 55; YP09.c_val := CVal 1 (SOff 45 0) |};
{| c_off := 54; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 44 0) (SLit 8)) |};
{| c_off := 53; YP09.c_val := CVal 1 (SOff 44 0) |};
{| c_off := 57; YP09.c_val := CVal 1 (SAlu ALU_OR (SOff 661 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 43 0) (SLit 2)) (SLit 5))) |}] |};
{| r_base := Some 529%nat; r_lo := 0; r_hi := 16; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 14; YP09.c_val := CVal 1 (SLit 1) |};
{| c_off := 7; YP09.c_val := CVal 1 (SLit 2) |};
{| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 10; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}] |};
{| r_base := Some 516%nat; r_lo := 0; r_hi := 49; r_wlo := 0; r_whi := 49; r_chunks := [{| c_off := 48; YP09.c_val := CVal 1 (SLit 44) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 240 1820) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 249 0) |};
{| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}] |};
{| r_base := Some 516%nat; r_lo := 58; r_hi := 128; r_wlo := 58; r_whi := 128; r_chunks := [{| c_off := 112; YP09.c_val := CVal 1 (SAlu ALU_ADD (SAlu ALU_AND (SOff 759 0) (SLit 255)) (SLit (-1))) |};
{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{| r_base := Some 2%nat; r_lo := -104; r_hi := 0; r_wlo := -104; r_whi := 0; r_chunks := [{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
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
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}] |};
{| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 40 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 55 0) |}] |};
{| r_base := Some 55%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 250%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 1820) |}] |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 48; r_wlo := 40; r_whi := 44; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 53 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 35 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 2 (SOff 37 0) |};
{| c_off := 34; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 39 0) |}] |};
{| r_base := Some 11%nat; r_lo := 0; r_hi := 40; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |};
{| c_off := 16; YP09.c_val := CVal 4 (SOff 43 0) |};
{| c_off := 20; YP09.c_val := CVal 2 (SOff 44 0) |};
{| c_off := 22; YP09.c_val := CVal 2 (SOff 45 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 46 0) |};
{| c_off := 26; YP09.c_val := CVal 2 (SOff 47 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 48 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 49 0) |};
{| c_off := 32; YP09.c_val := CVal 1 (SOff 50 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 51 0) |}] |};
{| r_base := Some 32%nat; r_lo := 0; r_hi := 96; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 54 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 52 0) |};
{| c_off := 80; YP09.c_val := CVal 8 (SLit 0) |}] |}]
None
{| f_atoms := [(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
(516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
(10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
(32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(35%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(37%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(40%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(42%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(43%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(44%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(45%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(46%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(47%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(48%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(49%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(50%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(51%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(52%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(660%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(662%nat, {| af_lo := 0; af_hi := 8; af_al2 := 0 |});
(710%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(759%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |});
(814%nat, {| af_lo := 4; af_hi := 256; af_al2 := 0 |});
(815%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 40 0), SOff 529 0)] |}).
Definition ss_Tf : sstate :=
(mkSS 3512
[SLit 0; SOff 1061 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 1062 0; SOff 1063 0; SOff 1064 0; SOff 2 0; SOff 2 (-320); SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 40) (SLit 3)) (SOff 40 0); SOff 1066 0; SOff 1067 0; SOff 1068 0; SOff 1069 0; SOff 1070 0; SOff 1071 0; SOff 1072 0; SOff 516 0; SOff 1065 0; SOff 529 0; SOff 1077 0; SOff 11 0; SOff 49 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 22) (SLit 3)) (SOff 40 0); SOff 10 40; SOff 516 0; SOff 10 0; SOff 1073 0; SOff 1074 0; SOff 1075 0; SOff 1076 0]
[{| r_base := Some 2%nat; r_lo := -320; r_hi := -120; r_wlo := -320; r_whi := -120; r_chunks := [{| c_off := -176; YP09.c_val := CVal 8 (SOff 516 80) |};
{| c_off := -256; YP09.c_val := CVal 8 (SOff 516 32) |};
{| c_off := -224; YP09.c_val := CVal 8 (SOff 516 48) |};
{| c_off := -216; YP09.c_val := CVal 8 (SOff 516 112) |};
{| c_off := -192; YP09.c_val := CVal 8 (SOff 814 0) |};
{| c_off := -152; YP09.c_val := CVal 8 (SOff 11 0) |};
{| c_off := -184; YP09.c_val := CVal 8 (SOff 815 0) |};
{| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 40) (SLit 3)) (SOff 40 0)) |};
{| c_off := -208; YP09.c_val := CVal 8 (SOff 10 24) |};
{| c_off := -232; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 40 0)) |};
{| c_off := -264; YP09.c_val := CVal 8 (SOff 662 0) |};
{| c_off := -160; YP09.c_val := CVal 8 (SOff 11 30) |};
{| c_off := -248; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 30) (SLit 3)) (SOff 40 0)) |};
{| c_off := -200; YP09.c_val := CVal 8 (SOff 11 16) |};
{| c_off := -168; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 40 0)) |};
{| c_off := -136; YP09.c_val := CVal 8 (SOff 40 0) |};
{| c_off := -128; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := -320; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 516%nat; r_lo := 49; r_hi := 58; r_wlo := 49; r_whi := 58; r_chunks := [{| c_off := 52; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 46 0) (SLit 8)) |};
{| c_off := 51; YP09.c_val := CVal 1 (SOff 46 0) |};
{| c_off := 50; YP09.c_val := CVal 1 (SAlu ALU_SRL (SExt true 16 (SOff 47 0)) (SLit 8)) |};
{| c_off := 49; YP09.c_val := CVal 1 (SExt true 16 (SOff 47 0)) |};
{| c_off := 56; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 45 0) (SLit 8)) |};
{| c_off := 55; YP09.c_val := CVal 1 (SOff 45 0) |};
{| c_off := 54; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 44 0) (SLit 8)) |};
{| c_off := 53; YP09.c_val := CVal 1 (SOff 44 0) |};
{| c_off := 57; YP09.c_val := CVal 1 (SAlu ALU_OR (SOff 661 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 43 0) (SLit 2)) (SLit 5))) |}] |};
{| r_base := Some 529%nat; r_lo := 0; r_hi := 16; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 14; YP09.c_val := CVal 1 (SLit 1) |};
{| c_off := 7; YP09.c_val := CVal 1 (SLit 2) |};
{| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 10; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}] |};
{| r_base := Some 516%nat; r_lo := 0; r_hi := 49; r_wlo := 0; r_whi := 49; r_chunks := [{| c_off := 48; YP09.c_val := CVal 1 (SLit 44) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 240 1820) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 249 0) |};
{| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}] |};
{| r_base := Some 516%nat; r_lo := 58; r_hi := 128; r_wlo := 58; r_whi := 128; r_chunks := [{| c_off := 112; YP09.c_val := CVal 1 (SAlu ALU_ADD (SAlu ALU_AND (SOff 759 0) (SLit 255)) (SLit (-1))) |};
{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{| r_base := Some 2%nat; r_lo := -104; r_hi := 0; r_wlo := -104; r_whi := 0; r_chunks := [{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
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
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}] |};
{| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 40 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 55 0) |}] |};
{| r_base := Some 55%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 250%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 1820) |}] |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 48; r_wlo := 40; r_whi := 44; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 53 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 35 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 2 (SOff 37 0) |};
{| c_off := 34; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 39 0) |}] |};
{| r_base := Some 11%nat; r_lo := 0; r_hi := 40; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |};
{| c_off := 16; YP09.c_val := CVal 4 (SOff 43 0) |};
{| c_off := 20; YP09.c_val := CVal 2 (SOff 44 0) |};
{| c_off := 22; YP09.c_val := CVal 2 (SOff 45 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 46 0) |};
{| c_off := 26; YP09.c_val := CVal 2 (SOff 47 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 48 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 49 0) |};
{| c_off := 32; YP09.c_val := CVal 1 (SOff 50 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 51 0) |}] |};
{| r_base := Some 32%nat; r_lo := 0; r_hi := 96; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 54 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 52 0) |};
{| c_off := 80; YP09.c_val := CVal 8 (SLit 0) |}] |}]
None
{| f_atoms := [(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
(516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
(10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
(32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(35%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(37%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(40%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(42%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(43%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(44%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(45%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(46%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(47%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(48%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(49%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(50%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(51%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(52%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(660%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(662%nat, {| af_lo := 0; af_hi := 8; af_al2 := 0 |});
(710%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(759%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |});
(814%nat, {| af_lo := 4; af_hi := 256; af_al2 := 0 |});
(815%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |});
(1077%nat, {| af_lo := 2; af_hi := 5; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 40 0), SOff 529 0)] |}).
Definition INV_T0 (B : asyms) : racx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= 22 /\
(exists K1, ew E 662 = Z_to_bv 64 K1 /\ 0 <= K1 <= 8 /\ (c_slct cx <> 0 -> 1 <= K1 /\ c_slct cx <= 2 ^ K1)) /\
exists bb Lbb M, ew E 1059 = Z_to_bv 64 bb /\ ew E 1060 = Z_to_bv 64 (M mod 2 ^ 32) /\
Permutation (ablocks B ly3 S3) ((bb, Lbb) :: ablocks B (c_ly cx) (c_S cx)) /\ 4096 <= bb /\ 1 <= M <= Lbb /\
(forall blc i, In (bb, Lbb) blc -> 0 <= i < Lbb ->
awr_byte TRAWADD_STK (spZ (c_regs cx)) [(c_raw cx + 40, c_raw cx + 44)] (ablocks B (c_ly cx) (c_S cx)) blc ly3 [(1, c_fpos cx)] (bb + i)) /\
aftok [(c_raw cx + 40, c_raw cx + 44)] (ablocks B (c_ly cx) (c_S cx)) (bb, Lbb).
Definition INV_Tf (B : asyms) : racx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= 22 /\
(exists K1, ew E 662 = Z_to_bv 64 K1 /\ 0 <= K1 <= 8 /\ (c_slct cx <> 0 -> 1 <= K1 /\ c_slct cx <= 2 ^ K1)) /\
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)).
Definition ra_deads_G2 : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 15; 16; 17; 24; 28; 29; 30; 31]%bv.
Definition ss_G2 : sstate :=
(mkSS 3796
[SLit 0; SOff 1159 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 1160 0; SOff 1161 0; SOff 1162 0; SOff 2 0; SOff 2 (-320); SOff 1163 0; SOff 1164 0; SOff 1165 0; SOff 1166 0; SOff 516 48; SOff 1167 0; SOff 1168 0; SOff 1169 0; SOff 516 0; SAlu ALU_SRL (SOff 10 0) (SLit 3); SOff 529 0; SOff 10 8; SLit 0; SOff 49 0; SOff 1170 0; SOff 10 40; SOff 516 0; SOff 10 0; SOff 1171 0; SOff 1172 0; SOff 1173 0; SOff 1174 0]
[{| r_base := Some 2%nat; r_lo := -120; r_hi := -104; r_wlo := -120; r_whi := -104; r_chunks := [{| c_off := -120; YP09.c_val := CVal 8 (SOff 1059 0) |};
{| c_off := -112; YP09.c_val := CVal 4 (SOff 1060 0) |}] |};
{| r_base := Some 2%nat; r_lo := -320; r_hi := -120; r_wlo := -320; r_whi := -120; r_chunks := [{| c_off := -240; YP09.c_val := CVal 8 (SOff 10 40) |};
{| c_off := -176; YP09.c_val := CVal 8 (SOff 516 80) |};
{| c_off := -256; YP09.c_val := CVal 8 (SOff 516 32) |};
{| c_off := -224; YP09.c_val := CVal 8 (SOff 516 48) |};
{| c_off := -216; YP09.c_val := CVal 8 (SOff 516 112) |};
{| c_off := -192; YP09.c_val := CVal 8 (SOff 814 0) |};
{| c_off := -152; YP09.c_val := CVal 8 (SOff 11 0) |};
{| c_off := -184; YP09.c_val := CVal 8 (SOff 815 0) |};
{| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 40) (SLit 3)) (SOff 40 0)) |};
{| c_off := -208; YP09.c_val := CVal 8 (SOff 10 24) |};
{| c_off := -232; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 40 0)) |};
{| c_off := -264; YP09.c_val := CVal 8 (SOff 662 0) |};
{| c_off := -160; YP09.c_val := CVal 8 (SOff 11 30) |};
{| c_off := -248; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 30) (SLit 3)) (SOff 40 0)) |};
{| c_off := -200; YP09.c_val := CVal 8 (SOff 11 16) |};
{| c_off := -168; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 40 0)) |};
{| c_off := -136; YP09.c_val := CVal 8 (SOff 40 0) |};
{| c_off := -128; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := -320; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 516%nat; r_lo := 49; r_hi := 58; r_wlo := 49; r_whi := 58; r_chunks := [{| c_off := 52; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 46 0) (SLit 8)) |};
{| c_off := 51; YP09.c_val := CVal 1 (SOff 46 0) |};
{| c_off := 50; YP09.c_val := CVal 1 (SAlu ALU_SRL (SExt true 16 (SOff 47 0)) (SLit 8)) |};
{| c_off := 49; YP09.c_val := CVal 1 (SExt true 16 (SOff 47 0)) |};
{| c_off := 56; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 45 0) (SLit 8)) |};
{| c_off := 55; YP09.c_val := CVal 1 (SOff 45 0) |};
{| c_off := 54; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 44 0) (SLit 8)) |};
{| c_off := 53; YP09.c_val := CVal 1 (SOff 44 0) |};
{| c_off := 57; YP09.c_val := CVal 1 (SAlu ALU_OR (SOff 661 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 43 0) (SLit 2)) (SLit 5))) |}] |};
{| r_base := Some 529%nat; r_lo := 0; r_hi := 16; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 14; YP09.c_val := CVal 1 (SLit 1) |};
{| c_off := 7; YP09.c_val := CVal 1 (SLit 2) |};
{| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 10; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}] |};
{| r_base := Some 516%nat; r_lo := 0; r_hi := 49; r_wlo := 0; r_whi := 49; r_chunks := [{| c_off := 48; YP09.c_val := CVal 1 (SLit 44) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 240 1820) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 249 0) |};
{| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}] |};
{| r_base := Some 516%nat; r_lo := 58; r_hi := 128; r_wlo := 58; r_whi := 128; r_chunks := [{| c_off := 112; YP09.c_val := CVal 1 (SAlu ALU_ADD (SAlu ALU_AND (SOff 759 0) (SLit 255)) (SLit (-1))) |};
{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{| r_base := Some 2%nat; r_lo := -104; r_hi := 0; r_wlo := -104; r_whi := 0; r_chunks := [{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
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
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}] |};
{| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 40 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 55 0) |}] |};
{| r_base := Some 55%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 250%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 1820) |}] |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 48; r_wlo := 40; r_whi := 44; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 53 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 35 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 2 (SOff 37 0) |};
{| c_off := 34; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 39 0) |}] |};
{| r_base := Some 11%nat; r_lo := 0; r_hi := 40; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |};
{| c_off := 16; YP09.c_val := CVal 4 (SOff 43 0) |};
{| c_off := 20; YP09.c_val := CVal 2 (SOff 44 0) |};
{| c_off := 22; YP09.c_val := CVal 2 (SOff 45 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 46 0) |};
{| c_off := 26; YP09.c_val := CVal 2 (SOff 47 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 48 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 49 0) |};
{| c_off := 32; YP09.c_val := CVal 1 (SOff 50 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 51 0) |}] |};
{| r_base := Some 32%nat; r_lo := 0; r_hi := 96; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 54 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 52 0) |};
{| c_off := 80; YP09.c_val := CVal 8 (SLit 0) |}] |}]
None
{| f_atoms := [(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
(516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
(10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
(32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(35%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(37%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(40%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(42%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(43%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(44%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(45%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(46%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(47%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(48%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(49%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(50%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(51%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(52%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(660%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(662%nat, {| af_lo := 0; af_hi := 8; af_al2 := 0 |});
(710%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(759%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |});
(814%nat, {| af_lo := 4; af_hi := 256; af_al2 := 0 |});
(815%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 40 0), SOff 529 0)] |}).
End b.
End a.
Lemma ra_k1_cases : forall K, 1 <= K <= 8 -> K = 1 \/ K = 2 \/ K = 3 \/ K = 4 \/ K = 5 \/ K = 6 \/ K = 7 \/ K = 8.
Proof. intros K HK. lia. Qed.
Lemma denot_ra_pow : forall E k K, ew E k = Z_to_bv 64 K -> 1 <= K <= 8 ->
sv_denot E (SAluw ALU_SLL (SLit 1) (SOff k 0)) = Z_to_bv 64 (2 ^ K).
Proof.
intros E k K HK Hr. cbn [sv_denot]. rewrite HK. apply bv_eq.
destruct (ra_k1_cases K Hr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma denot_ra_pow_mask : forall E k K, ew E k = Z_to_bv 64 K -> 1 <= K <= 8 ->
sv_denot E (SAlu ALU_AND (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SLit 65535)) = Z_to_bv 64 (2 ^ K).
Proof.
intros E k K HK Hr. cbn [sv_denot]. rewrite HK. apply bv_eq.
destruct (ra_k1_cases K Hr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma U_ra_ndummy : forall E k ks K sg, ew E k = Z_to_bv 64 K -> 1 <= K <= 8 -> ew E ks = Z_to_bv 64 sg -> 1 <= sg < 2 ^ K ->
U E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLL (SAlu ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0)) (SLit 1))
(SAlu ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0))) (SLit 65535))
= 3 * (2 ^ K - sg).
Proof.
intros E k ks K sg HK Hr Hs Hsg.
assert (Hp : 2 <= 2 ^ K <= 256).
{ destruct (ra_k1_cases K Hr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; cbn; lia. }
assert (P : U E (SAluw ALU_SLL (SLit 1) (SOff k 0)) = 2 ^ K).
{ unfold U. rewrite (denot_ra_pow E k K HK Hr). apply unsigned_lit_small. lia. }
assert (Q : U E (SOff ks 0) = sg) by (apply U_atom; [exact Hs | lia]).
set (p := 2 ^ K) in *.
assert (D : U E (SAlu ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0)) = p - sg).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite P, Q. apply zcanon_id. rewrite M64_val. lia. }
assert (D2 : U E (SAlu ALU_SLL (SAlu ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0)) (SLit 1)) = 2 * (p - sg)).
{ apply (U_sll1_small E); [exact D | lia | lia]. }
assert (D3 : U E (SAlu ALU_ADD (SAlu ALU_SLL (SAlu ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0)) (SLit 1))
(SAlu ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0))) = 3 * (p - sg)).
{ rewrite (U_add_small E _ _ _ _ D2 D); lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite D3, U_SLit. change (zcanon 65535) with (Z.ones 16).
rewrite Z.land_ones_low; [apply zcanon_id; rewrite M64_val; lia | lia |].
apply (Z.le_lt_trans _ (Z.log2 1024)); [apply Z.log2_le_mono; lia | cbn; lia].
Qed.
Lemma U_ra_ndummy_b : forall E k ks K sg, ew E k = Z_to_bv 64 K -> 1 <= K <= 8 -> ew E ks = Z_to_bv 64 sg -> 1 <= sg <= 2 ^ K ->
U E (SAlu ALU_ADD (SAlu ALU_SLL (SAluw ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0)) (SLit 1))
(SAluw ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0))) = 3 * (2 ^ K - sg)
/\ U E (SAluw ALU_ADD (SAlu ALU_SLL (SAluw ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0)) (SLit 1))
(SAluw ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0))) = 3 * (2 ^ K - sg)
/\ U E (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_SLL (SAluw ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0)) (SLit 1))
(SAluw ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0))) (SLit 48)) (SLit 48))
= 3 * (2 ^ K - sg).
Proof.
intros E k ks K sg HK Hr Hs Hsg.
assert (Hp : 2 <= 2 ^ K <= 256).
{ destruct (ra_k1_cases K Hr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; cbn; lia. }
assert (P : U E (SAluw ALU_SLL (SLit 1) (SOff k 0)) = 2 ^ K).
{ unfold U. rewrite (denot_ra_pow E k K HK Hr). apply unsigned_lit_small. lia. }
assert (Q : U E (SOff ks 0) = sg) by (apply U_atom; [exact Hs | lia]).
set (p := 2 ^ K) in *.
set (x := SAluw ALU_SUB (SAluw ALU_SLL (SLit 1) (SOff k 0)) (SOff ks 0)).
assert (D : U E x = p - sg).
{ subst x. rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw]. fold (U E (SAluw ALU_SLL (SLit 1) (SOff k 0))). fold (U E (SOff ks 0)).
rewrite P, Q. rewrite (Z.mod_small p), (Z.mod_small sg) by lia. rewrite swrap32_small by lia. apply wrap64_small. lia. }
assert (D2 : U E (SAlu ALU_SLL x (SLit 1)) = 2 * (p - sg)) by (apply (U_sll1_small E); [exact D | lia | lia]).
assert (D3 : U E (SAlu ALU_ADD (SAlu ALU_SLL x (SLit 1)) x) = 3 * (p - sg)) by (rewrite (U_add_small E _ _ _ _ D2 D); lia).
split; [exact D3|]. split; [rewrite (U_addw_small E _ _ _ _ D2 D); lia|].
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite D3, !U_SLit. change (Z.land (zcanon 48) 63) with 48.
rewrite Z.shiftl_mul_pow2 by lia. rewrite (zcanon_id (3 * (p - sg) * 2 ^ 48)) by (rewrite M64_val; split; [lia|]; change (2 ^ 64) with (2 ^ 16 * 2 ^ 48); nia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Definition ra_deads_G3 : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 27; 28; 29; 30; 31]%bv.
Definition ss_G3 : sstate :=
(mkSS 4140
[SLit 0; SOff 1209 0; SOff 2 (-320); SOff 3 0; SOff 4 0; SOff 1210 0; SOff 1211 0; SOff 1212 0; SOff 2 0; SOff 2 (-320); SOff 1213 0; SOff 1214 0; SOff 1215 0; SOff 1216 0; SOff 1217 0; SOff 1218 0; SOff 1219 0; SOff 1220 0; SOff 516 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 40 0); SOff 529 0; SOff 10 8; SOff 10 0; SOff 1221 0; SLit 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 40 0); SOff 516 0; SOff 1222 0; SOff 1223 0; SOff 1224 0; SOff 1225 0; SOff 1226 0]
[{| r_base := Some 2%nat; r_lo := -120; r_hi := -104; r_wlo := -120; r_whi := -104; r_chunks := [{| c_off := -120; YP09.c_val := CVal 8 (SOff 1059 0) |};
{| c_off := -112; YP09.c_val := CVal 4 (SOff 1060 0) |}] |};
{| r_base := Some 2%nat; r_lo := -320; r_hi := -120; r_wlo := -320; r_whi := -120; r_chunks := [{| c_off := -240; YP09.c_val := CVal 8 (SOff 10 40) |};
{| c_off := -176; YP09.c_val := CVal 8 (SOff 516 80) |};
{| c_off := -256; YP09.c_val := CVal 8 (SOff 516 32) |};
{| c_off := -224; YP09.c_val := CVal 8 (SOff 516 48) |};
{| c_off := -216; YP09.c_val := CVal 8 (SOff 516 112) |};
{| c_off := -192; YP09.c_val := CVal 8 (SOff 814 0) |};
{| c_off := -184; YP09.c_val := CVal 8 (SOff 815 0) |};
{| c_off := -144; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 40) (SLit 3)) (SOff 40 0)) |};
{| c_off := -208; YP09.c_val := CVal 8 (SOff 10 24) |};
{| c_off := -232; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 24) (SLit 3)) (SOff 40 0)) |};
{| c_off := -264; YP09.c_val := CVal 8 (SOff 662 0) |};
{| c_off := -160; YP09.c_val := CVal 8 (SOff 11 30) |};
{| c_off := -248; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 30) (SLit 3)) (SOff 40 0)) |};
{| c_off := -200; YP09.c_val := CVal 8 (SOff 11 16) |};
{| c_off := -168; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 40 0)) |};
{| c_off := -128; YP09.c_val := CVal 8 (SOff 516 0) |};
{| c_off := -320; YP09.c_val := CVal 8 (SLit 0) |}] |};
{| r_base := Some 516%nat; r_lo := 49; r_hi := 58; r_wlo := 49; r_whi := 58; r_chunks := [{| c_off := 52; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 46 0) (SLit 8)) |};
{| c_off := 51; YP09.c_val := CVal 1 (SOff 46 0) |};
{| c_off := 50; YP09.c_val := CVal 1 (SAlu ALU_SRL (SExt true 16 (SOff 47 0)) (SLit 8)) |};
{| c_off := 49; YP09.c_val := CVal 1 (SExt true 16 (SOff 47 0)) |};
{| c_off := 56; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 45 0) (SLit 8)) |};
{| c_off := 55; YP09.c_val := CVal 1 (SOff 45 0) |};
{| c_off := 54; YP09.c_val := CVal 1 (SAlu ALU_SRL (SOff 44 0) (SLit 8)) |};
{| c_off := 53; YP09.c_val := CVal 1 (SOff 44 0) |};
{| c_off := 57; YP09.c_val := CVal 1 (SAlu ALU_OR (SOff 661 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 43 0) (SLit 2)) (SLit 5))) |}] |};
{| r_base := Some 529%nat; r_lo := 0; r_hi := 16; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 14; YP09.c_val := CVal 1 (SLit 1) |};
{| c_off := 7; YP09.c_val := CVal 1 (SLit 2) |};
{| c_off := 6; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |};
{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 10; YP09.c_val := CVal 1 (SLit 0) |};
{| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 8; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 15; YP09.c_val := CVal 1 (SLit 18446744073709551603) |};
{| c_off := 13; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 12; YP09.c_val := CVal 1 (SLit 18446744073709551602) |};
{| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |};
{| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}] |};
{| r_base := Some 516%nat; r_lo := 0; r_hi := 49; r_wlo := 0; r_whi := 49; r_chunks := [{| c_off := 48; YP09.c_val := CVal 1 (SLit 44) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 240 1820) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 249 0) |};
{| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}] |};
{| r_base := Some 516%nat; r_lo := 58; r_hi := 128; r_wlo := 58; r_whi := 128; r_chunks := [{| c_off := 112; YP09.c_val := CVal 1 (SAlu ALU_ADD (SAlu ALU_AND (SOff 759 0) (SLit 255)) (SLit (-1))) |};
{| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}] |};
{| r_base := Some 2%nat; r_lo := -104; r_hi := 0; r_wlo := -104; r_whi := 0; r_chunks := [{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |};
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
{| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}] |};
{| r_base := Some 241%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 253 0) |}] |};
{| r_base := Some 253%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 40 0) |}] |};
{| r_base := Some 242%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 55 0) |}] |};
{| r_base := Some 55%nat; r_lo := 0; r_hi := 4; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 4 (SLit 1) |}] |};
{| r_base := Some 250%nat; r_lo := 0; r_hi := 8; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 240 1820) |}] |};
{| r_base := Some 10%nat; r_lo := 0; r_hi := 48; r_wlo := 40; r_whi := 44; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 53 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 32 0) |};
{| c_off := 16; YP09.c_val := CVal 8 (SOff 33 0) |};
{| c_off := 24; YP09.c_val := CVal 4 (SOff 34 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 35 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 36 0) |};
{| c_off := 32; YP09.c_val := CVal 2 (SOff 37 0) |};
{| c_off := 34; YP09.c_val := CVal 2 (SOff 38 0) |};
{| c_off := 40; YP09.c_val := CVal 4 (SOff 39 0) |}] |};
{| r_base := Some 11%nat; r_lo := 0; r_hi := 40; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 0; YP09.c_val := CVal 8 (SOff 41 0) |};
{| c_off := 8; YP09.c_val := CVal 8 (SOff 42 0) |};
{| c_off := 16; YP09.c_val := CVal 4 (SOff 43 0) |};
{| c_off := 20; YP09.c_val := CVal 2 (SOff 44 0) |};
{| c_off := 22; YP09.c_val := CVal 2 (SOff 45 0) |};
{| c_off := 24; YP09.c_val := CVal 2 (SOff 46 0) |};
{| c_off := 26; YP09.c_val := CVal 2 (SOff 47 0) |};
{| c_off := 28; YP09.c_val := CVal 2 (SOff 48 0) |};
{| c_off := 30; YP09.c_val := CVal 2 (SOff 49 0) |};
{| c_off := 32; YP09.c_val := CVal 1 (SOff 50 0) |};
{| c_off := 33; YP09.c_val := CVal 1 (SOff 51 0) |}] |};
{| r_base := Some 32%nat; r_lo := 0; r_hi := 96; r_wlo := 0; r_whi := 0; r_chunks := [{| c_off := 56; YP09.c_val := CVal 8 (SOff 54 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SOff 52 0) |};
{| c_off := 80; YP09.c_val := CVal 8 (SLit 0) |}] |}]
None
{| f_atoms := [(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |});
(528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |});
(516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |});
(10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 3 |});
(32%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(33%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(34%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(35%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(36%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(37%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(40%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |});
(41%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(42%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(43%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(44%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(45%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(46%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(47%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(48%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(49%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(50%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(51%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(52%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(660%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(662%nat, {| af_lo := 0; af_hi := 8; af_al2 := 0 |});
(710%nat, {| af_lo := 0; af_hi := 256; af_al2 := 0 |});
(759%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |});
(814%nat, {| af_lo := 4; af_hi := 256; af_al2 := 0 |});
(815%nat, {| af_lo := 3; af_hi := 9; af_al2 := 0 |})];
f_conds := [];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 40 0), SOff 529 0)] |}).
Ltac solve_INV_T0 Hk EK HK1r HK1s E1059 E1060 HPerm Hbb HM Abb Tbb :=
split; [first [exact Hk | lia] |];
split; [eexists; split; [rewrite ?ew_havoc_old by (clear; lia); exact EK | split; [exact HK1r | exact HK1s]] |];
eexists; eexists; eexists; split; [rewrite ?ew_havoc_old by (clear; lia); exact E1059|]; split; [rewrite ?ew_havoc_old by (clear; lia); exact E1060|];
split; [exact HPerm|]; split; [exact Hbb|]; split; [exact HM|]; split; [exact Abb | exact Tbb].
