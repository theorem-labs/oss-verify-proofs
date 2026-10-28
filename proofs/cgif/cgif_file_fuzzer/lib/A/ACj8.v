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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACkc ACj4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj1 ACj0 ACj6 ACiy ACj7.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition ss_S : sstate := Eval vm_compute in ss_set_pc (ss_havoc_regs ss_DIFF 681 [10; 11]%nat) 6792.
Definition ss_Fv : sstate := Eval vm_compute in ss_set_pc (ss_havoc_regs ss_DIFF 681 [10; 11]%nat) 7480.
Definition fl_dims_deads : list nat := [26; 27; 23; 1; 5; 7; 12; 13; 14; 15; 16; 17; 19; 24; 25; 28; 29; 30; 31]%nat.
Definition fl_dims_deads_bv : list (bv 5) := [26; 27; 23; 1; 5; 7; 12; 13; 14; 15; 16; 17; 19; 24; 25; 28; 29; 30; 31]%bv.
Definition ss_DIMS : sstate := Eval vm_compute in
ss_set_regs (ss_set_pc (ss_havoc_regs ss_DIFF 861 fl_dims_deads) 8076)
[(10%nat, SOff 516 112); (11%nat, SOff 516 128); (6%nat, SOff 32 0)].
Definition INV_DIMS (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\
ew E 625 = Z_to_bv 64 (fl_npal cx) /\
(exists fb, fl_bef cx fb E) /\
exists w h top left, ew E 861 = Z_to_bv 64 w /\ val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 160) 8 h /\ ew E 862 = Z_to_bv 64 top /\ ew E 863 = Z_to_bv 64 left /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx).
Definition ss_DIMSi : sstate := Eval vm_compute in
ss_set_regs (ss_set_pc (ss_havoc_regs ss_DIFF 861 fl_dims_deads) 8076)
[(10%nat, SOff 516 128); (11%nat, SOff 516 112); (6%nat, SOff 32 0);
(26%nat, SLit 1); (27%nat, SLit 0); (23%nat, SLit 0)].
Definition INV_DIMSi (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\
ew E 625 = Z_to_bv 64 (fl_npal cx) /\
(exists fb, fl_bef cx fb E) /\
val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 160) 8 1.
Definition ss_D1_0 : sstate :=
(mkSS 8120
[(SLit 0); (SOff 864 0); (SOff 60 0); (SOff 3 0); (SOff 4 0); (SOff 865 0); (SOff 32 0); (SOff 866 0); (SOff 2 0); (SOff 60 0); (SLit 2); (SOff 516 128); (SLit 1); (SLit 1); (SOff 869 0); (SOff 870 0); (SOff 871 0); (SOff 872 0); (SOff 516 0); (SOff 873 0); (SOff 516 0); (SOff 10 0); (SOff 11 0); (SOff 863 0); (SOff 874 0); (SOff 529 0); (SOff 861 0); (SOff 862 0); (SOff 876 0); (SOff 877 0); (SOff 878 0); (SOff 879 0)]
[YP09.mkRegion (Some 12%nat) 0 40 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 651 0)); YP09.mkChunk 8 (CVal 8 (SOff 652 0)); YP09.mkChunk 16 (CVal 4 (SOff 653 0)); YP09.mkChunk 20 (CVal 4 (SOff 654 0)); YP09.mkChunk 24 (CVal 2 (SOff 655 0)); YP09.mkChunk 26 (CVal 2 (SOff 656 0)); YP09.mkChunk 28 (CVal 1 (SOff 657 0)); YP09.mkChunk 32 (CVal 1 (SOff 658 0)); YP09.mkChunk 33 (CVal 1 (SOff 659 0))];
YP09.mkRegion (Some 529%nat) 0 32 0 0 [YP09.mkChunk 7 (CVal 1 (SLit 0)); YP09.mkChunk 6 (CVal 1 (SLit 0)); YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0)); YP09.mkChunk 17 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 16 (CVal 1 (SLit 2)); YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 14 (CVal 1 (SLit 2)); YP09.mkChunk 19 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 18 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 8 (CVal 1 (SLit 0)); YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 24 (CVal 8 (SLit 0))];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 128 (CVal 2 (SOff 863 0)); YP09.mkChunk 112 (CVal 2 (SOff 862 0)); YP09.mkChunk 16 (CVal 8 (SOff 240 5884)); YP09.mkChunk 8 (CVal 8 (SOff 246 0)); YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 280 0 280 [YP09.mkChunk 160 (CVal 8 (SOff 880 0)); YP09.mkChunk 24 (CVal 8 (SOff 625 0)); YP09.mkChunk 48 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0))); YP09.mkChunk 56 (CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 1))); YP09.mkChunk 64 (CVal 8 (SOff 11 20)); YP09.mkChunk 96 (CVal 8 (SOff 516 0)); YP09.mkChunk 80 (CVal 8 (SOff 529 0)); YP09.mkChunk 104 (CVal 8 (SOff 516 0)); YP09.mkChunk 208 (CVal 8 (SOff 41 0)); YP09.mkChunk 144 (CVal 8 (SOff 516 128)); YP09.mkChunk 176 (CVal 8 (SOff 516 112)); YP09.mkChunk 224 (CVal 8 (SOff 51 0)); YP09.mkChunk 120 (CVal 8 (SOff 11 26)); YP09.mkChunk 72 (CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 4))); YP09.mkChunk 112 (CVal 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))))); YP09.mkChunk 232 (CVal 8 (SOff 58 0)); YP09.mkChunk 136 (CVal 8 (SOff 57 0)); YP09.mkChunk 32 (CVal 8 (SOff 11 16)); YP09.mkChunk 128 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0))); YP09.mkChunk 200 (CVal 8 (SOff 40 0)); YP09.mkChunk 272 (CVal 8 (SOff 516 0)); YP09.mkChunk 240 (CVal 8 (SOff 32 0)); YP09.mkChunk 248 (CVal 8 (SOff 12 0))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 59 0))];
YP09.mkRegion (Some 59%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))];
YP09.mkRegion (Some 10%nat) 0 96 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 40 (CVal 4 (SOff 38 0)); YP09.mkChunk 44 (CVal 4 (SOff 39 0)); YP09.mkChunk 48 (CVal 2 (SOff 40 0)); YP09.mkChunk 50 (CVal 2 (SOff 41 0)); YP09.mkChunk 52 (CVal 2 (SOff 42 0)); YP09.mkChunk 54 (CVal 2 (SOff 43 0)); YP09.mkChunk 56 (CVal 8 (SOff 44 0)); YP09.mkChunk 64 (CVal 8 (SOff 45 0)); YP09.mkChunk 72 (CVal 8 (SOff 46 0)); YP09.mkChunk 80 (CVal 8 (SOff 47 0)); YP09.mkChunk 88 (CVal 4 (SOff 48 0)); YP09.mkChunk 92 (CVal 4 (SOff 49 0))];
YP09.mkRegion (Some 11%nat) 0 40 20 24 [YP09.mkChunk 0 (CVal 8 (SOff 50 0)); YP09.mkChunk 8 (CVal 8 (SOff 51 0)); YP09.mkChunk 16 (CVal 4 (SOff 52 0)); YP09.mkChunk 20 (CVal 4 (SOff 621 0)); YP09.mkChunk 24 (CVal 2 (SOff 54 0)); YP09.mkChunk 26 (CVal 2 (SOff 55 0)); YP09.mkChunk 28 (CVal 1 (SOff 56 0)); YP09.mkChunk 32 (CVal 1 (SOff 57 0)); YP09.mkChunk 33 (CVal 1 (SOff 58 0))]]
None
(mkFacts
[(880%nat, mkAF 1 65535 0); (863%nat, mkAF 0 65535 0); (862%nat, mkAF 0 65535 0); (861%nat, mkAF 1 65535 0); (12%nat, mkAF 4096 140737479966720 4); (651%nat, mkAF 0 18446744073709551615 0); (652%nat, mkAF 4096 140737479966720 4); (653%nat, mkAF 0 4294967295 0); (654%nat, mkAF 0 4294967295 0); (655%nat, mkAF 0 65535 0); (656%nat, mkAF 0 65535 0); (657%nat, mkAF 0 255 0); (658%nat, mkAF 0 255 0); (659%nat, mkAF 0 255 0); (529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (10%nat, mkAF 4096 140737479966720 4); (11%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF 2147450880 2147450880 0); (36%nat, mkAF 0 18446744073709551615 0); (38%nat, mkAF 0 4294967295 0); (39%nat, mkAF 0 4294967295 0); (40%nat, mkAF 1 65535 0); (41%nat, mkAF 1 65535 0); (42%nat, mkAF 0 65535 0); (43%nat, mkAF 0 65535 0); (46%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 4294967295 0); (49%nat, mkAF 0 4294967295 0); (50%nat, mkAF 0 18446744073709551615 0); (51%nat, mkAF 4096 140737479966720 4); (52%nat, mkAF 0 4294967295 0); (53%nat, mkAF 0 4294967295 0); (54%nat, mkAF 0 65535 0); (55%nat, mkAF 0 65535 0); (56%nat, mkAF 0 255 0); (57%nat, mkAF 0 255 0); (58%nat, mkAF 0 255 0); (621%nat, mkAF 0 4294967295 0); (625%nat, mkAF 0 65535 0)]
[]
[((SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0)), (SOff 529 0))])).
Definition fl_D1_deads : list nat := [1; 5; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 24; 28; 29; 30; 31]%nat.
Definition fl_D1_deads_bv : list (bv 5) := [1; 5; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 24; 28; 29; 30; 31]%bv.
Definition ss_D1 : sstate := Eval vm_compute in
ss_set_facts (ss_rechunk_off (ss_rechunk_off (ss_rechunk_off
(ss_set_regs (ss_havoc_regs ss_D1_0 891 fl_D1_deads) [(26%nat, SOff 887 0); (27%nat, SOff 889 0); (23%nat, SOff 890 0)])
516 112 (SOff 889 0)) 516 128 (SOff 890 0)) 60 160 (SOff 888 0))
(f_atoms (ss_facts ss_DIMS) ++ [(887%nat, mkAF 1 65535 0); (888%nat, mkAF 1 65535 0); (889%nat, mkAF 0 65535 0); (890%nat, mkAF 0 65535 0)]).
Definition INV_D1 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\
ew E 625 = Z_to_bv 64 (fl_npal cx) /\
(exists fb, fl_bef cx fb E) /\
exists w h top left, ew E 887 = Z_to_bv 64 w /\ ew E 888 = Z_to_bv 64 h /\ ew E 889 = Z_to_bv 64 top /\ ew E 890 = Z_to_bv 64 left /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx).
End b.
End a.
