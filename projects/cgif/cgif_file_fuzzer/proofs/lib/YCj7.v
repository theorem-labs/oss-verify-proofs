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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkc YCj4 YC8g YCjr YCj1 YCj0 YCj6 YCiy.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition fl_bef (cx : flcx) (fb : frame_st) (E : env) : Prop :=
nth (c_i cx - 1) (cg_frames (c_s cx)) None = Some fb /\
forall j v, nth_error (frame_vals fb) j = Some v -> ew E (651 + j) = Z_to_bv 64 v.
Lemma fl_bef_havoc : forall cx fb E N vs, (660 <= N)%nat -> fl_bef cx fb E -> fl_bef cx fb (havoc E N vs).
Proof.
intros cx fb E N vs HN [Hfb EB]. split; [exact Hfb|]. intros j v Hj.
assert (Hlt : (j < 9)%nat).
{ destruct (Nat.lt_ge_cases j 9) as [Hl|Hge]; [exact Hl|]. rewrite (proj2 (nth_error_None _ _)) in Hj; [discriminate|]. cbn [frame_vals length]. exact Hge. }
rewrite !ew_havoc_old by lia. exact (EB j v Hj).
Qed.
Definition INV_DIFF (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32 /\ Z.land gen 2 <> 0) /\
ew E 625 = Z_to_bv 64 (fl_npal cx) /\
(exists fb, fl_bef cx fb E).
Definition ra_deads_DIFF : list (bv 5) := [14]%bv.
Definition ss_DIFF_0 : sstate :=
(mkSS 7560
[SLit 0; SOff 512 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 57 0; SOff 11 16; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0); SOff 2 0; SOff 60 0; SOff 12 8; SOff 653 0; SOff 52 0; SAlu ALU_AND (SOff 653 0) (SLit 1);
SAlu ALU_AND (SOff 52 0) (SLit 4); SOff 10 0; SOff 11 0; SOff 12 0; SOff 18 0; SOff 41 0; SOff 625 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 40 0; SOff 11 20; SOff 32 0;
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
[{| c_off := 16; YP09.c_val := CVal 8 (SOff 625 0) |}; {| c_off := 136; YP09.c_val := CVal 8 (SOff 41 0) |}; {| c_off := 168; YP09.c_val := CVal 8 (SOff 51 0) |};
{| c_off := 64; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)) |}; {| c_off := 56; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 4)) |};
{| c_off := 72; YP09.c_val := CVal 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2)))) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 11 20) |};
{| c_off := 88; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0)) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 11 16) |}; {| c_off := 96; YP09.c_val := CVal 8 (SOff 57 0) |};
{| c_off := 120; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 1)) |}; {| c_off := 184; YP09.c_val := CVal 8 (SOff 58 0) |}; {| c_off := 176; YP09.c_val := CVal 8 (SOff 40 0) |};
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
[(12%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (651%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (652%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(653%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (654%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (655%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (656%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(657%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (658%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (659%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(60%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (40%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(42%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(51%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (53%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(54%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (55%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (621%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (625%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_NE; ac_a := SAlu ALU_AND (SExt false 8 (SOff 621 0)) (SLit 2); ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)]
|}).
Definition ss_DIFF : sstate := Eval vm_compute in ss_clear_conds (ss_havoc_regs ss_DIFF_0 681 [14]%nat).
Definition fl_tmpblk (B : asyms) (cx : flcx) (pt n : Z) (ly3 : alayout) (S3 : astate) : Prop :=
(4096 <= pt /\ zone2 pt n) /\ pt + n <= alloc_ceiling /\ pt mod 16 = 0 /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(pt, n)] /\
(forall blc lyq ownq i, In (pt, n) blc -> 0 <= i < n ->
awr_byte TFLUSH_STK (spZ (c_regs cx)) (fl_FP cx) (ablocks B (c_ly cx) (c_S cx)) blc lyq ownq (pt + i)) /\
aftok (fl_FP cx) (ablocks B (c_ly cx) (c_S cx)) (pt, n).
Definition fl_R_deads : list nat := [24; 21; 23; 22; 1; 10; 11; 12; 13; 14; 19; 26; 27; 20]%nat.
Definition fl_R_deads_bv : list (bv 5) := [24; 21; 23; 22; 1; 10; 11; 12; 13; 14; 19; 26; 27; 20]%bv.
Definition ss_R_0 : sstate :=
(mkSS 10648
[SLit 0; SOff 512 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 57 0; SOff 841 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0); SOff 2 0; SOff 60 0; SAlu ALU_AND (SExt false 8 (SOff 621 0)) (SLit 1); SOff 627 0;
SOff 52 0; SOff 624 0; SAlu ALU_AND (SOff 52 0) (SLit 4); SOff 10 0; SOff 11 0; SOff 12 0; SOff 516 0; SOff 41 0; SOff 625 0; SOff 40 0; SLit 0; SOff 41 0; SLit 0; SOff 516 32; SOff 26 0; SOff 40 0; SOff 11 20; SOff 32 0;
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
r_chunks := [{| c_off := 16; YP09.c_val := CVal 8 (SOff 240 6660) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 246 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 528 0) |}]
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
(58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (621%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (625%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_EQ; ac_a := SAlu ALU_AND (SExt false 8 (SOff 621 0)) (SLit 1); ac_b := SLit 0 |}; {| ac_c := BC_EQ; ac_a := SAlu ALU_AND (SExt false 8 (SOff 621 0)) (SLit 2); ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)]
|}).
Definition ss_R : sstate := Eval vm_compute in
ss_clear_conds (ss_set_facts (ss_havoc_regs ss_R_0 843 fl_R_deads)
(f_atoms (ss_facts ss_R_0) ++ [(841%nat, mkAF 0 65535 0); (844%nat, mkAF 1 65535 0); (845%nat, mkAF 1 65535 0); (846%nat, mkAF 0 65535 0)])).
Definition INV_R (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (fl_npal cx) /\
exists pt w h top left tidx,
ew E 843 = Z_to_bv 64 pt /\ ew E 844 = Z_to_bv 64 w /\ ew E 845 = Z_to_bv 64 h /\ ew E 841 = Z_to_bv 64 top /\
ew E 846 = Z_to_bv 64 left /\ ew E 842 = Z_to_bv 64 tidx /\ 0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\ 0 <= tidx < 2 ^ 64 /\
((pt = 0 /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ k <= 2 /\ fl_tmpblk B cx pt (w * h) ly3 S3)).
Definition fl_T0_deads : list nat := [24; 21; 23; 22; 1; 10; 11; 12; 13; 14; 18; 25; 26]%nat.
Definition fl_T0_deads_bv : list (bv 5) := [24; 21; 23; 22; 1; 10; 11; 12; 13; 14; 18; 25; 26]%bv.
Definition ss_T0_0 : sstate :=
(mkSS 9976
[SLit 0; SOff 512 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 57 0; SOff 681 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0); SOff 2 0; SOff 60 0; SAlu ALU_AND (SExt false 8 (SOff 621 0)) (SLit 2); SOff 623 0;
SOff 52 0; SOff 624 0; SAlu ALU_AND (SOff 52 0) (SLit 4); SOff 10 0; SOff 11 0; SOff 12 0; SOff 18 0; SOff 41 0; SOff 625 0; SOff 40 0; SLit 0; SOff 41 0; SLit 0; SOff 25 0; SOff 26 0; SOff 40 0; SOff 11 20; SOff 32 0;
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
[{| c_off := 64; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)) |}; {| c_off := 56; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 4)) |};
{| c_off := 72; YP09.c_val := CVal 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2)))) |}; {| c_off := 80; YP09.c_val := CVal 8 (SOff 11 20) |};
{| c_off := 88; YP09.c_val := CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0)) |}; {| c_off := 24; YP09.c_val := CVal 8 (SOff 11 16) |}; {| c_off := 96; YP09.c_val := CVal 8 (SOff 57 0) |};
{| c_off := 120; YP09.c_val := CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 1)) |}; {| c_off := 184; YP09.c_val := CVal 8 (SOff 58 0) |}; {| c_off := 176; YP09.c_val := CVal 8 (SOff 40 0) |};
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
[(12%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (651%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |}); (652%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(653%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (654%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (655%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (656%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |});
(657%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (658%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (659%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(529%nat, {| af_lo := 2147451392; af_hi := 17594333495296; af_al2 := 2 |}); (528%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 0 |}); (516%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 5 |});
(60%nat, {| af_lo := 70368744177152; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (10%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(11%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |}); (36%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(38%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (39%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (40%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |}); (41%nat, {| af_lo := 1; af_hi := 65535; af_al2 := 0 |});
(42%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (43%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (46%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |});
(48%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (49%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (50%nat, {| af_lo := 0; af_hi := 18446744073709551615; af_al2 := 0 |});
(51%nat, {| af_lo := 4096; af_hi := 140737479966720; af_al2 := 4 |}); (52%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (53%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |});
(54%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (55%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |}); (56%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (57%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |});
(58%nat, {| af_lo := 0; af_hi := 255; af_al2 := 0 |}); (621%nat, {| af_lo := 0; af_hi := 4294967295; af_al2 := 0 |}); (625%nat, {| af_lo := 0; af_hi := 65535; af_al2 := 0 |})];
f_conds := [{| ac_c := BC_EQ; ac_a := SAlu ALU_AND (SExt false 8 (SOff 621 0)) (SLit 2); ac_b := SLit 0 |}];
f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)]
|}).
Definition ss_T0 : sstate := Eval vm_compute in
ss_clear_conds (ss_set_facts (ss_havoc_regs ss_T0_0 682 fl_T0_deads)
(f_atoms (ss_facts ss_T0_0) ++ [(681%nat, mkAF 0 65535 0); (683%nat, mkAF 1 65535 0); (684%nat, mkAF 1 65535 0); (685%nat, mkAF 0 65535 0)])).
Definition INV_T0 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (fl_npal cx) /\
(exists fb, fl_bef cx fb E) /\
exists pt w h top left,
ew E 682 = Z_to_bv 64 pt /\ ew E 683 = Z_to_bv 64 w /\ ew E 684 = Z_to_bv 64 h /\ ew E 681 = Z_to_bv 64 top /\ ew E 685 = Z_to_bv 64 left /\
0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\
((pt = 0 /\ w = cg_W (c_s cx) /\ h = cg_H (c_s cx) /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ k <= 2 /\ fl_tmpblk B cx pt (w * h) ly3 S3)).
Definition chunk_redesc (off : Z) (e : sv) (c : YP09.chunk) : YP09.chunk :=
if Z.eqb (YP09.c_off c) off then match YP09.c_val c with CVal w _ => YP09.mkChunk off (CVal w e) | _ => c end else c.
Definition ss_rechunk_off (s : sstate) (base : nat) (off : Z) (e : sv) : sstate :=
ss_set_mem s (map (fun r => match YP09.r_base r with
| Some b => if Nat.eqb b base then YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(map (chunk_redesc off e) (YP09.r_chunks r)) else r
| None => r end) (ss_mem s)).
Definition fl_R2_deads : list nat := [10; 24; 11]%nat.
Definition fl_R2_deads_bv : list (bv 5) := [10; 24; 11]%bv.
Definition INV_R2 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (fl_npal cx) /\
exists pt w h top left tidx img,
ew E 892 = Z_to_bv 64 pt /\ ew E 844 = Z_to_bv 64 w /\ ew E 845 = Z_to_bv 64 h /\ ew E 841 = Z_to_bv 64 top /\
ew E 846 = Z_to_bv 64 left /\ ew E 842 = Z_to_bv 64 tidx /\ ew E 891 = Z_to_bv 64 img /\ 0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\ 0 <= tidx < 2 ^ 64 /\
((pt = 0 /\ img = fr_img (c_f cx) /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ img = pt /\ k <= 2 /\ fl_tmpblk B cx pt (w * h) ly3 S3)).
Definition fl_R3_deads : list nat := [10; 11]%nat.
Definition fl_R3_deads_bv : list (bv 5) := [10; 11]%bv.
Definition INV_R3 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (fl_npal cx) /\
(exists attr, ew E 901 = Z_to_bv 64 attr /\ 0 <= attr <= 1) /\
exists pt w h top left tidx img,
ew E 892 = Z_to_bv 64 pt /\ ew E 844 = Z_to_bv 64 w /\ ew E 845 = Z_to_bv 64 h /\ ew E 841 = Z_to_bv 64 top /\
ew E 846 = Z_to_bv 64 left /\ ew E 842 = Z_to_bv 64 tidx /\ ew E 891 = Z_to_bv 64 img /\ 0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\ 0 <= tidx < 2 ^ 64 /\
((pt = 0 /\ img = fr_img (c_f cx) /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ img = pt /\ k <= 2 /\ fl_tmpblk B cx pt (w * h) ly3 S3)).
Definition fl_slct (cx : flcx) : Z := if fl_uselct cx then fr_nlp (c_f cx) else 0.
Definition fl_R4_deads : list nat := [10; 11; 12; 13]%nat.
Definition fl_R4_deads_bv : list (bv 5) := [10; 11; 12; 13]%bv.
Definition INV_R4 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (fl_npal cx) /\
(exists attr, ew E 901 = Z_to_bv 64 attr /\ 0 <= attr <= 1) /\ ew E 911 = Z_to_bv 64 (fl_slct cx) /\
exists pt w h top left tidx img,
ew E 892 = Z_to_bv 64 pt /\ ew E 844 = Z_to_bv 64 w /\ ew E 845 = Z_to_bv 64 h /\ ew E 841 = Z_to_bv 64 top /\
ew E 846 = Z_to_bv 64 left /\ ew E 842 = Z_to_bv 64 tidx /\ ew E 891 = Z_to_bv 64 img /\ 0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\ 0 <= tidx < 2 ^ 64 /\
((pt = 0 /\ img = fr_img (c_f cx) /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ img = pt /\ k <= 2 /\ fl_tmpblk B cx pt (w * h) ly3 S3)).
Definition region_filter_offs (keep : list Z) (r : YP09.region) : YP09.region :=
YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(filter (fun c => existsb (Z.eqb (YP09.c_off c)) keep) (YP09.r_chunks r)).
Definition fl_X_mem (m : smem) : smem :=
map (fun r => match YP09.r_base r with
| Some b => if Nat.eqb b 516 then region_filter_offs [0; 8; 16; 120] r
else if Nat.eqb b 60 then region_filter_offs [112] r else r
| None => r end) m.
Definition fl_X_deads : list nat := [19; 1; 5; 6; 7; 10; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Definition fl_X_deads_bv : list (bv 5) := [19; 1; 5; 6; 7; 10; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition INV_X (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= EV_FLUSH /\ (exists r, ew E 961 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64) /\
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)).
Definition INV_R5 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= 2 + EV_RAWADD /\ (exists res, ew E 920 = Z_to_bv 64 res /\ 0 <= res < 2 ^ 64) /\
exists pt, ew E 892 = Z_to_bv 64 pt /\ 0 <= pt < 2 ^ 64 /\
((pt = 0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx))) \/
(pt <> 0 /\ exists n, 0 <= n /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(pt, n)]) /\
aftok (fl_FP cx) (ablocks B (c_ly cx) (c_S cx)) (pt, n))).
End d.
End a.
