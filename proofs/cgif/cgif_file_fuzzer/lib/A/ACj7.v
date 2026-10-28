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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjr ACj1 ACj0 ACj6 ACiy.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
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
Definition ra_deads_DIFF : list (bv 5) := []%bv.
Definition ss_DIFF_0 : sstate :=
(mkSS 6772
[(SLit 0); (SOff 512 0); (SOff 60 0); (SOff 3 0); (SOff 4 0); (SOff 513 0); (SOff 32 0); (SOff 515 0); (SOff 2 0); (SOff 60 0); (SOff 653 0); (SAlu ALU_AND (SOff 653 0) (SLit 1)); (SOff 52 0); (SOff 516 128); (SOff 625 0); (SOff 41 0); (SLit 18446744073709551602); (SOff 523 0); (SOff 516 0); (SOff 11 20); (SOff 516 0); (SOff 10 0); (SOff 11 0); (SOff 23 0); (SAlu ALU_AND (SOff 52 0) (SLit 1)); (SOff 529 0); (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)); (SOff 27 0); (SOff 524 0); (SOff 525 0); (SOff 526 0); (SOff 527 0)]
[YP09.mkRegion (Some 12%nat) 0 40 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 651 0)); YP09.mkChunk 8 (CVal 8 (SOff 652 0)); YP09.mkChunk 16 (CVal 4 (SOff 653 0)); YP09.mkChunk 20 (CVal 4 (SOff 654 0)); YP09.mkChunk 24 (CVal 2 (SOff 655 0)); YP09.mkChunk 26 (CVal 2 (SOff 656 0)); YP09.mkChunk 28 (CVal 1 (SOff 657 0)); YP09.mkChunk 32 (CVal 1 (SOff 658 0)); YP09.mkChunk 33 (CVal 1 (SOff 659 0))];
YP09.mkRegion (Some 529%nat) 0 32 0 0 [YP09.mkChunk 7 (CVal 1 (SLit 0)); YP09.mkChunk 6 (CVal 1 (SLit 0)); YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0)); YP09.mkChunk 17 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 16 (CVal 1 (SLit 2)); YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 14 (CVal 1 (SLit 2)); YP09.mkChunk 19 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 18 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 8 (CVal 1 (SLit 0)); YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 24 (CVal 8 (SLit 0))];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 16 (CVal 8 (SOff 240 5884)); YP09.mkChunk 8 (CVal 8 (SOff 246 0)); YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 280 0 280 [YP09.mkChunk 24 (CVal 8 (SOff 625 0)); YP09.mkChunk 48 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0))); YP09.mkChunk 56 (CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 1))); YP09.mkChunk 64 (CVal 8 (SOff 11 20)); YP09.mkChunk 96 (CVal 8 (SOff 516 0)); YP09.mkChunk 80 (CVal 8 (SOff 529 0)); YP09.mkChunk 104 (CVal 8 (SOff 516 0)); YP09.mkChunk 208 (CVal 8 (SOff 41 0)); YP09.mkChunk 144 (CVal 8 (SOff 516 128)); YP09.mkChunk 176 (CVal 8 (SOff 516 112)); YP09.mkChunk 224 (CVal 8 (SOff 51 0)); YP09.mkChunk 120 (CVal 8 (SOff 11 26)); YP09.mkChunk 72 (CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 4))); YP09.mkChunk 112 (CVal 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))))); YP09.mkChunk 232 (CVal 8 (SOff 58 0)); YP09.mkChunk 136 (CVal 8 (SOff 57 0)); YP09.mkChunk 32 (CVal 8 (SOff 11 16)); YP09.mkChunk 128 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0))); YP09.mkChunk 200 (CVal 8 (SOff 40 0)); YP09.mkChunk 272 (CVal 8 (SOff 516 0)); YP09.mkChunk 240 (CVal 8 (SOff 32 0)); YP09.mkChunk 248 (CVal 8 (SOff 12 0))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 59 0))];
YP09.mkRegion (Some 59%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))];
YP09.mkRegion (Some 10%nat) 0 96 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 40 (CVal 4 (SOff 38 0)); YP09.mkChunk 44 (CVal 4 (SOff 39 0)); YP09.mkChunk 48 (CVal 2 (SOff 40 0)); YP09.mkChunk 50 (CVal 2 (SOff 41 0)); YP09.mkChunk 52 (CVal 2 (SOff 42 0)); YP09.mkChunk 54 (CVal 2 (SOff 43 0)); YP09.mkChunk 56 (CVal 8 (SOff 44 0)); YP09.mkChunk 64 (CVal 8 (SOff 45 0)); YP09.mkChunk 72 (CVal 8 (SOff 46 0)); YP09.mkChunk 80 (CVal 8 (SOff 47 0)); YP09.mkChunk 88 (CVal 4 (SOff 48 0)); YP09.mkChunk 92 (CVal 4 (SOff 49 0))];
YP09.mkRegion (Some 11%nat) 0 40 20 24 [YP09.mkChunk 0 (CVal 8 (SOff 50 0)); YP09.mkChunk 8 (CVal 8 (SOff 51 0)); YP09.mkChunk 16 (CVal 4 (SOff 52 0)); YP09.mkChunk 20 (CVal 4 (SOff 621 0)); YP09.mkChunk 24 (CVal 2 (SOff 54 0)); YP09.mkChunk 26 (CVal 2 (SOff 55 0)); YP09.mkChunk 28 (CVal 1 (SOff 56 0)); YP09.mkChunk 32 (CVal 1 (SOff 57 0)); YP09.mkChunk 33 (CVal 1 (SOff 58 0))]]
None
(mkFacts
[(12%nat, mkAF 4096 140737479966720 4); (651%nat, mkAF 0 18446744073709551615 0); (652%nat, mkAF 4096 140737479966720 4); (653%nat, mkAF 0 4294967295 0); (654%nat, mkAF 0 4294967295 0); (655%nat, mkAF 0 65535 0); (656%nat, mkAF 0 65535 0); (657%nat, mkAF 0 255 0); (658%nat, mkAF 0 255 0); (659%nat, mkAF 0 255 0); (529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (10%nat, mkAF 4096 140737479966720 4); (11%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF 2147450880 2147450880 0); (36%nat, mkAF 0 18446744073709551615 0); (38%nat, mkAF 0 4294967295 0); (39%nat, mkAF 0 4294967295 0); (40%nat, mkAF 1 65535 0); (41%nat, mkAF 1 65535 0); (42%nat, mkAF 0 65535 0); (43%nat, mkAF 0 65535 0); (46%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 4294967295 0); (49%nat, mkAF 0 4294967295 0); (50%nat, mkAF 0 18446744073709551615 0); (51%nat, mkAF 4096 140737479966720 4); (52%nat, mkAF 0 4294967295 0); (53%nat, mkAF 0 4294967295 0); (54%nat, mkAF 0 65535 0); (55%nat, mkAF 0 65535 0); (56%nat, mkAF 0 255 0); (57%nat, mkAF 0 255 0); (58%nat, mkAF 0 255 0); (621%nat, mkAF 0 4294967295 0); (625%nat, mkAF 0 65535 0)]
[mkAC BC_NE (SAlu ALU_AND (SExt false 8 (SOff 621 0)) (SLit 2)) (SLit 0)]
[((SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0)), (SOff 529 0))])).
Definition ss_DIFF : sstate := Eval vm_compute in ss_clear_conds ss_DIFF_0.
Definition chunk_redesc (off : Z) (e : sv) (c : YP09.chunk) : YP09.chunk :=
if Z.eqb (YP09.c_off c) off then match YP09.c_val c with CVal w _ => YP09.mkChunk off (CVal w e) | _ => c end else c.
Definition ss_rechunk_off (s : sstate) (base : nat) (off : Z) (e : sv) : sstate :=
ss_set_mem s (map (fun r => match YP09.r_base r with
| Some b => if Nat.eqb b base then YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(map (chunk_redesc off e) (YP09.r_chunks r)) else r
| None => r end) (ss_mem s)).
Definition fl_tmpblk (B : asyms) (cx : flcx) (pt n : Z) (ly3 : alayout) (S3 : astate) : Prop :=
(4096 <= pt /\ zone2 pt n) /\ pt + n <= alloc_ceiling /\ pt mod 16 = 0 /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(pt, n)] /\
(forall blc lyq ownq i, In (pt, n) blc -> 0 <= i < n ->
awr_byte TFLUSH_STK (spZ (c_regs cx)) (fl_FP cx) (ablocks B (c_ly cx) (c_S cx)) blc lyq ownq (pt + i)) /\
aftok (fl_FP cx) (ablocks B (c_ly cx) (c_S cx)) (pt, n).
Definition fl_R_deads : list nat := [23; 1; 27; 5; 7; 10; 11; 12; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition fl_R_deads_bv : list (bv 5) := [23; 1; 27; 5; 7; 10; 11; 12; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition ss_R_0 : sstate :=
(mkSS 8944
[(SLit 0); (SOff 512 0); (SOff 60 0); (SOff 3 0); (SOff 4 0); (SOff 513 0); (SOff 32 0); (SOff 515 0); (SOff 2 0); (SOff 60 0); (SAlu ALU_AND (SExt false 8 (SOff 621 0)) (SLit 1)); (SOff 627 0); (SOff 52 0); (SOff 516 32); (SOff 625 0); (SOff 41 0); (SLit 18446744073709551602); (SOff 523 0); (SOff 516 0); (SOff 11 20); (SOff 516 0); (SOff 10 0); (SOff 11 0); (SLit 0); (SAlu ALU_AND (SOff 52 0) (SLit 1)); (SOff 529 0); (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)); (SOff 41 0); (SOff 524 0); (SOff 525 0); (SOff 526 0); (SOff 527 0)]
[YP09.mkRegion (Some 529%nat) 0 32 0 0 [YP09.mkChunk 7 (CVal 1 (SLit 0)); YP09.mkChunk 6 (CVal 1 (SLit 0)); YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0)); YP09.mkChunk 17 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 16 (CVal 1 (SLit 2)); YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 14 (CVal 1 (SLit 2)); YP09.mkChunk 19 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 18 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 8 (CVal 1 (SLit 0)); YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 24 (CVal 8 (SLit 0))];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 16 (CVal 8 (SOff 240 5884)); YP09.mkChunk 8 (CVal 8 (SOff 246 0)); YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 280 0 280 [YP09.mkChunk 168 (CVal 8 (SOff 40 0)); YP09.mkChunk 144 (CVal 8 (SLit 0)); YP09.mkChunk 152 (CVal 8 (SLit 0)); YP09.mkChunk 120 (CVal 8 (SOff 11 26)); YP09.mkChunk 72 (CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 4))); YP09.mkChunk 112 (CVal 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))))); YP09.mkChunk 232 (CVal 8 (SOff 58 0)); YP09.mkChunk 136 (CVal 8 (SOff 57 0)); YP09.mkChunk 32 (CVal 8 (SOff 11 16)); YP09.mkChunk 128 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0))); YP09.mkChunk 200 (CVal 8 (SOff 40 0)); YP09.mkChunk 272 (CVal 8 (SOff 516 0)); YP09.mkChunk 240 (CVal 8 (SOff 32 0)); YP09.mkChunk 248 (CVal 8 (SOff 12 0))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 59 0))];
YP09.mkRegion (Some 59%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))];
YP09.mkRegion (Some 10%nat) 0 96 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 40 (CVal 4 (SOff 38 0)); YP09.mkChunk 44 (CVal 4 (SOff 39 0)); YP09.mkChunk 48 (CVal 2 (SOff 40 0)); YP09.mkChunk 50 (CVal 2 (SOff 41 0)); YP09.mkChunk 52 (CVal 2 (SOff 42 0)); YP09.mkChunk 54 (CVal 2 (SOff 43 0)); YP09.mkChunk 56 (CVal 8 (SOff 44 0)); YP09.mkChunk 64 (CVal 8 (SOff 45 0)); YP09.mkChunk 72 (CVal 8 (SOff 46 0)); YP09.mkChunk 80 (CVal 8 (SOff 47 0)); YP09.mkChunk 88 (CVal 4 (SOff 48 0)); YP09.mkChunk 92 (CVal 4 (SOff 49 0))];
YP09.mkRegion (Some 11%nat) 0 40 20 24 [YP09.mkChunk 0 (CVal 8 (SOff 50 0)); YP09.mkChunk 8 (CVal 8 (SOff 51 0)); YP09.mkChunk 16 (CVal 4 (SOff 52 0)); YP09.mkChunk 20 (CVal 4 (SOff 621 0)); YP09.mkChunk 24 (CVal 2 (SOff 54 0)); YP09.mkChunk 26 (CVal 2 (SOff 55 0)); YP09.mkChunk 28 (CVal 1 (SOff 56 0)); YP09.mkChunk 32 (CVal 1 (SOff 57 0)); YP09.mkChunk 33 (CVal 1 (SOff 58 0))]]
None
(mkFacts
[(529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (10%nat, mkAF 4096 140737479966720 4); (11%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF 2147450880 2147450880 0); (36%nat, mkAF 0 18446744073709551615 0); (38%nat, mkAF 0 4294967295 0); (39%nat, mkAF 0 4294967295 0); (40%nat, mkAF 1 65535 0); (41%nat, mkAF 1 65535 0); (42%nat, mkAF 0 65535 0); (43%nat, mkAF 0 65535 0); (46%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 4294967295 0); (49%nat, mkAF 0 4294967295 0); (50%nat, mkAF 0 18446744073709551615 0); (51%nat, mkAF 4096 140737479966720 4); (52%nat, mkAF 0 4294967295 0); (53%nat, mkAF 0 4294967295 0); (54%nat, mkAF 0 65535 0); (55%nat, mkAF 0 65535 0); (56%nat, mkAF 0 255 0); (57%nat, mkAF 0 255 0); (58%nat, mkAF 0 255 0); (621%nat, mkAF 0 4294967295 0); (625%nat, mkAF 0 65535 0)]
[mkAC BC_EQ (SAlu ALU_AND (SExt false 8 (SOff 621 0)) (SLit 1)) (SLit 0); mkAC BC_EQ (SAlu ALU_AND (SExt false 8 (SOff 621 0)) (SLit 2)) (SLit 0)]
[((SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0)), (SOff 529 0))])).
Definition ss_R : sstate := Eval vm_compute in
ss_clear_conds (ss_set_facts
(ss_havoc_regs (ss_rechunk_off (ss_rechunk_off (ss_rechunk_off (ss_rechunk_off (ss_set_pc ss_R_0 8944) 60 168 (SOff 839 0)) 60 144 (SOff 840 0)) 60 152 (SOff 841 0)) 60 232 (SOff 842 0)) 843 fl_R_deads)
(f_atoms (ss_facts ss_R_0) ++ [(839%nat, mkAF 1 65535 0); (840%nat, mkAF 0 65535 0); (841%nat, mkAF 0 65535 0); (845%nat, mkAF 1 65535 0)])).
Definition INV_R (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (fl_npal cx) /\
exists pt w h top left tidx,
ew E 843 = Z_to_bv 64 pt /\ ew E 839 = Z_to_bv 64 w /\ ew E 845 = Z_to_bv 64 h /\ ew E 841 = Z_to_bv 64 top /\
ew E 840 = Z_to_bv 64 left /\ ew E 842 = Z_to_bv 64 tidx /\ 0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\ 0 <= tidx < 2 ^ 64 /\
((pt = 0 /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ k <= 2 /\ fl_tmpblk B cx pt (w * h) ly3 S3)).
Definition fl_T0_deads : list nat := [23; 1; 27; 5; 7; 10; 11; 12; 13; 16; 17; 28; 29; 30; 31]%nat.
Definition fl_T0_deads_bv : list (bv 5) := [23; 1; 27; 5; 7; 10; 11; 12; 13; 16; 17; 28; 29; 30; 31]%bv.
Definition ss_T0_0 : sstate :=
(mkSS 8356
[(SLit 0); (SOff 512 0); (SOff 60 0); (SOff 3 0); (SOff 4 0); (SOff 513 0); (SOff 32 0); (SOff 515 0); (SOff 2 0); (SOff 60 0); (SOff 40 0); (SOff 623 0); (SOff 52 0); (SOff 624 0); (SOff 625 0); (SOff 41 0); (SLit 18446744073709551602); (SOff 523 0); (SOff 516 0); (SOff 11 20); (SOff 516 0); (SOff 10 0); (SOff 11 0); (SLit 0); (SAlu ALU_AND (SOff 52 0) (SLit 1)); (SOff 529 0); (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 20) (SLit 3)) (SOff 32 0)); (SOff 41 0); (SOff 524 0); (SOff 525 0); (SOff 526 0); (SOff 527 0)]
[YP09.mkRegion (Some 12%nat) 0 40 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 651 0)); YP09.mkChunk 8 (CVal 8 (SOff 652 0)); YP09.mkChunk 16 (CVal 4 (SOff 653 0)); YP09.mkChunk 20 (CVal 4 (SOff 654 0)); YP09.mkChunk 24 (CVal 2 (SOff 655 0)); YP09.mkChunk 26 (CVal 2 (SOff 656 0)); YP09.mkChunk 28 (CVal 1 (SOff 657 0)); YP09.mkChunk 32 (CVal 1 (SOff 658 0)); YP09.mkChunk 33 (CVal 1 (SOff 659 0))];
YP09.mkRegion (Some 529%nat) 0 32 0 0 [YP09.mkChunk 7 (CVal 1 (SLit 0)); YP09.mkChunk 6 (CVal 1 (SLit 0)); YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0)); YP09.mkChunk 17 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 16 (CVal 1 (SLit 2)); YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 14 (CVal 1 (SLit 2)); YP09.mkChunk 19 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 18 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 8 (CVal 1 (SLit 0)); YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 24 (CVal 8 (SLit 0))];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 16 (CVal 8 (SOff 240 5884)); YP09.mkChunk 8 (CVal 8 (SOff 246 0)); YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 280 0 280 [YP09.mkChunk 168 (CVal 8 (SOff 40 0)); YP09.mkChunk 144 (CVal 8 (SLit 0)); YP09.mkChunk 152 (CVal 8 (SLit 0)); YP09.mkChunk 120 (CVal 8 (SOff 11 26)); YP09.mkChunk 72 (CVal 8 (SAlu ALU_AND (SOff 52 0) (SLit 4))); YP09.mkChunk 112 (CVal 8 (SAlu ALU_SLTU (SLit 0) (SAlu ALU_OR (SAlu ALU_AND (SExt false 8 (SOff 38 0)) (SLit 8)) (SAlu ALU_AND (SOff 52 0) (SLit 2))))); YP09.mkChunk 232 (CVal 8 (SOff 58 0)); YP09.mkChunk 136 (CVal 8 (SOff 57 0)); YP09.mkChunk 32 (CVal 8 (SOff 11 16)); YP09.mkChunk 128 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 11 16) (SLit 3)) (SOff 32 0))); YP09.mkChunk 200 (CVal 8 (SOff 40 0)); YP09.mkChunk 272 (CVal 8 (SOff 516 0)); YP09.mkChunk 240 (CVal 8 (SOff 32 0)); YP09.mkChunk 248 (CVal 8 (SOff 12 0))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 59 0))];
YP09.mkRegion (Some 59%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))];
YP09.mkRegion (Some 10%nat) 0 96 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 40 (CVal 4 (SOff 38 0)); YP09.mkChunk 44 (CVal 4 (SOff 39 0)); YP09.mkChunk 48 (CVal 2 (SOff 40 0)); YP09.mkChunk 50 (CVal 2 (SOff 41 0)); YP09.mkChunk 52 (CVal 2 (SOff 42 0)); YP09.mkChunk 54 (CVal 2 (SOff 43 0)); YP09.mkChunk 56 (CVal 8 (SOff 44 0)); YP09.mkChunk 64 (CVal 8 (SOff 45 0)); YP09.mkChunk 72 (CVal 8 (SOff 46 0)); YP09.mkChunk 80 (CVal 8 (SOff 47 0)); YP09.mkChunk 88 (CVal 4 (SOff 48 0)); YP09.mkChunk 92 (CVal 4 (SOff 49 0))];
YP09.mkRegion (Some 11%nat) 0 40 20 24 [YP09.mkChunk 0 (CVal 8 (SOff 50 0)); YP09.mkChunk 8 (CVal 8 (SOff 51 0)); YP09.mkChunk 16 (CVal 4 (SOff 52 0)); YP09.mkChunk 20 (CVal 4 (SOff 621 0)); YP09.mkChunk 24 (CVal 2 (SOff 54 0)); YP09.mkChunk 26 (CVal 2 (SOff 55 0)); YP09.mkChunk 28 (CVal 1 (SOff 56 0)); YP09.mkChunk 32 (CVal 1 (SOff 57 0)); YP09.mkChunk 33 (CVal 1 (SOff 58 0))]]
None
(mkFacts
[(12%nat, mkAF 4096 140737479966720 4); (651%nat, mkAF 0 18446744073709551615 0); (652%nat, mkAF 4096 140737479966720 4); (653%nat, mkAF 0 4294967295 0); (654%nat, mkAF 0 4294967295 0); (655%nat, mkAF 0 65535 0); (656%nat, mkAF 0 65535 0); (657%nat, mkAF 0 255 0); (658%nat, mkAF 0 255 0); (659%nat, mkAF 0 255 0); (529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (10%nat, mkAF 4096 140737479966720 4); (11%nat, mkAF 4096 140737479966720 4); (32%nat, mkAF 2147450880 2147450880 0); (36%nat, mkAF 0 18446744073709551615 0); (38%nat, mkAF 0 4294967295 0); (39%nat, mkAF 0 4294967295 0); (40%nat, mkAF 1 65535 0); (41%nat, mkAF 1 65535 0); (42%nat, mkAF 0 65535 0); (43%nat, mkAF 0 65535 0); (46%nat, mkAF 4096 140737479966720 4); (48%nat, mkAF 0 4294967295 0); (49%nat, mkAF 0 4294967295 0); (50%nat, mkAF 0 18446744073709551615 0); (51%nat, mkAF 4096 140737479966720 4); (52%nat, mkAF 0 4294967295 0); (53%nat, mkAF 0 4294967295 0); (54%nat, mkAF 0 65535 0); (55%nat, mkAF 0 65535 0); (56%nat, mkAF 0 255 0); (57%nat, mkAF 0 255 0); (58%nat, mkAF 0 255 0); (621%nat, mkAF 0 4294967295 0); (625%nat, mkAF 0 65535 0)]
[mkAC BC_EQ (SAlu ALU_AND (SExt false 8 (SOff 621 0)) (SLit 2)) (SLit 0)]
[((SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0)), (SOff 529 0))])).
Definition ss_T0 : sstate := Eval vm_compute in
ss_clear_conds (ss_set_facts
(ss_havoc_regs (ss_rechunk_off (ss_rechunk_off (ss_rechunk_off ss_T0_0 60 168 (SOff 679 0)) 60 144 (SOff 680 0)) 60 152 (SOff 681 0)) 682 fl_T0_deads)
(f_atoms (ss_facts ss_T0_0) ++ [(679%nat, mkAF 1 65535 0); (680%nat, mkAF 0 65535 0); (681%nat, mkAF 0 65535 0); (684%nat, mkAF 1 65535 0)])).
Definition INV_T0 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (fl_npal cx) /\
(exists fb, fl_bef cx fb E) /\
exists pt w h top left,
ew E 682 = Z_to_bv 64 pt /\ ew E 679 = Z_to_bv 64 w /\ ew E 684 = Z_to_bv 64 h /\ ew E 681 = Z_to_bv 64 top /\ ew E 680 = Z_to_bv 64 left /\
0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\
((pt = 0 /\ w = cg_W (c_s cx) /\ h = cg_H (c_s cx) /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ k <= 2 /\ fl_tmpblk B cx pt (w * h) ly3 S3)).
Definition fl_R2_deads : list nat := [23; 10; 11]%nat.
Definition fl_R2_deads_bv : list (bv 5) := [23; 10; 11]%bv.
Definition INV_R2 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (fl_npal cx) /\
exists pt w h top left tidx img,
ew E 892 = Z_to_bv 64 pt /\ ew E 839 = Z_to_bv 64 w /\ ew E 845 = Z_to_bv 64 h /\ ew E 841 = Z_to_bv 64 top /\
ew E 840 = Z_to_bv 64 left /\ ew E 842 = Z_to_bv 64 tidx /\ ew E 891 = Z_to_bv 64 img /\ 0 <= pt < 2 ^ 64 /\
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
ew E 892 = Z_to_bv 64 pt /\ ew E 839 = Z_to_bv 64 w /\ ew E 845 = Z_to_bv 64 h /\ ew E 841 = Z_to_bv 64 top /\
ew E 840 = Z_to_bv 64 left /\ ew E 842 = Z_to_bv 64 tidx /\ ew E 891 = Z_to_bv 64 img /\ 0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\ 0 <= tidx < 2 ^ 64 /\
((pt = 0 /\ img = fr_img (c_f cx) /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ img = pt /\ k <= 2 /\ fl_tmpblk B cx pt (w * h) ly3 S3)).
Definition fl_slct (cx : flcx) : Z := if fl_uselct cx then fr_nlp (c_f cx) else 0.
Definition fl_R4_deads : list nat := [10; 12; 13]%nat.
Definition fl_R4_deads_bv : list (bv 5) := [10; 12; 13]%bv.
Definition INV_R4 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\ ew E 625 = Z_to_bv 64 (fl_npal cx) /\
(exists attr, ew E 901 = Z_to_bv 64 attr /\ 0 <= attr <= 1) /\ ew E 911 = Z_to_bv 64 (fl_slct cx) /\
exists pt w h top left tidx img,
ew E 892 = Z_to_bv 64 pt /\ ew E 839 = Z_to_bv 64 w /\ ew E 845 = Z_to_bv 64 h /\ ew E 841 = Z_to_bv 64 top /\
ew E 840 = Z_to_bv 64 left /\ ew E 842 = Z_to_bv 64 tidx /\ ew E 891 = Z_to_bv 64 img /\ 0 <= pt < 2 ^ 64 /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx) /\ 0 <= tidx < 2 ^ 64 /\
((pt = 0 /\ img = fr_img (c_f cx) /\ k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx)) \/
(pt <> 0 /\ img = pt /\ k <= 2 /\ fl_tmpblk B cx pt (w * h) ly3 S3)).
Definition region_filter_offs (keep : list Z) (r : YP09.region) : YP09.region :=
YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) (YP09.r_wlo r) (YP09.r_whi r)
(filter (fun c => existsb (Z.eqb (YP09.c_off c)) keep) (YP09.r_chunks r)).
Definition fl_X_mem (m : smem) : smem :=
map (fun r => match YP09.r_base r with
| Some b => if Nat.eqb b 516 then region_filter_offs [0; 8; 16; 248] r
else if Nat.eqb b 60 then region_filter_offs [] r else r
| None => r end) m.
Definition fl_X_deads : list nat := [19; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat.
Definition fl_X_deads_bv : list (bv 5) := [19; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv.
Definition INV_X (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= EV_FLUSH /\ (exists r, ew E 961 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64) /\
Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)).
Definition INV_R5 (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 =>
k <= 2 + EV_RAWADD /\ (exists res, ew E 919 = Z_to_bv 64 res /\ 0 <= res < 2 ^ 64) /\
exists pt, ew E 892 = Z_to_bv 64 pt /\ 0 <= pt < 2 ^ 64 /\
((pt = 0 /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx))) \/
(pt <> 0 /\ exists n, 0 <= n /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(pt, n)]) /\
aftok (fl_FP cx) (ablocks B (c_ly cx) (c_S cx)) (pt, n))).
End d.
End a.
