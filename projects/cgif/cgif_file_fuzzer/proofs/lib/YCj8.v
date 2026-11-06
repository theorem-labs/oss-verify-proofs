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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkc YCj4 YC8g YCjr YCj1 YCj0 YCj6 YCiy YCj7.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
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
Definition ss_S : sstate := Eval vm_compute in ss_set_pc (ss_havoc_regs ss_DIFF 682 [11; 12]%nat) 7584.
Definition ss_Fv : sstate := Eval vm_compute in ss_set_pc (ss_havoc_regs ss_DIFF 682 [11; 12]%nat) 8312.
Definition fl_dims_deads : list nat := [21; 23; 22; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 24; 25; 26; 28; 29; 30; 31]%nat.
Definition fl_dims_deads_bv : list (bv 5) := [21; 23; 22; 1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 24; 25; 26; 28; 29; 30; 31]%bv.
Definition ss_DIMS : sstate := Eval vm_compute in ss_set_pc (ss_havoc_regs ss_DIFF 861 fl_dims_deads) 9660.
Definition INV_DIMS (B : asyms) : flcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
(exists gen, ew E 621 = Z_to_bv 64 gen /\ 0 <= gen < 2 ^ 32) /\
ew E 625 = Z_to_bv 64 (fl_npal cx) /\
(exists fb, fl_bef cx fb E) /\
exists w h top left, ew E 861 = Z_to_bv 64 w /\ ew E 862 = Z_to_bv 64 h /\ ew E 863 = Z_to_bv 64 left /\
val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx + 152) 8 top /\
1 <= w /\ 0 <= left /\ left + w <= cg_W (c_s cx) /\ 1 <= h /\ 0 <= top /\ top + h <= cg_H (c_s cx).
End b.
End a.
