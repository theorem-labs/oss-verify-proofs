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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0z YC4a YC80 YC1f YC1g YC1h YC81 YC4b YC8g YC44 YC45 YC44 YCjr YCj1 YCj0 YCja.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCj0 YCj6 YCiy YCj7.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC7x YC85.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YChz YCid YCie.
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
Section e.
Variable MT : ameter_ops.
#[local] Notation INVT := (flcx -> flxx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop).
Definition INV_SX (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_DIFFX MT B cx xx E k ly3 S3 W3 ms3 md3 /\
(forall b, x_bef xx = Some b -> YO07.px_ne (xG cx xx) (x_cur xx) b = YO07.cmp_pixel (xG cx xx) (x_cur xx) b).
Definition INV_FvX (B : asyms) : INVT :=
fun cx xx E k ly3 S3 W3 ms3 md3 => INV_DIFFX MT B cx xx E k ly3 S3 W3 ms3 md3 /\
(forall b, x_bef xx = Some b -> YO07.px_ne (xG cx xx) (x_cur xx) b = (fun c q : Z => negb (c =? q))).
End e.
End d.
End a.
