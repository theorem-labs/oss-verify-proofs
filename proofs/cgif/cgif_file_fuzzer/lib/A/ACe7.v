(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YI08 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AI12.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC1f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC20 YC7y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8f AC8c AC8d.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ _ PB_tfib1) (@pa_relro_lo _ _ PB_tfib1) (@pa_relro_hi _ _ PB_tfib1)}.
Remark tfib_cblX_pc : @pa_val _ _ PB_tfib1 A_TEXT + A_cbl = 0x86764.   Proof. reflexivity. Qed.
Theorem tfib_cblX : forall B : asyms,
AR_laws tfibsegs B -> PALib (PI := PB_tfib1) B -> tcbl_specX tfibsegs B TCBL_STK 0x86764.
Proof. intros B LAWS TL. rewrite <- tfib_cblX_pc. exact (AC8d.pb_cblX (PI := PB_tfib1) B LAWS TL). Qed.
End a.
