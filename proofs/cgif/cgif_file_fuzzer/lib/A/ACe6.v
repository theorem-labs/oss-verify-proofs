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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC8b.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ _ PB_tfib1) (@pa_relro_lo _ _ PB_tfib1) (@pa_relro_hi _ _ PB_tfib1)}.
Remark tfib_cbbX_pc : @pa_val _ _ PB_tfib1 A_TEXT + A_cbb = 0x86a2c.   Proof. reflexivity. Qed.
Theorem tfib_cbbX : forall B : asyms,
AR_laws tfibsegs B -> PALib (PI := PB_tfib1) B -> aintrin_realizes tfibsegs B OCpy (pa_sigma (PAImg := PB_tfib1) AS_asan_memcpy) ->
tcbb_specX tfibsegs B 0x86a2c.
Proof. intros B LAWS TL AI. rewrite <- tfib_cbbX_pc. exact (AC8b.pb_cbbX (PI := PB_tfib1) B LAWS TL AI). Qed.
End a.
