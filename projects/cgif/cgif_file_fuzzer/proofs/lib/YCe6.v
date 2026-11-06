(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YI08 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1v YCef.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI10 YI12 YC4a YC8i YCbj YC1f.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC8g YCbh YC8a YC8b.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ _ PB_tfib1) (@pa_relro_lo _ _ PB_tfib1) (@pa_relro_hi _ _ PB_tfib1)}.
Remark tfib_cbbX_pc : @pa_val _ _ PB_tfib1 A_TEXT + A_cbb = 0x86a68.   Proof. reflexivity. Qed.
Theorem tfib_cbbX : forall B : asyms,
AR_laws tfibsegs B -> PALib (PI := PB_tfib1) B -> aintrin_realizes tfibsegs B OCpy (pa_sigma (PAImg := PB_tfib1) AS_asan_memcpy) ->
tcbb_specX tfibsegs B 0x86a68.
Proof. intros B LAWS TL AI. rewrite <- tfib_cbbX_pc. exact (YC8b.pb_cbbX (PI := PB_tfib1) B LAWS TL AI). Qed.
End a.
