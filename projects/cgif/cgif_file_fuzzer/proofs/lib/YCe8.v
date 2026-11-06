(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1v YCef.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI10 YI12 YC4a YC8i YCbj YC1f.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8g YC5d YCbh YC93 YC8s.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ _ PB_tfib1) (@pa_relro_lo _ _ PB_tfib1) (@pa_relro_hi _ _ PB_tfib1)}.
Remark tfib_lzwX_pc : @pa_val _ _ PB_tfib1 A_TEXT + A_LZW = 0x85480.   Proof. reflexivity. Qed.
Definition tfib_lzwX := @YC8s.pb_lzwX fx rc SK PB_tfib1.
End a.
