(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YI09 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1v YCef.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0z YI10 YI12 YC4a YC8i YCbj YC1f YC8g YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC7x.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCid YCic.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ _ PB_tfib) (@pa_relro_lo _ _ PB_tfib) (@pa_relro_hi _ _ PB_tfib)}.
Remark tfib_flushFrameX_pc : @pa_val _ _ PB_tfib A_TEXT + AF_both3_flushFrame = 0x826f4.   Proof. reflexivity. Qed.
Remark tfib_flushFrameX_rawadd_slot : @pa_sigma _ _ PB_tfib AS_cgif_raw_addframe = 0x845d8.   Proof. reflexivity. Qed.
Definition tfib_flushFrameX := @YCic.pb_flushFrameX fx rc SK PB_tfib.
Check tfib_flushFrameX.
End a.
