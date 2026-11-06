(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1v YCef YF0m YB1w.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YE2k YE26 YE27.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0z YI12 YC4a YC8i YCbj YC1f.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8g YCbk YC7z YCbl.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ _ PB_tfib) (@pa_relro_lo _ _ PB_tfib) (@pa_relro_hi _ _ PB_tfib)}.
Remark tfib_wcbF_pc : A_cgif_writecbP (PI := PB_tfib) = 0x8131c.   Proof. reflexivity. Qed.
Remark tfib_wcbF_fwrite : pa_sigma (PAImg := PB_tfib) AS_fwrite = FW_ENTRY.   Proof. reflexivity. Qed.
Theorem tfib_wcbF : forall B : asyms,
AR_laws tfibsegs B -> PALib (PI := PB_tfib) B -> TfibSyms B -> asink_img_laws tfibsegs B tfib_K ->
twcbF_spec tfibsegs tfib_K B 0x8131c.
Proof. intros B LAWS TL TB AIL. exact (YCbl.pb_wcbF (PI := PB_tfib) B LAWS TL tfib_K AIL (tfib_afwrite_spec B LAWS TB AIL)). Qed.
End a.
