(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0m AB1w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AE26 AE27.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AI12.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC1f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC7z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbl.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ _ PB_tfib) (@pa_relro_lo _ _ PB_tfib) (@pa_relro_hi _ _ PB_tfib)}.
Remark tfib_wcbF_pc : A_cgif_writecbP (PI := PB_tfib) = 0x81a18.   Proof. reflexivity. Qed.
Remark tfib_wcbF_fwrite : pa_sigma (PAImg := PB_tfib) AS_fwrite = FW_ENTRY.   Proof. reflexivity. Qed.
Theorem tfib_wcbF : forall B : asyms,
AR_laws tfibsegs B -> PALib (PI := PB_tfib) B -> TfibSyms B -> asink_img_laws tfibsegs B tfib_K ->
twcbF_spec tfibsegs tfib_K B 0x81a18.
Proof. intros B LAWS TL TB AIL. exact (ACbl.pb_wcbF (PI := PB_tfib) B LAWS TL tfib_K AIL (tfib_afwrite_spec B LAWS TB AIL)). Qed.
End a.
