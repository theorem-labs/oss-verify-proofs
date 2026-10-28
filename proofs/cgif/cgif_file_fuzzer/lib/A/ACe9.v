(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0m AB1w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AE26 AE27 AE2m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0x YI0y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AI12.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC1f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC9k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbl ACec AC9l.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ _ PB_tfib) (@pa_relro_lo _ _ PB_tfib) (@pa_relro_hi _ _ PB_tfib)}.
Remark tfib_raw_closeX_pc : A_cgif_raw_closeP (PI := PB_tfib1) = 0x86684.   Proof. reflexivity. Qed.
Remark tfib_raw_closeX_trailer : pa_val (PAImg := PB_tfib1) (A_OBJ 11) = ak_trailer tfib_K.   Proof. reflexivity. Qed.
Theorem tfib_raw_closeX : forall (B : asyms) (MT : ameter_ops),
AR_laws tfibsegs B -> PALib (PI := PB_tfib1) B -> PALib (PI := PB_tfib) B ->
TfibSyms B -> asink_img_laws tfibsegs B tfib_K ->
afree04_rule tfibsegs B MT ->
trawclose_specX tfibsegs tfib_K B MT 0x86684 [pc_free_ra0 (as_code B); 0x86720] 0x81a18 0.
Proof.
intros B MT LAWS TL1 TL0 TB AIL AF4.
exact (AC9l.pb_raw_closeX (PI := PB_tfib1) B LAWS TL1 MT AF4 0x81a18 0
ltac:(split; [lia | reflexivity]) ltac:(lia) tfib_K AIL
(tfib_wcbF B LAWS TL0 TB AIL) eq_refl (tfib_trailer_shadow B TB)).
Qed.
End a.
