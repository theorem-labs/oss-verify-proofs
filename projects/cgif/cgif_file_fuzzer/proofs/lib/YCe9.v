(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1v YCef YF0m YB1w.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YE2k YE26 YE27 YE2m.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0z YI10 YI12 YC4a YC8i YCbj YC1f.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8g YCbk YC9k YC5d YC7z YCbl YCec YC9l.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ _ PB_tfib) (@pa_relro_lo _ _ PB_tfib) (@pa_relro_hi _ _ PB_tfib)}.
Remark tfib_raw_closeX_pc : A_cgif_raw_closeP (PI := PB_tfib1) = 0x8656c.   Proof. reflexivity. Qed.
Remark tfib_raw_closeX_trailer : pa_val (PAImg := PB_tfib1) (A_OBJ 11) = ak_trailer tfib_K.   Proof. reflexivity. Qed.
Theorem tfib_raw_closeX : forall (B : asyms) (MT : ameter_ops),
AR_laws tfibsegs B -> PALib (PI := PB_tfib1) B -> PALib (PI := PB_tfib) B ->
TfibSyms B -> asink_img_laws tfibsegs B tfib_K ->
afree04_rule tfibsegs B MT ->
trawclose_specX tfibsegs tfib_K B MT 0x8656c [pc_free_ra0 (as_code B); 0x86614] 0x8131c 0.
Proof.
intros B MT LAWS TL1 TL0 TB AIL AF4.
exact (YC9l.pb_raw_closeX (PI := PB_tfib1) B LAWS TL1 MT AF4 0x8131c 0
ltac:(split; [lia | reflexivity]) ltac:(lia) tfib_K AIL
(tfib_wcbF B LAWS TL0 TB AIL) eq_refl (tfib_trailer_shadow B TB)).
Qed.
End a.
