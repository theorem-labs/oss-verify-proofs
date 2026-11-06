(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YI09 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1v YCef YF0m YB1w.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YE2k YE26 YE27.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0z YI10 YI12 YC4a YC8i YCbj YC1f.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbk.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YCbh YC7x YCbl YCec YCa3 YCa2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ _ PB_tfib) (@pa_relro_lo _ _ PB_tfib) (@pa_relro_hi _ _ PB_tfib)}.
Remark tfib_cgif_raw_addframeX_pc : @pa_val _ _ PB_tfib1 A_TEXT + AF_both3_cgif_raw_addframe = 0x845d8.   Proof. reflexivity. Qed.
Definition tfib_cgif_raw_addframeX := @YCa2.pb_cgif_raw_addframeX fx rc _ PB_tfib1.
Check tfib_cgif_raw_addframeX.
Definition tfib_cgif_raw_addframeX_w (B : asyms) (LAWS : AR_laws tfibsegs B) (TL0 : PALib (PI := PB_tfib) B) (TL1 : PALib (PI := PB_tfib1) B)
(TB : TfibSyms B) (AIL : asink_img_laws tfibsegs B tfib_K) :=
fun ML AMEMSET AMEMCPY ASM1 SMP ASF FFL TLF HGOT9 CTX HDEEP MT MLAW MLAWF XN HXM HXN HXMN AMALLOC4 AFREE4 =>
@YCa2.pb_cgif_raw_addframeX fx rc _ PB_tfib1 RO B TL1 LAWS ML AMEMSET AMEMCPY ASM1 SMP ASF FFL TLF HGOT9 CTX HDEEP
tfib_K AIL MT MLAW MLAWF XN HXM HXN HXMN AMALLOC4 AFREE4 0x8131c ltac:(split; [lia | reflexivity]) (tfib_wcbF B LAWS TL0 TB AIL).
Check tfib_cgif_raw_addframeX_w.
End a.
