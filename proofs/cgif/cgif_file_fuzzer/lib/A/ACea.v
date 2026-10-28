(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP0b YP09 YI04 YI09 YK04 YA0n YG00 YG0f YG0n YG0d YM05 YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0m AB1w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AE26 AE27.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0w YI0x YI0y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AI12.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC1f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC7x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbl ACec ACa3 ACa2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ _ PB_tfib) (@pa_relro_lo _ _ PB_tfib) (@pa_relro_hi _ _ PB_tfib)}.
Remark tfib_cgif_raw_addframeX_pc : @pa_val _ _ PB_tfib1 A_TEXT + AF_asan3_cgif_raw_addframe = 0x84894.   Proof. reflexivity. Qed.
Definition tfib_cgif_raw_addframeX := @ACa2.pb_cgif_raw_addframeX fx rc _ PB_tfib1.
Check tfib_cgif_raw_addframeX.
Definition tfib_cgif_raw_addframeX_w (B : asyms) (LAWS : AR_laws tfibsegs B) (TL0 : PALib (PI := PB_tfib) B) (TL1 : PALib (PI := PB_tfib1) B)
(TB : TfibSyms B) (AIL : asink_img_laws tfibsegs B tfib_K) :=
fun ML AMEMSET AMEMCPY ASM1 SMP ASF FFL TLF HGOT9 CTX HDEEP MT MLAW MLAWF XN HXM HXN HXMN AMALLOC4 AFREE4 =>
@ACa2.pb_cgif_raw_addframeX fx rc _ PB_tfib1 RO B TL1 LAWS ML AMEMSET AMEMCPY ASM1 SMP ASF FFL TLF HGOT9 CTX HDEEP
tfib_K AIL MT MLAW MLAWF XN HXM HXN HXMN AMALLOC4 AFREE4 0x81a18 ltac:(split; [lia | reflexivity]) (tfib_wcbF B LAWS TL0 TB AIL).
Check tfib_cgif_raw_addframeX_w.
End a.
