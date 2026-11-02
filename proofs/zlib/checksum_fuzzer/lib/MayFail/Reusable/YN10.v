(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN10.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN19.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem src0_alloc_slot_of : NEST_SUCC -> alloc_meta_hyp src0_msyms -> alloc_slot_hyp src0_msyms.
Proof. intros SU AMH. exact (src0_alloc_slot_partial4 AMH (src0_SEG_head AMH) SU). Qed.
Theorem src0_alloc_slot : alloc_slot_hyp src0_msyms.
Proof. exact (src0_alloc_slot_of src0_NEST_SUCC src0_alloc_meta). Qed.
End a.
