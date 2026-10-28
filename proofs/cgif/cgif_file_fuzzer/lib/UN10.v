(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN03 YN2b UN1d UN1f UN19 UN1a UN0i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem ubs0_alloc_slot_of : NEST_SUCC -> alloc_meta_hyp ubs0_msyms -> alloc_slot_hyp ubs0_msyms.
Proof using. intros SU AMH. exact (ubs0_alloc_slot_partial4 AMH (ubs0_SEG_head AMH) SU). Qed.
Theorem ubs0_alloc_slot : alloc_slot_hyp ubs0_msyms.
Proof using. exact (ubs0_alloc_slot_of ubs0_NEST_SUCC ubs0_alloc_meta). Qed.
End a.
