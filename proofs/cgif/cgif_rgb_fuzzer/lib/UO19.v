(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YO2f UO1l UO1n UO1h UO1i UO0i.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Unset Lia Cache. Unset Nia Cache.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Theorem ubs2_alloc_slot_of : NEST_SUCC -> alloc_meta_hyp ubs2_msyms -> alloc_slot_hyp ubs2_msyms.
Proof. intros SU AMH. exact (ubs2_alloc_slot_partial4 AMH (ubs2_SEG_head AMH) SU). Qed.
Theorem ubs2_alloc_slot : alloc_slot_hyp ubs2_msyms.
Proof. exact (ubs2_alloc_slot_of ubs2_NEST_SUCC ubs2_alloc_meta). Qed.
End a.
