(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YO2f YO1l YO1n YO1h YO1i YO0i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Unset Lia Cache. Unset Nia Cache.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Theorem src2_alloc_slot_of : NEST_SUCC -> alloc_meta_hyp src2_msyms -> alloc_slot_hyp src2_msyms.
Proof. intros SU AMH. exact (src2_alloc_slot_partial4 AMH (src2_SEG_head AMH) SU). Qed.
Theorem src2_alloc_slot : alloc_slot_hyp src2_msyms.
Proof. exact (src2_alloc_slot_of src2_NEST_SUCC src2_alloc_meta). Qed.
End a.
