(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF66.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
#[local] Notation TSEGS0 := tfx_loaded_segments (only parsing).
Definition tfx_popfree_head {imgk : img} : Z := (0x36cd0 + D_150).
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => img_apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Lemma PF0 {imgk : img} : fetch_word TSEGS0 (Z_to_bv 64 tfx_popfree_head) = Some PW0. Proof. (img_case; vm_refl). Qed.
Lemma PF1 {imgk : img} : fetch_word TSEGS0 (Z_to_bv 64 (tfx_popfree_head + 4)) = Some PW1. Proof. (img_case; vm_refl). Qed.
Lemma PF2 {imgk : img} : fetch_word TSEGS0 (Z_to_bv 64 (tfx_popfree_head + 8)) = Some PW2. Proof. (img_case; vm_refl). Qed.
Lemma PF3 {imgk : img} : fetch_word TSEGS0 (Z_to_bv 64 (tfx_popfree_head + 12)) = Some PW3. Proof. (img_case; vm_refl). Qed.
Lemma PF4 {imgk : img} : fetch_word TSEGS0 (Z_to_bv 64 (tfx_popfree_head + 16)) = Some PW4. Proof. (img_case; vm_refl). Qed.
Lemma PF5 {imgk : img} : fetch_word TSEGS0 (Z_to_bv 64 (tfx_popfree_head + 20)) = Some PW5. Proof. (img_case; vm_refl). Qed.
Lemma PF6 {imgk : img} : fetch_word TSEGS0 (Z_to_bv 64 (tfx_popfree_head + 24)) = Some PW6. Proof. (img_case; vm_refl). Qed.
Lemma PF7 {imgk : img} : fetch_word TSEGS0 (Z_to_bv 64 (tfx_popfree_head + 28)) = Some PW7. Proof. (img_case; vm_refl). Qed.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Theorem tfx_popfree_spec {imgk : img} : popfree_spec tfx_loaded_segments tfx_popfree_head.
Proof.
img_apply popfree_spec_of_code; [img_try (unfold tfx_popfree_head; img_lia) | img_try (img_exact PF0) | img_try (img_exact PF1) | img_try (img_exact PF2) | img_try (img_exact PF3) | img_try (img_exact PF4) | img_try (img_exact PF5) | img_try (img_exact PF6) | img_try (img_exact PF7)].
Qed.

End a.
