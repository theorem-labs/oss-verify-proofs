(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
#[local] Notation TSEGS0 := AsanUbsan.M.loaded_segments (only parsing).
Definition trb_popfree_head : Z := 0x36e20.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Lemma PF0 : fetch_word TSEGS0 (Z_to_bv 64 trb_popfree_head) = Some PW0. Proof. vm_refl. Qed.
Lemma PF1 : fetch_word TSEGS0 (Z_to_bv 64 (trb_popfree_head + 4)) = Some PW1. Proof. vm_refl. Qed.
Lemma PF2 : fetch_word TSEGS0 (Z_to_bv 64 (trb_popfree_head + 8)) = Some PW2. Proof. vm_refl. Qed.
Lemma PF3 : fetch_word TSEGS0 (Z_to_bv 64 (trb_popfree_head + 12)) = Some PW3. Proof. vm_refl. Qed.
Lemma PF4 : fetch_word TSEGS0 (Z_to_bv 64 (trb_popfree_head + 16)) = Some PW4. Proof. vm_refl. Qed.
Lemma PF5 : fetch_word TSEGS0 (Z_to_bv 64 (trb_popfree_head + 20)) = Some PW5. Proof. vm_refl. Qed.
Lemma PF6 : fetch_word TSEGS0 (Z_to_bv 64 (trb_popfree_head + 24)) = Some PW6. Proof. vm_refl. Qed.
Lemma PF7 : fetch_word TSEGS0 (Z_to_bv 64 (trb_popfree_head + 28)) = Some PW7. Proof. vm_refl. Qed.
Local Instance asanreflect_fx : YK11.FPState := YK11.fx0.
Section a. Context {rc : YN05.RunCeil}.
Theorem trb_popfree_spec : popfree_spec AsanUbsan.M.loaded_segments trb_popfree_head.
Proof.
apply popfree_spec_of_code; [unfold trb_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.

End a.
