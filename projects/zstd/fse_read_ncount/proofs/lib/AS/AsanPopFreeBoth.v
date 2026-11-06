(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.zstd.fse_read_ncount.images Require Import AsanUbsan.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk AsanPopFree.
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
#[local] Notation BSEGS := AsanUbsan.M.loaded_segments (only parsing).
Definition both_popfree_head : Z := 0x37530.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Lemma PF0 : fetch_word BSEGS (Z_to_bv 64 both_popfree_head) = Some PW0. Proof. vm_refl. Qed.
Lemma PF1 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 4)) = Some PW1. Proof. vm_refl. Qed.
Lemma PF2 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 8)) = Some PW2. Proof. vm_refl. Qed.
Lemma PF3 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 12)) = Some PW3. Proof. vm_refl. Qed.
Lemma PF4 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 16)) = Some PW4. Proof. vm_refl. Qed.
Lemma PF5 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 20)) = Some PW5. Proof. vm_refl. Qed.
Lemma PF6 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 24)) = Some PW6. Proof. vm_refl. Qed.
Lemma PF7 : fetch_word BSEGS (Z_to_bv 64 (both_popfree_head + 28)) = Some PW7. Proof. vm_refl. Qed.
Theorem both_popfree_spec : popfree_spec AsanUbsan.M.loaded_segments both_popfree_head.
Proof.
apply popfree_spec_of_code; [unfold both_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.
