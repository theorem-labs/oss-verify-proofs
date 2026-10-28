(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YFk4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
#[local] Notation TSEGS0 := Asan.M.loaded_segments (only parsing).
Definition tfib_popfree_head : Z := 0x366c8.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Lemma PF0 : fetch_word TSEGS0 (Z_to_bv 64 tfib_popfree_head) = Some PW0. Proof. vm_refl. Qed.
Lemma PF1 : fetch_word TSEGS0 (Z_to_bv 64 (tfib_popfree_head + 4)) = Some PW1. Proof. vm_refl. Qed.
Lemma PF2 : fetch_word TSEGS0 (Z_to_bv 64 (tfib_popfree_head + 8)) = Some PW2. Proof. vm_refl. Qed.
Lemma PF3 : fetch_word TSEGS0 (Z_to_bv 64 (tfib_popfree_head + 12)) = Some PW3. Proof. vm_refl. Qed.
Lemma PF4 : fetch_word TSEGS0 (Z_to_bv 64 (tfib_popfree_head + 16)) = Some PW4. Proof. vm_refl. Qed.
Lemma PF5 : fetch_word TSEGS0 (Z_to_bv 64 (tfib_popfree_head + 20)) = Some PW5. Proof. vm_refl. Qed.
Lemma PF6 : fetch_word TSEGS0 (Z_to_bv 64 (tfib_popfree_head + 24)) = Some PW6. Proof. vm_refl. Qed.
Lemma PF7 : fetch_word TSEGS0 (Z_to_bv 64 (tfib_popfree_head + 28)) = Some PW7. Proof. vm_refl. Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem tfib_popfree_spec : popfree_spec Asan.M.loaded_segments tfib_popfree_head.
Proof.
apply popfree_spec_of_code; [unfold tfib_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.
Theorem tfib_popfree_loop_run : forall regs mem rom i e c s n,
getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
(0 <= i)%Z -> (i < n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
(0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
(forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 4 * (n - i))%Z ->
RiscvSemantics.store_ok TSEGS0 mem (Z_to_bv 64 (e - 4 * n + d)) m = true) ->
exists regs',
msteps TSEGS0 (mkst regs (Z_to_bv 64 tfib_popfree_head) mem rom)
(mkst regs' (Z_to_bv 64 (tfib_popfree_head + 32)) (pf_mem mem e c s i (Z.to_nat (n - i))) rom)
/\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
/\ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
/\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
/\ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
/\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
apply (popfree_loop_run TSEGS0 tfib_popfree_head); [unfold tfib_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.
End a.
