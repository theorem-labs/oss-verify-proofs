(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSZ.

Definition sz64 (m : Z) : Z :=
  bv_unsigned (mul_div Instr.M_MUL (Z_to_bv 64 (-3689348814741910323)) (alu64 Instr.ALU_SRA (Z_to_bv 64 m) (Z_to_bv 64 3))).
Definition sz32 (m : Z) : Z :=
  bv_unsigned (sext 64 (mul_div Instr.M_MUL (low32 (alu64 Instr.ALU_SRL (Z_to_bv 64 m) (Z_to_bv 64 3))) (low32 (Z_to_bv 64 18446744072850558157)))).

Lemma sz_tab : forallb (fun n => Z.eqb (sz64 (40 * Z.of_nat n)) (Z.of_nat n) && Z.eqb (sz32 (40 * Z.of_nat n)) (Z.of_nat n)) (seq 0 1026) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sz_ok n : 0 <= n <= 1025 -> sz64 (40 * n) = n /\ sz32 (40 * n) = n.
Proof.
  intros Hn. pose proof sz_tab as T. rewrite forallb_forall in T.
  specialize (T (Z.to_nat n) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in T by lia.
  apply andb_prop in T. destruct T as [A B]. apply Z.eqb_eq in A. apply Z.eqb_eq in B. split; assumption.
Qed.

Lemma size64 m n : m = 40 * n -> 0 <= n <= 1025 ->
  bv_unsigned (mul_div Instr.M_MUL (Z_to_bv 64 (-3689348814741910323)) (alu64 Instr.ALU_SRA (Z_to_bv 64 m) (Z_to_bv 64 3))) = n.
Proof. intros -> Hn. exact (proj1 (sz_ok n Hn)). Qed.
Lemma size32 m n : m = 40 * n -> 0 <= n <= 1025 ->
  bv_unsigned (sext 64 (mul_div Instr.M_MUL (low32 (alu64 Instr.ALU_SRL (Z_to_bv 64 m) (Z_to_bv 64 3))) (low32 (Z_to_bv 64 18446744072850558157)))) = n.
Proof. intros -> Hn. exact (proj2 (sz_ok n Hn)). Qed.

End PNSZ.
