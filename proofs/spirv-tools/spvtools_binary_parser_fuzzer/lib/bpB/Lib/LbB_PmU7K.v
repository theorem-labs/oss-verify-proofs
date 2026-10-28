(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec SymExec SymExec3 SymExec3Sound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Fixpoint zlist7 (a : Z) (n : nat) : list Z := match n with O => [] | S k => a :: zlist7 (a + 1) k end.
Lemma in_zlist7 : forall n a t, a <= t < a + Z.of_nat n -> In t (zlist7 a n).
Proof.
  induction n as [|n IH]; intros a t Ht; cbn [zlist7]; [lia|].
  destruct (Z.eq_dec a t) as [E|NE]; [left; exact E | right; apply IH; rewrite Nat2Z.inj_succ in Ht; lia].
Qed.

Definition SUBLEN : expr :=
  EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SLTU (EVar 11) (EAlu ALU_ADD (EVar 11) (ELit (-2)))) (ELit (-1))) (EAlu ALU_ADD (EVar 11) (ELit (-2))).

Lemma sublen_val : forall (E : env) n, edenot E (EVar 11) = Z_to_bv 64 n -> 3 <= n <= 48 ->
  edenot E SUBLEN = Z_to_bv 64 (n - 2).
Proof.
  intros E n E11 Hn. unfold SUBLEN. cbn [edenot]. cbn [edenot] in E11. rewrite E11. clear E11.
  pose proof (in_zlist7 46 3 n ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as Hin. clear Hn.
  cbn [zlist7 Z.add Pos.add Pos.succ] in Hin.
  repeat (destruct Hin as [<-|Hin]; [apply bv_eq; vm_compute; reflexivity|]). destruct Hin.
Qed.

Definition SUBPTR : expr := EAlu ALU_ADD (EVar 10) (ELit 8).
Lemma subptr_val : forall (E : env) p, edenot E (EVar 10) = Z_to_bv 64 p -> edenot E SUBPTR = Z_to_bv 64 (p + 8).
Proof.
  intros E p E10. unfold SUBPTR. cbn [edenot]. cbn [edenot] in E10. rewrite E10. apply SymExec.alu64_add_lit.
Qed.
