(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HSymExec2 HSymExec2Sound HSymRun HSymDrive HSymDriveX HAgentLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import HPropExec.
Import SX2. Import SX2S.
Open Scope Z_scope.

Definition scF (e : Z) : Prop :=
  branch_taken BC_LTU (sext 64 (alu32 ALU_ADD (low32 (errno_ret e)) (low32 (Z_to_bv 64 0))))
               (Z_to_bv 64 18446744073709547521) = false.

Lemma scF_openat : forall e, In e openat_errnos -> scF e.
Proof.
  intros e He. unfold openat_errnos in He. cbn [In] in He.
  destruct He as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity.
Qed.

Lemma scF_ENAMETOOLONG : scF ENAMETOOLONG. Proof. vm_compute. reflexivity. Qed.

Lemma scF_ENOENT : scF ENOENT. Proof. vm_compute. reflexivity. Qed.

Lemma openat_errnos_range : forall e, In e openat_errnos -> (1 <= e <= 4095)%Z.
Proof.
  intros e He. unfold openat_errnos in He. cbn in He.
  unfold ENOMEM, EACCES, EMFILE, ENFILE in He. lia.
Qed.

Lemma errno_ret_range : forall e, (1 <= e <= 4095)%Z ->
  (2 ^ 64 - 4095 <= bv_unsigned (errno_ret e))%Z.
Proof. intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  replace ((- e) mod 2 ^ 64)%Z with (2 ^ 64 - e)%Z; [lia|].
  apply Z.mod_unique with (q := (-1)%Z); lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HSymExec2 HSymAux.
Definition regA : list HSymAux.sregion := [(SX2.SA (SX2.EVar 0) (-224), 176)]%Z.
Definition regU : list HSymAux.sregion := [(SX2.SA (SX2.EVar 0) (-128), 80)]%Z.
