(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ShapeAlg Spec BigintSpec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Common Require Import MustExitOfShape.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition halts_codes : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma in_halts_codes_0 : In (exit_code 0) halts_codes.
Proof. left. reflexivity. Qed.
Lemma in_halts_codes_2 : In (exit_code 2) halts_codes.
Proof. right. left. reflexivity. Qed.
Lemma Forall_exit_ok_W : forall S ch s, Forall (ev_exit_ok S) (W ch s).
Proof.
intros S ch s. unfold W. induction s as [|b s IH]; cbn; constructor; [exact I | exact IH].
Qed.
Section FPX_1.
Context {fx : PropExec.FPState}.
Lemma exits_in_W_emit : forall S ch s T, exits_in S T -> exits_in S (t_emit (W ch s) T).
Proof. intros S ch s T HT. apply exits_in_emit; [apply Forall_exit_ok_W | exact HT]. Qed.
Lemma exits_in_die : forall msg fs, exits_in halts_codes (t_die msg fs).
Proof.
intros msg fs. unfold t_die. apply exits_in_W_emit. apply exits_in_exit. apply in_halts_codes_2.
Qed.
Lemma exits_in_exit0 : forall fs, exits_in halts_codes (t_exit (exit_code 0) fs).
Proof. intros fs. apply exits_in_exit. apply in_halts_codes_0. Qed.
Lemma exits_in_exit2 : forall fs, exits_in halts_codes (t_exit (exit_code 2) fs).
Proof. intros fs. apply exits_in_exit. apply in_halts_codes_2. Qed.
Ltac exits_in_struct :=
repeat first [ apply exits_in_die
| apply exits_in_exit0
| apply exits_in_exit2
| apply exits_in_W_emit
| match goal with |- exits_in _ (t_alt2 _ _) => apply exits_in_alt2 end
| match goal with |- exits_in _ (if ?c then _ else _) => destruct c end
| match goal with |- exits_in _ (match ?c with _ => _ end) => destruct c end ].
Lemma exits_in_bigint_t_body : forall data fs, exits_in halts_codes (BigintSpec.t_body data fs).
Proof. intros data fs. unfold BigintSpec.t_body. exits_in_struct. Qed.
Theorem exits_in_bigint_spec : forall argv fs, exits_in halts_codes (BigintSpec.spec argv fs).
Proof.
intros argv fs. unfold BigintSpec.spec.
repeat first [ apply exits_in_die
| apply exits_in_bigint_t_body
| match goal with |- exits_in _ (t_alt2 _ _) => apply exits_in_alt2 end
| match goal with |- exits_in _ (if ?c then _ else _) => destruct c end
| match goal with |- exits_in _ (match ?c with _ => _ end) => destruct c end ].
Qed.
Lemma exits_in_t_body : forall data fs, exits_in halts_codes (Spec.t_body data fs).
Proof.
intros data fs. unfold Spec.t_body.
repeat first [ apply exits_in_die
| apply exits_in_exit0
| apply exits_in_exit2
| apply exits_in_W_emit
| match goal with |- exits_in _ (t_alt2 _ _) => apply exits_in_alt2 end
| match goal with |- exits_in _ (t_exit (exit_code (if ?c then _ else _)) _) => destruct c end
| match goal with |- exits_in _ (if ?c then _ else _) => destruct c end
| match goal with |- exits_in _ (match ?c with _ => _ end) => destruct c end ].
Qed.
Lemma exits_in_t_opened : forall data fs, exits_in halts_codes (Spec.t_opened data fs).
Proof. intros data fs. unfold Spec.t_opened. apply exits_in_alt2; [apply exits_in_die | apply exits_in_t_body]. Qed.
Lemma exits_in_t_opened_dir : forall path fs, exits_in halts_codes (Spec.t_opened_dir path fs).
Proof. intros path fs. unfold Spec.t_opened_dir. apply exits_in_alt2; apply exits_in_die. Qed.
Theorem exits_in_spec : forall argv fs, exits_in halts_codes (Spec.spec argv fs).
Proof.
intros argv fs. unfold Spec.spec.
repeat first [ apply exits_in_die
| apply exits_in_t_opened
| apply exits_in_t_opened_dir
| match goal with |- exits_in _ (t_alt2 _ _) => apply exits_in_alt2 end
| match goal with |- exits_in _ (if ?c then _ else _) => destruct c end
| match goal with |- exits_in _ (match ?c with _ => _ end) => destruct c end ].
Qed.
End FPX_1.
