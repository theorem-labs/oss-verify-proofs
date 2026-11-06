(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.

From OSSVerify.Proofs.openssl.pem.lib.Common Require Import StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.openssl.pem.lib.Cls Require Import ClsMeLite ClsStartupDefs ClsStartup Cls_code_11350_12078.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.




Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)


Lemma must_exit_with_scfg_unfold : forall cfg code segs pc ph sp brk0 mbase rnd lim inp,
  must_exit_with_scfg cfg code (mkImage segs pc ph) lim (mkEntry sp brk0 mbase rnd) inp
  = must_exit_at_cfg cfg segs code (init_config segs pc ph sp brk0 mbase rnd lim inp).
Proof. reflexivity. Qed.

Section MainThm.
  Variable inp : ProcInput.
  Variables (sp brk0 mbase : word) (rdraw : EntryDraw).
  Hypothesis Hvi : valid_input inp.


  Lemma Hva : valid_argv (in_argv inp). Proof. destruct Hvi as (H & _). exact H. Qed.
  Lemma Hve : valid_envp (in_envp inp). Proof. destruct Hvi as (_ & H & _). exact H. Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End MainThm.
(* [comment removed for export] *)




Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
