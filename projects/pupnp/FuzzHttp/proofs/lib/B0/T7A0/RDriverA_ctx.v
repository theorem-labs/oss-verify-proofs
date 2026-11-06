(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import Stdio_base Printf_lib Stdio_iface RDriverA_kit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Definition RATPA : Z := 0x5e75b0.

Section AtMainAddrs.
  Variables (sp0 : word) (argv envp : list (list byte)).
  Notation usp0 := (bv_unsigned sp0).
  Definition envp_addr : Z := (usp0 + 8 * (argc argv + 2))%Z.
  Definition auxv_addr : Z := (usp0 + 8 * (argc argv + envc envp + 3))%Z.
End AtMainAddrs.

Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATPA).

  Definition LO : Z := usp0 - 8388608.

  Definition MFRAME (mm : mem) (pad : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells asegs mm (usp0 + -128)
      [CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (Z_to_bv 64 (envp_addr sp0 argv)); C8 (Z_to_bv 64 0x8605c);
       C8 (Z_to_bv 64 (argc argv)); C8 (Z_to_bv 64 (usp0 + 8)); C8 (Z_to_bv 64 0x94fe8)].
End CTX.

Definition stdout_addr (a : Z) : Prop := (0xaf818 <= a < 0xaf900) \/ (0x607cc0 <= a < 0x6080c0).
Definition stderr_addr (a : Z) : Prop := 0xaf728 <= a < 0xaf810.
Definition stdin_addr (a : Z) : Prop := 0xaf908 <= a < 0xaf9f0.

Lemma stdout_file_agree : forall (P : Z -> Prop) m m' so,
  gagree_on P m m' -> (forall a, stdout_addr a -> P a) -> stdout_file m so -> stdout_file m' so.
Proof.
  intros P m m' so AG HP (flags & mode & tail & bufbytes & F1 & F2 & F3 & F4 & F5 & F6).
  exists flags, mode, tail, bufbytes. split; [| split; [exact F2| split; [| split; [exact F4| split; [exact F5| exact F6]]]]].
  - eapply rw_cells_gagree; [exact AG| exact F1|]. intros a Ha. apply HP. left. cbn in Ha. lia.
  - eapply rw_cells_gagree; [exact AG| exact F3|]. intros a Ha. apply HP. right. cbn in Ha. lia.
Qed.

Lemma stderr_wfile0_agree : forall (P : Z -> Prop) m m',
  gagree_on P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof.
  intros P m m' AG HP (flags & mode & e & wend & tail & F1 & F2 & F3 & F4).
  exists flags, mode, e, wend, tail. split; [| split; [exact F2| split; [exact F3| exact F4]]].
  eapply rw_cells_gagree; [exact AG| exact F1|]. intros a Ha. apply HP. unfold stderr_addr. cbn in Ha. lia.
Qed.

Lemma stdin_file_agree : forall (P : Z -> Prop) m m',
  gagree_on P m m' -> (forall a, stdin_addr a -> P a) -> stdin_file m -> stdin_file m'.
Proof.
  intros P m m' AG HP H. unfold stdin_file in *.
  eapply rw_cells_gagree; [exact AG| exact H|]. intros a Ha. apply HP. unfold stdin_addr. cbn in Ha. lia.
Qed.

Lemma stdout_file_munch : forall W m m' so, munch W m m' -> wmono asegs m m' -> (forall a, stdout_addr a -> outside W a) -> stdout_file m so -> stdout_file m' so.
Proof. intros W m m' so MU WM HW. apply (stdout_file_agree _ _ _ _ (gagree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma stderr_wfile0_munch : forall W m m', munch W m m' -> wmono asegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof. intros W m m' MU WM HW. apply (stderr_wfile0_agree _ _ _ (gagree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma stdin_file_munch : forall W m m', munch W m m' -> wmono asegs m m' -> (forall a, stdin_addr a -> outside W a) -> stdin_file m -> stdin_file m'.
Proof. intros W m m' MU WM HW. apply (stdin_file_agree _ _ _ (gagree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
