(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the write-certified stack window). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import RT_iface.
From OSSVerify.Proofs.openssl.pem.lib.A Require Export D_agree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* STACK_WOK is spelled in RT_ibase as [STACK_WIN - StoreOk.stack_window_reach] so that the
   number lives in exactly one place, but [StoreOk] is only Required along the chain and not
   Imported here, so [unfold stack_window_reach] has no name to resolve in the D_* files and
   [lia] sees an opaque atom.  This lemma closes that by conversion (the kernel does not need
   the name), and the D_* [ul] tactics [pose proof] it, which gives [lia] the atom's value as
   a linear equation without unfolding STACK_WOK anywhere. *)
Lemma STACK_WOK_val : STACK_WOK = 6144513.
Proof. reflexivity. Qed.

(* The D_iface / D_libiface / D_libiface_pem contracts carry a side condition
   [rt_sp0 RT Σ - STACK_WIN <= lo] on the abstract [lo] they are instantiated at.  While
   lo WAS the mapping floor that goal was [x <= x], which [try reflexivity] closed through
   Z.le's Reflexive instance, so it never appeared in a bullet.  At the write-certified
   floor it is a real, and easier, goal -- so without this it would silently SHIFT every
   bullet list that follows such an [apply].  [try exact (win_le_wok _)] beside the
   [try reflexivity; try assumption] restores the old shape; its type is specific enough
   that it can close nothing else. *)
Lemma win_le_wok : forall z : Z, z - STACK_WIN <= z - STACK_WOK.
Proof. intro z. pose proof STACK_WOK_val. unfold STACK_WIN. lia. Qed.

Lemma agree_of_pres : forall live frames sp m m' (P : Z -> Prop),
  rt_pres live frames sp m m' -> (forall x, P x -> aclient live frames sp x) -> agree_on P m m'.
Proof. intros live frames sp m m' P H HP a Ha. exact (H a (HP _ Ha)). Qed.

Lemma agree_of_pres_fp : forall live frames sp W m m' (P : Z -> Prop),
  rt_pres_fp live frames sp W m m' -> (forall x, P x -> aclient live frames sp x /\ outside W x) -> agree_on P m m'.
Proof. intros live frames sp W m m' P H HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (H a H1 H2). Qed.

Lemma agree_of_pres_ex : forall live frames sp d n m m' (P : Z -> Prop),
  rt_pres_ex live frames sp d n m m' -> (forall x, P x -> aclient live frames sp x /\ ~ (d <= x < d + n)) -> agree_on P m m'.
Proof. intros live frames sp d n m m' P H HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (H a H1 H2). Qed.

