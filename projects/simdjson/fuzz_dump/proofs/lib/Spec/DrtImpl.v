(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes MonadX.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad Stdio SjModel DrtModel Target.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section DrtImpl.
Variable segs : list Segment.
Context {St ptr : Type}.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.
Local Notation implM := (Monad.implM segs).

Lemma drt_print_eq :
  drt_print ops = (ok <- mcho ;; if ok =? 0 then mret tt else drt_free_nulls ops).
Proof. reflexivity. Qed.

Lemma drt_free_nulls_eq :
  drt_free_nulls ops = (mret tt ;;; mret tt ;;; mret tt ;;; mret tt).
Proof. reflexivity. Qed.

Lemma implM_drt_gate_fail : forall {B} (rest : unit -> Monad.M St B) s Q ms,
  implM (rest tt) s Q ms -> implM (u <- drt_print ops ;; rest u) s Q ms.
Proof.
  intros B rest s Q ms H. rewrite drt_print_eq. apply implM_bind_assoc. apply (implM_chok segs 0). cbn [Z.eqb].
  apply implM_retb. exact H.
Qed.

Lemma implM_drt_gate_ok : forall {B} (rest : unit -> Monad.M St B) s Q ms,
  implM (u <- drt_free_nulls ops ;; rest u) s Q ms -> implM (u <- drt_print ops ;; rest u) s Q ms.
Proof.
  intros B rest s Q ms H. rewrite drt_print_eq. apply implM_bind_assoc. apply (implM_chok segs 1). cbn [Z.eqb Pos.eqb].
  exact H.
Qed.

Lemma implM_drt_free_nulls : forall {B} (rest : unit -> Monad.M St B) s Q ms,
  implM (rest tt) s Q ms -> implM (u <- drt_free_nulls ops ;; rest u) s Q ms.
Proof.
  intros B rest s Q ms H. rewrite drt_free_nulls_eq.
  do 3 (apply implM_bind_assoc; apply implM_retb). apply implM_retb. exact H.
Qed.

End DrtImpl.
