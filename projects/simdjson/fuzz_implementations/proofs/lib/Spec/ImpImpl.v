(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes MonadX.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Monad Stdio SjModel PjModel ImpModel Target AtpImpl PjImpl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section ImpImpl.
Variable segs : list Segment.
Context {St ptr : Type}.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.
Local Notation implM := (Monad.implM segs).

Lemma imp_print_eq : forall len,
  imp_print ops len
  = (ok <- mcho ;; if ok =? 0 then mret tt
                   else (blk <- pj_chain ops PJ_FUEL len PJ_INLINE None ;;
                         sblk <- pj_chain ops PJ_FUEL len IMP_SCAP0 None ;;
                         del_opt ops blk ;;;
                         cpy <- imp_copy ops len ;;
                         del_opt ops sblk ;;;
                         pj_free_nulls ops ;;;
                         del_opt ops cpy)).
Proof. reflexivity. Qed.

Lemma imp_static_some_eq : forall p, imp_static ops (Some p) = mret (Some p).
Proof. reflexivity. Qed.
Lemma imp_static_none_eq : imp_static ops None = (p <- newnt ops IMP_VEC ;; mret (Some p)).
Proof. reflexivity. Qed.
Lemma imp_copy_eq : forall len,
  imp_copy ops len = (S <- mcho ;; if copy_ok len S then (b <- newnt ops S ;; mret (Some b)) else mret None).
Proof. reflexivity. Qed.
Lemma pj_free_nulls_eq : pj_free_nulls ops = (mret tt ;;; mret tt ;;; mret tt ;;; mret tt).
Proof. reflexivity. Qed.

Lemma implM_imp_gate_fail : forall {B} len (rest : unit -> Monad.M St B) s Q ms,
  implM (rest tt) s Q ms -> implM (u <- imp_print ops len ;; rest u) s Q ms.
Proof.
  intros B len rest s Q ms H. rewrite imp_print_eq. apply implM_bind_assoc. apply (implM_chok segs 0). cbn [Z.eqb].
  apply implM_retb. exact H.
Qed.

Lemma implM_imp_gate_ok : forall {B} len (rest : unit -> Monad.M St B) s Q ms,
  implM (blk <- pj_chain ops PJ_FUEL len PJ_INLINE None ;;
         u <- (sblk <- pj_chain ops PJ_FUEL len IMP_SCAP0 None ;;
               del_opt ops blk ;;;
               cpy <- imp_copy ops len ;;
               del_opt ops sblk ;;;
               pj_free_nulls ops ;;;
               del_opt ops cpy) ;;
         rest u) s Q ms ->
  implM (u <- imp_print ops len ;; rest u) s Q ms.
Proof.
  intros B len rest s Q ms H. rewrite imp_print_eq. apply implM_bind_assoc. apply (implM_chok segs 1). cbn [Z.eqb Pos.eqb].
  apply implM_bind_assoc. exact H.
Qed.

Lemma implM_imp_gate_ok_cps : forall {B} len (rest : unit -> Monad.M St B) s Q ms,
  implM (blk <- pj_chain ops PJ_FUEL len PJ_INLINE None ;;
         sblk <- pj_chain ops PJ_FUEL len IMP_SCAP0 None ;;
         u1 <- del_opt ops blk ;;
         cpy <- imp_copy ops len ;;
         u2 <- del_opt ops sblk ;;
         u3 <- pj_free_nulls ops ;;
         (u4 <- del_opt ops cpy ;; rest u4)) s Q ms ->
  implM (u <- imp_print ops len ;; rest u) s Q ms.
Proof.
  intros B len rest s Q ms H. apply implM_imp_gate_ok.
  eapply implM_bind_cong; [| exact H]. intros blk s1 ms1 H1. cbn beta in H1.
  apply implM_bind_assoc. eapply implM_bind_cong; [| exact H1]. intros sblk s2 ms2 H2. cbn beta in H2.
  apply implM_bind_assoc. eapply implM_bind_cong; [| exact H2]. intros u1 s3 ms3 H3. cbn beta in H3.
  apply implM_bind_assoc. eapply implM_bind_cong; [| exact H3]. intros cpy s4 ms4 H4. cbn beta in H4.
  apply implM_bind_assoc. eapply implM_bind_cong; [| exact H4]. intros u2 s5 ms5 H5. cbn beta in H5.
  apply implM_bind_assoc. eapply implM_bind_cong; [| exact H5]. intros u3 s6 ms6 H6. cbn beta in H6.
  exact H6.
Qed.

Lemma implM_imp_static_some : forall {B} p (rest : option ptr -> Monad.M St B) s Q ms,
  implM (rest (Some p)) s Q ms -> implM (v' <- imp_static ops (Some p) ;; rest v') s Q ms.
Proof. intros B p rest s Q ms H. rewrite imp_static_some_eq. apply implM_retb. exact H. Qed.

Lemma implM_imp_static_none : forall {B} (rest : option ptr -> Monad.M St B) s Q ms,
  implM (p <- newnt ops IMP_VEC ;; rest (Some p)) s Q ms -> implM (v' <- imp_static ops None ;; rest v') s Q ms.
Proof.
  intros B rest s Q ms H. rewrite imp_static_none_eq. apply implM_bind_assoc.
  eapply implM_bind_cong; [| exact H]. intros p s' ms' H'. cbn beta in H'. apply implM_retb. exact H'.
Qed.

Lemma implM_imp_copy_some : forall {B} len z (rest : option ptr -> Monad.M St B) s Q ms,
  copy_ok len z = true ->
  implM (b <- newnt ops z ;; rest (Some b)) s Q ms -> implM (c <- imp_copy ops len ;; rest c) s Q ms.
Proof.
  intros B len z rest s Q ms HZ H. rewrite imp_copy_eq. apply implM_bind_assoc. apply (implM_chok segs z). rewrite HZ.
  apply implM_bind_assoc. eapply implM_bind_cong; [| exact H]. intros b s' ms' H'. cbn beta in H'. apply implM_retb. exact H'.
Qed.

Lemma implM_imp_copy_none : forall {B} len (rest : option ptr -> Monad.M St B) s Q ms,
  implM (rest None) s Q ms -> implM (c <- imp_copy ops len ;; rest c) s Q ms.
Proof.
  intros B len rest s Q ms H. rewrite imp_copy_eq. apply implM_bind_assoc. apply (implM_chok segs 0).
  replace (copy_ok len 0) with false by (unfold copy_ok; reflexivity). apply implM_retb. exact H.
Qed.

Lemma implM_pj_free_nulls : forall {B} (rest : unit -> Monad.M St B) s Q ms,
  implM (rest tt) s Q ms -> implM (u <- pj_free_nulls ops ;; rest u) s Q ms.
Proof.
  intros B rest s Q ms H. rewrite pj_free_nulls_eq.
  do 3 (apply implM_bind_assoc; apply implM_retb). apply implM_retb. exact H.
Qed.

Lemma implM_del_opt_none : forall {B} (rest : unit -> Monad.M St B) s Q ms,
  implM (rest tt) s Q ms -> implM (u <- del_opt ops None ;; rest u) s Q ms.
Proof. intros B rest s Q ms H. cbn [del_opt]. apply implM_retb. exact H. Qed.
Lemma implM_del_opt_some : forall {B} p (rest : unit -> Monad.M St B) s Q ms,
  implM (u <- del ops p ;; rest u) s Q ms -> implM (u <- del_opt ops (Some p) ;; rest u) s Q ms.
Proof. intros B p rest s Q ms H. cbn [del_opt]. exact H. Qed.

End ImpImpl.
