(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes MonadX.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim Monad Stdio SjModel PjModel Target AtpImpl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section PjImpl.
Variable segs : list Segment.
Context {St ptr : Type}.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.
Local Notation implM := (Monad.implM segs).

Definition chst : Type := (nat * Z * option ptr)%type.
Definition ch_fuel (c : chst) : nat := fst (fst c).
Definition ch_cap (c : chst) : Z := snd (fst c).
Definition ch_blk (c : chst) : option ptr := snd c.

Fixpoint pj_part (fuel : nat) (len cap : Z) (blk : option ptr) : Monad.M St chst :=
  match fuel with
  | O => mret (O, cap, blk)
  | S f =>
      z <- mcho ;;
      if chain_ok len cap z then
        b <- newnt ops z ;;
        del_opt ops blk ;;;
        pj_part f len z (Some b)
      else mret (S f, cap, blk)
  end.

Definition pj_grow1 (z : Z) (blk : option ptr) : Monad.M St ptr :=
  b <- newnt ops z ;; del_opt ops blk ;;; mret b.

Lemma pj_chain_O : forall len cap blk, pj_chain ops O len cap blk = mret blk.
Proof. reflexivity. Qed.
Lemma pj_chain_S : forall f len cap blk,
  pj_chain ops (S f) len cap blk
  = (z <- mcho ;; if chain_ok len cap z then b <- newnt ops z ;; del_opt ops blk ;;; pj_chain ops f len z (Some b) else mret blk).
Proof. reflexivity. Qed.
Lemma pj_part_O : forall len cap blk, pj_part O len cap blk = mret (O, cap, blk).
Proof. reflexivity. Qed.
Lemma pj_part_S : forall f len cap blk,
  pj_part (S f) len cap blk
  = (z <- mcho ;; if chain_ok len cap z then b <- newnt ops z ;; del_opt ops blk ;;; pj_part f len z (Some b) else mret (S f, cap, blk)).
Proof. reflexivity. Qed.
Lemma del_opt_some : forall p, del_opt ops (Some p) = del ops p.
Proof. reflexivity. Qed.
Lemma del_opt_none : del_opt ops None = mret tt.
Proof. reflexivity. Qed.

Lemma chain_ok_zero : forall len cap, 0 < cap -> chain_ok len cap 0 = false.
Proof. intros len cap H. unfold chain_ok. replace (2 * cap <=? 0) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. Qed.

Lemma implM_pj_part_stop : forall fuel len cap blk s (Q : chst -> St -> machine_state -> Prop) ms,
  0 < cap ->
  evt segs (Q (fuel, cap, blk) s) ms -> implM (pj_part fuel len cap blk) s Q ms.
Proof.
  intros [|f] len cap blk s Q ms HC H.
  - rewrite pj_part_O. apply implM_ret. exact H.
  - rewrite pj_part_S. apply (implM_chok segs 0). rewrite chain_ok_zero by exact HC. apply implM_ret. exact H.
Qed.

Lemma implM_pj_part_grow : forall f len cap blk z s (Q : chst -> St -> machine_state -> Prop) ms,
  chain_ok len cap z = true ->
  implM (b <- pj_grow1 z blk ;; pj_part f len z (Some b)) s Q ms ->
  implM (pj_part (S f) len cap blk) s Q ms.
Proof.
  intros f len cap blk z s Q ms HZ H. rewrite pj_part_S. apply (implM_chok segs z). rewrite HZ.
  unfold pj_grow1 in H. apply implM_bind_assoc_rev in H.
  eapply implM_bind_cong; [| exact H]. intros b s' ms' H'. cbn beta in H'.
  apply implM_bind_assoc_rev in H'.
  eapply implM_bind_cong; [| exact H']. intros u s'' ms'' H''. cbn beta in H''.
  exact H''.
Qed.

Lemma implM_pj_part_seq : forall fuel len cap blk s (Q : chst -> St -> machine_state -> Prop) ms,
  implM (c <- pj_part fuel len cap blk ;; pj_part (ch_fuel c) len (ch_cap c) (ch_blk c)) s Q ms ->
  implM (pj_part fuel len cap blk) s Q ms.
Proof.
  induction fuel as [|f IH]; intros len cap blk s Q ms H.
  - rewrite pj_part_O in H. exact H.
  - rewrite pj_part_S in H. apply implM_bind_assoc_rev in H. apply implM_chok_inv in H. destruct H as [z H].
    destruct (chain_ok len cap z) eqn:E.
    + rewrite pj_part_S. apply (implM_chok segs z). rewrite E.
      apply implM_bind_assoc_rev in H.
      eapply implM_bind_cong; [| exact H]. intros b s' ms' H'. cbn beta in H'.
      apply implM_bind_assoc_rev in H'.
      eapply implM_bind_cong; [| exact H']. intros u s'' ms'' H''. cbn beta in H''.
      apply IH. exact H''.
    + exact H.
Qed.

Lemma implM_pj_chain_part : forall {B} fuel len cap blk (K : option ptr -> Monad.M St B) s Q ms,
  implM (c <- pj_part fuel len cap blk ;; r <- pj_chain ops (ch_fuel c) len (ch_cap c) (ch_blk c) ;; K r) s Q ms ->
  implM (r <- pj_chain ops fuel len cap blk ;; K r) s Q ms.
Proof.
  intros B. induction fuel as [|f IH]; intros len cap blk K s Q ms H.
  - rewrite pj_part_O in H. exact H.
  - rewrite pj_part_S in H. apply implM_bind_assoc_rev in H. apply implM_chok_inv in H. destruct H as [z H].
    destruct (chain_ok len cap z) eqn:E.
    + rewrite pj_chain_S. apply implM_bind_assoc. apply (implM_chok segs z). rewrite E.
      apply implM_bind_assoc.
      apply implM_bind_assoc_rev in H.
      eapply implM_bind_cong; [| exact H]. intros b s' ms' H'. cbn beta in H'.
      apply implM_bind_assoc. apply implM_bind_assoc_rev in H'.
      eapply implM_bind_cong; [| exact H']. intros u s'' ms'' H''. cbn beta in H''.
      apply IH. exact H''.
    + exact H.
Qed.

Lemma implM_pj_chain_stop : forall {B} fuel len cap blk (K : option ptr -> Monad.M St B) s Q ms,
  0 < cap ->
  implM (K blk) s Q ms -> implM (r <- pj_chain ops fuel len cap blk ;; K r) s Q ms.
Proof.
  intros B [|f] len cap blk K s Q ms HC H.
  - rewrite pj_chain_O. apply implM_retb. exact H.
  - rewrite pj_chain_S. apply implM_bind_assoc. apply (implM_chok segs 0). rewrite chain_ok_zero by exact HC.
    apply implM_retb. exact H.
Qed.

Lemma implM_pj_chain_grow : forall {B} f len cap blk z (K : option ptr -> Monad.M St B) s Q ms,
  chain_ok len cap z = true ->
  implM (b <- pj_grow1 z blk ;; r <- pj_chain ops f len z (Some b) ;; K r) s Q ms ->
  implM (r <- pj_chain ops (S f) len cap blk ;; K r) s Q ms.
Proof.
  intros B f len cap blk z K s Q ms HZ H. rewrite pj_chain_S. apply implM_bind_assoc. apply (implM_chok segs z). rewrite HZ.
  apply implM_bind_assoc.
  unfold pj_grow1 in H. apply implM_bind_assoc_rev in H.
  eapply implM_bind_cong; [| exact H]. intros b s' ms' H'. cbn beta in H'.
  apply implM_bind_assoc. apply implM_bind_assoc_rev in H'.
  eapply implM_bind_cong; [| exact H']. intros u s'' ms'' H''. cbn beta in H''.
  exact H''.
Qed.

Lemma pj_print_eq : forall len,
  pj_print ops len
  = (ok <- mcho ;; if ok =? 0 then mret tt
                   else (blk <- pj_chain ops PJ_FUEL len PJ_INLINE None ;; del_opt ops blk ;;; pj_free_nulls ops)).
Proof. reflexivity. Qed.

Lemma implM_pj_gate_fail : forall {B} len (rest : unit -> Monad.M St B) s Q ms,
  implM (rest tt) s Q ms -> implM (u <- pj_print ops len ;; rest u) s Q ms.
Proof.
  intros B len rest s Q ms H. rewrite pj_print_eq. apply implM_bind_assoc. apply (implM_chok segs 0). cbn [Z.eqb].
  apply implM_retb. exact H.
Qed.

Lemma implM_pj_gate_ok : forall {B} len (rest : unit -> Monad.M St B) s Q ms,
  implM (blk <- pj_chain ops PJ_FUEL len PJ_INLINE None ;; u <- (del_opt ops blk ;;; pj_free_nulls ops) ;; rest u) s Q ms ->
  implM (u <- pj_print ops len ;; rest u) s Q ms.
Proof.
  intros B len rest s Q ms H. rewrite pj_print_eq. apply implM_bind_assoc. apply (implM_chok segs 1). cbn [Z.eqb Pos.eqb].
  apply implM_bind_assoc. exact H.
Qed.

End PjImpl.
