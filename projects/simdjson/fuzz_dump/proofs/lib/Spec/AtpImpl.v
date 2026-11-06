(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes MonadX.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad Stdio SjModel AtpModel Target.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Section AtpImpl.
Variable segs : list Segment.
Context {St ptr : Type}.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.
Local Notation implM := (Monad.implM segs).

Lemma vpushes_O : forall v, vpushes ops O v = mret v.
Proof. reflexivity. Qed.
Lemma vpushes_S : forall n v, vpushes ops (S n) v = (v' <- vpush ops v ;; vpushes ops n v').
Proof. reflexivity. Qed.
Lemma atp_walk_nil : atp_walk ops [] = mret tt.
Proof. reflexivity. Qed.
Lemma atp_walk_cons : forall k rest,
  atp_walk ops (k :: rest)
  = (z <- mcho ;; if z =? 0 then mret tt
                  else ((if seg_alloc z k then p <- newnt ops (str_sz (zlength k)) ;; del ops p else mret tt) ;;; atp_walk ops rest)).
Proof. reflexivity. Qed.
Lemma newnt_eq : forall n, newnt ops n = (r <- raw_malloc n ;; match r with Some p => mret p | None => munr end).
Proof. reflexivity. Qed.
Lemma del_eq : forall p, del ops p = raw_free p.
Proof. reflexivity. Qed.

Lemma implM_atp_gate_fail : forall {B} (rest : unit -> Monad.M St B) segsl s Q ms,
  implM (rest tt) s Q ms ->
  implM (ok <- mcho ;; u <- (if ok =? 0 then mret tt else atp_walk ops segsl) ;; rest u) s Q ms.
Proof.
  intros B rest segsl s Q ms H. apply (implM_chok segs 0). cbn [Z.eqb]. apply implM_retb. exact H.
Qed.

Lemma implM_atp_gate_ok : forall {B} (rest : unit -> Monad.M St B) segsl s Q ms,
  implM (u <- atp_walk ops segsl ;; rest u) s Q ms ->
  implM (ok <- mcho ;; u <- (if ok =? 0 then mret tt else atp_walk ops segsl) ;; rest u) s Q ms.
Proof.
  intros B rest segsl s Q ms H. apply (implM_chok segs 1). cbn [Z.eqb Pos.eqb]. exact H.
Qed.

Lemma implM_atp_walk_stop : forall segsl s (Q : unit -> St -> machine_state -> Prop) ms,
  evt segs (Q tt s) ms -> implM (atp_walk ops segsl) s Q ms.
Proof.
  intros [|k rest] s Q ms H.
  - rewrite atp_walk_nil. apply implM_ret. exact H.
  - rewrite atp_walk_cons. apply (implM_chok segs 0). cbn [Z.eqb]. apply implM_ret. exact H.
Qed.

Lemma implM_atp_walk_plain : forall k rest s Q ms,
  implM (atp_walk ops rest) s Q ms -> implM (atp_walk ops (k :: rest)) s Q ms.
Proof.
  intros k rest s Q ms H. rewrite atp_walk_cons. apply (implM_chok segs 1). cbn [Z.eqb Pos.eqb seg_alloc andb].
  apply implM_retb. exact H.
Qed.

Lemma implM_atp_walk_string : forall k rest s Q ms,
  has_tilde k = true -> SSO_MAX < zlength k ->
  implM (p <- newnt ops (str_sz (zlength k)) ;; del ops p ;;; atp_walk ops rest) s Q ms ->
  implM (atp_walk ops (k :: rest)) s Q ms.
Proof.
  intros k rest s Q ms Ht HL H. rewrite atp_walk_cons. apply (implM_chok segs 2). unfold seg_alloc.
  rewrite Ht. replace (SSO_MAX <? zlength k) with true by (symmetry; apply Z.ltb_lt; exact HL). cbn [Z.eqb Pos.eqb andb].
  apply implM_bind_assoc. exact H.
Qed.

Lemma implM_atp_walk_stop_k : forall {B} segsl (c : unit -> Monad.M St B) s Q ms,
  implM (c tt) s Q ms -> implM (u <- atp_walk ops segsl ;; c u) s Q ms.
Proof.
  intros B [|k rest] c s Q ms H.
  - rewrite atp_walk_nil. apply implM_retb. exact H.
  - rewrite atp_walk_cons. apply implM_bind_assoc. apply (implM_chok segs 0). cbn [Z.eqb]. apply implM_retb. exact H.
Qed.

Lemma implM_bind_cong : forall {A B} (m : Monad.M St A) (k1 k2 : A -> Monad.M St B) s Q ms,
  (forall a s' ms', implM (k1 a) s' Q ms' -> implM (k2 a) s' Q ms') ->
  implM (mbind m k1) s Q ms -> implM (mbind m k2) s Q ms.
Proof.
  intros A B m k1 k2 s Q ms HK H. unfold Monad.implM, mbind, ebind in *.
  eapply impl_bind_cong; [| exact H]. intros [|[a s']] ms' H'; cbn [fst snd] in *; [exact H'| apply HK; exact H'].
Qed.

Lemma implM_bind_assoc_rev : forall {A B C} (m : Monad.M St A) (g : A -> Monad.M St B) (f : B -> Monad.M St C) s Q ms,
  implM (mbind (mbind m g) f) s Q ms -> implM (mbind m (fun a => mbind (g a) f)) s Q ms.
Proof.
  intros A B C m g f s Q ms H. unfold Monad.implM, mbind, ebind in *.
  apply impl_bind_inv in H. apply impl_bind_inv in H.
  eapply impl_bind; [exact H|]. intros [|[a s']] ms' H'; cbn [fst snd] in *.
  - cbn in H'. cbn. eapply evt_cut; [exact H'|]. intros ms'' H''. exact H''.
  - eapply impl_bind; [exact H'|]. intros r ms'' H''. exact H''.
Qed.

Lemma implM_vpushes_split : forall {B} a b v (c : vec -> Monad.M St B) s Q ms,
  implM (v1 <- vpushes ops a v ;; v2 <- vpushes ops b v1 ;; c v2) s Q ms ->
  implM (v2 <- vpushes ops (a + b) v ;; c v2) s Q ms.
Proof.
  intros B a. induction a as [|a IH]; intros b v c s Q ms H.
  - cbn [Nat.add]. rewrite vpushes_O in H. exact H.
  - cbn [Nat.add]. rewrite vpushes_S. rewrite vpushes_S in H.
    apply implM_bind_assoc. apply implM_bind_assoc_rev in H.
    eapply implM_bind_cong; [| exact H]. intros v' s' ms' H'. cbn beta in H'. apply IH. exact H'.
Qed.

End AtpImpl.
