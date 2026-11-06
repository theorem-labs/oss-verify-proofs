(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpSdKit.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.

(* [comment removed for export] *)
Definition isite_b (segs : list Segment) (a q : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 a), fetch_word segs (Z_to_bv 64 q) with
  | Some w1, Some w2 => Z.eqb (bv_unsigned w1) (bv_unsigned w2)
  | _, _ => false
  end.

Lemma isite_b_ok : forall segs a q, isite_b segs a q = true -> isite segs a q.
Proof.
  intros segs a q. unfold isite_b, isite.
  destruct (fetch_word segs (Z_to_bv 64 a)) as [w1|]; [|discriminate].
  destruct (fetch_word segs (Z_to_bv 64 q)) as [w2|]; [|discriminate].
  intros H. apply Z.eqb_eq in H. apply bv_eq in H. subst w2. exists w1. split; reflexivity.
Qed.

Fixpoint same_code_b (segs : list Segment) (p q : Z) (n : nat) : bool :=
  match n with O => true | S n' => isite_b segs p q && same_code_b segs (p + 4) (q + 4) n' end.

Lemma same_code_b_ok : forall segs n p q, same_code_b segs p q n = true -> same_code segs p q n.
Proof.
  intros segs n. induction n as [|n IH]; intros p q H; [exact I|].
  cbn [same_code_b] in H. apply andb_prop in H. destruct H as [H0 H]. split.
  - apply isite_b_ok. exact H0.
  - apply IH. exact H.
Qed.

(* [comment removed for export] *)
Ltac same_code_tac_orig :=
  cbn [same_code]; repeat match goal with |- _ /\ _ => split end; try exact I;
  lazymatch goal with
  | |- isite ?segs ?a ?q =>
      let aa := eval vm_compute in a in let qq := eval vm_compute in q in
      change (isite segs aa qq);
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 qq)) in
      lazymatch fw with Some ?w => exists w; split; vm_compute; reflexivity end
  end.
Ltac same_code_tac_fast :=
  first [ lazymatch goal with
          | |- same_code ?segs ?p ?q ?n =>
              exact (same_code_b_ok segs n p q (@eq_refl bool true <: same_code_b segs p q n = true))
          end
        | same_code_tac_orig ].
