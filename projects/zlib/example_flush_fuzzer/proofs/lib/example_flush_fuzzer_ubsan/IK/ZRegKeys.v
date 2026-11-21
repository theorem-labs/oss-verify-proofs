(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK Require Import MstepsGrows.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition rkeys (t t' : tree word) : Prop := forall k, tget k t <> None -> tget k t' <> None.

Lemma rkeys_refl : forall t, rkeys t t.
Proof. intros t k H. exact H. Qed.


Lemma tget_tset_keep : forall {A} (p q : positive) (x : A) t,
  tget q t <> None -> tget q (tset p x t) <> None.
Proof.
  intros A p q x t H. destruct (Pos.eq_dec p q) as [<-|Hne].
  - rewrite tget_tset_same. discriminate.
  - rewrite tget_tset_other by exact Hne. exact H.
Qed.

Lemma rkeys_tset : forall t t' p x, rkeys t t' -> rkeys t (tset p x t').
Proof. intros t t' p x H k Hk. apply tget_tset_keep. apply H, Hk. Qed.

Definition ckeys (c0 c1 : core) : Prop := rkeys (c_regs c0) (c_regs c1).

Lemma ckeys_refl : forall c, ckeys c c.
Proof. intros c. apply rkeys_refl. Qed.
Lemma ckeys_rset : forall c0 r v c, ckeys c0 c -> ckeys c0 (rset r v c).
Proof.
  intros c0 r v c H. unfold rset. destruct (is_x0 r); [exact H|].
  unfold ckeys, with_regs, bvmap_set in *. cbn. apply rkeys_tset. exact H.
Qed.
Lemma ckeys_with_pc : forall c0 v c, ckeys c0 c -> ckeys c0 (with_pc v c).
Proof. intros c0 v c H. exact H. Qed.
Lemma ckeys_with_fcsr : forall c0 v c, ckeys c0 c -> ckeys c0 (with_fcsr v c).
Proof. intros c0 v c H. exact H. Qed.
Lemma ckeys_with_resv : forall c0 v c, ckeys c0 c -> ckeys c0 (with_resv v c).
Proof. intros c0 v c H. exact H. Qed.
Lemma ckeys_with_fregs : forall c0 f c, ckeys c0 c -> ckeys c0 (with_fregs f c).
Proof. intros c0 f c H. exact H. Qed.
Lemma ckeys_fset : forall c0 r v c, ckeys c0 c -> ckeys c0 (fset r v c).
Proof. intros c0 r v c H. exact H. Qed.
Lemma ckeys_fwrite : forall c0 fmt r v c, ckeys c0 c -> ckeys c0 (fwrite fmt r v c).
Proof. intros c0 fmt r v c H. unfold fwrite. destruct fmt; apply ckeys_fset; exact H. Qed.
Lemma ckeys_accrue : forall c0 fl c, ckeys c0 c -> ckeys c0 (accrue fl c).
Proof. intros c0 fl c H. exact H. Qed.
Lemma ckeys_inval_resv : forall c0 a c, ckeys c0 c -> ckeys c0 (inval_resv a c).
Proof.
  intros c0 a c H. unfold inval_resv. destruct (c_resv c) as [r|]; [|exact H].
  destruct (Z.eqb _ _); [apply ckeys_with_resv|]; exact H.
Qed.

End FXG.
#[local] Hint Resolve ckeys_refl ckeys_rset ckeys_with_pc ckeys_with_fcsr ckeys_with_resv ckeys_with_fregs
  ckeys_fset ckeys_fwrite ckeys_accrue ckeys_inval_resv : ckeys.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Fixpoint eff_all (P : core -> Prop) (t : eff) : Prop :=
  match t with
  | EDone c => P c
  | EIllegal _ | EDefinedIllegal _ | EEcall _ | EEbreak _ | EFault _ => True
  | ELoad n a k => forall v, eff_all P (k v)
  | EStore n a v k => eff_all P k
  end.

Lemma eff_all_load_val : forall P sz sgn a k,
  (forall v, eff_all P (k v)) -> eff_all P (load_val sz sgn a k).
Proof. intros P sz sgn a k H. destruct sz; cbn; intros; apply H. Qed.

Lemma eff_all_store_val : forall P sz a v k, eff_all P k -> eff_all P (store_val sz a v k).
Proof. intros P sz a v k H. destruct sz; cbn; exact H. Qed.

Lemma eff_all_exec_csr : forall c0 op rd x wr csr c,
  ckeys c0 c -> eff_all (ckeys c0) (exec_csr op rd x wr csr c).
Proof.
  intros c0 op rd x wr csr c H. unfold exec_csr.
  destruct (csr_slice csr) as [[lo len]|]; cbn; [|exact I].
  apply ckeys_rset. destruct wr; [apply ckeys_with_fcsr|]; exact H.
Qed.

End FXG.
Ltac keys_leaf := cbn [eff_all]; intros; eauto 12 with ckeys.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac keys_go :=
  cbn [eff_all];
  first
    [ exact I
    | match goal with
      | |- eff_all _ (match ?x with _ => _ end) => destruct x; keys_go
      | |- eff_all _ ((match ?x with _ => _ end) _) => destruct x; keys_go
      | |- eff_all _ (if ?x then _ else _) => destruct x; keys_go
      | |- eff_all _ (load_val _ _ _ _) => apply eff_all_load_val; intros; keys_go
      | |- eff_all _ (store_val _ _ _ _) => apply eff_all_store_val; keys_go
      | |- eff_all _ (exec_csr _ _ _ _ _ _) => apply eff_all_exec_csr; eauto 12 with ckeys
      | |- forall _, _ => intros; keys_go
      | |- ckeys _ (match ?x with _ => _ end) => destruct x; keys_go
      | |- ckeys _ _ => eauto 12 with ckeys
      end ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Section Keys.
Variable segs : list Segment.





End Keys.
End FXG.
