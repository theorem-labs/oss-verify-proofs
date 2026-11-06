(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

Definition A_IMG_END : Z := 0x603000.          (* [comment removed for export] *)
Definition A_LOWAPP_END : Z := 0x7fff7000.     (* [comment removed for export] *)
Definition A_HIGH_BEG : Z := 0x10007fff8000.   (* [comment removed for export] *)

Definition placed (X n : Z) : Prop :=
  A_IMG_END <= X /\ X + n <= alloc_ceiling /\ (X + n <= A_LOWAPP_END \/ A_HIGH_BEG <= X).

Lemma placed_high : forall X n, A_HIGH_BEG <= X -> X + n <= alloc_ceiling -> placed X n.
Proof. aceil. intros X n H1 H2. unfold placed, A_IMG_END, A_HIGH_BEG in *. split; [lia|]. split; [exact H2|]. right; exact H1. Qed.

Lemma placed_low : forall X n, A_IMG_END <= X -> X + n <= A_LOWAPP_END -> placed X n.
Proof. aceil.
  intros X n H1 H2. pose proof alloc_ceiling_range as C. unfold placed, A_IMG_END, A_LOWAPP_END in *.
  split; [exact H1|]. split; [lia|]. left; exact H2.
Qed.

Lemma placed_sub : forall X n Y k, placed X n -> X <= Y -> Y + k <= X + n -> placed Y k.
Proof. aceil. intros X n Y k (P1 & P2 & P3) HY HK. unfold placed in *. lia. Qed.

(* [comment removed for export] *)
Lemma placed_num : forall X n, placed X n -> 0 <= n ->
  0x603000 <= X /\ X + n <= 0x7fffff800000 /\ (X + n <= 0x7fff7000 \/ 0x10007fff8000 <= X).
Proof. aceil.
  intros X n (P1 & P2 & P3) Hn. pose proof alloc_ceiling_range as C.
  unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in *. lia.
Qed.

(* [comment removed for export] *)
Lemma placed_shadow : forall X n, placed X n -> 0 <= n ->
  (0x800b8600 <= 0x7fff8000 + X / 8 /\ 0x7fff8000 + (X + n) / 8 <= 0x8fff6e00)
  \/ (0x2008fff7000 <= 0x7fff8000 + X / 8 /\ 0x7fff8000 + (X + n) / 8 <= 0x10007fef8000).
Proof. aceil.
  intros X n P Hn. pose proof (placed_num X n P Hn) as (Q1 & Q2 & Q3). clear P.
  destruct Q3 as [L|H]; [left|right]; (split; [Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia]).
Qed.

(* [comment removed for export] *)
Definition placed_s (X n : Z) : Prop :=
  0x1000 <= X /\ X + n <= alloc_ceiling /\ (X + n <= 0x10000 \/ A_IMG_END <= X) /\ (X + n <= A_LOWAPP_END \/ A_HIGH_BEG <= X).

Lemma placed_placed_s : forall X n, placed X n -> placed_s X n.
Proof. aceil. intros X n (P1 & P2 & P3). unfold placed_s, A_IMG_END in *. repeat split; try lia. Qed.

Lemma placed_s_num : forall X n, placed_s X n -> 0 <= n ->
  0x1000 <= X /\ X + n <= 0x7fffff800000 /\ (X + n <= 0x10000 \/ 0x603000 <= X) /\ (X + n <= 0x7fff7000 \/ 0x10007fff8000 <= X).
Proof. aceil.
  intros X n (P1 & P2 & P3 & P4) Hn. pose proof alloc_ceiling_range as C.
  unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in *. lia.
Qed.
End RC__1.

(* [comment removed for export] *)
Ltac plopen H :=
  lazymatch type of H with
  | placed_s _ _ =>
      let a := fresh H "i" in let b := fresh H "c" in let c := fresh H "g" in let d := fresh H "s" in
      destruct H as (a & b & c & d); unfold A_IMG_END in c; unfold A_LOWAPP_END, A_HIGH_BEG in d
  | _ =>
      let a := fresh H "i" in let b := fresh H "c" in let c := fresh H "s" in
      destruct H as (a & b & c); unfold A_IMG_END in a; unfold A_LOWAPP_END, A_HIGH_BEG in c
  end.
