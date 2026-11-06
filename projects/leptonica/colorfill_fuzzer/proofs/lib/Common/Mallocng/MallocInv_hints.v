(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocInv_defs MallocInv_tables.
Import ListNotations.
Local Open Scope Z_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
Definition size_to_class_z (n : Z) : Z :=
  let m := (n + 3) / 16 in
  if m <? 10 then m else
  let m1 := m + 1 in
  let i := (Z.log2 m1 - 3) * 4 + 8 in
  let i1 := if size_class (i + 1) <? m1 then i + 2 else i in
  if size_class i1 <? m1 then i1 + 1 else i1.

(* [comment removed for export] *)
Fixpoint halvings (k : nat) (c : Z) : list Z :=
  match k with
  | O => [c]
  | S k' => if Z.even c then c :: halvings k' (c / 2) else [c]
  end.

(* [comment removed for export] *)
Fixpoint shrink (k : nat) (size c : Z) : Z :=
  match k with
  | O => c
  | S k' => if size * c <? 2^20 then c else shrink k' size (c / 2)
  end.

Definition cnt_base (sc : Z) : list Z :=
  if sc <? 9 then [small_cnt (3 * sc); small_cnt (3 * sc + 1); small_cnt (3 * sc + 2)]
  else halvings 8 (med_cnt (Z.land sc 3)).

Definition cnt_cands (sc : Z) : list Z :=
  map (shrink 40 (16 * size_class sc)) (cnt_base sc).

(* [comment removed for export] *)
Definition cnt1_of (size c : Z) : Z :=
  if c =? 1 then (if 2048 <? size + 16 then 1 else 2) else c.

(* [comment removed for export] *)
Definition nest_target (sc c : Z) : option Z :=
  let size := 16 * size_class sc in
  let c1 := cnt1_of size c in
  if size * c1 + 16 <=? 2048 then Some (size_to_class_z (size * c1 + 12)) else None.

Definition nest_rank (sc : Z) : Z :=
  if sc =? 15 then 1 else if sc =? 19 then 2 else if sc =? 23 then 3 else 0.

Definition chk_nest (sc : Z) : bool :=
  forallb (fun c => match nest_target sc c with
                    | None => true
                    | Some j => (nest_rank sc <? nest_rank j) && ((j =? 15) || (j =? 19) || (j =? 23))
                    end) (cnt_cands sc).

Lemma chk_nests : forallb chk_nest (Zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem nest_rank_ok : forall sc c j, 0 <= sc < 48 -> In c (cnt_cands sc) ->
  nest_target sc c = Some j -> nest_rank sc < nest_rank j /\ (j = 15 \/ j = 19 \/ j = 23).
Proof.
  intros sc c j Hsc Hc Hj.
  pose proof (proj1 (forallb_forall _ _) chk_nests sc (Zseq_In 48 0 sc ltac:(llia))) as H.
  unfold chk_nest in H. apply (proj1 (forallb_forall _ _)) with (x := c) in H; [| exact Hc].
  rewrite Hj in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.ltb_lt in H1. split; [exact H1|].
  apply Bool.orb_prop in H2. destruct H2 as [H2 | H2]; [apply Bool.orb_prop in H2; destruct H2 as [H2 | H2]|];
    apply Z.eqb_eq in H2; llia.
Qed.

(* [comment removed for export] *)
Definition chk_cnt_range (sc : Z) : bool := forallb (fun c => (1 <=? c) && (c <=? 32)) (cnt_cands sc).
Lemma chk_cnt_ranges : forallb chk_cnt_range (Zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition chk_cnt_span (sc : Z) : bool :=
  forallb (fun c => 16 * size_class sc * cnt1_of (16 * size_class sc) c <? 2^20) (cnt_cands sc).
Lemma chk_cnt_spans : forallb chk_cnt_span (Zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.

End WithLayout.
