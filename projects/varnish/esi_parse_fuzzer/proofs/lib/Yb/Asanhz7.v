(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition byte_ok (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some _ => true | None => false end.

(* [comment removed for export] *)
Fixpoint scanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_ok s base
      else let h := N.div2 n in (scanN s f base h && scanN s f (base + h) (n - h))%bool
  end.

Lemma scanN_sound : forall s fuel base n,
  scanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N <> None.
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [scanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_ok in H.
      destruct (hex_byte_at s base); [discriminate|discriminate].
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

(* [comment removed for export] *)
Lemma segment_byte_at_some1 : forall s (n : N) (off : N),
  scanN s 64 0 n = true ->
  (n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N ->
  (Z.of_N off < Z.of_N n)%Z ->
  segment_byte_at [s] off <> None.
Proof.
  intros s n off Hs Hn Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true
    by (symmetry; apply N.ltb_lt; lia).
  exact (scanN_sound s 64 0 n Hs off ltac:(lia)).
Qed.
