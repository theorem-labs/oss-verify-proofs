(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac natlit_is_pos_lit p :=
  lazymatch p with xH => idtac | xO ?q => natlit_is_pos_lit q | xI ?q => natlit_is_pos_lit q end.

Ltac natlen_ctx :=
  repeat match goal with
  | H : @eq nat (@length _ _) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ?k)))))))))))))))) |- _ =>
      let K := constr:(S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k)))))))))))))))) in
      let p := eval vm_compute in (Pos.of_nat K) in
      natlit_is_pos_lit p;
      change K with (Pos.to_nat p) in H
  end.

Ltac natlit_hyp_core H :=
  repeat (lazymatch type of H with
          | context [Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ?k))))))))))))))))] =>
              let K := constr:(S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k)))))))))))))))) in
              let z := eval vm_compute in (Z.of_nat K) in
              lazymatch z with Zpos ?p => natlit_is_pos_lit p end;
              change (Z.of_nat K) with z in H
          | context [S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ?k)))))))))))))))] =>
              let K := constr:(S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k)))))))))))))))) in
              let p := eval vm_compute in (Pos.of_nat K) in
              natlit_is_pos_lit p;
              change K with (Pos.to_nat p) in H
          end).
Tactic Notation "natlit_hyp" ident(H) := first [ natlit_hyp_core H | idtac ].

(* [comment removed for export] *)
Goal forall (l : list nat) (a : Z), length l = 257%nat -> (0 <= a /\ a + 4 * Z.of_nat 257%nat <= 2^64)%Z ->
  (Z.of_nat (length l) < 300 /\ a < 2^64)%Z.
Proof. intros l a H B. natlit_hyp B. natlen_ctx. lia. Qed.
Goal forall (l : list nat), length l = 257%nat -> (Z.of_nat (length l) = 257)%Z.
Proof. intros l H. natlen_ctx. lia. Qed.
