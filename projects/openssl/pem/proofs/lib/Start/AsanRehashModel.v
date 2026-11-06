(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module RHM.

Definition EMPTY : Z := 2 ^ 64 - 1.
Definition TOMB : Z := 2 ^ 64 - 2.
(* [comment removed for export] *)
Definition is_live (k : Z) : bool := Z.leb k (2 ^ 64 - 3).
(* [comment removed for export] *)
Definition hash0 (N key : Z) : Z := Z.land ((key * 37) mod 2 ^ 64) (N - 1).

(* [comment removed for export] *)
Fixpoint probe_free (N : Z) (ks : list Z) (idx t : Z) (fuel : nat) : option Z :=
  match fuel with
  | O => None
  | S f => if Z.eqb (nth (Z.to_nat idx) ks 0) EMPTY then Some idx
           else probe_free N ks (Z.land (idx + t) (N - 1)) (t + 1) f
  end.

Fixpoint upd (ks : list Z) (i : nat) (v : Z) : list Z :=
  match ks, i with
  | [], _ => []
  | _ :: r, O => v :: r
  | k :: r, S i' => k :: upd r i' v
  end.

(* [comment removed for export] *)
Fixpoint rehash (N : Z) (ks : list Z) (olds : list Z) (j : Z) (pl : list (Z * Z)) : option (list Z * list (Z * Z)) :=
  match olds with
  | [] => Some (ks, rev pl)
  | k :: r =>
      if is_live k then
        match probe_free N ks (hash0 N k) 1 (Z.to_nat N) with
        | Some d => rehash N (upd ks (Z.to_nat d) k) r (j + 1) ((j, d) :: pl)
        | None => None
        end
      else rehash N ks r (j + 1) pl
  end.

(* [comment removed for export] *)
Definition rehash0 (N : Z) (olds : list Z) : option (list Z * list (Z * Z)) :=
  rehash N (repeat EMPTY (Z.to_nat N)) olds 0 [].

End RHM.
