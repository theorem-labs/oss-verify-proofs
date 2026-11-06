(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.
Definition u8 (x : Z) : Z := x mod 2^8.
Definition zlength {A} (l : list A) : Z := Z.of_nat (length l).
Definition znth (l : list Z) (i : Z) : Z :=
if i <? 0 then 0 else nth (Z.to_nat i) l 0.
Definition zrepeat (v : Z) (n : Z) : list Z := repeat v (Z.to_nat n).
