(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

Definition bptr : Type := unit.
Definition block : Type := (bptr * Z * Z)%type.
Definition blk_addr (b : block) : Z := snd (fst b).
Definition blk_size (b : block) : Z := snd b.
Definition blk_id (b : block) : Z := blk_addr b.
Definition in_block (LB : list block) (a : Z) : Prop :=
exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b.
Definition blocks_ivs (LB : list block) : list (Z * Z) := map (fun b => (blk_addr b, blk_addr b + blk_size b)) LB.

Definition blocks_live (LB : list block) : list (Z * Z) := map (fun b => (blk_addr b, blk_size b)) LB.
