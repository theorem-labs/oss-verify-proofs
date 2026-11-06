(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith PArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac lia_guard :=
  lazymatch goal with
  | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac | |- Z.gt _ _ => idtac
  | |- le _ _ => idtac | |- lt _ _ => idtac | |- ge _ _ => idtac | |- gt _ _ => idtac
  | |- N.le _ _ => idtac | |- N.lt _ _ => idtac | |- N.ge _ _ => idtac | |- N.gt _ _ => idtac
  | |- Pos.le _ _ => idtac | |- Pos.lt _ _ => idtac | |- Pos.ge _ _ => idtac | |- Pos.gt _ _ => idtac
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- @eq N _ _ => idtac | |- @eq positive _ _ => idtac
  | |- ~ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- _ <-> _ => idtac
  | |- False => idtac | |- True => idtac
  | |- _ => fail "lia_guard: not an arithmetic goal"
  end.
