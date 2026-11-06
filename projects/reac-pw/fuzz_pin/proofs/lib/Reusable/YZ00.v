(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From stdpp Require Import bitvector.definitions.
Ltac bvk_ground_pos p :=
lazymatch p with BinNums.xH => idtac | BinNums.xO ?q => bvk_ground_pos q | BinNums.xI ?q => bvk_ground_pos q end.
Ltac bvk_ground_N n := lazymatch n with BinNums.N0 => idtac | BinNums.Npos ?p => bvk_ground_pos p end.
Ltac bvk_ground_Z z :=
lazymatch z with BinNums.Z0 => idtac | BinNums.Zpos ?p => bvk_ground_pos p | BinNums.Zneg ?p => bvk_ground_pos p end.
#[global] Hint Extern 0 (BvWf ?n ?z) => (bvk_ground_N n; bvk_ground_Z z; exact I) : typeclass_instances.
Goal True.
let a := constr:(@BV 5%N 10%Z _) in
lazymatch a with @BV _ _ I => idtac | _ => fail "KitBvWfKernel: literal not elaborated to [BV n z I]" end.
exact I.
Qed.
