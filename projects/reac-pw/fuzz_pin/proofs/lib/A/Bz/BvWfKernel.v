(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/glaze/binary_reflection/lib/BvWfKernel.v, with only its comments or blank lines changed. *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_boxreg/lib/A/Bz/BvWfKernel.v at origin/ossv/recipes f26f9fbd8777; module paths changed; no numeral changed. *)
From stdpp Require Import bitvector.definitions.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
