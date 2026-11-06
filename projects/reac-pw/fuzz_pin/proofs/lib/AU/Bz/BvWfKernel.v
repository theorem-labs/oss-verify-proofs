(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/glaze/binary_reflection/lib/BvWfKernel.v, with only its comments or blank lines changed. *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_boxreg/lib/A/Bz/BvWfKernel.v at origin/ossv/recipes f26f9fbd8777; module paths changed; no numeral changed. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/Bz/BvWfKernel.v of this library, for reac-pw/fuzz_pin's asan-ubsan image (fuzz_pin.asan-ubsan d6f83d301522) instead of its asan image (fuzz_pin.asan 3e4859aed23f): no numeral changed (every address numeral checked on the asan-ubsan image). The comment lines above describe how lib/A/Bz/BvWfKernel.v was made and quote the asan image's values; the code and comments below carry the asan-ubsan values. *)
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
