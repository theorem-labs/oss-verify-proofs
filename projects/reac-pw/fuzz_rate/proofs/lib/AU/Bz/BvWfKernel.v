(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/glaze/binary_reflection/lib/BvWfKernel.v, with only its comments or blank lines changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Bz/BvWfKernel.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/Bz/BvWfKernel.v at 71994ff034c7, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/Bz/BvWfKernel.v was made and quote that file's image-A values; the code below carries image B's values; a numeral in a comment that quotes the donor's text (lib/A/Bz/BvWfKernel.v keeps its donor's comment text) is kept as lib/A/Bz/BvWfKernel.v writes it. *)
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
