(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/glaze/binary_reflection/lib/BvWfKernel.v; 1 of its 13 lines of code is new or changed and 1 line of the source is left out. *)
(* Modified by Theorem Labs, 2026-10: moved from image B (fuzz_preset.asan-ubsan f8f98a95), commit 3244f5c71f6, to the #102 pin B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5): 0 address numerals by the frozen alreloc (sha256 c4338d099cfb8025, commit d99acc3edd9, same-unit move, --assume-source), each by symbol + offset in both images, or for a .rodata string by its unique content in both; GXA keys and history lines kept (report and decisions: the relocation record, the internal file resolve-B-why.tsv). *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_preset.asan-ubsan (image B, f8f98a95) from commit 7e395de08f5 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/BvWfKernel.v: module paths (lib/A/Bz -> lib/AU/PSnpBz), the image binding Asan -> AsanUbsan, and 0 address numerals by alreloc (sha256 c4338d099cfb8025, commit d99acc3edd97, --build asan-ubsan --from-build asan), each by symbol + offset in both images (per-numeral report: the relocation record, reloc-B). *)
(* Ported by the runtime port from commit affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/BvWfKernel.v, unchanged. *)
(* [comment removed for export] *)
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
