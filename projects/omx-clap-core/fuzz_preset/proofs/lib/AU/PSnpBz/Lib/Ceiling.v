(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/leptonica/colorfill_fuzzer/lib/K5/Lib/Ceiling.v; 1 of its 51 lines of code is new or changed. *)
(* Modified by Theorem Labs, 2026-10: moved from image B (fuzz_preset.asan-ubsan f8f98a95), commit 3244f5c71f6, to the #102 pin B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5): 0 address numerals by the frozen alreloc (sha256 c4338d099cfb8025, commit d99acc3edd9, same-unit move, --assume-source), each by symbol + offset in both images, or for a .rodata string by its unique content in both; GXA keys and history lines kept (report and decisions: the relocation record, the internal file resolve-B-why.tsv). *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_preset.asan-ubsan (image B, f8f98a95) from commit 7e395de08f5 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/Lib/Ceiling.v: module paths (lib/A/Bz -> lib/AU/PSnpBz), the image binding Asan -> AsanUbsan, and 0 address numerals by alreloc (sha256 c4338d099cfb8025, commit d99acc3edd97, --build asan-ubsan --from-build asan), each by symbol + offset in both images (per-numeral report: the relocation record, reloc-B). *)
(* Ported by the runtime port from commit affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/Lib/Ceiling.v, unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Class Ceiling : Type := mkCeiling {
  alloc_ceiling : Z;
  (* [comment removed for export] *)
  alloc_ceiling_ge : 0x7fff7f800000 <= alloc_ceiling;
  (* [comment removed for export] *)
  alloc_ceiling_le : alloc_ceiling + 8388608 <= 0x800000000000;
  (* [comment removed for export] *)
  alloc_ceiling_al : alloc_ceiling mod 16 = 0
}.

Ltac ceil_bounds :=
  pose proof alloc_ceiling_ge; pose proof alloc_ceiling_le; pose proof alloc_ceiling_al.

Section Facts.
  Context {CE : Ceiling}.

  Lemma alloc_ceiling_lt_2p47 : alloc_ceiling < 2^47.
  Proof. ceil_bounds. lia. Qed.

  Lemma alloc_ceiling_lt_2p63 : alloc_ceiling < 2^63.
  Proof. ceil_bounds. lia. Qed.

  Lemma alloc_ceiling_pos : 0 < alloc_ceiling.
  Proof. ceil_bounds. lia. Qed.

  Lemma alloc_ceiling_range : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
  Proof. ceil_bounds. lia. Qed.
End Facts.

(* [comment removed for export] *)

Definition ceiling_raw (sp : Z) : Z :=
  Z.max 0x7fff7f800000 (Z.min 0x7fffff800000 ((sp - 8388608) / 16 * 16)).

Lemma ceiling_raw_ge : forall sp, 0x7fff7f800000 <= ceiling_raw sp.
Proof. intros sp. unfold ceiling_raw. lia. Qed.

Lemma ceiling_raw_le : forall sp, ceiling_raw sp + 8388608 <= 0x800000000000.
Proof. intros sp. unfold ceiling_raw. lia. Qed.

Lemma ceiling_raw_al : forall sp, ceiling_raw sp mod 16 = 0.
Proof.
  intros sp. unfold ceiling_raw.
  destruct (Z.max_spec 0x7fff7f800000 (Z.min 0x7fffff800000 ((sp - 8388608) / 16 * 16))) as [[_ ->]|[_ ->]];
    [|reflexivity].
  destruct (Z.min_spec 0x7fffff800000 ((sp - 8388608) / 16 * 16)) as [[_ ->]|[_ ->]]; [reflexivity|].
  apply Z_mod_mult.
Qed.

Definition ceiling_of_sp (sp : Z) : Ceiling :=
  mkCeiling (ceiling_raw sp) (ceiling_raw_ge sp) (ceiling_raw_le sp) (ceiling_raw_al sp).

Lemma ceiling_of_sp_eq : forall sp,
  0x7fff80000000 <= sp <= 0x800000000000 -> sp mod 16 = 0 ->
  @alloc_ceiling (ceiling_of_sp sp) = sp - 8388608.
Proof.
  intros sp Hsp Hal. cbn [alloc_ceiling ceiling_of_sp]. unfold ceiling_raw.
  assert (E : (sp - 8388608) / 16 * 16 = sp - 8388608).
  { pose proof (Z.div_mod (sp - 8388608) 16 ltac:(lia)) as D.
    replace ((sp - 8388608) mod 16) with 0 in D.
    - lia.
    - rewrite Zminus_mod, Hal. reflexivity. }
  rewrite E. lia.
Qed.
