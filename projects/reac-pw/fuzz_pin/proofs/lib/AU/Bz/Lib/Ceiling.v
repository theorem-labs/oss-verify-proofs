(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/leptonica/colorfill_fuzzer/lib/K5/Lib/Ceiling.v; 3 of its 51 lines of code are new or changed and 2 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_boxreg/lib/A/Bz/Lib/Ceiling.v at origin/ossv/recipes f26f9fbd8777; module paths changed; no numeral changed. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/Bz/Lib/Ceiling.v of this library, for reac-pw/fuzz_pin's asan-ubsan image (fuzz_pin.asan-ubsan d6f83d301522) instead of its asan image (fuzz_pin.asan 3e4859aed23f): module paths lib.A -> lib.AU; no numeral changed (every address numeral checked on the asan-ubsan image). The comment lines above describe how lib/A/Bz/Lib/Ceiling.v was made and quote the asan image's values; the code and comments below carry the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz Require BvWfKernel.
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
