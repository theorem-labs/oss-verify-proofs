(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac Mem Bytes Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA Layout RT_iface Lept_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma bytes_le_to_Z_nonneg : forall bs : list byte, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply (proj2 (Z.lor_nonneg _ _)). split; [apply (proj1 (bv_unsigned_in_range 8 b)) | apply (proj2 (Z.shiftl_nonneg _ _)); exact IH].
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap8_mod. change (2 ^ 8) with 256.
    Z.div_mod_to_equations. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; lia).
    exact IH.
Qed.

Lemma bytes_le_to_Z_bound8 : forall bs : list byte, length bs = 8%nat -> 0 <= bytes_le_to_Z bs < 2^64.
Proof.
  intros bs H. rewrite bytes_le_to_Z_le_val.
  pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as R.
  rewrite length_map, H in R. change (256 ^ Z.of_nat 8) with (2^64) in R. exact R.
Qed.

Lemma le8_of_bytes8 : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs H. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound8 bs H) as R.
  replace (bv_wrap 64 (bytes_le_to_Z bs)) with (bytes_le_to_Z bs)
    by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); rewrite Z.mod_small by lia; reflexivity).
  rewrite <- H. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma rw_cells_CB8_C8 : forall (m : mem) a bs cs,
  rw_cells asegs m a (CB 8 bs :: cs) -> rw_cells asegs m a (C8 (le_bytes_to_word bs) :: cs).
Proof.
  intros m a bs cs [[[Hwf Hwfs] HB] HW]. cbn [cell_wf] in Hwf.
  split; [split; [split; [exact I | exact Hwfs] |] | exact HW].
  cbn [cells_bytes cbytes]. rewrite (le8_of_bytes8 bs Hwf). exact HB.
Qed.
