(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec SeqExec SymExec PropExecFP SymExecFP SymExecFPSound LibBswap LibBswapSx.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SXF. Import SXFS.

Section SxM.
Variable E : env.
Variable nu : nat -> Z.
Hypothesis Hnu : forall k, 0 <= nu k < 256.

(* [comment removed for export] *)
Theorem beval_bytes_sx_mod : forall atoms e ks k0,
  atoms_ok E nu atoms ->
  (length ks <= 8)%nat ->
  match beval atoms e with Some l => list_bbit_eqb l (bytes_bits_sx ks k0) | None => false end = true ->
  bv_unsigned (edenot E e) mod 2 ^ (8 * Z.of_nat (length ks)) = bytes_val nu ks.
Proof.
  intros atoms e ks k0 Hok Hlen H.
  destruct (beval atoms e) as [l|] eqn:Hb; [|discriminate].
  apply list_bbit_eqb_eq in H. subst l.
  pose proof (beval_sound E nu Hnu atoms e _ Hok Hb) as W.
  set (x := bv_unsigned (edenot E e)) in *.
  set (n := length ks) in *.
  assert (Hp : 0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpl : 2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  apply (wbits_bytes_val nu Hnu); [exact Hlen | |].
  - pose proof (Z.mod_pos_bound x (2 ^ (8 * Z.of_nat n)) Hp). lia.
  - destruct W as [L W]. split.
    + unfold bytes_bits. rewrite length_app, flat_map_bytes_length, repeat_length. fold n. lia.
    + intros i Hi.
      unfold bytes_bits. rewrite nth_app_cases, flat_map_bytes_length. fold n.
      destruct (Nat.ltb_spec i (8 * n)).
      * rewrite Z.mod_pow2_bits_low by lia.
        rewrite W by exact Hi. unfold bytes_bits_sx. rewrite nth_app_cases, flat_map_bytes_length. fold n.
        rewrite (proj2 (Nat.ltb_lt i (8 * n))) by lia. reflexivity.
      * rewrite Z.mod_pow2_bits_high by lia.
        rewrite nth_repeat_any by lia. reflexivity.
Qed.
End SxM.
