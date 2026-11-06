(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition hdr_b0 (content : list byte) : Z := bv_unsigned (nth 0 content (Z_to_bv 8 0)).
Definition hdr_b1 (content : list byte) : Z := bv_unsigned (nth 1 content (Z_to_bv 8 0)).
Definition hdr_cfg (content : list byte) : Z := hdr_b0 content + 256 * hdr_b1 content.
Definition hdr_cfglen (content : list byte) : Z := hdr_cfg content mod 32768.
Definition hdr_paylen (content : list byte) : Z := Z.of_nat (length content) - 6 - hdr_cfglen content.

(* [comment removed for export] *)
Definition t_target (content : list byte) (fs : Fs.Fs) : TSet :=
  let b2 := bv_unsigned (nth 2 content (Z_to_bv 8 0)) in
  let cfg := hdr_cfg content in
  let config_len := Z.to_nat (cfg mod 32768) in
  let counting := (32768 <=? cfg) in
  let payload_len := (length content - 6 - config_len)%nat in
  let calls := match config_len with O => 1%nat | _ => S (Z.to_nat (b2 mod 4)) end in
  let succ := t_emit (W 1 (zero_lines calls)) (t_exit (exit_code 0) fs) in
  match payload_len with
  | O => succ
  | _ => t_alt2 (t_exit (exit_code (if counting then 0 else 2)) fs) succ
  end.

Lemma t_body_target : forall content fs,
  (Z.of_nat (length content) < MAX_INPUT) ->
  (6 + Z.to_nat (hdr_cfg content mod 32768) <= length content)%nat ->
  t_body content fs = t_target content fs.
Proof.
  intros content fs Hmax Hlen. unfold t_body, t_target, hdr_cfg, hdr_b0, hdr_b1 in *.
  destruct (MAX_INPUT <=? Z.of_nat (length content)) eqn:E1; [apply Z.leb_le in E1; lia|].
  destruct (length content <? 6)%nat eqn:E2; [apply Nat.ltb_lt in E2; lia|].
  destruct (length content <? 6 + Z.to_nat ((bv_unsigned (nth 0 content (Z_to_bv 8 0)) +
             256 * bv_unsigned (nth 1 content (Z_to_bv 8 0))) mod 32768))%nat eqn:E3;
    [apply Nat.ltb_lt in E3; lia|].
  reflexivity.
Qed.
