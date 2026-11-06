(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocImg.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RPH0 : PhdrInfo := {| ph_addr := 0x10040%N; ph_ent := 56%N; ph_num := 10%N |}.

Definition start_ok (dABS_ data_lo : Z) : bool := ((dABS_ =? 0) && (0x10270 <=? data_lo))%Z.

Class RelocStart (RL : Reloc) (RD : RelocData RL) := {
  rl_start_ok : start_ok dABS rl_data_lo = true
}.

Section Facts.
  Context {RL : Reloc} {RD : RelocData RL} {RST : RelocStart RL RD}.

  Lemma rl_dABS0 : dABS = 0%Z.
  Proof. pose proof rl_start_ok as H. unfold start_ok in H. apply andb_prop in H as [H _]. apply Z.eqb_eq in H. exact H. Qed.

  Lemma rl_hdr_below : (0x10270 <= rl_data_lo)%Z.
  Proof. pose proof rl_start_ok as H. unfold start_ok in H. apply andb_prop in H as [_ H]. apply Z.leb_le in H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma rl_abs : forall c, rl dABS c = Z_to_bv 64 c.
  Proof. intros c. unfold rl. rewrite rl_dABS0, Z.add_0_r. reflexivity. Qed.
End Facts.

