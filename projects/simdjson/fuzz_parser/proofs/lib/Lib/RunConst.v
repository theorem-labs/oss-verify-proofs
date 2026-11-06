(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run StackLayout.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import LiaTuning InitMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Class runConstT : Type := RunConst {
  ATOP : Z;
  SECRET : Z;
  CAN : word;
  ATOP_lo : 0x7fff7f800000 <= ATOP;
  ATOP_hi : ATOP <= 0x7FFFFF800000;
  ATOP_al16 : ATOP mod 16 = 0;
  SECRET_rng : 0 <= SECRET < 2^64
}.

(* [comment removed for export] *)
Definition ATOP_MIN : Z := 0x7fff7f800000.
Definition ATOP_MAX : Z := 0x7FFFFF800000.

Lemma ATOP_range {rc : runConstT} : ATOP_MIN <= ATOP <= ATOP_MAX.
Proof. unfold ATOP_MIN, ATOP_MAX. split; [apply ATOP_lo | apply ATOP_hi]. Qed.

(* [comment removed for export] *)
Lemma entry_atop_lo : forall en, valid_sp (en_sp en) -> 0x7fff7f800000 <= entry_atop en.
Proof. intros en (L & H & M). unfold entry_atop, sp_window_lo, stack_max_size in *. lia. Qed.
Lemma entry_atop_hi : forall en, valid_sp (en_sp en) -> entry_atop en <= 0x7FFFFF800000.
Proof. intros en (L & H & M). unfold entry_atop, sp_window_hi, stack_max_size in *. lia. Qed.
Lemma entry_atop_al16 : forall en, valid_sp (en_sp en) -> entry_atop en mod 16 = 0.
Proof. intros en (L & H & M). unfold entry_atop, stack_max_size in *. Z.div_mod_to_equations. lia. Qed.

Definition run_consts_of (en : ExecEntry) (c : word) (V : valid_sp (en_sp en)) : runConstT :=
  {| ATOP := entry_atop en; SECRET := entry_secret en; CAN := c;
     ATOP_lo := entry_atop_lo en V; ATOP_hi := entry_atop_hi en V; ATOP_al16 := entry_atop_al16 en V;
     SECRET_rng := draw_secret_range (en_draw en) |}.

Lemma run_consts_of_ATOP : forall en c V, @ATOP (run_consts_of en c V) = entry_atop en.
Proof. reflexivity. Qed.
Lemma run_consts_of_SECRET : forall en c V, @SECRET (run_consts_of en c V) = entry_secret en.
Proof. reflexivity. Qed.
Lemma run_consts_of_CAN : forall en c V, @CAN (run_consts_of en c V) = c.
Proof. reflexivity. Qed.
