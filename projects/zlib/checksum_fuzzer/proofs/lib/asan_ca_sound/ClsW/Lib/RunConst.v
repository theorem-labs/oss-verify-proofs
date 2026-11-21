(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run StackLayout.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.ClsW.Lib Require Import LiaTuning InitMem.
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

Definition ATOP_MIN : Z := 0x7fff7f800000.
Definition ATOP_MAX : Z := 0x7FFFFF800000.

Lemma ATOP_range {rc : runConstT} : ATOP_MIN <= ATOP <= ATOP_MAX.
Proof. unfold ATOP_MIN, ATOP_MAX. split; [apply ATOP_lo | apply ATOP_hi]. Qed.

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

(* The launch's facts the entry block is a function of, beside argv, envp,
   uid and hwcap: the auxv's launch fields ([Run.launch_auxv inp mbase]), the
   stack VMA's end ([ed_top] of the draw), the exec name and the gid.  The
   start-up and the drivers read the block through these. *)
Class runLaunchT : Type := RunLaunch {
  RL_la : LaunchAuxv;
  RL_top : word;
  RL_execfn : list byte;
  RL_gid : word
}.

Definition run_launch_of (inp : ProcInput) (sp mbase : word) (draw : EntryDraw) : runLaunchT :=
  {| RL_la := launch_auxv inp sp mbase; RL_top := ed_top draw; RL_execfn := in_execfn inp; RL_gid := in_gid inp |}.
