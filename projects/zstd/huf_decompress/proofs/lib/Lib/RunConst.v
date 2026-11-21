(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (7 recorded proofs replaced by written proofs (ATOP_range, entry_atop_lo, entry_atop_hi and 4 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run StackLayout.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import LiaTuning InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RunConst () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02c59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib3Lib8RunConst7ATOP_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib8RunConst7ATOP_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib4Init5Logic3and00i59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03c59OSSVerify5KrLib3Lib8RunConst8ATOP_MINC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib8RunConst8ATOP_MAXC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib3Lib7InitMem:entry_atopC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib3Lib7InitMem<entry_secretC1?~~~~~~~~~~~~~~~".
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
