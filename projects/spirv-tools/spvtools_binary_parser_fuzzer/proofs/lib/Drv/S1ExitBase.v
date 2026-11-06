(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Export SumWalkTac RefNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1StartInit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1ExitBase () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01C59OSSVerify5KrLib3Drv;S1StartInit8rw_wviewC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7StoreOk?store_ok_of_allC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes3nat00C69OSSVerify6KrSpec8ProblemscSrc_spirv_tools_spvtools_binary_parser_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma store_ok_data : forall m (a : word) n,
  (0xee000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x122000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_S1ExitBase ()) [] "h04__x1h14__x2h22Hah37__arithh44__ffh58__varmaph65__with74__x3h84cstrh93Hhih:3Hloh;2Hxh<6__sat0h=6__sat1h>1ah?1mh@1nhA1xp;1p;2p;3p;4p;6p;7p;8g0000j11Tg000Uj1GTg0013j1DTg001Vj1bTg0028j13Tg002]j1=Tg003;j26Tg003ej20Tg004Aj17Tg004aj28Tg005>j1ETg005cj2aTg006Kj29Tg006gj2`Tg007Dj3[Tg007hj1YTg008Hj1XTg008hj2ITg009Fj1WTg009dj4HTg00:Bj1VTg00:`j1UTg00;Kj2ATg00;nj3FTg00<Qj2BTg00=4j1TTg00=Vj3STg00>9j2PTg00>[j2OTg00?5j2NTg00?aj3QTg00@;j3RTg00@Zj4MTg00ALj2@Tg00Agj1<Tg00BFj2:Tg00Boj3?Tg00CXj2LTg00DDj3KTg00Ddj4CTg00EOj3_Tg00FLj6^Tg00GHj7\Tg00Glj8ZTg00HPj7]Tf0R0#1#1p=>%10#1#1#1p=5g00I4R1f1R2g00IRP0CCp=4P2g00J9R3g00JXR4P4g00K8R5P0g00KXF\p=2f3R6P3P4P4P5f2R7P2P0GZp=;P7P3P4P4P5P2P0F]p=Jg00L8R3#1R8#>R9#1#>R:#GR;#DR<%G9#D#b[g00L]%33R9#3#1#3#3#3#1#5#5#5#=R=16;2'016;7%72'8%>3#3#1#>#3#1#5#5#5#=R>'0g00M<P7f4R?P6%E7g00O1R@%77'0%=8RA%=:R:'a19@A10@:1`A:RB,9@[[10@ARCg00OORDA[A:2UW210@B\D^2Cg00OkRC#YRD%XCR:P11I17REP2%W1CH%V1RF%U1RG1A13R31A18R85F1RH1B1>RI'4,2G%T4R41B1A=S1;,4H,2GC;1PG5R5P0P7g00PWRHg00Q7RA'O1N07=QHAdAR1@2CMRAb4b5b6X01X111802/0>1827RH/0B[^01^11P0f6RB#7RJf7,6;RKP?O3b3b<b=b816;?RL16;0RM'0%76,8L,9M'@%E?%7?,0@g00QWR@#<RM#<RL#<RN,:11:1L1:1@R@5?15?1g00R6RL'L%<N,:11:1M=?1@5?1/LL=KCD5KCP:P1PEP21I16CHPFPG1483,2GP1P3g00RbRF1A199F18R9CC,2G5JGP4PG149I,2GP4PG1B1=R9/48,2GP41493,2GP1P3PFPICC,2G5JGC;C;C;P5PAb4b5b6X01X11X711020190H'@1876/0>10=6R=196>,@=[[[^01^11^71P0PJPK16;6P7P?f5O6b3b89_B2W;XA<E^W9W:W@X><W?o"). Qed.

Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.

Definition file_clean (mem : word -> option byte) (f : Z) (wp rp : word) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (f + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 8)) 8%nat = Some (word_to_le_bytes 8 rp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 16)) 8%nat = Some (word_to_le_bytes 8 rp).

Definition stdio_globals (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x12094b) 1%nat = Some [Z_to_bv 8 0]
  /\ rdn RSEGS mem (Z_to_bv 64 0x120e88) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 0xee388) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xee2a0))
  /\ rdn RSEGS mem (Z_to_bv 64 0xee478) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xee390))
  /\ rdn RSEGS mem (Z_to_bv 64 0xee298) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xee1b0)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
