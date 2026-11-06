(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HCatExec HCatSim HSeqExec HStepTac HHoare HWalkTac HStoreOk HStreamSim HMmapSim HLibAtomic HExitSim HShapeAlg HNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Export HSumWalkTac HRefNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_HRefExitBase () := "K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib3bpA2HF:HStreamSim7wseg_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K47Corelib4Init7Decimal4uint0:K47Corelib4Init7Decimal4uint04K47Corelib4Init7Decimal4uint03K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintK47Corelib4Init7Decimal4uint01K47Corelib4Init7Decimal4uint05K47Corelib4Init7Decimal4uint06K47Corelib4Init7Decimal4uint07I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib3bpA2HF8HStoreOk?store_ok_windowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00c69OSSVerify5KrLib3bpA3Drv<HRefExitBase>ref_wseg_filesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv<HRefExitBase<ref_wseg_crtC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA3Drv<HRefExitBase=ref_wseg_tailC1?~~~~~~~~~~~~~~~".
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Asan.M.loaded_segments.

Lemma ref_wseg_files : wseg_ok RSEGS (0x187f60 : word) 720%nat = true.
Proof.
ltac2:(KReplay.run1 (kr_t_HRefExitBase ()) [] "p;2p;1p;3g0000j2<Tg000Jj18Tg000hj12Tg001Mj14Tg0022j1;Tg002Pj3:Tg0033j17Tg003Vj35Tg004Tj39Tg004nj10Tf0R0#4#4p=3%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=6%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g005MR0g005mR1'<g006Mg007kR2#3#3#3#8R3%22#3#3#2#2#2#2#2#2#2#4#2#2#4#3#3#;g008P3:%73eg008l#6#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#135=901do"). Qed.
Lemma ref_wseg_crt : wseg_ok RSEGS (0x18b000 : word) 12288%nat = true.
Proof.
ltac2:(KReplay.run1 (kr_t_HRefExitBase ()) [] "p;2p;1p;3g0000j2>Tg000Jj17Tg000hj11Tg001Mj12Tg0022j1;Tg002Pj3:Tg0033j16Tg009Kj13Tg009ij14Tg00:Gj15Tg00:ej18Tg00;Bj19Tg003Vj3=Tg004Tj3<Tf0#2#2p=0g005MR0g005mR1'>g006Mg007kR2#0#0#0#7R3%12#2#0#1#2#1#1#0#0#0#0#0#0#;g008P3:%63eg00;a#3#3#4#4#5#8#93==<01do"). Qed.
Lemma ref_wseg_tail : wseg_ok RSEGS (0x6c1d40 : word) 146376%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma store_ok_data : forall m (a : word) n,
  ((0x187f60 <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= 0x188230)
   \/ (0x18b000 <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= 0x18e000)
   \/ (0x6c1d40 <= bv_unsigned a /\ bv_unsigned a + Z.of_nat n <= 0x6e5908))%Z ->
  store_ok RSEGS m a n = true.
Proof.
  intros m a n H.
  destruct H as [H|[H|H]].
  - apply (store_ok_window RSEGS m (0x187f60 : word) a 720%nat n 0x187f60%Z 0x188230%Z);
      [reflexivity | reflexivity | lia | exact ref_wseg_files | lia | lia].
  - apply (store_ok_window RSEGS m (0x18b000 : word) a 12288%nat n 0x18b000%Z 0x18e000%Z);
      [reflexivity | reflexivity | lia | exact ref_wseg_crt | lia | lia].
  - apply (store_ok_window RSEGS m (0x6c1d40 : word) a 146376%nat n 0x6c1d40%Z 0x6e5908%Z);
      [reflexivity | reflexivity | lia | exact ref_wseg_tail | lia | lia].
Qed.

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
  rdn RSEGS mem (Z_to_bv 64 0x6e41ab) 1%nat = Some [Z_to_bv 8 0]
  /\ rdn RSEGS mem (Z_to_bv 64 0x6e4720) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 0x188138) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x188050))
  /\ rdn RSEGS mem (Z_to_bv 64 0x188228) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x188140))
  /\ rdn RSEGS mem (Z_to_bv 64 0x188048) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x187f60)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
