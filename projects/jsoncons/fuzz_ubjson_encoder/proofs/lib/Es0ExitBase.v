(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Export SumWalkTac RefNodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Es0ExitBase () := "K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01I45stdpp9bitvector;definitions2bv00K47Corelib4Init7Decimal4uint08K47Corelib4Init7Decimal4uint0;K47Corelib4Init7Decimal4uint0:K47Corelib4Init7Decimal4uint02K47Corelib4Init7Decimal4uint04K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9StreamSim7wseg_okC13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images5Plain1M?loaded_segmentsC13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib4Init7Decimal4uint01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk?store_ok_windowC13~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Es0ExitBase;ref_wseg_1cC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_wseg_1c : wseg_ok RSEGS (0xb9000 : word) 208896%nat = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0ExitBase ()) ["FPX_1"] "p;2p;1p;3g0000j2@Tg000Jj11Tg000oj14Tg001Mj12Tg0022j1;Tg002Pj3:Tg0033j15Tg003Vj16Tg0044j17Tg004Rj13Tg0050j18Tg005Nj19Tg005lj1?Tg006Ij1>Tg006hj3=Tg0084j3<Tf0#1#1p=0g008NR0g008nR1'@g009Ng00:\#1R2#1#0#0#4R3%22#2#2#0#2#0#0#0#0#0#0#;g00;A3:%53eg00;]#6#7#3#3#8#9#?#>3==<01do"). Qed.

Lemma store_ok_data : forall m (a : word) n,
  (0xb9000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0xec000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0ExitBase ()) ["FPX_1"] "h02Hah13Hhih23Hloh37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with91ah:4cstrh;1mh<1np;1p;2p;3p;4p;7p;>g000Jj10Tg000oj19Tg0033j1<Tg00<;j1XTg001Mj11Tg0022j14Tg00<]j2:Tg00=Gj22Tg00=cj1;Tg00>Cj2?Tg002Pj3>Tg003Vj1WTg0044j1UTg004Rj1=Tg0050j1NTg005Nj1MTg005lj1LTg006Ij1ITg0000j26Tg00>`j1HTg00?Ej2ETg00?mj28Tg00@Ij2DTg00@fj3CTg00AJj1FTg00Ajj1GTg00BJj1BTg00Bhj1JTg00CFj1KTg00D1j27Tg00DTj3ATg00E7j4@Tg00Ebj7OTg00FFj2PTg00Fhj2QTg0084j3RTg00GTj3STg00H3j4TTg00Hel>VTf0R0#0#0p=5%00#0#0#0p=3g00:\R1#0R2#5R3#0#5R4#9R5#<R6%93#<#X[g00J7%12#1#1#5#1#3#3#3#4R3f1R7,:5'2f2R8,:5%;7'?%11#1#0#1#1#5#3#3#3#4R1'2g009Nf4g00;A9>53f3g00;]#W#U#=#=#N#M#L#IP8P3P1g00JVR9/631691%H8g00K4R3%;8'2%42R2%44R4'E183212341D24R:,83[[1232R;g00KRR<AC247UW0123:\<^0;g00KnR;#F%G;%B9%J9%K9R;g00LZg00M9R<P<g00MYR<P91791g00N91792=A95C@g00N`FO1P;<P0P8g008NR<g008nR;'61Q08=R<;dAS937CTb4b7b8121:P0b3b5b6b:g00O@P7P0M>VW1W2W<X96W;o"). Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.
Section FPX_2. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_clean (mem : word -> option byte) (f : Z) (wp rp : word) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (f + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 8)) 8%nat = Some (word_to_le_bytes 8 rp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 16)) 8%nat = Some (word_to_le_bytes 8 rp).

(* [comment removed for export] *)
Definition stdio_globals (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0xeb2d3) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xeb818) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xeb808) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xb9590) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb94a8)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xb94a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb93b8)).
End FPX_2.
 (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
