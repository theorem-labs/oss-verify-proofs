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
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg DivergeSim SpinAlg SpinAlgX Nodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Export SumWalkTac RefNodes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Eu0ExitBase () := "K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01I45stdpp9bitvector;definitions2bv00K47Corelib4Init7Decimal4uint04K47Corelib4Init7Decimal4uint0;K47Corelib4Init7Decimal4uint03K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9StreamSim7wseg_okC13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images5Ubsan1M?loaded_segmentsC13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib4Init7Decimal4uint01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StoreOk?store_ok_windowC13~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eu0ExitBase;ref_wseg_1cC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_wseg_1c : wseg_ok RSEGS (0xba000 : word) 212992%nat = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Eu0ExitBase ()) ["FPX_1"] "p;2p;1p;3g0000j2>Tg000Jj11Tg000oj15Tg001Mj12Tg0022j1;Tg002Pj3:Tg0033j16Tg003Vj13Tg0044j14Tg004Rj17Tg0050j18Tg005Mj19Tg005lj3=Tg0078j3<Tf0#1#1p=0g007RR0g0082R1'>g008Rg009`#1R2#1#0#0#5R3%22#2#2#1#2#1#0#0#0#0#0#0#;g00:E3:%63eg00:a#3#4#4#3#7#3#8#93==<01do"). Qed.

Lemma store_ok_data : forall m (a : word) n,
  (0xba000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0xee000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Eu0ExitBase ()) ["FPX_1"] "h02Hah13Hhih23Hloh37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with91ah:4cstrh;1mh<1np;1p;2p;3p;4p;7p;>g000Jj10Tg000oj19Tg0033j1;Tg00;?j1VTg001Mj11Tg0022j14Tg00;aj2<Tg00<Kj22Tg00<gj17Tg00=Gj2@Tg002Pj3?Tg003Vj16Tg0044j1>Tg004Rj1UTg0050j1TTg005Mj1STg0000j25Tg00=dj1LTg00>Ij2KTg00?1j28Tg00?Mj2GTg00?jj3FTg00@Nj1ETg00@nj1DTg00ANj1HTg00Alj1ITg00BJj1CTg00C5j2:Tg00CXj3JTg00D;j4BTg00Dfj7ATg00EJj2MTg00Elj2NTg0078j3OTg00FXj3PTg00G7j4QTg00Gil>RTf0R0#0#0p==%00#0#0#0p=3g009`R1#0R2#=R3#0#=R4#9R5#;R6%93#;#V[g00I;%12#1#1#0#1#0#3#3#3#4R3f1R7,<5'2f2R8,<5%77'@%11#1#0#1#1#1#0#3#3#3#4R1'2g008Rf4g00:E9?53f3g00:a#6#>#>#6#U#6#T#SP8P3P1g00IZR9/531591%L8g00J8R3%78'2%42R2%44R4'K183212341G24R:,83[[1232R;g00JVR<AF247UW0123:\<^0;g00K2R;#E%D;%H9%I9%C9R;g00K^g00L=R<P<g00L]R<P91:91g00M=1:92=J95CBg00MdFA1M;<P0P8g007RR<g0082R;'51N08=O<;dAP937CQb4b7b8121:P0b3b5b6b:g00NDP7P0M>RW1W2W<X96W;o"). Qed.
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
  rdn RSEGS mem (Z_to_bv 64 0xece53) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xed398) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xed388) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xbb110) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xbb028)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xbb020) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xbaf38)).
End FPX_2.
 (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
