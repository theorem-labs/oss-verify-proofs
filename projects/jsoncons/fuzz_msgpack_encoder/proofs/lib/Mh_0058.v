(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs State Monad Specs Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module Ns0ExitBase.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
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
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.LibAtomic OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.ExitSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Export OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.SumWalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Ns0ExitBase () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01I45stdpp9bitvector;definitions2bv00K47Corelib4Init7Decimal4uint04K47Corelib4Init7Decimal4uint0;K47Corelib4Init7Decimal4uint03K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintC59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01K47Corelib4Init7Decimal4uint01I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_windowC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01c59OSSVerify5KrLib7Mh_0058;Ns0ExitBase;ref_wseg_1cC1?~~~~~~~~~~~~~~~".
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

Lemma ref_wseg_1c : wseg_ok RSEGS (0xc6000 : word) 212992%nat = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0ExitBase ()) ["FPX_1"] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210p1003<p4p710R0p8p1003Zp4p710P0p8p10045p4p710p1004Tp4p710p8g0050j2>Tg005Jj17Tg005hj12Tg006Mj11Tg0072j1;Tg007Pj3:Tg0083j16Tg008Vj13Tg0094j14Tg009Rj15Tg00:0j18Tg00:Mj19Tg00:lj3=Tg00;jj3<Tf0#1#1p=0g00<DR0g00<dR1'>g00=Dg00>mR2#0#0#0#7R3%22#1#0#2#2#1#0#0#0#0#0#0#;g00?R3:%63eg00?n#3#4#4#3#5#3#8#93==<01do"). Qed.

Lemma store_ok_data : forall m (a : word) n,
  (0xc6000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0xfa000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0ExitBase ()) ["FPX_1"] "h02Hah13Hhih23Hloh37__arithh44__ffh56__sat0h66__sat1h78__varmaph85__with91ah:4cstrh;1mh<1np;1p;2p;3p;4p;7p;>p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210p1003<p4p710R0p8p1003Zp4p710P0p8p10045p4p710p1004Tp4p710p8g006Mj10Tg005Jj1:Tg0083j1<Tg00@Lj1VTg005hj11Tg0072j14Tg00@nj2=Tg00AXj22Tg00B4j18Tg00BTj2@Tg007Pj3?Tg008Vj17Tg0094j1>Tg009Rj1UTg00:0j1TTg00:Mj1STg0050j25Tg00C1j1LTg00CVj2KTg00D>j29Tg00DZj2GTg00E7j3FTg00E[j1ETg00F;j1DTg00F[j1HTg00G9j1ITg00GWj1CTg00HBj2;Tg00Hej3JTg00IHj4BTg00J3j7ATg00JWj2MTg00K9j2NTg00;jj3OTg00Kej3PTg00LDj4QTg00M6l>RTf0R0#0#0p=6%00#0#0#0p=3g00>mR1#0R2#6R3#0#6R4#:R5#<R6%:3#<#V[g00N:%11#0#6#1#1#0#3#3#3#4R3f1R7,=5'2f2R8,=5%87'@%11#1#1#1#0#1#0#3#3#3#4R1'2g00=Df4g00?R9?53f3g00?n#7#>#>#7#U#7#T#SP8P3P1g00NYR9/531591%L8g00O7R3%88'2%42R2%44R4'K193212341G24R:,93[[1232R;g00OUR<AF247UW0123:\<^0;g00P1R;#E%D;%H9%I9%C9R;g00P]g00Q<R<P<g00Q\R<P91;91g00R<1;92=J95CBg00RcFA1M;<P0P8g00<DR<g00<dR;'51N08=O<;dAP937CQb4b7b8121:P0b3b5b6b:g00SCP7P0M>RW1W2W<X96W;o"). Qed.
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
  rdn RSEGS mem (Z_to_bv 64 0xf8ae3) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xf9028) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xf9018) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xc6da8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc6cc0)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xc6cb8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc6bd0)).
End FPX_2.
 (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0ExitBase.
From Stdlib Require ZArith List.
Module Ns0Img.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Lemma img_10040_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10050_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10078_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_100b0_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_100e8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10120_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10158_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10190_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_101c8_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_101f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10200_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_10238_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_bf9a0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 784864) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 232232)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c58e8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 809256) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c58f0_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 809264) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 232492)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c58f8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 809272) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 690532)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c5900_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 809280) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 692864)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c5908_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 809288) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c5a50_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 809616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 886656)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c5a58_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 809624) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1018584)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c5a60_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 809632) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1018576)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c5a68_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 809640) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 784872)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c5a70_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 809648) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 784864)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c5a78_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 809656) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1018560)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c6d70_4 : rdn SEGS (fun _ => None) (Z_to_bv 64 814512) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_c6d90_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 814544) 1%nat = Some ([Z_to_bv 8 0]).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_d8758_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1017960) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_d8768_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1017976) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_d8770_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1017984) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_d8b08_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1018568) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_d8b30_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1018608) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_d8b48_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 1018632) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. vm_refl_bv. Qed.

End Ns0Img.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0058 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01I46Stdlib9micromega7EnvRing5PExpr00I46Stdlib9micromega=RingMicromega7Formula00I46Stdlib9micromega5Tauto8GFormula00I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3powC46Stdlib5Lists4List2InC45stdpp9bitvector;definitions5bv_eqK46Stdlib9micromega7EnvRing5PExpr07K47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega:ZMicromega=Zeval_formulaK47Corelib4Init9Datatypes6option02K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbI47Corelib4Init9Datatypes4prod00C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6shiftlC49OSSVerify5KrLib8PropExec5v_luiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4prod01C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_mulhuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_srliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4v_orC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C45stdpp9bitvector;definitions4BvWfK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_00417ZStores5zerosC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_subwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare:regs_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init5Logic2ex01C56Stdlib6ZArith4Zdiv1Z>mod_mod_divideI47Corelib4Init5Logic2ex00C49OSSVerify5KrLib8PropExec4c_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00387MmapSim:step_sb_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec;step_add_atC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<step_bltu_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387WalkTac=wf_getr_chainC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_subwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_luiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0041:StartupAuxAnegw_and3_alignedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec<step_andi_atC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare7at_selfC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C49OSSVerify5KrLib8PropExec9step_andiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:step_mulhuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:step_sw_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0041:StartupAuxAv_andi_4_aligned8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_srliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7step_orC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec<step_jalr_x0C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00417ZStores7zstoresC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00417ZStores=zstores_coverC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare?regs_agree_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare>regs_agree_updC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega6VarMap4findC46Stdlib9micromega5Tauto7eval_bfK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib4Init9Datatypes4list02C49OSSVerify5KrLib8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelI59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:step_sd_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec<step_addi_atC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<step_bltu_tkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes4bool02C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9fa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9fa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9fa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9fa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9fa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9fa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9fa8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9fa8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9fa8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9facC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9facC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9facC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1N00C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib7Mh_00589Ns0Memset;memset_clobC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic4True00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ebcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ebcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ebcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ec0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ec0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ec0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ec4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ec4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ec4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ec8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ec8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ec8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9eccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9eccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9eccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ed0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ed0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ed0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ed4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ed4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ed4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ed8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ed8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ed8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9edcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9edcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9edcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ee0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ee0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ee0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ee4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ee4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ee4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ee8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ee8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ee8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9eecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9eecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9eecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ef0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ef0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ef0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ef4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ef4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ef4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ef8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ef8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ef8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9efcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9efcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9efcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f3cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f3cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f3cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9f90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9f90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9f90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9fb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9fb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9fb0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00589Ns0Memset<memset304_wsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00589Ns0Memset@memset304_ws_inbC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00589Ns0MemsetBmemset304_ws_coverC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega=RingMicromega5Psatz00C47Corelib4Init3Nat3mulC47Corelib4Init3Nat3addK46Stdlib9micromega=RingMicromega5Psatz07C47Corelib4Init9Datatypes6lengthC49OSSVerify5KrLib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega5Psatz05C49OSSVerify5KrLib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec8v_addi_0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC59OSSVerify5KrLib7Mh_00568MemSplit6win_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4v_lwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit4cmemC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup12J1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup19regs_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit3wfJC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit:wfJ_wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:step_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0041:StartupAuxBv_andi_m16_alignedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_jal_x0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C59OSSVerify5KrLib7Mh_00417ArgvEnv;read_argc_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0041:StartupAux=rdn_low_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit>rdn_cmem_aboveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0041:StartupAuxEbytes_le_to_Z_4_smallC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7step_lwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit=rdn_cmem_dataC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC49OSSVerify5KrLib8PropExec7step_ldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac<word_add_natC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib7Mh_00417ArgvEnv?read_argv_ptr_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib7Mh_00387SeqExec<step_slli_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t03C59OSSVerify5KrLib7Mh_00387SeqExec=step_jal_linkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit?wbytes_cmem_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0041:StartupAux:v_lw_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK46Stdlib9micromega7EnvRing5PExpr04C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplitAstore_ok_cmem_winC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06C59OSSVerify5KrLib7Mh_0041:StartupAux:getr_emptyC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC59OSSVerify5KrLib7Mh_00387CatExecBstack_max_size_valC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M5phdrsC1@~~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup16len_avC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup16u_argcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38a98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38a98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38a98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38a9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38a9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38a9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38aa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38aa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38aa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38aa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38aa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38aa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38aa8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38aa8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38aa8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38aacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38aacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38aacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ab0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ab0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ab0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ab4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ab4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ab4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ab8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ab8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ab8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38abcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38abcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38abcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ac0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ac0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ac0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ac4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ac4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ac4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c58f0_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ac8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ac8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ac8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c58f8_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38accC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c5900_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ad0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ad0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ad0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ad4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ad4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ad4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ad8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ad8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ad8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38adcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38adcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38adcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8ba0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8ba0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8ba0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8ba4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8ba4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8ba4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8ba8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8ba8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8ba8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bb4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bb4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bb4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bbcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bbcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bbcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bc0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bc0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bc0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bc8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bc8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bc8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8920C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8920C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8920C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8924C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8924C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8924C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8928C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8928C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8928C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a892cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a892cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a892cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8930C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8930C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8930C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8934C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8934C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8934C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8938C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8938C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8938C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a893cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a893cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a893cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8944C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8944C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8944C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8948C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8948C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8948C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout=at_random_ptrK46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic3notC59OSSVerify5KrLib7Mh_0041:StartupTac3bwdC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs@after_last_slashC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs6envp_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs5J_auxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs6D_libcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit@wbytes_cmem_dataC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC49OSSVerify5KrLib8PropExec:getr_otherC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup27rd_auxvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_tkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec?rdn_wbytes_hit8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib7Mh_00568MemSplit<rdn_cmem_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00417ZStoresCrdn_wbytes_zeros_inC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<c_eq_0_falseC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_bne_tkC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib7Mh_00385Hoare?regs_agree_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare@regs_agree_transC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup29prog_loopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup29envp_loopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplitBstore_ok_cmem_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup28rdn_addrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib7Mh_00387CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_addC59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8994C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8994C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8994C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8998C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8998C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8998C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a899cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a899cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a899cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8988C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8988C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8988C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a898cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a898cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a898cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8990C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8990C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8990C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00c59OSSVerify5KrLib7Mh_0058;Ns0Startup26len_avC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup26len_evC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup29pn_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a894cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a894cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a894cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8950C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8950C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8950C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c5a50_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8954C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8954C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8954C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8964C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8964C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8964C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8968C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8968C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8968C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a896cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a896cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a896cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8970C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8970C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8970C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8974C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8974C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8974C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8978C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8978C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8978C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a897cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a897cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a897cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8980C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8980C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8980C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8984C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8984C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8984C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89f4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c5a58_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89fcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c5a60_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a2cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs5rnd_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs5J_lsmC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs4pn_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs6argc_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs6auxv_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs:progname_wC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7v_addiwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_lwuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:step_addiwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup36len_avC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup3:rnd_boundsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c94C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c6d70_4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c98C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c58e8_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8ca0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8ca0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8ca0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8ca4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8ca4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8ca4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8ca8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8ca8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8ca8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cb0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cc8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cc8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cc8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cbcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cbcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cbcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cc0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cc0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cc0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cd0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cd0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cd0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8ce4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8ce4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8ce4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8ce8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8ce8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8ce8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cf0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cf0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cf0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d14C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_10040_4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cb4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cb4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cb4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_10050_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cb8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_10078_4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_100b0_4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_100e8_4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_10120_4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_10158_4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_bne_ftC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<step_bgeu_tkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_10190_4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_101c8_4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cf4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cf4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cf4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_101f0_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8cf8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8cf8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8cf8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_10200_4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_10238_4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_andC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_xoriC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387WalkTac9v_add_0_rC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_andC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_xoriC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5c_ltsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_blt_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387WalkTac9v_add_0_lC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d50C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_d8758_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d54C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_d8768_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d58C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_d8770_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8d9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8d9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8d9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8da0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8da0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8da0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8da4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8da4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8da4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8da8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8da8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8da8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8de8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8de8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8de8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8decC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8decC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8decC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8df0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8df0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8df0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8df4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8df4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8df4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_d8b48_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8df8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8df8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8df8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_d8b30_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8dfcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8dfcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8dfcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8e00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8e00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8e00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8e04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8e04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8e04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8e08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8e08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8e08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8e0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8e0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8e0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8e10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8e10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8e10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8e14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8e14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8e14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8e18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8e18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8e18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8e1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8e1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8e1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8e20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8e20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8e20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8e24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8e24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8e24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r59000_59c907W_bbffcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r59000_59c907F_bbffcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r59000_59c907D_bbffcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r59000_59c907W_bc000C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r59000_59c907F_bc000C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r59000_59c907D_bc000C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r59000_59c907W_bc004C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r59000_59c907F_bc004C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r59000_59c907D_bc004C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8e9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8e9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8e9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ea0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ea0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ea0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ea4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ea4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ea4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8eacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8eacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8eacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8eb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8eb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8eb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8eb4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8eb4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8eb4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8eb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8eb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8eb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ebcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ebcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ebcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ec0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ec0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ec0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_d8b08_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ec4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ec4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ec4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ec8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ec8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ec8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8eccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8eccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8eccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ed0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ed0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ed0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ed8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ed8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ed8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8edcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8edcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8edcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ee0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ee0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ee0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ee4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ee4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ee4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ee8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ee8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ee8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8eecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8eecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8eecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ef0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ef0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ef0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ef4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ef4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ef4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8ef8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8ef8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8ef8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9ed_randomc59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs3rlwC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs5rnd4wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs8canary_wC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs4rnd4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs;guard_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0041:StartupAux@v_andi_3_alignedC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout?at_random_bytesC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnc59OSSVerify5KrLib7Mh_0058;Ns0Startup46rd_rndC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs7rnd4_eqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup48rdn_addrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs8rnd4_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs;rd_guard_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs:canary_valC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup4:rnd_boundsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c5a78_8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup46len_avC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a93ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a93ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a93ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a93f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a93f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a93f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a93f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a93f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a93f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a93f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a93f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a93f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a93fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a93fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a93fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9400C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9400C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9400C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9404C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9404C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9404C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9408C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9408C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9408C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b993cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b993cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b993cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9a50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9a50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9a50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9a54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9a54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9a54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9a58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9a58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9a58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9a5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9a5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9a5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9a60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9a60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9a60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9a98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9a98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9a98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9a9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9a9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9a9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9aa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9aa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9aa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9aa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9aa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9aa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9aa8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9aa8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9aa8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9aacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9aacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9aacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ab0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ab0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ab0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ab4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ab4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ab4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9ab8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9ab8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9ab8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9abcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9abcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9abcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9cfcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9cfcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9cfcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9d00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9d00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9d00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9d04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9d04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9d04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9d08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9d08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9d08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_b9d0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_b9d0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_b9d0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a940cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a940cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a940cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9428C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9428C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9428C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a942cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a942cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a942cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9430C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9430C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9430C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9434C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9434C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9434C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9438C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9438C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9438C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a943cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a943cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a943cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9440C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9440C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9440C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9444C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9444C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9444C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9448C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9448C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9448C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00417ZStores<length_zerosC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9c_eq_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0041:StartupAux<Z_to_bv_u_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a3cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a3cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a3cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b3cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b3cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b3cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b40C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bd0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bd0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bd0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bd4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bd4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bd4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bd8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bdcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bdcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bdcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8be0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8be0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8be0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8be4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8be4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8be4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8be8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8be8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8be8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8becC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8becC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8becC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bf0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bf0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bf0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bf4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bf4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bf4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<step_bgeu_ftC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec>step_jalr_linkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bf8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bf8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bf8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bfcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bfcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bfcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c1cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup49slli_argcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b54C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b58C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b5cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a891cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a891cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a891cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b68C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c5a68_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b6cC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c5a70_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b74C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_bf9a0_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b78C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8step_lbuC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ae0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ae0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ae0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ae4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ae4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ae4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ae8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ae8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ae8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38aecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38aecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38aecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38af0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38af0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38af0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38af4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38af4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38af4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38af8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38af8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38af8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c6d90_1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38afcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38afcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38afcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38b00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38b00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38b00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38b0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38b0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38b0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38b10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38b10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38b10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38b14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38b14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38b14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38b18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38b18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38b18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38b1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38b1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38b1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38b20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38b20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38b20C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_00586Ns0Img;img_c5908_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38b24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38b24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38b24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38b44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38b44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38b44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38b48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38b48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38b48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38b4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38b4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38b4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38b50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38b50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38b50C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b90C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b94C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c30C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8c38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8c38C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8c38C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib7Mh_00568MemSplit=wbytes_insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit>wbytes_outsideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs6D_mainC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib9micromega;ZifyClasses6eq_iffc59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts6len_avC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058<Ns0MainEntry5vals0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058<Ns0MainEntry6blobs0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive8blobs_evC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058<Ns0MainEntry2E0C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25a_offC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX22evC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S5elenZC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX22ebC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26adenotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058<Ns0MainEntry5auxvpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K47Corelib4Init;Hexadecimal4uint02K47Corelib4Init;Hexadecimal4uint06K47Corelib4Init;Hexadecimal4uint03K47Corelib4Init6Number4uint02C47Corelib4Init3Nat;of_num_uintC59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_windowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058<Ns0MainEntry7kimg_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts;D_main_selfC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058:Ns0StartupCmain_entry_rdn_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts>main_entry_tidC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts=D_main_localeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts;D_canary_ptC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058:Ns0StartupCmain_entry_mem_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts:D_guard_ptC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058<Ns0MainEntry<D_main_auxvpC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts?D_main_pagesizeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts:D_hwcap_ptC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058?Ns0StartupFacts<D_main_missbC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_lK47Corelib5Lists7ListDef6Forall02I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058<Ns0MainEntry3ke5C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058<Ns0MainEntry5kp_loC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058<Ns0MainEntry5kp_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init;Hexadecimal4uint01c59OSSVerify5KrLib7Mh_0058<Ns0MainEntry9wseg_dataC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02c59OSSVerify5KrLib7Mh_0058<Ns0MainEntry3ke3C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058<Ns0MainEntry8kn_imageC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4v_lbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:SumWalkTac?bytes_le_to_Z_4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0ExitBase:file_cleanC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0ExitBase=stdio_globalsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7step_lbC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_blt_tkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:SumWalkTac9c_eq_reflC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058<Ns0Exit_run27mem_w3aC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae938C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae938C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae938C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae93cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae93cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae93cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae944C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae944C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae944C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_aed60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_aed60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_aed60C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_aed64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_aed64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_aed64C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_aed68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_aed68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_aed68C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_aed6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_aed6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_aed6cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_aed70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_aed70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_aed70C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_aed74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_aed74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_aed74C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_aed78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_aed78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_aed78C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba5ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba5ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba5ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba5d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba5d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba5d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba5d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba5d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba5d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba7c4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba7c4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba7c4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_aed7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_aed7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_aed7cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_aed80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_aed80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_aed80C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_aed84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_aed84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_aed84C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_aed88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_aed88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_aed88C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007W_aed8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007F_aed8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4e000_4f0007D_aed8cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae948C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae948C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae948C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae94cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae94cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae94cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae950C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae950C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae950C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae954C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae954C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae954C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae958C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae958C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae958C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9c8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9c8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9c8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9ccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9d0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aeaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aeaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aeaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aead0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aead0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aead0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aead4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aead4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aead4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aead8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aead8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aead8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9300C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9300C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9300C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9304C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9304C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9304C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8f9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8f9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8f9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8fa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8fa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8fa0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058<Ns0Exit_run3@stdout_dirty_hdrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib7Mh_0055:SumWalkTac6c_eq_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9e0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9e4C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058=Ns0MainEntryN8kimg_okNC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058=Ns0MainEntryN=D_main_auxvpNC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058=Ns0MainEntryN2ENC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058=Ns0MainEntryN5valsNC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058=Ns0MainEntryN6blobsNC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058=Ns0MainEntryN4keN5C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058=Ns0MainEntryN6auxvpNC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058=Ns0MainEntryN:wseg_dataNC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058=Ns0MainEntryN4keN3C1?~~~~~~~~~~~~~~~".
Module Ns0Memset.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022.Ns0_code_r58000_59000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Definition memset304_ws : list (Z * nat) :=
  [(0,1%nat); (303,1%nat); (1,1%nat); (2,1%nat); (301,1%nat); (302,1%nat); (3,1%nat); (300,1%nat); (0,4%nat); (300,4%nat); (4,4%nat); (8,4%nat); (292,4%nat); (296,4%nat); (12,4%nat); (16,4%nat); (20,4%nat); (24,4%nat); (276,4%nat); (280,4%nat); (284,4%nat); (288,4%nat); (24,8%nat); (32,8%nat); (40,8%nat); (48,8%nat); (56,8%nat); (64,8%nat); (72,8%nat); (80,8%nat); (88,8%nat); (96,8%nat); (104,8%nat); (112,8%nat); (120,8%nat); (128,8%nat); (136,8%nat); (144,8%nat); (152,8%nat); (160,8%nat); (168,8%nat); (176,8%nat); (184,8%nat); (192,8%nat); (200,8%nat); (208,8%nat); (216,8%nat); (224,8%nat); (232,8%nat); (240,8%nat); (248,8%nat); (256,8%nat); (264,8%nat); (272,8%nat)]%Z.

Lemma memset304_ws_inb : ws_inb memset304_ws 304 = true.
Proof using. vm_compute. reflexivity. Qed.
Lemma memset304_ws_cover : ws_cover memset304_ws 304 = true.
Proof using. vm_compute. reflexivity. Qed.

Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

(* [comment removed for export] *)
Lemma memset304_run : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 304 ->
  (bv_unsigned d mod 8 = 0)%Z ->
  (bv_unsigned d + 304 < 2^64)%Z ->
  store_ok SEGS mem d 304 = true ->
  exists regs' mem',
    msteps SEGS (mkst regs (0xb9ef8 : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof using fx.
  intros regs mem rom d ret Hra Hret Hd H11 H12 Hal Hnw Hok.
  pose proof (u64_range d) as Hdr.
  assert (Hal4 : (bv_unsigned d mod 4 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity). rewrite Hal. reflexivity. }
  eexists. eexists. split; [|split].
  - 
    stepb_ft F_b9ebc D_b9ebc ltac:(pin; cond_compute).
    stw F_b9ec0 D_b9ec0 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_b9ec4 D_b9ec4 (Z_to_bv 64 (bv_unsigned d + 304)).
    sn F_b9ec8 D_b9ec8.
    stw F_b9ecc D_b9ecc (Z_to_bv 64 (bv_unsigned d + 303)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_b9ed0 D_b9ed0 ltac:(pin; cond_compute).
    stw F_b9ed4 D_b9ed4 (Z_to_bv 64 (bv_unsigned d + 1)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9ed8 D_b9ed8 (Z_to_bv 64 (bv_unsigned d + 2)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b9edc D_b9edc.
    stw F_b9ee0 D_b9ee0 (Z_to_bv 64 (bv_unsigned d + 301)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9ee4 D_b9ee4 (Z_to_bv 64 (bv_unsigned d + 302)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_b9ee8 D_b9ee8 ltac:(pin; cond_compute).
    stw F_b9eec D_b9eec (Z_to_bv 64 (bv_unsigned d + 3)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b9ef0 D_b9ef0.
    stw F_b9ef4 D_b9ef4 (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_b9ef8 D_b9ef8 ltac:(pin; cond_compute).
    sn F_b9efc D_b9efc.
    sn F_b9f00 D_b9f00.
    sn F_b9f04 D_b9f04.
    stepiv F_b9f08 D_b9f08 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply negw_and3_aligned; exact Hal4).
    sn F_b9f0c D_b9f0c.
    sn F_b9f10 D_b9f10.
    sv F_b9f14 D_b9f14 (d).
    sn F_b9f18 D_b9f18.
    sn F_b9f1c D_b9f1c.
    sn F_b9f20 D_b9f20.
    stw F_b9f24 D_b9f24 (Z_to_bv 64 (bv_unsigned d + 0)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_b9f28 D_b9f28 (Z_to_bv 64 (bv_unsigned d + 304)).
    stw F_b9f2c D_b9f2c (Z_to_bv 64 (bv_unsigned d + 300)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_b9f30 D_b9f30 ltac:(pin; cond_compute).
    stw F_b9f34 D_b9f34 (Z_to_bv 64 (bv_unsigned d + 4)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f38 D_b9f38 (Z_to_bv 64 (bv_unsigned d + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b9f3c D_b9f3c.
    stw F_b9f40 D_b9f40 (Z_to_bv 64 (bv_unsigned d + 292)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f44 D_b9f44 (Z_to_bv 64 (bv_unsigned d + 296)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_b9f48 D_b9f48 ltac:(pin; cond_compute).
    stw F_b9f4c D_b9f4c (Z_to_bv 64 (bv_unsigned d + 12)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f50 D_b9f50 (Z_to_bv 64 (bv_unsigned d + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f54 D_b9f54 (Z_to_bv 64 (bv_unsigned d + 20)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f58 D_b9f58 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepiv F_b9f5c D_b9f5c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_4_aligned8; exact Hal).
    sn F_b9f60 D_b9f60.
    sn F_b9f64 D_b9f64.
    sn F_b9f68 D_b9f68.
    stw F_b9f6c D_b9f6c (Z_to_bv 64 (bv_unsigned d + 276)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f70 D_b9f70 (Z_to_bv 64 (bv_unsigned d + 280)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f74 D_b9f74 (Z_to_bv 64 (bv_unsigned d + 284)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f78 D_b9f78 (Z_to_bv 64 (bv_unsigned d + 288)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stepb_ft F_b9f7c D_b9f7c ltac:(pin; cond_compute).
    sn F_b9f80 D_b9f80.
    sv F_b9f84 D_b9f84 (Z_to_bv 64 (bv_unsigned d + 24)).
    sn F_b9f88 D_b9f88.
    sn F_b9f8c D_b9f8c.
    sn F_b9f90 D_b9f90.
    stw F_b9f94 D_b9f94 (Z_to_bv 64 (bv_unsigned d + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f98 D_b9f98 (Z_to_bv 64 (bv_unsigned d + 32)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f9c D_b9f9c (Z_to_bv 64 (bv_unsigned d + 40)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9fa0 D_b9fa0 (Z_to_bv 64 (bv_unsigned d + 48)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b9fa4 D_b9fa4.
    sv F_b9fa8 D_b9fa8 (Z_to_bv 64 (bv_unsigned d + 56)).
    stepb_tk F_b9fac D_b9fac ltac:(pin; cond_compute).
    stw F_b9f94 D_b9f94 (Z_to_bv 64 (bv_unsigned d + 56)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f98 D_b9f98 (Z_to_bv 64 (bv_unsigned d + 64)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f9c D_b9f9c (Z_to_bv 64 (bv_unsigned d + 72)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9fa0 D_b9fa0 (Z_to_bv 64 (bv_unsigned d + 80)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b9fa4 D_b9fa4.
    sv F_b9fa8 D_b9fa8 (Z_to_bv 64 (bv_unsigned d + 88)).
    stepb_tk F_b9fac D_b9fac ltac:(pin; cond_compute).
    stw F_b9f94 D_b9f94 (Z_to_bv 64 (bv_unsigned d + 88)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f98 D_b9f98 (Z_to_bv 64 (bv_unsigned d + 96)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f9c D_b9f9c (Z_to_bv 64 (bv_unsigned d + 104)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9fa0 D_b9fa0 (Z_to_bv 64 (bv_unsigned d + 112)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b9fa4 D_b9fa4.
    sv F_b9fa8 D_b9fa8 (Z_to_bv 64 (bv_unsigned d + 120)).
    stepb_tk F_b9fac D_b9fac ltac:(pin; cond_compute).
    stw F_b9f94 D_b9f94 (Z_to_bv 64 (bv_unsigned d + 120)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f98 D_b9f98 (Z_to_bv 64 (bv_unsigned d + 128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f9c D_b9f9c (Z_to_bv 64 (bv_unsigned d + 136)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9fa0 D_b9fa0 (Z_to_bv 64 (bv_unsigned d + 144)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b9fa4 D_b9fa4.
    sv F_b9fa8 D_b9fa8 (Z_to_bv 64 (bv_unsigned d + 152)).
    stepb_tk F_b9fac D_b9fac ltac:(pin; cond_compute).
    stw F_b9f94 D_b9f94 (Z_to_bv 64 (bv_unsigned d + 152)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f98 D_b9f98 (Z_to_bv 64 (bv_unsigned d + 160)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f9c D_b9f9c (Z_to_bv 64 (bv_unsigned d + 168)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9fa0 D_b9fa0 (Z_to_bv 64 (bv_unsigned d + 176)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b9fa4 D_b9fa4.
    sv F_b9fa8 D_b9fa8 (Z_to_bv 64 (bv_unsigned d + 184)).
    stepb_tk F_b9fac D_b9fac ltac:(pin; cond_compute).
    stw F_b9f94 D_b9f94 (Z_to_bv 64 (bv_unsigned d + 184)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f98 D_b9f98 (Z_to_bv 64 (bv_unsigned d + 192)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f9c D_b9f9c (Z_to_bv 64 (bv_unsigned d + 200)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9fa0 D_b9fa0 (Z_to_bv 64 (bv_unsigned d + 208)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b9fa4 D_b9fa4.
    sv F_b9fa8 D_b9fa8 (Z_to_bv 64 (bv_unsigned d + 216)).
    stepb_tk F_b9fac D_b9fac ltac:(pin; cond_compute).
    stw F_b9f94 D_b9f94 (Z_to_bv 64 (bv_unsigned d + 216)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f98 D_b9f98 (Z_to_bv 64 (bv_unsigned d + 224)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f9c D_b9f9c (Z_to_bv 64 (bv_unsigned d + 232)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9fa0 D_b9fa0 (Z_to_bv 64 (bv_unsigned d + 240)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b9fa4 D_b9fa4.
    sv F_b9fa8 D_b9fa8 (Z_to_bv 64 (bv_unsigned d + 248)).
    stepb_tk F_b9fac D_b9fac ltac:(pin; cond_compute).
    stw F_b9f94 D_b9f94 (Z_to_bv 64 (bv_unsigned d + 248)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f98 D_b9f98 (Z_to_bv 64 (bv_unsigned d + 256)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9f9c D_b9f9c (Z_to_bv 64 (bv_unsigned d + 264)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_b9fa0 D_b9fa0 (Z_to_bv 64 (bv_unsigned d + 272)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sn F_b9fa4 D_b9fa4.
    sv F_b9fa8 D_b9fa8 (Z_to_bv 64 (bv_unsigned d + 280)).
    stepb_ft F_b9fac D_b9fac ltac:(pin; cond_compute).
    stepret F_b9fb0 D_b9fb0 ret ltac:(pin; reflexivity).
    apply mst_refl.
  - rewrite <- (zstores_cover d 304 Hnw memset304_ws mem 304%nat eq_refl memset304_ws_inb memset304_ws_cover).
    reflexivity.
  - unfold memset_clob. solve_regs_agree.
Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0Memset.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.
Module Ns0Startup1.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Img OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r1ff24_20000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r20000_21000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4a000_4b000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4b000_4c000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022.Ns0_code_r58000_59000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Ns0Startup1 () := "C59OSSVerify5KrLib7Mh_00417ArgvEnv7u_argcNC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesI47Corelib5Lists7ListDef6Forall00C45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathI47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib7Mh_00568MemSplit3wfJC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc59OSSVerify5KrLib7Mh_0058;Ns0Startup19regs_initC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit4cmemC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyC49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulC49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC45stdpp9bitvector;definitions9bv_signedC56Stdlib6ZArith6BinInt1Z6shiftlC49OSSVerify5KrLib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:step_auipcC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions4BvWfK47Corelib7Numbers7BinNums1Z03C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_addiC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_00387WalkTac=wf_getr_chainC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C49OSSVerify5KrLib8PropExec6v_andiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0041:StartupAuxBv_andi_m16_alignedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib7Mh_00387SeqExec<step_andi_atC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_jal_x0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4v_lwC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01I47Corelib4Init5Peano2le00K46Stdlib9micromega6VarMap1t01C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00417ArgvEnv;read_argc_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0041:StartupAux=rdn_low_bytesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00568MemSplit>rdn_cmem_aboveC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8v_addi_0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib7Mh_0041:StartupAuxEbytes_le_to_Z_4_smallC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7step_lwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit6win_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit=rdn_cmem_dataC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=bytes_le_to_ZC49OSSVerify5KrLib8PropExec7step_ldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec<step_addi_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:step_sd_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit:wfJ_wbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC47Corelib4Init3Nat3addC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib7Mh_00387StepTac<word_add_natC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC59OSSVerify5KrLib7Mh_00417ArgvEnv?read_argv_ptr_wC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C59OSSVerify5KrLib7Mh_00387SeqExec<step_slli_atC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib7Mh_00387SeqExec;step_add_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec=step_jal_linkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit?wbytes_cmem_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0041:StartupAux:v_lw_smallC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib7Mh_0058;Ns0Startup12J1C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr04C35stdpp7tactics<f_equal_helpC59OSSVerify5KrLib7Mh_00568MemSplitAstore_ok_cmem_winC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib7Mh_0041:StartupAux:getr_emptyC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op205C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC59OSSVerify5KrLib7Mh_00387CatExecBstack_max_size_valC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00c59OSSVerify5KrLib7Mh_0058;Ns0Startup16len_avC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup16u_argcC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M5phdrsC1@~~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38a98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38a98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38a98C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38a9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38a9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38a9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38aa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38aa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38aa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38aa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38aa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38aa4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38aa8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38aa8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38aa8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38aacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38aacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38aacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ab0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ab0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ab0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ab4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ab4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ab4C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ab8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ab8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ab8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38abcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38abcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38abcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ac0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ac0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ac0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ac4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ac4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ac4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00586Ns0Img;img_c58f0_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ac8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ac8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ac8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00586Ns0Img;img_c58f8_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38accC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00586Ns0Img;img_c5900_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ad0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ad0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ad0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ad4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ad4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ad4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38ad8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38ad8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38ad8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007W_38adcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007F_38adcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r1ff24_200007D_38adcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b98C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8b9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8b9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8b9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8ba0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8ba0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8ba0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8ba4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8ba4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8ba4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8ba8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8ba8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8ba8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bacC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bb0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bb4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bb4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bb4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bb8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bbcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bbcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bbcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bc0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bc0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bc0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bc4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8bc8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8bc8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8bc8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8920C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8920C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8920C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8924C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8924C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8924C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8928C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8928C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8928C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a892cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a892cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a892cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8930C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8930C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8930C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8934C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8934C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8934C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8938C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8938C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8938C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a893cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a893cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a893cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8940C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8944C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8944C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8944C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8948C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8948C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8948C1?~~~~~~~~~~~~~~~".
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition regs_init (sp0 : word) : bvmap 5 word :=
  regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp0.

Section P1.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  Let argc : word := argcN av.
  Local Notation argvp := (Z_to_bv 64 (bv_unsigned sp0 + 8)) (only parsing).
  Let envp : word := envp_ptr sp0 av.
  Let pn : word := cat_argv_ptr sp0 av ev 0.

  Lemma u_argc : bv_unsigned argc = Z.of_nat (length av).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup1 ()) ["FPX_1"; "P1"] "p;2g0000j20Tp,2avp,3Hva'0o"). Qed.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup1 ()) ["FPX_1"; "P1"] "h01ah14__x1h21Hh32H1h42H2h52_Hh67__arithh74__ffh86__sat3h98__varmaph:5__with;4cstrh<1vp;1p;2p;3p;4p;7p;8g000lj15Tg001Jj14Tg001oj19Tg002Mj1ZTg0030j1>Tg003Pj2<Tg0040j1;Tg004Pj20Tg004lR0j23Tg005Gj1DTg006Cj37Tg006dj2YTg007Jj3VTg007aj1UTg008:j1RTg009>j36Tg009Xj2QTg00:Lj2OTg00:cj1NTg00;Hj2LTg00<2j2KTg00<cj2JTg00=Cj1ITg00=cj2FTg00>Aj1GTg00>_j1HTg00?Jj2ETg00?mj2?Tg00@Pj4:Tg00A;j1CTg00A]j7MTg00BAj2BTg00Bcj2PTg00C=j2ATg00Cij3STg00DHj4TTg00E:j1@Tg00E_j7XTg00FCj8WTf0R1#4#4p=1%@1#@p=2f1R2g00FgR3g00GFR4P4g00GfR5P1g00HFFXp=8f3P3P4P4P5f2R6P2P1GWp==p,3Hvag00HfR7#5R8%47#1R9#9R:#ZR;#>R<p,2avR='<R>#;R?'0R@%49R9#1RA#1#1RB#5RC,0?RD'3RE%D=%4B#1#1#1#1#1#5'01<;1#;%27#2#2#2#2#2#2#2#5'0X0<=7<=g00IKRB,Y:=V;1#UX0<=7<=g00IiR;g00JYR:%R1g00K9RF36g00KY,Q1=6:F'3X0;1O<=37'3'3'3R='3P0PEP=PEP1P0P@PDPE\=P1%N>10B?%9Ap,3sp0'LRA%59R9'K10BA10B91JA9,0B[[g00LZR9g00M8RA#I%>A1F92%G9%H9RAP91E97R7g00MdR>1?9CC:,8AR0%C4R<PAP91?98P>P7C:,8AR7P<PAP3P4P4P5P7P0FMC=C=1BA5P1P6g00NKRA,P:1A16=6:AdAS9B2CTb7b9b:W1101C10821086106C'3[[^19P1P?f4f5O3b6b8b;X5=X4DX3@P2P1O2n2001000010121000000X2EP2P1O2n2001000000121000000b<o"). Qed.

  (* [comment removed for export] *)
  Definition J1 (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0xa8c14)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argvp))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x38c2c)).

  Lemma p1_run : forall rom (J : word -> option byte),
    wfJ sp0 J ->
    exists regs',
      msteps SEGS (mkst (regs_init sp0) (0x38ae0 : word) (CM J (fun _ => None)) rom)
                  (mkst regs' (0xb9ef8 : word) (CM (J1 J) (fun _ => None)) rom)
      /\ getr regs' 1 = Z_to_bv 64 0xa8994
      /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416)
      /\ getr regs' 3 = Z_to_bv 64 0x10800
      /\ getr regs' 4 = Z_to_bv 64 0
      /\ getr regs' 8 = pn
      /\ getr regs' 9 = envp
      /\ getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368)
      /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 304
      /\ getr regs' 18 = Z_to_bv 64 0x38c2c
      /\ (forall r : reg, In r [5;19;20;21;22;23;24;25;26;27]%list -> getr regs' r = Z_to_bv 64 0).
Proof using fx sp0 av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros rom J HJ.
pose proof len_av as Hlen. pose proof u_argc as Hargc.
eexists. split.
- unfold regs_init.
stepn F_38a98 D_38a98.
stepn F_38a9c D_38a9c.
stepn F_38aa0 D_38aa0.
stepn F_38aa4 D_38aa4.
stepn F_38aa8 D_38aa8.
stepiv F_38aac D_38aac sp0 ltac:(gres; imm_norm; apply v_andi_m16_aligned; exact Hal).
stepn F_38ab0 D_38ab0.
chain_step; [reflexivity | eapply step_lw with (bs := word_to_le_bytes 4 argc) (v := argc);
[ exact F_38ab4 | reflexivity | exact D_38ab4
| addr_norm; rewrite rdn_cmem_above by region_side;
apply (rdn_low_bytes SEGS mem0 sp0 argc 4); [lia|];
exact (read_argc_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hhi)
| apply bytes_le_to_Z_4_small; rewrite Hargc; lia ]
| step_simpl]; vnorm.
rewrite (v_lw_small argc) by (rewrite Hargc; lia).
stepn F_38ab8 D_38ab8.
stepn F_38abc D_38abc.
stepn F_38ac0 D_38ac0.
chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0x38c2c);
[exact F_38ac4 | reflexivity | exact D_38ac4 | rd_img img_c58f0_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0xa8964);
[exact F_38ac8 | reflexivity | exact D_38ac8 | rd_img img_c58f8_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
chain_step; [reflexivity | eapply step_ld with (v := Z_to_bv 64 0xa9280);
[exact F_38acc | reflexivity | exact D_38acc | rd_img img_c5900_8 | vm_compute; reflexivity] | step_simpl]; vnorm.
sv F_38ad0 D_38ad0 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
stepn F_38ad4 D_38ad4.
stepn F_38ad8 D_38ad8.
stepn F_38adc D_38adc.
sv F_a8b98 D_a8b98 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
stw F_a8b9c D_a8b9c (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_a8ba0 D_a8ba0 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_a8ba4 D_a8ba4 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_a8ba8 D_a8ba8 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stepn F_a8bac D_a8bac.
stepn F_a8bb0 D_a8bb0.
stepn F_a8bb4 D_a8bb4.
chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 pn) (v := pn);
[ exact F_a8bb8 | reflexivity | exact D_a8bb8
| addr_norm; rewrite rdn_cmem_above by region_side;
replace (Z_to_bv 64 (bv_unsigned sp0 + 8)) with (sp0 + nat_to_word (8 + 8 * 0))
by (rewrite word_add_nat; f_equal; lia);
exact (read_argv_ptr_w SEGS RPH sp0 av ev uid hw rdraw Hva Hve Hlo Hhi 0 ltac:(lia))
| apply bytes_le_to_Z_8 ]
| step_simpl]; vnorm.
stepiv F_a8bbc D_a8bbc (Z_to_bv 64 (8 * Z.of_nat (length av)))
ltac:(gres; imm_norm; rewrite <- Hargc; unfold v_slli; f_equal; rewrite Z.shiftl_mul_pow2 by lia; change (2^3)%Z with 8%Z; lia).
stepiv F_a8bc0 D_a8bc0 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))) vclose.
stepiv F_a8bc4 D_a8bc4 envp
ltac:(gres; imm_norm; unfold envp, envp_ptr, v_addi; unorm; f_equal; lia).
stepn F_a8bc8 D_a8bc8.
sv F_a8920 D_a8920 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stw F_a8924 D_a8924 (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0xa8c14) ltac:(ok_win HJ).
stw F_a8928 D_a8928 (Z_to_bv 64 (bv_unsigned sp0 - 48)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
stw F_a892c D_a892c (Z_to_bv 64 (bv_unsigned sp0 - 56)) argc ltac:(ok_win HJ).
stw F_a8930 D_a8930 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 0x38c2c) ltac:(ok_win HJ).
stepn F_a8934 D_a8934.
stepn F_a8938 D_a8938.
sv F_a893c D_a893c (Z_to_bv 64 (bv_unsigned sp0 - 368)).
stepn F_a8940 D_a8940.
stepn F_a8944 D_a8944.
stepn F_a8948 D_a8948.
apply mst_refl.
- repeat split; gres; try reflexivity.
intros r Hr. cbn [In] in Hr.
repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
[ .. | contradiction]; gres; apply getr_empty.
Qed.
End P1.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0Startup1.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.
Module Ns0StartupDefs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Abbreviation RPH := Plain.M.phdrs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.

Lemma after_last_slash_le : forall s i acc, (acc <= i)%nat ->
  (after_last_slash s i acc <= i + length s)%nat.
Proof.
  induction s as [|c s IH]; intros i acc H; cbn [after_last_slash length]; [lia|].
  etransitivity; [apply IH; destruct (bv_eqb _ _); lia | lia].
Qed.

Lemma progname_off_le : forall s, (progname_off s <= length s)%nat.
Proof. intro s. unfold progname_off. pose proof (after_last_slash_le s 0 0). lia. Qed.

(* [comment removed for export] *)
Definition rnd4 (rnd : bv 128) (j : nat) : list byte := firstn 4 (skipn j (at_random_bytes rnd)).
Definition rnd4w (rnd : bv 128) (j : nat) : word := Z_to_bv 64 (bytes_le_to_Z (rnd4 rnd j)).
Definition rlw (rnd : bv 128) (j : nat) : word := v_lw (rnd4w rnd j).
Definition guard_bytes (rnd : bv 128) : list byte :=
  firstn 1 (word_to_le_bytes 4 (rlw rnd 0)) ++ [Z_to_bv 8 0] ++ sub (word_to_le_bytes 4 (rlw rnd 0)) 2 2
  ++ word_to_le_bytes 4 (rlw rnd 4).
Definition canary_w (rnd : bv 128) : word := Z_to_bv 64 (bytes_le_to_Z (guard_bytes rnd)).

Lemma rnd4_eq : forall rnd j, firstn 4 (skipn j (at_random_bytes rnd)) = rnd4 rnd j.
Proof. reflexivity. Qed.
Lemma length_rnd4 : forall rnd j, (j + 4 <= 16)%nat -> length (rnd4 rnd j) = 4%nat.
Proof. intros rnd j Hj. unfold rnd4. rewrite length_firstn, length_skipn, length_at_random_bytes. lia. Qed.
Lemma rnd4_val : forall rnd j, bytes_le_to_Z (rnd4 rnd j) = bv_unsigned (rnd4w rnd j).
Proof.
  intros rnd j. unfold rnd4w. symmetry.
  pose proof (bytes_le_to_Z_nonneg (rnd4 rnd j)). pose proof (bytes_le_to_Z_bound (rnd4 rnd j)) as Hb.
  assert (Hl : (length (rnd4 rnd j) <= 4)%nat).
  { unfold rnd4. rewrite length_firstn. lia. }
  assert (2 ^ (8 * Z.of_nat (length (rnd4 rnd j))) <= 2 ^ 32)%Z by (apply Z.pow_le_mono_r; lia).
  apply u_Z2bv; lia.
Qed.
Lemma length_word_to_le_bytes : forall n v, length (word_to_le_bytes n v) = n.
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.
Lemma length_guard_bytes : forall rnd, length (guard_bytes rnd) = 8%nat.
Proof.
  intro rnd. unfold guard_bytes, sub. rewrite !length_app, !length_firstn, length_skipn, !length_word_to_le_bytes. reflexivity.
Qed.
Lemma canary_val : forall rnd, bytes_le_to_Z (guard_bytes rnd) = bv_unsigned (canary_w rnd).
Proof.
  intro rnd. unfold canary_w. symmetry.
  pose proof (bytes_le_to_Z_nonneg (guard_bytes rnd)). pose proof (bytes_le_to_Z_bound (guard_bytes rnd)) as Hb.
  rewrite length_guard_bytes in Hb. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in Hb. apply u_Z2bv; lia.
Qed.
Lemma canary_bytes : forall rnd, word_to_le_bytes 8 (canary_w rnd) = guard_bytes rnd.
Proof.
  intro rnd. unfold canary_w, word_to_le_bytes.
  pose proof (canary_val rnd) as Hv. unfold canary_w in Hv. rewrite <- Hv.
  rewrite <- (length_guard_bytes rnd) at 1. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
Lemma rd_guard_gen : forall segs (D : word -> option byte) (w0 w4 : list byte) (g : Z),
  length w0 = 4%nat -> length w4 = 4%nat ->
  (0 <= g)%Z -> (g + 8 < 2^64)%Z ->
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 g) w0)
                          (Z_to_bv 64 (g + 4)) w4)
                  (Z_to_bv 64 (g + 1)) [Z_to_bv 8 0]) (Z_to_bv 64 g) 8 = Some (firstn 1 w0 ++ [Z_to_bv 8 0] ++ sub w0 2 2 ++ w4).
Proof.
  intros segs D w0 w4 g L0 L4 Hg0 Hg1.
  assert (U : forall k, (0 <= k <= 8)%Z -> bv_unsigned (Z_to_bv 64 (g + k)) = (g + k)%Z) by (intros; apply u_Z2bv; lia).
  assert (U0 : bv_unsigned (Z_to_bv 64 g) = g) by (apply u_Z2bv; lia).
  assert (A : forall k j z, (0 <= k)%Z -> (k + Z.of_nat j <= 8)%Z -> (z = k + Z.of_nat j)%Z ->
             (Z_to_bv 64 (g + k) + nat_to_word j)%bv = Z_to_bv 64 (g + z)).
  { intros k j z Hk Hj ->. rewrite at_nat. unfold at_. rewrite U by lia. f_equal. lia. }
  change 8%nat with (1 + (1 + (2 + 4)))%nat.
  apply rdn_app.
  { rewrite rdn_wbytes_out by (cbn [length]; rewrite ?U, ?U0; lia).
    rewrite rdn_wbytes_out by (rewrite ?U, ?U0, ?L4; lia).
    apply (rdn_firstn segs _ 4); [|lia]. rewrite <- L0. apply rdn_wbytes_hit. rewrite U0, L0. lia. }
  replace (Z_to_bv 64 g + nat_to_word 1)%bv with (Z_to_bv 64 (g + 1))
    by (rewrite at_nat; unfold at_; rewrite U0; reflexivity).
  apply rdn_app.
  { apply (rdn_wbytes_hit segs [Z_to_bv 8 0]). cbn [length]. rewrite U; lia. }
  rewrite (A 1%Z 1%nat 2%Z) by lia.
  apply rdn_app.
  { rewrite rdn_wbytes_out by (cbn [length]; rewrite ?U; lia).
    rewrite rdn_wbytes_out by (rewrite ?U, ?L4; lia).
    replace (Z_to_bv 64 (g + 2)) with (at_ (Z_to_bv 64 g) (Z.of_nat 2)) by (unfold at_; rewrite U0; reflexivity).
    apply (rdn_sub segs _ 4). 2: lia. rewrite <- L0. apply rdn_wbytes_hit. rewrite U0, L0. lia. }
  rewrite (A 2%Z 2%nat 4%Z) by lia.
  rewrite rdn_wbytes_out by (cbn [length]; rewrite ?U; lia).
  rewrite <- L4 at 1. apply rdn_wbytes_hit. rewrite U, L4; lia.
Qed.

Lemma rd_guard_at : forall segs (D : word -> option byte) rnd (g : Z),
  (0 <= g)%Z -> (g + 8 < 2^64)%Z ->
  rdn segs (wbytes (wbytes (wbytes D (Z_to_bv 64 g) (word_to_le_bytes 4 (rlw rnd 0)))
                          (Z_to_bv 64 (g + 4)) (word_to_le_bytes 4 (rlw rnd 4)))
                  (Z_to_bv 64 (g + 1)) [Z_to_bv 8 0]) (Z_to_bv 64 g) 8 = Some (guard_bytes rnd).
Proof.
  intros. unfold guard_bytes. apply rd_guard_gen; try assumption; apply length_word_to_le_bytes.
Qed.

Section Defs.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rnd : bv 128.

  (* [comment removed for export] *)
  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  (* [comment removed for export] *)
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN av.
  (* [comment removed for export] *)
  Definition pn_w : word := cat_argv_ptr sp0 av ev 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  (* [comment removed for export] *)
  Definition rnd_w : word := at_random_ptr sp0 av ev.

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0xd8780) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xf8ae8) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0xf8b48) (word_to_le_bytes 8 hw))            (* [comment removed for export] *)
      (Z_to_bv 64 0xf8b10) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0xf8ad8) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0xf8ad0) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0xa8c14)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x38c2c)).

  (* [comment removed for export] *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))                   (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))     (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))                  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))                  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w).                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xf8878) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xf8888) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xf8880) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xf8af8) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0xf8b00) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xd8860) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0xd8848) (word_to_le_bytes 8 (Z_to_bv 64 0xd8860)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xd8788) (word_to_le_bytes 8 (Z_to_bv 64 0xd8788)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xf8ae0) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0xd87b0) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xd87a8) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0xd8820) (word_to_le_bytes 8 (Z_to_bv 64 0xf8b18)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xd8800) (word_to_le_bytes 8 (Z_to_bv 64 0xd8800)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xd8790) (word_to_le_bytes 8 (Z_to_bv 64 0xd8788)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xd8798) (word_to_le_bytes 8 (Z_to_bv 64 0xd8788)))  (* [comment removed for export] *)
      (Z_to_bv 64 0xd87a0) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

  Definition D_tls (tid : word) (D : word -> option byte) : word -> option byte :=
    D_tlsB tid (D_tlsA D).

  (* [comment removed for export] *)
  Definition J_tls (J : word -> option byte) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 s4))
      (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 s5).

  (* [comment removed for export] *)
  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0xf8ac0) (word_to_le_bytes 4 (rlw rnd 0)))   (* [comment removed for export] *)
      (Z_to_bv 64 0xf8ac4) (word_to_le_bytes 4 (rlw rnd 4)))   (* [comment removed for export] *)
      (Z_to_bv 64 0xf8ac1) [Z_to_bv 8 0])                       (* [comment removed for export] *)
      (Z_to_bv 64 0xd8840) (word_to_le_bytes 8 (canary_w rnd)). (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0xc6dd0) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.

End FPX_1.

End Ns0StartupDefs.
Module Ns0Startup2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Img OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0StartupDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4a000_4b000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RPH := Plain.M.phdrs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Ns0Startup2 () := "C46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesI47Corelib5Lists7ListDef6Forall00C45stdpp9bitvector;definitions7Z_to_bvC46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC45stdpp9bitvector;definitions;bv_unsignedC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathI47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib7Mh_00387StepTac9bsb_boundC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M5phdrsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8wrap_memC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExecDrdn_wrap_stack_aboveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit4cmemC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit>rdn_cmem_aboveC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3mulC59OSSVerify5KrLib7Mh_00419RefLayout<cat_envp_ptrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib7Mh_00419RefLayout8envp_offC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3mulC47Corelib4Init3Nat3addC35stdpp7tactics<f_equal_helpC4ELinuxProcessSemantics?LinuxProcessSem6BvBase;nat_to_wordC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib7Mh_00387StepTac<word_add_natC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00419RefLayout?read_envp_ptr_kC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup28rd_aboveC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulc59OSSVerify5KrLib7Mh_0058;Ns0Startup26len_avC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup26len_evC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib7Mh_0058;Ns0Startup27Hsp_hi'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00419RefLayout>read_envp_nullC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem;StackLayout=at_random_ptrC59OSSVerify5KrLib7Mh_00419RefLayout:auxv_wordsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthC59OSSVerify5KrLib7Mh_00419RefLayout8auxv_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00419RefLayout>read_auxv_wordC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0041:StartupTac3bwdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib7Mh_00385Hoare:regs_agreeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedc59OSSVerify5KrLib7Mh_0058;Ns0Startup2<rd_envp_nullC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8v_addi_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions4BvWfI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_00387WalkTac=wf_getr_chainC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4c_eqC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_bne_ftC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib7Mh_00385Hoare?regs_agree_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare>regs_agree_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00419RefLayout?cat_envp_ptr_nzC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup27rd_envpC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<c_eq_0_falseC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_bne_tkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare@regs_agree_transC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes7nat_indC49OSSVerify5KrLib8PropExec7step_ldC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec<step_addi_atC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8958C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8958C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8958C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a895cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a895cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a895cC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8960C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8960C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8960C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c59OSSVerify5KrLib7Mh_0058;Ns0Startup27Hsp_lo'C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00417ArgvEnvBargv_ptr_bounds_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00417ArgvEnv6bsb_nwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec@read_argv_byte_kC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_lec59OSSVerify5KrLib7Mh_0058;Ns0Startup29pn_boundsC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C49OSSVerify5KrLib8PropExec8u8_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib5Lists7ListDef5skipnC59OSSVerify5KrLib7Mh_00387CatExecAvalid_argv_str_nzC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC47Corelib4Init3Nat3subC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib5Arith8PeanoNat3Nat8sub_diagC47Corelib4Init5Peano2geC56Stdlib6ZArith6BinInt1Z2geC46Stdlib5Lists4List8app_nth2c59OSSVerify5KrLib7Mh_0058;Ns0Startup2=rd_argv0_byteC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup28rdn_addrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_skipnC56Stdlib5Arith8PeanoNat3Nat7add_0_rC46Stdlib5Lists4List8app_nth1C46Stdlib5Lists4List6nth_InC46Stdlib5Lists4List;skipn_skipnC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup2;c_eq_byte47C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_tkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplitBstore_ok_cmem_dataC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:step_sd_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit=wbytes_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit6win_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit@wbytes_cmem_dataC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup2:c_eq_byte0C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs@after_last_slashC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C49OSSVerify5KrLib8PropExec8step_lbuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_geC59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a1cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a20C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a18C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op204C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a14C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC59OSSVerify5KrLib7Mh_00387CatExecBstack_max_size_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit3wfJC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs6envp_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs5J_auxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0058>Ns0StartupDefs6D_libcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00417ZStores5zerosC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC49OSSVerify5KrLib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec:step_auipcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit=rdn_cmem_dataC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC49OSSVerify5KrLib8PropExec:getr_otherC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_jal_x0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup27rd_auxvC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_slliC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplit:wfJ_wbytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec?rdn_wbytes_hit8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib7Mh_00568MemSplit<rdn_cmem_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00417ZStoresCrdn_wbytes_zeros_inC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C59OSSVerify5KrLib7Mh_00385Hoare7at_selfC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib7Mh_00568MemSplit?wbytes_cmem_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec=step_jal_linkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare?regs_agree_monoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup29prog_loopC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058;Ns0Startup29envp_loopC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC49OSSVerify5KrLib8PropExec5c_ltuC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec<step_bltu_ftC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_slliC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec;step_add_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00568MemSplitAstore_ok_cmem_winC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8994C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8994C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8994C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8998C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8998C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8998C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a899cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a899cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a899cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89a0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89a4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89a8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8988C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8988C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8988C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a898cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a898cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a898cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8990C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8990C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8990C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a894cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a894cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a894cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8950C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8950C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8950C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00586Ns0Img;img_c5a50_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8954C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8954C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8954C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8964C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8964C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8964C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8968C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8968C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8968C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a896cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a896cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a896cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8970C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8970C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8970C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8974C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8974C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8974C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8978C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8978C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8978C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a897cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a897cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a897cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8980C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8980C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8980C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8984C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8984C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8984C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89acC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89b0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89b4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89b8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89bcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89d4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89d8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89dcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89e4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89f4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00586Ns0Img;img_c5a58_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89f8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a89fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a89fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a89fcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00586Ns0Img;img_c5a60_8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a04C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007W_a8a2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007F_a8a2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4a000_4b0007D_a8a2cC1?~~~~~~~~~~~~~~~".
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Section P3.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation mem0 := (wrap_mem RPH sp0 av ev uid hw rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).
  Local Notation stk := (stack_to_mem sp0 (entry_stack_image RPH sp0 av ev uid hw rdraw)) (only parsing).
  (* [comment removed for export] *)
  Local Notation E := (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))%Z (only parsing).
  Local Notation A := (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))%Z (only parsing).

  Local Notation pn := (cat_argv_ptr sp0 av ev 0) (only parsing).
  Local Notation rnd := (at_random_ptr sp0 av ev) (only parsing).
  Local Notation s := (nth 0 av []) (only parsing).
  Local Notation A8 := (Z_to_bv 64 0xf8ad0) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "h01ah14__x1h21Hh32H1h42H2h52_Hh67__arithh74__ffh86__sat3h98__varmaph:5__with;4cstrh<1vp;1p;2p;3p;4p;7p;8p10000p4p710p1000Kp4p710p8p1000ip4p710p1001Hp4p710p8g001dj15Tg002Bj14Tg002gj19Tg003Ej1ZTg003hj1>Tg004Hj2<Tg004hj1;Tg005Hj20Tg005dR0j23Tg006?j1DTg007;j37Tg007\j2YTg008Bj3VTg008Yj1UTg0092j1RTg00:6j36Tg00:Pj2QTg00;Dj2OTg00;[j1NTg00<@j2LTg00<jj2KTg00=[j2JTg00>;j1ITg00>[j2FTg00?9j1GTg00?Wj1HTg00@Bj2ETg00@ej2?Tg00AHj4:Tg00B3j1CTg00BUj7MTg00C9j2BTg00C[j2PTg00D5j2ATg00Daj3STg00E@j4TTg00F2j1@Tg00FWj7XTg00G;j8WTf0R1#4#4p=1%@1#@p=2f1R2g00G_R3g00H>R4P4g00H^R5P1g00I>FXp=8f3P3P4P4P5f2R6P2P1GWp==p,3Hvag00I^R7#5R8%47#1R9#9R:#ZR;#>R<p,2avR='<R>#;R?'0R@%49R9#1RA#1#1RB#5RC,0?RD'3RE%D=%4B#1#1#1#1#1#5'01<;1#;%27#2#2#2#2#2#2#2#5'0X0<=7<=g00JCRB,Y:=V;1#UX0<=7<=g00JaR;g00KQR:%R1g00L1RF36g00LQ,Q1=6:F'3X0;1O<=37'3'3'3R='3P0PEP=PEP1P0P@PDPE\=P1%N>10B?%9Ap,3sp0'LRA%59R9'K10BA10B91JA9,0B[[g00MRR9g00N0RA#I%>A1F92%G9%H9RAP91E97R7g00N\R>1?9CC:,8AR0%C4R<PAP91?98P>P7C:,8AR7P<PAP3P4P4P5P7P0FMC=C=1BA5P1P6g00OCRA,P:1A16=6:AdAS9B2CTb7b9b:W1101C10821086106C'3[[^19P1P?f4f5O3b6b8b;X5=X4DX3@P2P1O2n2001000010121000000X2EP2P1O2n2001000000121000000b<o"). Qed.
  Lemma len_ev : (Z.of_nat (length ev) <= 256)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "h04__x1h11eh22H1h32_Hh47__arithh54__ffh66__sat2h78__varmaph85__with94cstrh:1vp;1p;2p;3p;4p;7p;8g002Bj13Tg002gj1:Tg003Ej1?Tg003hj1;Tg004Hj29Tg004hj18Tg001dj14Tg005Hj20Tg006?j1@Tg007;j36Tg007\j2<Tg008Bj3TTg008Yj1STg005dR0j25Tg00;[j1RTg00<@j2QTg00<jj2PTg00=[j2LTg00>;j1KTg00>[j2ETg00?9j1CTg00?Wj1BTg00@Bj2DTg00@ej2ATg00AHj4FTg00FWj7GTg00B3j1HTg00G;j8ITg00C9j2JTg00C[j2>Tg00D5j2MTg00:6j3NTg00Daj3=Tg00E@j4OTg00F2j17Tf0R1#3#3p=2%71#7p=1p,3Hveg00I^R2#3#2R3#:R4#?R5#;R6p,2evR7'9R8#8R9%33R3#2R:#2R;#4R<'0R=%@7%3;#2#2#2#2#4'01951#8%12#1#1#1#1#1#1#1#4'0X16=667g00JCR;,<4=T51#SX16=667'5'5R7'5P0P=P7P=P1%R810;9%::p,3sp0'QR:%43R3'P10;:10;31L:3,0;[[g00MRR3g00N0R:#K%;:f1R:,E3%C3%B3R8g00G_R0g00H>R6P6g00H^R5P8P0P6P6P5P31D32g00N\1A3<CFg00I>FGR2%H6P2GI1J85P1f2R5g00KQR8g00OCR2'>1M15=N82dA=3;:COb5b7b8W0101<10:<[^03P1P9f4O2b4b6b9X37X2=P:P1O2n2001000000121000000b:o"). Qed.

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "p,3Hloo"). Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "p,3Hhio"). Qed.

  Lemma bsb_len : (Z.of_nat (length (build_stack_bytes RPH sp0 av ev uid hw rdraw)) <= 2240000)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "p;9g00Ocl90Tg00Pap,3sp0p,2avp,2evp,3uidp,2hwp,5rdrawp,3Hvap,3HveM90o"). Qed.

  (* [comment removed for export] *)
  Lemma rd_above : forall J D (a : Z) n bs,
    (bv_unsigned sp0 <= a)%Z -> (a + Z.of_nat n < 2^64)%Z ->
    rdn SEGS stk (Z_to_bv 64 a) n = Some bs ->
    rdn SEGS (CM J D) (Z_to_bv 64 a) n = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "h04__x1h14__x2h27__arithh34__ffh46__sat1h56__sat2h66__sat3h78__varmaph85__with94cstrh:2Hah;4__x3h<1zh=1Dh>1Hh?2H0h@2HnhA1JhB1ahC2bshD1nhE1op;1p;2p;7p;4p;3p;6p;<p;9p;8g002Bj10Tg002gj1LTg003Ej1ITg00R@j1STg003hj1OTg00<@j2CTg005Hj21Tg004hj1:Tg00Rbj29Tg001dj1>Tg00S?j2VTg00S\j26Tg00T8j7oTg00U6j2jTg007\j2BTg00V7j4<Tg00Vhj2MTg00:6j3ETg00WJj1dTg005dj2aTg00XAj7`Tg00;[j1_Tg00Y7j2^Tg00Y_j3]Tg00<jj2\Tg00=[j2[Tg00>;j1ZTg00>[j2JTg00ZCj1YTg00Zaj4ATg00?9j1XTg00?Wj1WTg00@Bj2@Tg00B3j1UTg00C9j2TTg00C[j2nTg00D5j2mTg00Daj3lTg00E@j4iTg00[?j1FTg00[^j2;Tg00\Gj3=Tg00]0j2PTg00]\j3KTg00F2j1HTg00@ej2DTg00^<j3NTg00^_j3fTg00_Bj3eTg000Kj6?Tg00`=l<cTg00a?j4gTg00b9l9hTg00AHj4QTg00FWj7bTg00G;j8kTf0R0#0#0p=Rg00JCR1/10p=3g00MRR2f1R3g00N\P0CQp=8P3g00G_R4g00H>R5P5g00H^R6P0g00I>Fbp=2f3R7P4P5P5P6f2R4P3P0Gkp=5%H0#Hp=4%00#0#0#0p=7P2P3g00c=P0CQp=Gg00I^R8#0R9#0R:#0R;#0R<#RR=#LR>#I%L;#IR;#S[R?g00cd%O;R;p,3sp0R@,C>RA/14%:4,97%>9RB%>=R='VRC'6%S;RDg00dCREg00PaRFP@p,2avRGp,2evRHp,3uidRIp,2hwRJp,5rdrawRKFo,j@RLf4RM,B>P7C<1M;43Ef5RN,B>RO#d1C>ORO#316OC'aPDPEPFP@PGPHPIPJPKF`ROf6RP,B>RQPNC<RR1M;N9ED0XEDR;PDPEPLPQPNC<P;P3PRPEPFP@PGPHPQPNPIPJPKP2PP11A0X<2%_NRK%:N#3RJ1^B=RI161B%3=161C[[RH%3BRGg00elRFA]B=3UW:R=%3C\F^:GRG%><R<,\ARF%3A%3<1[A<#3[[R<g00N0RR#ZR;%ORRLP21J24P3%Y2RDCARS%X2RT%W2RU1@28RV1@29R9'8,2URW%U5R5PWC51TU6R6P0P4g00KQRWg00OCRX'n1m04=EWXdAl213CiRXb3b7b8X02X1211031134[^02^12P0f;RWPAf8RYO3b2b4b5b6b91C>QRZPKPJPIPHP=PGPFP<g00fHR[#FR\#FR],;2R^1;2\1;2[R[5=25=2g00fgR\'P=KR;PLPSPTPU189V,2UP5PU%H8#4#4#4#4#4#4#4#0#R#7#7#7#7#7#7#7#>R8,D2/89,2UR_P51D21R1/8V,2UC5C5P6PXb3b7b8X02X1211301184%34R`[[^02^12P0PAPWPYp,3HloRaO4b2b4b5b6b9PKPJPIPHP=PGPFP<%F],;2A=2^[5=2/P\=KR;PLP2P21J27P4PDCAP3PDCAPTPU1@2:R:,81,2UP5PUAN2V:1D2B=f2>R>'G,2UP5PUP_P51GV>,2UC5C5C5P6PXb3b7b8X02X12X;21937/6C1187167C[[\`^02^12^;2P0f:#:R`PAPWPMf7RMPaO6b2b4b5b6b95ePRaE?RAP2PP%:P,90/1CX<2PKPJPIPHP=PGPFP<P;PLPSPTPUAN2V9R9/G>,2UP5189>,2UC5P6PXb3b7b8X02X121903/6C1934/1C[^02^12P0P`PWPMO3b2b4b5b6b9PZPaE?RaM<cE?PEP@POPYPMCgPQPNC<P@POPEPYPMPQPNPAPaM9hE?b?W>W@W:WCWDXB2X=?WAo"). Qed.

  Lemma rd_envp : forall J D k, (k < length ev)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat k)) 8
    = Some (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "h04__x1h14__x2h24__x3h34__p1h41xh53Hk0h67__arithh74__ffh86__sat2h98__varmaph:5__with;4cstrh<5cstr0h=5cstr1h>2Hah?4__x4h@1bhA1yhB1DhC1HhD2H0hE2H1hF2HkhG1JhH6__sat3hI6__sat4hJ1khK1mhL1np%0p&0p;1p;2p;4p;3p;<p;8p;6p;7p;=p;Bg002Bj10Tg002gj1\Tg003Ej1bTg00R@j1jTg003hj1cTg004Hj2_Tg00gSR0j2[Tg001dj18Tg004hR1j14Tg005Hj22Tg005dj2QTg00<@j2kTg00gkR2j23Tg00RbR3j21Tg00[?j1;Tg00hHj4dTg00iKj2aTg00S\R4j2<Tg00jSk401Tg00;[j1LTg00<jj2yTg00=[j2wTg00[^j2ETg00]0j2]Tg00k:j2rTg00>;j1qTg00]\j3eTg00>[j2KTg00Zaj4JTg00?9j1mTg00?Wj1lTg00@ej2VTg00F2j1GTg00@Bj2HTg00B3k10ETg00kfj3TTg00C9k20DTg00C[j2STg00D5k20CTg00:6j39j1{Tg00Dak30BTg00E@k40ATg00S?k20=Tg00lIj1`Tg00lgk40<Tg00mJl<RTg00Y7k20:Tg00Y_k304Tg00mok202Tg00nXj3PTg00ZCk100Tg00AHj4ITg00^_j3~Tg00oAj4ZTg00olj1}Tg010kj2OTg011Bj2DTg007\j2Nj1zTg011Yj8|Tg0126j1gTg0131j3WTg013Vj2vTg000Kj6uTg00T8j7tTg00U6k203Tg00V7j4sTg00Vhk205Tg014Wm=06Tg001Hk607Tg015]k808Tg00\Gk309Tg00FWj7pTg016^j6oTg00BUk70>Tg00^<j3nTg00G;k80?Tg017Bm<0@Tg017glBUTf0R5#0#0p=Ff2R6f1R7'1/15p=Cg00MRR8/S5p=5g00cdR9P8P0P1P4g018Mf5R0f4R:f3R;P6P7P5M<Rp>0;g00JCR</25p=6B09875p=BP8P7g00N\P5CIp=AP7g00G_R=g00H>R>P>g00H^R?P5g00I>Fpp=71V85p=:P7P=P>P>P?P5Eop=iP6P=P>P>P?P7P5K0>p=h%G5#Gp=@%05#0#0#0p=f%05#0#0#0#0#0#0#0p=?An875p==P;P=P>P>P?P6P7P5L0?p=>P9P8P8P8P1P1P0P:P;P6P7P5N<0@p=^P8P8P8P8P8P8P3P5P7P6P3P;P:P0f6R=f7R@f8S00f9RAMBUp=X1375,16p=xP9P9P9P8P8P8g018oP1P1P1P3g019OP0P:P;P6P7P5MBUp=MP9P9P9P8P8P8g01:2P1P1P1P2g01:RP0P:P;P6P7P5MBUp=Yg00I^R2#0R1#FR3#0RB#FRC#\RD#bRE%\3#bRF#j[RG%cFRFp,2evRH'_RI,[5g01;5%82RJp,2avRK,_FRL#4RM'2S01%FCRN#FRO#8RP,2MRQ'Qg01<4%4IRR%8NRN'2P0P:p,3sp0RS,kDRT%8BRB%83R3/3M3CRU%4;RV,33RW'1RXg00fHRY#;RZ#;R[#;R\#;R]#;R^#;#;#;R_PSPKPHP;Cd,a_1[;I1<VRR`P;PV%5VS02PIPR%5RJ0;P6H01RaP`%L:Rb%4:Rc#6Rd%LLRe%6MRf%LIRI%6RRg1yTBRh%6T%6B1wTB#6[[Rip-0Rjg00N0Rk1E8YRY1E8]R]1E8\R\'B,BYg00fgRl']'r%qkRm3e%ckRnP81K86S03P71K8;CJS04%m8Ro%l8Rp1V8<%G2Rq,H8Rr'A,7p&0E>R>Pp%:JRs1H81Rt'A,7p1ip05hpP>Pp%@q#@#@#@#@#@#@#0#F#f#?#?#?#8Rq#:1H82R2'A,7pS05P>%:B,=2%:3Ru=T8t'=AT8urRv'=Rw,A2,7pC>C>C>20Dp?R?P5P6g00KQRxg00OCRy'S20C56=9xydB0B8<7H0ARyb7b9b:X08X18X28W3%6612J6/Q:12q611;B133:13303C,2;[[[^08^18^28^3jP5PQ%4AS06PMPTP:P@p,3HloRQO7b6b8b=b<b;b5%4_Rx,1XRz%81R{%8CRC+0=R|'<11X3R}/<|P8P8P4P5X48R~P41<75#`XA8X48PzP}P~P~P~P8P8g01=31175H0<#5XK8XL8R}PXPX%5XS07PxP3P~P~%45#5X49RxP_P3%53RzE^M:XP|P|%5|M<RPaP`PbPdPePfPIPg20:{C1<<{%6C1<<|[[%6{R<g00elR4B04{C7UW>%6|\4^><PhPi20283R<1E8^5P8AP8<]AP8<\1E8[/BY'B'B'B/]l=ekmPnP8Q03P7P81K8:P;&008CJCJPoPpP8Prg00c=Rr%G1,H8R1CI,7pP>Pp%:N,A1,7pP>Pp1ip=%:P,At,7p5hpP>Pp%0O#f#?#?#?#?#8RO#:,A2,7pP>PpQ05P>P81=wuPr%:{=~8DCI,7pC>C>C>C>C>P?Pyb7b9b:X08X18X28X?8X3j1<6;12:N12;P,Q=12;O12q:133=9C0B133@;C3/<|[[[[[^08^18^28^?8^3jP5Q01PRf;#4PMPTP@Q00PAp,3HhiPQO:b6b8bHbIb=b<b;b5CZPE%}KRQ1O_;RA'DR@#4,1TRR,NDAxU3c,NDRc99E5X@EP8PE%zDRUPUPRPXPE\8/SU1DLZRU,O_Rj,D_R|/DAR=#4Rq,1TRO=98X11MJRP,33RN,13R{/1WRr,1TR>=98XP8P8%{8R1P~P1A9875#`XA8X48POP>P~P~P~P}PTPT%5TPqPrP~P~PxP=PrP|P{P_P3PzPjPNP_P3PzPUPPPLPM%5MPZPJ%5JEMEYEMPAPWP_P3PzP;PVQ02EYEME^M:XPXPXQ07M<RPaP`PbPdPePfPIPgPhPiPmPnQ04PoP81=ts9T8u,=u/=v,=2g01=WPwCI,7pP?Pyb7b9b:X08X18X28117J,331336R65C3,15115B1337;C6598^08^18^28P5Q06PMPTO3b6b8b=b<b;b5CZA98RXeG|%g@9WDSRR1vS@Eu1NDX99ERPE1O_:,DQ#g9WDS%jFg00dCRDg00PaRQPSPKPHp,3uidRRp,2hwRXp,5rdrawR@Ft-03SP5P_CsPSPKPHP0Cd,a_-05F39X@EPDPQPSP@PKPHPRPXp,3Hvap,3Hveg01>>P:P;N=06PcP5J07bEL08bDbCWFXJ9XBGWGo"). Qed.

  Lemma rd_envp_null : forall J D,
    rdn SEGS (CM J D) (Z_to_bv 64 (E + 8 * Z.of_nat (length ev))) 8
    = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "h04__x1h14__x2h24__x3h34__p1h41xh57__arithh64__ffh76__sat1h88__varmaph95__with:4cstrh;5cstr0h<2Hah=1bh>1yh?1Dh@1HhA2H0hB2H1hC1JhD6__sat2hE6__sat3hF1mhG1np&0p;1p;2p;3p;4p;6p;<p;8p;7p;;p;Bg002Bj10Tg002gj1WTg003Ej1STg00R@j1`Tg001dj17Tg003hj1[Tg004Hj2YTg004hR0j1ATg005Hj22Tg005dj2ITg00<@j2fTg00RbR1j21Tg00gkR2j24Tg00[?j1;Tg007\j2Mj1rTg00iKk20:Tg00;[j1QTg00<jj2yTg00=[j2uTg00[^j2ETg00\Gj3CTg00]0j2VTg00k:j2oTg00>;j1mTg00]\j3PTg00>[j2_Tg00Zaj4iTg00?9j1hTg00?Wj1gTg00@ej2RTg00F2j1HTg00@Bj2GTg00B3j1eTg016^j6dTg00kfj3OTg00C9k20=Tg00C[j2NTg00D5k20<Tg00:6j38j1qTg00Dak30;Tg00E@k409Tg00S?k208Tg00S\R3j2@Tg00lIj1^Tg00lgk402Tg00mJl<TTg00Y7j2xTg00Y_j3wTg00moj2vTg00nXj3ZTg00^_j3tTg00AHj4KTg00oAj4XTg00olj1sTg010kj2aTg011Bj2FTg011Yj8pTg0126j1nTg0131j3zTg013Vj2{Tg000Kj6|Tg00T8j7}Tg00U6j2~Tg00V7j4lTg00Vhk200Tg01?>m;01Tg001Hj6kTg015]j8jTg00FWk703Tg00BUk704Tg00^<k305Tg00G;k806Tg017Bm<07Tg017glBLTf0R4#0#0p=Df2R5f1R6'1/14p=Bg00JCR7/24p=5g00MRR8P6g00N\P4CKp=<P6g00G_R9g00H>R:P:g00H^R;P4g00I>K03p=61R84p=9P5P9P:P:P;P6P4K04p=c%H4#Hp==%04#0#0#0p=b%04#0#0#0#0#0#0#0p=?B05864p=:f3R<P9P:P:P;P5P6P4L06p=>1N84p=3g00cdR=P8P8P8P0P0f5R>f4R?P<P5P6P4N<07p=]P8P8P8P8P8P8P1P4P6P5P1P<P?P>f6R@f7RAf8f9MBLp=\P=P=P=P8P8P8g018oP0P0P0P1g019OP>P?P<P5P6P4MBLp=JP=P=P=P8P8P8g01:2P0P0P0P2g01:RP>P?P<P5P6P4MBLp=Ug00I^R2#0R0#DR1#0RB#DRC#WRD#SRE%W1#SRF#`[RGg01;5%72RH%[FRFp,2avRI'YRJ#ARK'2RL%DCRM#DRN#7RO,2KRP'Ig01<4p,2evRQ,YFRR#ARS%7MRM'2P<P5p,3sp0RT,fDRU%7BRB'1%71R1/4K141SRV3BRWg00fHRX#;RY#;RZ#;R[#;R\#;#;#;#;R]1MD7-0:]R^%QJR_%5KR`%QRRa%5SRb1yUBRc%5U%5B1uUB#5[[Rdp-0Reg00N0Rf1E8XRX1E8\R\1E8[R[5C89C8Xg00fgRg'V'o%mfRh3P%[fRiP81_85P61_8<CiRj%h8Rk%g8Rl1R87%H2Rm,G8Rn'<,6l%e:RoPl%9HRp1G80Rq'<,6lPlP9P:P:P;P>EdR:5clPoPl%=m#=#=#=#=#=#=#0#D#b#?#?#?#7Rm#91G82R2'<,6lR9Po%9B,:2%91Rr=O8q':AO8rnRs':Rt,<2,6lC>C>C>20=l;R;P4P5g00KQRug00OCRv'N20<45=8uvdB0;876H09Rvb6b8b9X08X18X28W3%5512H5/I?12m511<B141?141>Ru3B,2<[[[^08^18^28^3eP4PPPSPKPUP5P>p,3HloR>O7b5b7b;b:%A]RP,1WRw%70R0%7CRC+08Rx'@11W1Ry/@xP8P8P3P4X48RzP31@64#^X>8X48PwPyPzPzPzP8P8g01=31164H02#3XF8XG8RyPWPW%3WRwPPP1PzPz%A4#3X4=R=P]P1%31RPE]M:\PxPx%3xM<TP_P`PaPb1x0C1@70%5C1@7x[[%50R7g00elR3Aw0C6UW<%5x\3^<7PcPd1v81R7=Z8\AZ87[1E8Z=C8X5C85C8/Vg=PfhPiPjPkPl%9M,<n,6lPoPl%9O,<q,6l9cl:PoPl%0N#b#?#?#?#?#7RN#9,<2,6lPoPlP9PoP81:trg00c=%90=t8DCK,6lC>C>C>C>P;Pvb6b8b9X08X18X28X3e125M125O,I?125N12m<AB?Bu141@;B1/@x[[[[^08^18^28^3eP4PLPSPKPUP@PAp,3HhiP>O8b5b7bDbEb;b:CXPE%sI1a]RR>'FRA#A,1UR@,MD1MDWRL98E4X=EP8PE%rDRePeP@PWPE\8/Ne1FJYRe,a]Rx,F]Ru/F>R?#ARm,1UR<=88W11KHRN,41RO,11RM/1VR0,1URo=88WP8P8%q8R9PzP9A8864#^X>8X48P<PoPzPzPzPyPUPU%3UPmP0PzPzP=P?P0PuPMP]P1PPPxPOP]P1PPPePNPJPK%3KPYPH%3HEJEUEJP>PVP]P1PPPRPS%3SEUEJE]M:\PWPWPwM<TP_P`PaPbPcPdPhPiPjPkP81:qp9O8r,:r/:s,:2g01=WPtCK,6lP;Pvb6b8b9X08X18X28116H,411415R55B1,14114B1416;B5588^08^18^28P4PSPKPUO3b5b7b;b:CXA88@WeGp%nA9zDTRD1{TAE|A8EDLPEPD%`Fg00dCRDg00PaRAPTPIPQp,3uidR@p,2hwRWp,5rdrawR8F},~TP4P]Cl200F^38X=EPDPAPTP8PIPQP@PWp,3Hvap,3Hveg01>>N;01PLP4EkbBGjbAb@X?GWCo"). Qed.

  Lemma rd_auxv : forall J D j w, (j < 20)%nat ->
    nth j (auxv_words RPH rnd uid hw) (Z_to_bv 64 0) = w ->
    rdn SEGS (CM J D) (Z_to_bv 64 (A + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 w).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "h04__x1h14__x2h24__x3h34__x4h44__p1h51xh63Hj0h77__arithh84__ffh96__sat2h:8__varmaph;5__with<4cstrh=5cstr0h>5cstr1h?2Hah@1bhA1whB1yhC1DhD1HhE2H0hF2H1hG2HjhH2HwhI1JhJ6__sat3hK6__sat4hL1jhM1mhN1np%0p&0p;1p;2p;3p;4p;6p;<p;8p;7p;=p;Bg002Bj10Tg002gj1bTg003Ej1hTg00R@j1nTg00[?j1>Tg00gSR0j2aTg01@Ck300Tg01AEj4zTg007\j2Mj1|Tg01BFj4]Tg00:6j37j1}Tg001dj13Tg003hj1mTg004Hj2jTg004hR1j19Tg005Hj28Tg005dj2UTg00<@k20>Tg00F2j1KTg00RbR2j21Tg00gkR3j22Tg00iKj2OTg00S\R4j2?Tg00jSj4yTg00;[j1VTg00<jj2vTg00=[j2sTg00[^j2GTg00]0j2^Tg00k:j2qTg00>;j1pTg00]\j3[Tg00>[j2YTg00ZCk10GTg00Zaj4oTg00?9k10FTg00?Wk10ETg00@ej2lTg00@Bj2LTg00B3k10DTg016^k60BTg00kfj3ITg00C9k20ATg00C[j2TTg00D5k20=Tg00Dak30<Tg00E@k40;Tg00S?k20:Tg00lIj1dTg00lgk409Tg00mJl<STg00Y7k205Tg00Y_k304Tg00mok203Tg00nXj3RTg00AHj4JTg00^_k302Tg00oAj4`Tg01Bbj2~Tg010kj2HTg011Bj2=Tg011Yk801Tg0126j1NTg0131j3XTg013Vk206Tg000Kj6xTg00T8k707Tg00U6k208Tg00V7j4\Tg00Vhj2kTg01Cal=wTg001Hj6eTg015]j8uTg00\Gj3tTg00FWj7fTg00BUk70?Tg00^<k30@Tg00G;j8rTg017Bm<0CTg017glBWTf0R5#0#0p=E%>5#>p=Af2R6f1R7'1/15p=<g00MRR8/T5p=5g00cdR9P8P0P1P4g018Mf5R0f4R:f3R;P6P7P5M<Sp={g00JCR</85p=4At875p=DP6g00G_R=g00H>R>P>g00H^R?P8P7g00N\P5CJg00I>R@Ffp=@1l85p=:P6P=P>P>P?P7P5K0?p=i%K5#Kp=C%05#0#0#0p=g%05#0#0#0#0#0#0#0p=BB0@875p=6P;P=P>P>P?P6P7P5Grp=;P9P8P8P8P1P1P0P:P;P6P7P5N<0Cp=cP8P8P8P8P8P8P2P5P7P6P2P;P:P0f6RAf7RBf8RCf9S00MBWp=ZP7P=P>P>P?P5P@Ffp=P1275,16p=_P9P9P9P8P8P8g018oP1P1P1P2g019OP0P:P;P6P7P5MBWp=FP9P9P9P8P8P8g01:2P1P1P1P3g01:RP0P:P;P6P7P5MBWp=Qg00I^R3#0R1#0R2#0R@#0RD#ERE#bRF#hRG%b@#hRH#n[S01Q01g00fHRI#>RJ#>RK#>RL#>RM#>RN#>#ARO#A#A#A#A#A#ARP,a7PGP6g00PaS02p,3sp0RQp,2avRRp,2evRS400p,3uidS03p,2hwS04CzS051MF<S06C]=7G7g01;5%33RT%mHRH/jRRU#9RV'8S07%EERW#ERX#3RY,8VRZ'Ug01<41jHSR[#9R\%3WRW'8PBPA20>FQR]%K3R^#0#E#3R_'1%3@R@/2V12@\3<R`%90Ra,2@Rb'1RcPO1OO:1a0P%K1#E#3Rd,?aReP0Pa%5aS08PPPd%5dE{P;CyS09Pe%VAS0:%9ARP#4Rf%VURg%4VRh%V[Ri%4\Rj%3DRD,v]Rk%4]%4D1s]D#4[[RDp-0Rlg00N0Rm1G8IRI1G8NRN1G8MRM1G8LRL'D'D,DIg00fgRn'^'q%pmRo3[%mmRpP8P81Y8:P6&0G8CoP71Y8;CoRq&0F8Rr&0E8Rs1l8<Rt1L8^Ru5@s&0D>RvPs1L82R29@stPvPs%:TRt1L81Rw5@sPsP=P>P>P?PAJ0BR>5isPvPs%C^#C#C#C#C#C#C#0#E#g#B#B#B#3R^#:1L83R35@sS0;Pv%:_,63%:@R==I8w'6AI8=u'6AI8=2Rx'6Ry9@s3C;C;C;C;20As?R?P5P6g00KQRzg00OCR{'T20=56=7z{dB0<8<7H0;R{b8b:b;X08X18X28X38W4%46%4:18T;/UA18^;12@09<:_12@ARz12@BR|3<,8:[[[[^08^18^28^38^4lP5PZf;#9S0<P\PVP]P6P:PBp,3HloS0=O9b7b9b>b=b<b6%9OS0>,1cS0?%31R1%3ERE+0:RZ'?11c@R}/?ZP8P8P4P5X58R~P41?75#dXB8X58Q0?P}P~P~P~P8P8g01=31175H09#5XM8XN8S0?PcPc%5cS0@Q0>P@P~P~%95#5X59S0>POP@%5@R}EcM:ZPZPZ%5ZM<SQ09PeQ0:PfPgPhPiPj2051E1?<1%4E1?<Z[[%41R<g00elR4B041E7UW?%4Z\4^?<PkPD2038@R<=R8NAR8<MAR8<L1G8K/DI'D'D'D/^n=[moPpPqPrPsP8P2g00c=R2%:dCJ,PsPvPs%:W9@suPvPs%:Y9@sw9is>PvPs%0X#g#B#B#B#B#3RX#:9@s3PvPsQ0;PvP816y=P2%:1>028FCJ,PsC;C;C;C;C;P?P{b8b:b;X08X18X28X38X4l1?;d18;W18;Y,UA18;X18^:110_?<z|12@C;<@/?Z[[[[[^08^18^28^38^4lP5Q07f=#9P\PVP]PBPCQ00p,3HhiQ0=O:b7b9bJbKb>b=b<b6C`PG1~RSRC1HO0Rl'=RZ#9,1]R|,MFA_`@P,MFRP97G5X@GP8PG%|FR`P`P|PcPG\8/T`1=UJR`,HORz,=OR^1=[JRX,HORY'=RW/=lRd#9R1,1]R2=78c11VTRv,2@R>,1@Rm11\TRn,2@RI'1RK/1bR<,1]RL=78cP8P8%}8RMP~PMA7875#dXB8X58P2PLP~P~P~Q0?P]P]%5]P1P<P~P~Q0>PdP<PWPKP^PmPOP@P}PzP>POP@P}P`PvPUPV%5VPJPT%5TRUEFEQEFPYPIPOP@P}PXPnP[P\%5\PJPTPUEFEQEFPlPbPOP@P}P0PaQ08EQEFEcM:ZPcPcQ0@M<SQ09PeQ0:PfPgPhPiPjPkPDPoPpPqPrP816wt9I8=,6=16ut9I8='6/6x,63g01=WPyCJ,PsP?P{b8b:b;X08X18X28X38117T9_@@116T,2@12@;RT3<,1512@79<5_12@6;<T578^08^18^28^38P5Q0<P\PVP]O4b7b9b>b=b<b6C`A78|ceL01%NZ9XFQR|206QZEx1MFc97G|PG1HOA,=C#N9XFQ%nHR|g00dCRcQ02PQPRPSQ03Q04p,5rdrawRZK07-08QR8P5POC\1OOA,kH37X@GPGPGPAQ05Q06C]PcP81HOB,=C#N9XFQPOC\1OO5,kH57|XAGPcQ02PQPZPRPSQ03Q04p,3Hvap,3Hveg01>>PAP:M=wP0P;EePPP5EebFGubEbDWHWGXAGXL9WCWIo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma envp_loop : forall G, bwd SEGS G -> forall n k regs J D rom,
    (k + n = length ev)%nat ->
    getr regs 9 = Z_to_bv 64 (E + 8 * Z.of_nat k) ->
    (forall regs',
        getr regs' 9 = Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8) ->
        getr regs' 10 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [9; 10]%list) regs regs' ->
        G (mkst regs' (0xa89ac : word) (CM J D) rom)) ->
    G (mkst regs (0xa89a0 : word) (CM J D) rom).
Proof using fx sp0 av ev uid hw rdraw Hva Hve Hlo Hhi.
intros G HG.
pose proof len_av as Hlen. pose proof len_ev as Hlev.
induction n as [|n IH]; intros k regs J D rom Hkn H9 Hk0.
-
assert (k = length ev) by lia. subst k.
eapply HG.
{ ld_step F_a8958 D_a8958 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0)
ltac:(apply rd_envp_null) ltac:(apply bytes_le_to_Z_8).
sv F_a895c D_a895c (Z_to_bv 64 (E + 8 * Z.of_nat (length ev) + 8)).
stepb_ft F_a8960 D_a8960 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk0; [gres; reflexivity | gres; reflexivity | solve_regs_agree].
- assert (Hk : (k < length ev)%nat) by lia.
pose proof (cat_envp_ptr_nz RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' k Hk) as Hnz.
eapply HG.
{ ld_step F_a8958 D_a8958 (word_to_le_bytes 8 (cat_envp_ptr sp0 av ev k)) (cat_envp_ptr sp0 av ev k)
ltac:(apply rd_envp; exact Hk) ltac:(apply bytes_le_to_Z_8).
sv F_a895c D_a895c (Z_to_bv 64 (E + 8 * Z.of_nat (S k))).
stepb_tk F_a8960 D_a8960 ltac:(pin; apply c_eq_0_false; exact Hnz).
apply mst_refl. }
eapply (IH (S k)); [lia | gres; reflexivity |].
intros regs' H9' H10' Hag. apply Hk0; [exact H9' | exact H10' |].
eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pn_bounds :
    (bv_unsigned sp0 <= bv_unsigned pn)%Z
    /\ (bv_unsigned pn + Z.of_nat (length s) + 1 < 2^64)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "h04__p1h14__x1h21Hh37__arithh44__ffh56__sat1h68__varmaph75__with84cstrp;1p;2p;4p;6p;7p;8p;3p;<g001dj12Tg002Bj10Tg002gj14Tg003Ej1>Tg003hj1:Tg004Hj2OTg004hR0j1DTg005Hj21Tg005dj27Tg00gSR1j2?Tg00S\R2j29Tg00C[j23Tg00;[j1UTg00<@j2TTg00<jj2STg00=[j2NTg00>;j1KTg00>[j2ETg00?9j1CTg00?Wj1BTg00@ej28Tg00@Bj2ATg00AHj45Tg016^j6@Tg00BUj7FTg00B3j1GTg00G;j8HTg00C9j2ITg00D5j2JTg00:6j3=Tg00Daj3LTg00E@j4MTg00oAj4<Tg023Oj8PTg00mJl<QTg00FWj7RTg00cdg00MRR3P1P0P2g018Mg00fHR2g00JCR0f3R1f2R4f1R5f0R6M<Qp=;P5g00G_R7g00H>R8P8g00H^R9P6g00I>FRp=6g01;5g00I^R:#2R;%0:#0#0R<#4#>#:p,2avR='OR>#DR?'1%0<R<#0#0R@#0#0#0#0#2,1?RA'7p,3sp0RBP=p,2evp,3Hvap,3Hveg01>>P21?2>190?1330P>P?133?C;%U>110?%4@/TBRB%2<R<'S110B110<1NB<,10[[p-0R<g00N0RB#K%:B1E35%C3%B3RBP7P8P8P9PBP7P8P8P9P3183;g00N\1A3:R:C5,6BPBP7P8P8P9P1E@FF%G8P31830g00c=P:C5,6BGH1IB9P6P4g00KQRBg00OCR9'31J64==B9dAL305CMb4b6b7X13W011;6/751905[^13^0<P6PAP?P1O3b3b5b8C<GPb2o"). Qed.

  Lemma rd_argv0_byte : forall J D j b, (j <= length s)%nat ->
    nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j)) 1 = Some [b].
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "h04__x1h14__x2h24__x3h31bh43Hj0h57__arithh64__ffh76__sat3h86__sat4h96__sat5h:8__varmaph;5__with<4cstrh=5cstr0h>5cstr1h?1xh@2H0hA2HahB4__p1hC4__x4hD1DhE1HhF2HbhG2HjhH3Hp1hI3Hp2hJ1JhK1jhL1mhM1nhN1yp%0p&0p;1p;4p;2p;3p;7p;<p;6p;:p;=p;8p;Bg002Bj13Tg002gj1ZTg003Ej1UTg00R@j1`Tg003hj1_Tg00>;j1XTg01BFj4QTg004Hj2[Tg024VR0j2RTg007\j2@Tg00]\j3=Tg0250j3bTg00:6j39Tg001dj1>Tg004hR1j17Tg005HR2j21Tg005dR3j2LTg00<@j2\Tg025Mj4xTg00RbR4j20Tg00S?j2oTg00S\R5j24Tg00XAj7lTg00a?j4kTg00[?j1ITg00V7j4GTg00Vhj2NTg00jSj4VTg00;[j1DTg00Y7j2eTg00Y_j3dTg00<jj2cTg00=[j2aTg00[^j2FTg00\Gj3TTg00]0k207Tg00>[j2ATg00Zaj4STg00?9k106Tg00?Wk105Tg00@ej2CTg00F2j1OTg00@Bj2ETg00B3k104Tg00^<j3?Tg00C9k203Tg00C[j2BTg00D5k202Tg00Dak301Tg00E@j4}Tg00lIj1|Tg00lgj4{Tg00mJl<KTg00ZCj1qTg00^_j3pTg00oAj4YTg0126j1MTg0131j3JTg013Vj2nTg000Kj6mTg00T8j7sTg00U6j2tTg00gSR6j2uTg016^j6jTg00BUj7yTg026Nl:zTg027Il=iTg001Hj6^Tg015]j8~Tg00AHj4]Tg00FWj7hTg00G;k800Tg017Bl<gTg017glBfTf0R7#3#3p=P%37#3#3#3p=8g00MRR8/B7p=6g00cdR9P8P0P1P2g028Nf5R2f4R0f3R:f2R;f1R<P7M<Kp=Wg00JCR=/17p=2P8P<g00N\P7C]p=:P<g00G_R>g00H>R?P?g00H^R@P7g00I>Fhp=5%O7#Op=;P:P>P?P?P@P;P<P7L00p=<P9P8P8P8P1P1P2P0P:P;P<P7M<gp=wP8P8P8P8P8P8P4P7P<P;P4P:P0P2f6R4f7RAf8RBf9RCMBfp=rP8P<g00c=P7C]p=HP9P8P6P1P5g018Mg00fHR1P=P:P;P<P7M<Kp=vg00I^R6#3RD#PRE#3RF#PRG#ZRH#URI%ZERE#URJ#`[RK%_JRLP1p,2avRM%XJRNCQRO,[JRP,R<PJP;1@E=RE==JN9bJOS00PECQ=9J<g01;5%>6RO1[LMRQ#7RR'1%8G#>,1RS01'Lg0290p,3sp0RS,\HRTPSPMp,2evRUP1CxRV,\HRW'1RX%7PRY,0W/0O%>DRZ%>GRG'oR['4R\'LP3PXP\%`LR3g00dCR]PSg00PaR^PSPMPUp,3uidR_p,2hwR`p,5rdrawRaFlPBPACk%74,0W,@H%I1RbCGA=J2N,NL39P7f;Rcf:Rd%7CRe,0WRfPbA=JBN1RCP11eYRgPCPe%6ePPPY%6YS02EWPACVS03Pg%DdS04%7dRe#2S05%DPRh%2YRi%DQRj%2RRk1eZGRl14=Z%2G14=[[[Rm%2ZRng00elRoAdZG<UWARG%2[\o^AnRn%>FRF,cTRo%2T%2F1aTF#2[[RFg00N0Rp%IbRq#I,F81F8q1F815T85T8g00fg+07%XpS063=S07%_pRpP81A8;P<1A8:S08CS&068Rq&058Rr1C8=Rs%O6Rt,E8Ru':,5r&04?RvPr1E86R61E8DRD':,5rPvPr%;t#;#;#;#;#;#;#3#P#8#8#8#8#8#8#8#>Rw,C8Rx/:6,5rPvA?8Du,:6,5rC<C<C<203r@RyP7P;g00KQRzg00OCR{'B2027;=9z{dB018=<C}R{b6b:b;X08X18X28%2;11<;11w;1002,1:[[[^08^18^28P7fA#7R2PWPTP4PCp,3HloR4O6b5b7b8b9b>b=b<b4%7bRz,0fR|/4[10fOR}/4[P8P8P5P7X?8R~P514<7#|XN8X?8P|P}P~P~P~P8P8g01=310<7C{#6XL8XM8PfPf%6fPzPOP~P~%77#6X?9PbPO%6OEwM:rP[P[%6[M<KQ03PgQ04Q05PhPiPjPkPlPmPGPnPoPFQ07PpP8P8%q8P;1A80CSP<Q08CSPqPr%3t,E8Rt,:D,5rPvPrA?86t1C8ORt5?81C8Z=p8HRZ'H,5rPvPr1:xu,5rPvA?86D=?8t/HZ,5rC<C<C<PyP{b6b:b;X08X18X28XC811<:10<0/0O/4[11w010:0/0O/4[[[[^08^18^28^C8P7PYPTP2PWPAPBP4O7b5b7b8b9b>b=b<b4CYPI1@HfRf10We,@HRW99I7X3I1BIf%MC9JHVR41nVCEmA9I4fPI%Md9JHVP]P^PSPMPUP_P`PaFs,tSR4P7PbCGA=JdN,NL593X3IPJPJPdQ00PECQP]P4%Mc9JHVPbCGA=J7N,NL593X3JP^P]PSPMPUP1PdP_P`Pa1u1Q14=R1B8=PQPR%6RCv1RdP11eYRQPdPe%6ePPPYQ02EWPBCVPQ%Dc%7c#2PhPiPjPkPlPmPGPnPoPFp-0RFQ06Pp1A8<PqPrPrP>P?P?P@1:t6,5rPrP>P?P?P@P:EjFyPv1Hs6,5rC<PyP{b6b:b;X08WB11O7/L<14=<[^08^BFP7Q01PRf>O3b5b7b8b9b>b=b<b4CYPBP^PSPMPUP_P`Pap,3Hvap,3Hveg01>>M:zM=iPCPAE^PWP7E^b@G~XI\XHXP<P7O2n2001000000121000000b@bEWFWGX3JXK9XDKWJo"). Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "h01ah11rh22a'h31mh41nh54segsp;1p;4p;3p;2p;6g003hj15Tg002Bj10Tg002gj14Tg003Ej13Tg00R@j16Tg00V7j41Tg00:6j32Tg00C[j29Tg000Kj68Tg001Hj67Tg02:2#5g00I^#0#0#0R0#0#0#0#4#3R1%40#3R0#6[g00cd%50#6R0f5R2f4R3f2R4f1R5C1f0R6520f3R79213P0f7R8f6R9P3P7C1R7f8R:P8P9P3C1=206X10P1P3P:P8P6P3C1P:P8P2P3C1520X011907P2P6E8P4P5E7UUW1W4X21X01W3W5o"). Qed.

  Lemma c_eq_byte47 : forall b : byte,
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 47) = bv_eqb b (Z_to_bv 8 47).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "h07__arithh14__ffh24__p1h36__sat1h48__varmaph55__with64__x1h72Hah86__sat2h96__sat3h:1zh;1Hh<1bp;1p;2p;3p;4p;6p;7p;8g002Bj12Tg002gj1CTg003Ej1OTg02;1j1GTg00<@j21Tg001dj15Tg00S\j23Tg005dj2;Tg00F2j16Tg007\j2:Tg02;gj29Tg00:6j38Tg00C[j2@Tg00<jj2\Tg00=[j2WTg00>;j1VTg003hj1UTg00ZCj1TTg00?9j1RTg00?Wj1QTg00@ej27Tg00AHj4=Tg00C9j2NTg00D5j2MTg00Daj3LTg00E@j4KTg00Y7j2HTg00S?j2ITg00Y_j3JTg00^_j3FTg00_Bj3ATg000Kj6>Tg00>[j2ETg00@Bj2PTg016^j6DTg00B3j1STg01U>j2^Tg01Lmj3]Tg005Hj2[Tg00FWj7ZTg00BUj7XTg00G;j8YTg00JCR0f0R1'[p=0f1R2g00G_R3g00H>R4P4g00H^R5P1g00I>FZp=4g00MRR6P2g00c=P1C=p=<f2R7P3P4P4P5P2P1FXp=?f3R8P3P4P4P5P7P2P1GYp=Bg00I^R9#2R:#2#2R;#CR<#O%G111<1R=#0%2;R;#2#2R>#2#2#5R?,3=';P611<2R=g00KQR@%C>RA%6:#6#6#6#5RB,:ARC'1RD,9111<7RE1:<BRF,1<RG'9RH38X:6P6PB19E1=8@HX:619=G,@@PDp,3sp0,1ARD%5;R;'\RG%0D%0;1WD;#0[[R;g00N0RD#VRH%UDRD%T6RE%R6RI%Q6RJP61760RKg00N\RL176BRMC='41NJ5RNP1P7g00OCRO,@@1M17=8@OdAL602CKROb1b4b5%0BP1b0b3%5:R:%5>R>'HRP130:%0>1I:>RQ,30[[R0%0:RRg00elRSAJ:>2UW7R>%0Q\S^7RRRPGP;PHPDPEPI176:=F6AR:,<M,4JPNPOb1b4b513BQP1b0b3b8b95ABE>1:A=RB,1APGP;p-0RAPHPD1E62RMPIPJP6PKPL1P69R9C=,4JRLPJP3P4P4P5P8EDR55?J%S4R4PLCBPNPOb1b4b5X66W2%01/;2%02[^66^2AP111<8R8/3?P8P7O3b0b3PPP0P>PRPGP;PHPDPMPIPJ176?,<9,4J9?J5P41<9:,4JCBPNPOb1b4b5X66X2A131?,;2132Q[^66^2AP1f5,1<R1#0P1f4O3b0b3b8b95A=E>1^BCA]<2F58@eb;W<o"). Qed.

  Lemma c_eq_byte0 : forall b : byte, b <> Z_to_bv 8 0 ->
    c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0) = false.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Startup2 ()) ["FPX_1"; "P3"] "h04__p1h14__x1h22Hah37__arithh44__ffh56__sat1h68__varmaph75__with82b1h92b2h:1nh;1zh<1Hh=2H0h>2Hbh?2Hzh@6__sat2hA6__sat3hB1bp;1p;2p;3p;6p;4p;7p;8g002Bj13Tg002gj1?Tg003Ej14Tg007\j2>Tg00:6j32Tg008Yj1:Tg02;1j1MTg00<@j20Tg001dj16Tg00S\j25Tg005dR0j2;Tg01R5j3BTg00C[j2ATg000Kj6@Tg00<jj2WTg00=[j2VTg00>;j1UTg003hj1TTg00>[j2LTg00?9j1KTg00?Wj1ITg00@ej29Tg00@Bj2HTg00AHj47Tg016^j6GTg00B3j1FTg00C9j2JTg00D5j2ETg00Daj3DTg00E@j4NTg00Y7j2CTg00S?j2OTg00Y_j3PTg00^_j3QTg00_Bj3RTg01]nj2STg005Hj2[Tg00FWj7ZTg00BUj7YTg00G;j8XTg00JCR1f0R2'[p=1f1R3g00G_R4g00H>R5P5g00H^R6P2g00I>FZp=8f2R7P4P5P5P6P3P2FYp=<f3R8P4P5P5P6P7P3P2GXp==g00I^R9#3R:#3#3R;#?R<#4R=1><1R>92=2#:%M310<3R=#1%3;R;#3#3R?#3#3#6R@,5=';%??R=10<7RA'>RBg00MRRCPAA2C21#:X;CA2CA1RDP7g01n6RE%42RF%43RGP0%47?2321087108352CR0[1073107252C%48?273[RHf4RI#4?287\0AB732P2n2001000000120000000W9W8W:PH^9G^8F^:EP2P<PIP>PCP110<>R>92C2X;C1AC>10<IR>P3E@O4b=O1W?%:De10=Bp,3sp0,0=RB%6;R;'WRD%1B%1;1VB;#1[[R;p-0RBg00N0RE#URF%TERE1LC3RG%KCRH%ICR0PC19C1g00N\1HC9R9C7,80RJP0P4P5P5P6P8EGR85<0%F5R5PJC=1J06R6P2P7g00KQRJg00OCR4'A1E27=2J4dADC13CNR4b4b6b7X1CW0%12/;3%13[^1C^0BP215>@P>P7O3b3b5%6:R:%6?R?'C151:%1?1O:?R7,51[[%1:R1g00elR>AP:?3UW2%17\>^21PDP;PFPEPGPHP0PCP9g00c=RH19C@C7,809<08P5PCP9PH19C:=QC=C7,80C=P6P4b4b6b7X1CX0B152@,;31537[^1C^0BP2f6,0<R<#1P<PIO3b3b5b@bA5RAE@'Sb<W>WBo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma prog_loop : forall G, bwd SEGS G -> forall l2 j acc regs J D rom,
    skipn j s = l2 -> (j <= length s)%nat -> (acc <= j)%nat ->
    getr regs 10 = Z_to_bv 64 0xf8ad0 ->
    getr regs 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1) ->
    getr regs 12 = Z_to_bv 64 47 ->
    (forall regs',
        getr regs' 11 = Z_to_bv 64 (bv_unsigned pn + Z.of_nat (length s) + 1) ->
        regs_agree (fun r => In r [11; 13]%list) regs regs' ->
        G (mkst regs' (0xa8a70 : word)
                       (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn
                                 + Z.of_nat (after_last_slash l2 j acc)))))) rom)) ->
    G (mkst regs (0xa8a64 : word)
                   (CM J (wbytes D A8 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat acc))))) rom).
Proof using fx sp0 av ev uid hw rdraw Hva Hve Hlo Hhi.
intros G HG.
pose proof len_av as Hlen. pose proof pn_bounds as [Hp1 Hp2].
pose proof (valid_argv_str_nz av 0 Hva ltac:(lia)) as Hnz.
induction l2 as [|b l2 IH]; intros j acc regs J D rom Hskip Hj Hacc H10 H11 H12 Hk0.
-
assert (Hjl : j = length s).
{ pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
eapply HG.
{ lb_step F_a8a1c D_a8a1c (Z_to_bv 8 0)
ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | subst j; rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity] | f_equal; lia]).
stepb_ft F_a8a20 D_a8a20 ltac:(pin; cond_compute).
stepb_ft F_a8a24 D_a8a24 ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk0; [gres; pin; f_equal; lia | solve_regs_agree].
- assert (Hjlt : (j < length s)%nat).
{ pose proof (f_equal (@length byte) Hskip) as HL. rewrite length_skipn in HL. cbn in HL. lia. }
assert (Hb : nth j (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0) = b).
{ rewrite app_nth1 by lia. rewrite <- (Nat.add_0_r j), <- nth_skipn, Hskip. reflexivity. }
assert (Hbnz : b <> Z_to_bv 8 0).
{ intros Hb0. apply Hnz. rewrite <- Hb0, <- Hb, app_nth1 by lia. apply nth_In. lia. }
assert (Hskip' : skipn (S j) s = l2).
{ replace (S j) with (1 + j)%nat by lia. rewrite <- skipn_skipn, Hskip. reflexivity. }
cbn [after_last_slash] in Hk0.
destruct (bv_eqb b (Z_to_bv 8 47)) eqn:Eb.
+
eapply HG.
{ lb_step F_a8a1c D_a8a1c b
ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
stepb_tk F_a8a20 D_a8a20 ltac:(pin; rewrite c_eq_byte47; exact Eb).
stw F_a8a14 D_a8a14 (Z_to_bv 64 0xf8ad0) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat j + 1)) ltac:(ok_data).
rewrite wbytes_shadow by (rewrite ?length_N_to_le_bytes; rewrite ?length_N_to_le_bytes; first [reflexivity | region_side]).
sv F_a8a18 D_a8a18 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
apply mst_refl. }
replace (bv_unsigned pn + Z.of_nat j + 1)%Z with (bv_unsigned pn + Z.of_nat (S j))%Z by lia.
eapply (IH (S j) (S j)); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
intros regs' H11' Hag. apply Hk0; [exact H11'|].
eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
+ eapply HG.
{ lb_step F_a8a1c D_a8a1c b
ltac:(eapply rdn_addr; [apply (rd_argv0_byte _ _ j); [lia | exact Hb] | f_equal; lia]).
stepb_ft F_a8a20 D_a8a20 ltac:(pin; rewrite c_eq_byte47; exact Eb).
stepb_tk F_a8a24 D_a8a24 ltac:(pin; apply c_eq_byte0; exact Hbnz).
sv F_a8a18 D_a8a18 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat (S j) + 1)).
apply mst_refl. }
eapply (IH (S j) acc); [exact Hskip' | lia | lia | gres; pin; reflexivity | gres; reflexivity | gres; pin; reflexivity |].
intros regs' H11' Hag. apply Hk0; [exact H11'|].
eapply regs_agree_trans; [|exact Hag]. solve_regs_agree.
Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac rdA j w := eapply rdn_addr; [apply (rd_auxv _ _ j w); [lia | reflexivity] | f_equal; lia].

  Lemma p3_run : forall G, bwd SEGS G -> forall regs Jf rom,
    wfJ sp0 Jf ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 8 = pn ->
    getr regs 9 = envp_w sp0 av ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0xa8a78 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
        getr regs' 18 = Z_to_bv 64 0xf8ae0 ->
        regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 18]%list) regs regs' ->
        G (mkst regs' (0xa8c88 : word) (CM (J_aux sp0 av ev uid hw Jf) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0xa8994 : word)
         (CM (wbytes Jf (Z_to_bv 64 (bv_unsigned sp0 - 368)) (zeros 304)) (fun _ => None)) rom).
Proof using fx sp0 av ev uid hw rdraw Hva Hve Hlo Hhi.
intros G HG regs Jf rom HJ H2 H8 H9 H10 Hk.
pose proof len_av as Hlen. pose proof len_ev as Hlev. pose proof pn_bounds as [Hp1 Hp2].
unfold envp_w in H9.
eapply HG.
{ sn F_a894c D_a894c.
ld_step F_a8950 D_a8950 (word_to_le_bytes 8 (Z_to_bv 64 0xd8780)) (Z_to_bv 64 0xd8780)
ltac:(rd_img img_c5a50_8) ltac:(apply bytes_le_to_Z_8).
stw F_a8954 D_a8954 (Z_to_bv 64 0xd8780) (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))) ltac:(ok_data).
apply mst_refl. }
eapply (envp_loop G HG (length ev) 0); [lia | gres; pin; f_equal; lia |].
intros regs1 H9a H10a Hag1.
carry Hag1 H2 (2 : reg) H2a. carry Hag1 H8 (8 : reg) H8a.
clear H9 H10 H8 H2.
eapply HG.
{ sn F_a8964 D_a8964.
sn F_a8968 D_a8968.
stw F_a896c D_a896c (Z_to_bv 64 0xf8ae8)
(Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev))) ltac:(ok_data).
ld_step F_a8970 D_a8970 (word_to_le_bytes 8 (Z_to_bv 64 3)) (Z_to_bv 64 3) ltac:(rdA 0%nat (Z_to_bv 64 3)) ltac:(apply bytes_le_to_Z_8).
stepb_ft F_a8974 D_a8974 ltac:(pin; cond_compute).
sv F_a8978 D_a8978 (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 16)).
sn F_a897c D_a897c.
sv F_a8980 D_a8980 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
sn F_a8984 D_a8984.
stepb_ft F_a8994 D_a8994 ltac:(pin; cond_compute).
ld_step F_a8998 D_a8998 (word_to_le_bytes 8 (Z_to_bv 64 0x10040)) (Z_to_bv 64 0x10040) ltac:(rdA 1%nat (Z_to_bv 64 0x10040)) ltac:(apply bytes_le_to_Z_8).
sn F_a899c D_a899c.
sv F_a89a0 D_a89a0 (Z_to_bv 64 (bv_unsigned sp0 - 344)).
stw F_a89a4 D_a89a4 (Z_to_bv 64 (bv_unsigned sp0 - 344)) (Z_to_bv 64 0x10040) ltac:(ok_win HJ).
sn F_a89a8 D_a89a8.
ld_step F_a8988 D_a8988 (word_to_le_bytes 8 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rdA 2%nat (Z_to_bv 64 4)) ltac:(apply bytes_le_to_Z_8).
sv F_a898c D_a898c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 32)).
stepb_ft F_a8990 D_a8990 ltac:(pin; cond_compute).
stepb_ft F_a8994 D_a8994 ltac:(pin; cond_compute).
ld_step F_a8998 D_a8998 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rdA 3%nat (Z_to_bv 64 56)) ltac:(apply bytes_le_to_Z_8).
sn F_a899c D_a899c.
sv F_a89a0 D_a89a0 (Z_to_bv 64 (bv_unsigned sp0 - 336)).
stw F_a89a4 D_a89a4 (Z_to_bv 64 (bv_unsigned sp0 - 336)) (Z_to_bv 64 56) ltac:(ok_win HJ).
sn F_a89a8 D_a89a8.
ld_step F_a8988 D_a8988 (word_to_le_bytes 8 (Z_to_bv 64 5)) (Z_to_bv 64 5) ltac:(rdA 4%nat (Z_to_bv 64 5)) ltac:(apply bytes_le_to_Z_8).
sv F_a898c D_a898c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 48)).
stepb_ft F_a8990 D_a8990 ltac:(pin; cond_compute).
stepb_ft F_a8994 D_a8994 ltac:(pin; cond_compute).
ld_step F_a8998 D_a8998 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rdA 5%nat (Z_to_bv 64 10)) ltac:(apply bytes_le_to_Z_8).
sn F_a899c D_a899c.
sv F_a89a0 D_a89a0 (Z_to_bv 64 (bv_unsigned sp0 - 328)).
stw F_a89a4 D_a89a4 (Z_to_bv 64 (bv_unsigned sp0 - 328)) (Z_to_bv 64 10) ltac:(ok_win HJ).
sn F_a89a8 D_a89a8.
ld_step F_a8988 D_a8988 (word_to_le_bytes 8 (Z_to_bv 64 16)) (Z_to_bv 64 16) ltac:(rdA 6%nat (Z_to_bv 64 16)) ltac:(apply bytes_le_to_Z_8).
sv F_a898c D_a898c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 64)).
stepb_ft F_a8990 D_a8990 ltac:(pin; cond_compute).
stepb_ft F_a8994 D_a8994 ltac:(pin; cond_compute).
ld_step F_a8998 D_a8998 (word_to_le_bytes 8 hw) hw ltac:(rdA 7%nat hw) ltac:(apply bytes_le_to_Z_8).
sn F_a899c D_a899c.
sv F_a89a0 D_a89a0 (Z_to_bv 64 (bv_unsigned sp0 - 240)).
stw F_a89a4 D_a89a4 (Z_to_bv 64 (bv_unsigned sp0 - 240)) hw ltac:(ok_win HJ).
sn F_a89a8 D_a89a8.
ld_step F_a8988 D_a8988 (word_to_le_bytes 8 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rdA 8%nat (Z_to_bv 64 6)) ltac:(apply bytes_le_to_Z_8).
sv F_a898c D_a898c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 80)).
stepb_ft F_a8990 D_a8990 ltac:(pin; cond_compute).
stepb_ft F_a8994 D_a8994 ltac:(pin; cond_compute).
ld_step F_a8998 D_a8998 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096) ltac:(rdA 9%nat (Z_to_bv 64 4096)) ltac:(apply bytes_le_to_Z_8).
sn F_a899c D_a899c.
sv F_a89a0 D_a89a0 (Z_to_bv 64 (bv_unsigned sp0 - 320)).
stw F_a89a4 D_a89a4 (Z_to_bv 64 (bv_unsigned sp0 - 320)) (Z_to_bv 64 4096) ltac:(ok_win HJ).
sn F_a89a8 D_a89a8.
ld_step F_a8988 D_a8988 (word_to_le_bytes 8 (Z_to_bv 64 11)) (Z_to_bv 64 11) ltac:(rdA 10%nat (Z_to_bv 64 11)) ltac:(apply bytes_le_to_Z_8).
sv F_a898c D_a898c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 96)).
stepb_ft F_a8990 D_a8990 ltac:(pin; cond_compute).
stepb_ft F_a8994 D_a8994 ltac:(pin; cond_compute).
ld_step F_a8998 D_a8998 (word_to_le_bytes 8 uid) uid ltac:(rdA 11%nat uid) ltac:(apply bytes_le_to_Z_8).
sn F_a899c D_a899c.
sv F_a89a0 D_a89a0 (Z_to_bv 64 (bv_unsigned sp0 - 280)).
stw F_a89a4 D_a89a4 (Z_to_bv 64 (bv_unsigned sp0 - 280)) uid ltac:(ok_win HJ).
sn F_a89a8 D_a89a8.
ld_step F_a8988 D_a8988 (word_to_le_bytes 8 (Z_to_bv 64 12)) (Z_to_bv 64 12) ltac:(rdA 12%nat (Z_to_bv 64 12)) ltac:(apply bytes_le_to_Z_8).
sv F_a898c D_a898c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 112)).
stepb_ft F_a8990 D_a8990 ltac:(pin; cond_compute).
stepb_ft F_a8994 D_a8994 ltac:(pin; cond_compute).
ld_step F_a8998 D_a8998 (word_to_le_bytes 8 uid) uid ltac:(rdA 13%nat uid) ltac:(apply bytes_le_to_Z_8).
sn F_a899c D_a899c.
sv F_a89a0 D_a89a0 (Z_to_bv 64 (bv_unsigned sp0 - 272)).
stw F_a89a4 D_a89a4 (Z_to_bv 64 (bv_unsigned sp0 - 272)) uid ltac:(ok_win HJ).
sn F_a89a8 D_a89a8.
ld_step F_a8988 D_a8988 (word_to_le_bytes 8 (Z_to_bv 64 23)) (Z_to_bv 64 23) ltac:(rdA 14%nat (Z_to_bv 64 23)) ltac:(apply bytes_le_to_Z_8).
sv F_a898c D_a898c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 128)).
stepb_ft F_a8990 D_a8990 ltac:(pin; cond_compute).
stepb_ft F_a8994 D_a8994 ltac:(pin; cond_compute).
ld_step F_a8998 D_a8998 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 15%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
sn F_a899c D_a899c.
sv F_a89a0 D_a89a0 (Z_to_bv 64 (bv_unsigned sp0 - 184)).
stw F_a89a4 D_a89a4 (Z_to_bv 64 (bv_unsigned sp0 - 184)) (Z_to_bv 64 0) ltac:(ok_win HJ).
sn F_a89a8 D_a89a8.
ld_step F_a8988 D_a8988 (word_to_le_bytes 8 (Z_to_bv 64 25)) (Z_to_bv 64 25) ltac:(rdA 16%nat (Z_to_bv 64 25)) ltac:(apply bytes_le_to_Z_8).
sv F_a898c D_a898c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 144)).
stepb_ft F_a8990 D_a8990 ltac:(pin; cond_compute).
stepb_ft F_a8994 D_a8994 ltac:(pin; cond_compute).
ld_step F_a8998 D_a8998 (word_to_le_bytes 8 (at_random_ptr sp0 av ev)) (at_random_ptr sp0 av ev) ltac:(rdA 17%nat (at_random_ptr sp0 av ev)) ltac:(apply bytes_le_to_Z_8).
sn F_a899c D_a899c.
sv F_a89a0 D_a89a0 (Z_to_bv 64 (bv_unsigned sp0 - 168)).
stw F_a89a4 D_a89a4 (Z_to_bv 64 (bv_unsigned sp0 - 168)) (at_random_ptr sp0 av ev) ltac:(ok_win HJ).
sn F_a89a8 D_a89a8.
ld_step F_a8988 D_a8988 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdA 18%nat (Z_to_bv 64 0)) ltac:(apply bytes_le_to_Z_8).
sv F_a898c D_a898c (Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev) + 160)).
stepb_tk F_a8990 D_a8990 ltac:(pin; cond_compute).
ld_step F_a89ac D_a89ac (word_to_le_bytes 8 hw) hw
ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a89b0 D_a89b0 (zeros 8) (Z_to_bv 64 0)
ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia)
ltac:(reflexivity).
sn F_a89b4 D_a89b4.
stw F_a89b8 D_a89b8 (Z_to_bv 64 0xf8b48) hw ltac:(ok_data).
stepb_tk F_a89bc D_a89bc ltac:(pin; cond_compute).
ld_step F_a89d4 D_a89d4 (word_to_le_bytes 8 (Z_to_bv 64 4096)) (Z_to_bv 64 4096)
ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stw F_a89d8 D_a89d8 (Z_to_bv 64 0xf8b10) (Z_to_bv 64 4096) ltac:(ok_data).
stepb_tk F_a89dc D_a89dc ltac:(pin; apply c_eq_0_false; lia).
stepb_tk F_a89e4 D_a89e4 ltac:(pin; apply c_eq_0_false; lia).
sn F_a89f0 D_a89f0.
ld_step F_a89f4 D_a89f4 (word_to_le_bytes 8 (Z_to_bv 64 0xf8ad8)) (Z_to_bv 64 0xf8ad8)
ltac:(rd_img img_c5a58_8) ltac:(apply bytes_le_to_Z_8).
sn F_a89f8 D_a89f8.
ld_step F_a89fc D_a89fc (word_to_le_bytes 8 (Z_to_bv 64 0xf8ad0)) (Z_to_bv 64 0xf8ad0)
ltac:(rd_img img_c5a60_8) ltac:(apply bytes_le_to_Z_8).
stw F_a8a00 D_a8a00 (Z_to_bv 64 0xf8ad8) (cat_argv_ptr sp0 av ev 0) ltac:(ok_data).
sv F_a8a04 D_a8a04 (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0 + 1)).
stw F_a8a08 D_a8a08 (Z_to_bv 64 0xf8ad0) (Z_to_bv 64 (bv_unsigned pn + Z.of_nat 0)) ltac:(ok_data).
sn F_a8a0c D_a8a0c.
sn F_a8a10 D_a8a10.
apply mst_refl. }
eapply (prog_loop G HG s 0 0); [reflexivity | lia | lia | gres; reflexivity | gres; reflexivity | gres; reflexivity |].
intros regs2 H11b Hag2.
carry Hag2 H2a (2 : reg) H2b.
eapply HG.
{ sv F_a8a28 D_a8a28 (Z_to_bv 64 (bv_unsigned sp0 - 368)).
sn F_a8a2c D_a8a2c.
apply mst_refl. }
apply Hk.
- gres; bveq.
- gres; exact H2b.
- gres; reflexivity.
- gres. pose proof (Hag2 (18:reg) ltac:(notin_list)) as T; rewrite T; gres; reflexivity.
- ra_chain.
Qed.

End P3.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0Startup2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0_code_a8c88_a8f38.
Module Ns0Startup3.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0_code_a8c88_a8f38. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Img OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0StartupDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r59000_59c90 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Ns0_code_a8c88_a8f38.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

Section P.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation RND := (ed_random rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z.
Proof using Hlo. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z.
Proof using Hhi. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof using sp0 Hva. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
Proof using sp0 av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
  destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
  unfold rnd_w. repeat split; lia.
Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n = Some (firstn n (skipn j (at_random_bytes RND))).
Proof using sp0 av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
  intros J D j n Hjn.
  destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
  unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
  rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
Proof using. intros; subst; reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac RD_RND j :=
    eapply rdn_addr; [ rewrite <- (rnd4_eq RND j) by reflexivity; apply (rd_rnd _ _ j 4); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac RD_GUARD :=
    rewrite rdn_cmem_data by region_side;
    lazymatch goal with
    | |- rdn _ (wbytes (wbytes (wbytes ?DD (Z_to_bv 64 ?g) _) _ _) _ _) _ _ = _ =>
        let H := fresh in
        pose proof (rd_guard_at SEGS DD RND g ltac:(lia) ltac:(lia)) as H;
        cbn [Z.add Pos.add Pos.succ] in H; exact H
    end.

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
Proof using sp0 Hva.
  pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
  f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
Qed.

  (* [comment removed for export] *)
  Lemma tls_c1 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 690808 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 8 = (pn_w sp0 av ev) ->
    getr regs 9 = s1v ->
    getr regs 10 = Z_to_bv 64 (bv_unsigned sp0 - 368) ->
    getr regs 18 = Z_to_bv 64 1018592 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 5 = Z_to_bv 64 0 ->
        getr regs' 7 = Z_to_bv 64 7 ->
        getr regs' 9 = Z_to_bv 64 1018592 ->
        getr regs' 10 = Z_to_bv 64 56 ->
        getr regs' 11 = Z_to_bv 64 1017944 ->
        getr regs' 13 = Z_to_bv 64 10 ->
        getr regs' 15 = Z_to_bv 64 65600 ->
        getr regs' 16 = Z_to_bv 64 6 ->
        getr regs' 17 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        getr regs' 28 = Z_to_bv 64 1685382481 ->
        getr regs' 29 = Z_to_bv 64 65600 ->
        getr regs' 30 = Z_to_bv 64 131072 ->
        regs_agree (fun r => In r [2; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs' ->
        G (mkst regs' (0xa8d10 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0xa8c88 : word) (CM (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (D_libc sp0 av ev hw)) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H1 H2 H3 H8 H9 H10 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_a8c88 D_a8c88 (Z_to_bv 64 (bv_unsigned sp0 - 480)).
stw F_a8c8c D_a8c8c (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 690808) ltac:(ok_win HJ).
stw F_a8c90 D_a8c90 (Z_to_bv 64 (bv_unsigned sp0 - 432)) (pn_w sp0 av ev) ltac:(ok_win HJ).
stw F_a8c94 D_a8c94 (Z_to_bv 64 (bv_unsigned sp0 - 440)) s1v ltac:(ok_win HJ).
stw F_a8c98 D_a8c98 (Z_to_bv 64 (bv_unsigned sp0 - 448)) (Z_to_bv 64 1018592) ltac:(ok_win HJ).
stw F_a8c9c D_a8c9c (Z_to_bv 64 (bv_unsigned sp0 - 456)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_a8ca0 D_a8ca0 (Z_to_bv 64 (bv_unsigned sp0 - 464)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_a8ca4 D_a8ca4 (Z_to_bv 64 (bv_unsigned sp0 - 472)) (Z_to_bv 64 0) ltac:(ok_win HJ).
ld_step F_a8ca8 D_a8ca8 (word_to_le_bytes 8 (Z_to_bv 64 10)) (Z_to_bv 64 10) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_a8cac D_a8cac.
sn F_a8cb0 D_a8cb0.
sn F_a8cb4 D_a8cb4.
sn F_a8cb8 D_a8cb8.
stepb_ft F_a8cbc D_a8cbc ltac:(pin; cond_compute).
sn F_a8cc0 D_a8cc0.
sn F_a8cc4 D_a8cc4.
sn F_a8cc8 D_a8cc8.
ld_step F_a8ccc D_a8ccc (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8cd0 D_a8cd0 (word_to_le_bytes 8 (Z_to_bv 64 56)) (Z_to_bv 64 56) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_a8cd4 D_a8cd4.
sn F_a8cd8 D_a8cd8.
ld_step F_a8cdc D_a8cdc (word_to_le_bytes 4 (Z_to_bv 64 131072)) (Z_to_bv 64 131072) ltac:(rd_img img_c6d70_4) ltac:(vm_compute; reflexivity).
ld_step F_a8ce0 D_a8ce0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_c58e8_8) ltac:(apply bytes_le_to_Z_8).
sn F_a8ce4 D_a8ce4.
sn F_a8ce8 D_a8ce8.
sn F_a8cec D_a8cec.
sn F_a8cf0 D_a8cf0.
sn F_a8cf4 D_a8cf4.
sn F_a8cf8 D_a8cf8.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

  (* [comment removed for export] *)
  Lemma tls_c2 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 5 = Z_to_bv 64 0 ->
    getr regs 7 = Z_to_bv 64 7 ->
    getr regs 9 = Z_to_bv 64 1018592 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 1017944 ->
    getr regs 13 = Z_to_bv 64 10 ->
    getr regs 15 = Z_to_bv 64 65600 ->
    getr regs 16 = Z_to_bv 64 6 ->
    getr regs 17 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    getr regs 28 = Z_to_bv 64 1685382481 ->
    getr regs 29 = Z_to_bv 64 65600 ->
    getr regs 30 = Z_to_bv 64 131072 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 5 = Z_to_bv 64 0 ->
        getr regs' 7 = Z_to_bv 64 7 ->
        getr regs' 9 = Z_to_bv 64 1018592 ->
        getr regs' 10 = Z_to_bv 64 56 ->
        getr regs' 11 = Z_to_bv 64 1017944 ->
        getr regs' 13 = Z_to_bv 64 4 ->
        getr regs' 16 = Z_to_bv 64 6 ->
        getr regs' 17 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        getr regs' 28 = Z_to_bv 64 1685382481 ->
        getr regs' 29 = Z_to_bv 64 65936 ->
        getr regs' 30 = Z_to_bv 64 131072 ->
        regs_agree (fun r => In r [8; 12; 13; 17; 29; 31]%list) regs regs' ->
        G (mkst regs' (0xa8d10 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0xa8d10 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H15 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_a8d10 D_a8d10 (word_to_le_bytes 4 (Z_to_bv 64 6)) (Z_to_bv 64 6) ltac:(rd_img img_10040_4) ltac:(vm_compute; reflexivity).
stepb_tk F_a8d14 D_a8d14 ltac:(pin; cond_compute).
ld_step F_a8cfc D_a8cfc (word_to_le_bytes 8 (Z_to_bv 64 65600)) (Z_to_bv 64 65600) ltac:(rd_img img_10050_8) ltac:(apply bytes_le_to_Z_8).
sn F_a8d00 D_a8d00.
sn F_a8d04 D_a8d04.
sn F_a8d08 D_a8d08.
stepb_ft F_a8d0c D_a8d0c ltac:(pin; cond_compute).
ld_step F_a8d10 D_a8d10 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10078_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a8d14 D_a8d14 ltac:(pin; cond_compute).
stepb_tk F_a8d18 D_a8d18 ltac:(pin; cond_compute).
sn F_a8d2c D_a8d2c.
stepb_ft F_a8d30 D_a8d30 ltac:(pin; cond_compute).
sn F_a8d34 D_a8d34.
stepb_tk F_a8d38 D_a8d38 ltac:(pin; cond_compute).
sn F_a8d58 D_a8d58.
sn F_a8d5c D_a8d5c.
sn F_a8d04 D_a8d04.
sn F_a8d08 D_a8d08.
stepb_ft F_a8d0c D_a8d0c ltac:(pin; cond_compute).
ld_step F_a8d10 D_a8d10 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100b0_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a8d14 D_a8d14 ltac:(pin; cond_compute).
stepb_tk F_a8d18 D_a8d18 ltac:(pin; cond_compute).
sn F_a8d2c D_a8d2c.
stepb_ft F_a8d30 D_a8d30 ltac:(pin; cond_compute).
sn F_a8d34 D_a8d34.
stepb_tk F_a8d38 D_a8d38 ltac:(pin; cond_compute).
sn F_a8d58 D_a8d58.
sn F_a8d5c D_a8d5c.
sn F_a8d04 D_a8d04.
sn F_a8d08 D_a8d08.
stepb_ft F_a8d0c D_a8d0c ltac:(pin; cond_compute).
ld_step F_a8d10 D_a8d10 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_100e8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a8d14 D_a8d14 ltac:(pin; cond_compute).
stepb_tk F_a8d18 D_a8d18 ltac:(pin; cond_compute).
sn F_a8d2c D_a8d2c.
stepb_ft F_a8d30 D_a8d30 ltac:(pin; cond_compute).
sn F_a8d34 D_a8d34.
stepb_tk F_a8d38 D_a8d38 ltac:(pin; cond_compute).
sn F_a8d58 D_a8d58.
sn F_a8d5c D_a8d5c.
sn F_a8d04 D_a8d04.
sn F_a8d08 D_a8d08.
stepb_ft F_a8d0c D_a8d0c ltac:(pin; cond_compute).
ld_step F_a8d10 D_a8d10 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(rd_img img_10120_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a8d14 D_a8d14 ltac:(pin; cond_compute).
stepb_tk F_a8d18 D_a8d18 ltac:(pin; cond_compute).
sn F_a8d2c D_a8d2c.
stepb_ft F_a8d30 D_a8d30 ltac:(pin; cond_compute).
sn F_a8d34 D_a8d34.
stepb_tk F_a8d38 D_a8d38 ltac:(pin; cond_compute).
sn F_a8d58 D_a8d58.
sn F_a8d5c D_a8d5c.
sn F_a8d04 D_a8d04.
sn F_a8d08 D_a8d08.
stepb_ft F_a8d0c D_a8d0c ltac:(pin; cond_compute).
ld_step F_a8d10 D_a8d10 (word_to_le_bytes 4 (Z_to_bv 64 1685382482)) (Z_to_bv 64 1685382482) ltac:(rd_img img_10158_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a8d14 D_a8d14 ltac:(pin; cond_compute).
stepb_tk F_a8d18 D_a8d18 ltac:(pin; cond_compute).
sn F_a8d2c D_a8d2c.
stepb_ft F_a8d30 D_a8d30 ltac:(pin; cond_compute).
sn F_a8d34 D_a8d34.
stepb_tk F_a8d38 D_a8d38 ltac:(pin; cond_compute).
sn F_a8d58 D_a8d58.
sn F_a8d5c D_a8d5c.
sn F_a8d04 D_a8d04.
sn F_a8d08 D_a8d08.
stepb_ft F_a8d0c D_a8d0c ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

  (* [comment removed for export] *)
  Lemma tls_c3 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 5 = Z_to_bv 64 0 ->
    getr regs 7 = Z_to_bv 64 7 ->
    getr regs 9 = Z_to_bv 64 1018592 ->
    getr regs 10 = Z_to_bv 64 56 ->
    getr regs 11 = Z_to_bv 64 1017944 ->
    getr regs 13 = Z_to_bv 64 4 ->
    getr regs 16 = Z_to_bv 64 6 ->
    getr regs 17 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    getr regs 28 = Z_to_bv 64 1685382481 ->
    getr regs 29 = Z_to_bv 64 65936 ->
    getr regs 30 = Z_to_bv 64 131072 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 9 = Z_to_bv 64 1018592 ->
        getr regs' 11 = Z_to_bv 64 1017944 ->
        getr regs' 17 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [8; 13; 17; 29; 31]%list) regs regs' ->
        G (mkst regs' (0xa8d60 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom)) ->
    G (mkst regs (0xa8d10 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H5 H7 H9 H10 H11 H13 H16 H17 H22 H23 H24 H25 H26 H27 H28 H29 H30 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_a8d10 D_a8d10 (word_to_le_bytes 4 (Z_to_bv 64 1685382480)) (Z_to_bv 64 1685382480) ltac:(rd_img img_10190_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a8d14 D_a8d14 ltac:(pin; cond_compute).
stepb_tk F_a8d18 D_a8d18 ltac:(pin; cond_compute).
sn F_a8d2c D_a8d2c.
stepb_ft F_a8d30 D_a8d30 ltac:(pin; cond_compute).
sn F_a8d34 D_a8d34.
stepb_tk F_a8d38 D_a8d38 ltac:(pin; cond_compute).
sn F_a8d58 D_a8d58.
sn F_a8d5c D_a8d5c.
sn F_a8d04 D_a8d04.
sn F_a8d08 D_a8d08.
stepb_ft F_a8d0c D_a8d0c ltac:(pin; cond_compute).
ld_step F_a8d10 D_a8d10 (word_to_le_bytes 4 (Z_to_bv 64 1685382481)) (Z_to_bv 64 1685382481) ltac:(rd_img img_101c8_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a8d14 D_a8d14 ltac:(pin; cond_compute).
stepb_tk F_a8d18 D_a8d18 ltac:(pin; cond_compute).
sn F_a8d2c D_a8d2c.
stepb_ft F_a8d30 D_a8d30 ltac:(pin; cond_compute).
sn F_a8d34 D_a8d34.
stepb_ft F_a8d38 D_a8d38 ltac:(pin; cond_compute).
ld_step F_a8d3c D_a8d3c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_101f0_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_a8d40 D_a8d40 ltac:(pin; cond_compute).
sn F_a8d58 D_a8d58.
sn F_a8d5c D_a8d5c.
sn F_a8d04 D_a8d04.
sn F_a8d08 D_a8d08.
stepb_ft F_a8d0c D_a8d0c ltac:(pin; cond_compute).
ld_step F_a8d10 D_a8d10 (word_to_le_bytes 4 (Z_to_bv 64 4)) (Z_to_bv 64 4) ltac:(rd_img img_10200_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a8d14 D_a8d14 ltac:(pin; cond_compute).
stepb_tk F_a8d18 D_a8d18 ltac:(pin; cond_compute).
sn F_a8d2c D_a8d2c.
stepb_ft F_a8d30 D_a8d30 ltac:(pin; cond_compute).
sn F_a8d34 D_a8d34.
stepb_tk F_a8d38 D_a8d38 ltac:(pin; cond_compute).
sn F_a8d58 D_a8d58.
sn F_a8d5c D_a8d5c.
sn F_a8d04 D_a8d04.
sn F_a8d08 D_a8d08.
stepb_ft F_a8d0c D_a8d0c ltac:(pin; cond_compute).
ld_step F_a8d10 D_a8d10 (word_to_le_bytes 4 (Z_to_bv 64 1879048195)) (Z_to_bv 64 1879048195) ltac:(rd_img img_10238_4) ltac:(vm_compute; reflexivity).
stepb_ft F_a8d14 D_a8d14 ltac:(pin; cond_compute).
stepb_tk F_a8d18 D_a8d18 ltac:(pin; cond_compute).
sn F_a8d2c D_a8d2c.
stepb_ft F_a8d30 D_a8d30 ltac:(pin; cond_compute).
sn F_a8d34 D_a8d34.
stepb_tk F_a8d38 D_a8d38 ltac:(pin; cond_compute).
sn F_a8d58 D_a8d58.
sn F_a8d5c D_a8d5c.
sn F_a8d04 D_a8d04.
sn F_a8d08 D_a8d08.
stepb_tk F_a8d0c D_a8d0c ltac:(pin; cond_compute).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

  (* [comment removed for export] *)
  Lemma tls_c4 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 9 = Z_to_bv 64 1018592 ->
    getr regs 11 = Z_to_bv 64 1017944 ->
    getr regs 17 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 886864 ->
        getr regs' 10 = Z_to_bv 64 1017944 ->
        getr regs' 11 = Z_to_bv 64 1018648 ->
        getr regs' 12 = Z_to_bv 64 0 ->
        getr regs' 13 = Z_to_bv 64 886656 ->
        getr regs' 14 = Z_to_bv 64 0 ->
        getr regs' 15 = Z_to_bv 64 18446744073708664752 ->
        getr regs' 17 = Z_to_bv 64 96 ->
        getr regs' 18 = Z_to_bv 64 886664 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 4; 8; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20]%list) regs regs' ->
        G (mkst regs' (0xa8ee4 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1017976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1018616) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1018624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 886880) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 886856) (word_to_le_bytes 8 (Z_to_bv 64 886880))) (Z_to_bv 64 886664) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 1018592) ([Z_to_bv 8 1])) (Z_to_bv 64 886704) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom)) ->
    G (mkst regs (0xa8d60 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (D_libc sp0 av ev hw)) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H9 H11 H17 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ stepb_tk F_a8d60 D_a8d60 ltac:(pin; cond_compute).
ld_step F_a8d98 D_a8d98 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_d8758_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8d9c D_a8d9c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_d8768_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8da0 D_a8da0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_d8770_8) ltac:(apply bytes_le_to_Z_8).
sn F_a8da4 D_a8da4.
sn F_a8da8 D_a8da8.
sn F_a8dac D_a8dac.
sn F_a8db0 D_a8db0.
sn F_a8db4 D_a8db4.
sn F_a8db8 D_a8db8.
sn F_a8dbc D_a8dbc.
stw F_a8dc0 D_a8dc0 (Z_to_bv 64 1017976) (Z_to_bv 64 0) ltac:(ok_data).
stw F_a8dc4 D_a8dc4 (Z_to_bv 64 1017992) (Z_to_bv 64 0) ltac:(ok_data).
stepb_ft F_a8dc8 D_a8dc8 ltac:(pin; cond_compute).
sn F_a8dcc D_a8dcc.
stw F_a8dd0 D_a8dd0 (Z_to_bv 64 1017984) (Z_to_bv 64 8) ltac:(ok_data).
sn F_a8dd4 D_a8dd4.
sn F_a8dd8 D_a8dd8.
sn F_a8ddc D_a8ddc.
sn F_a8de0 D_a8de0.
sn F_a8de4 D_a8de4.
sn F_a8de8 D_a8de8.
stw F_a8dec D_a8dec (Z_to_bv 64 1018616) (Z_to_bv 64 224) ltac:(ok_data).
stw F_a8df0 D_a8df0 (Z_to_bv 64 1018624) (Z_to_bv 64 8) ltac:(ok_data).
stepb_tk F_a8df4 D_a8df4 ltac:(pin; cond_compute).
sn F_a8e28 D_a8e28.
ld_step F_a8e2c D_a8e2c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_d8b30_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8e30 D_a8e30 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_d8b48_8) ltac:(apply bytes_le_to_Z_8).
sn F_a8e34 D_a8e34.
sn F_a8e38 D_a8e38.
sn F_a8e3c D_a8e3c.
sn F_a8e40 D_a8e40.
sn F_a8e44 D_a8e44.
sn F_a8e48 D_a8e48.
sn F_a8e4c D_a8e4c.
sn F_a8e50 D_a8e50.
sn F_a8e54 D_a8e54.
sn F_a8e58 D_a8e58.
sn F_a8e5c D_a8e5c.
stepb_tk F_a8e60 D_a8e60 ltac:(pin; cond_compute).
stw F_a8ea8 D_a8ea8 (Z_to_bv 64 886880) (Z_to_bv 64 0) ltac:(ok_data).
stw F_a8eac D_a8eac (Z_to_bv 64 886856) (Z_to_bv 64 886880) ltac:(ok_data).
stw F_a8eb0 D_a8eb0 (Z_to_bv 64 886664) (Z_to_bv 64 886664) ltac:(ok_data).
sn F_a8eb4 D_a8eb4.
sn F_a8eb8 D_a8eb8.
sn F_bbffc D_bbffc.
sn F_bc000 D_bc000.
stepret F_bc004 D_bc004 (0xa8ebc : word) ltac:(pin; first [reflexivity | bveq]).
stepb_ft F_a8ebc D_a8ebc ltac:(pin; cond_compute).
stepb_ft F_a8ec0 D_a8ec0 ltac:(pin; cond_compute).
sn F_a8ec4 D_a8ec4.
stw F_a8ec8 D_a8ec8 (Z_to_bv 64 1018592) (Z_to_bv 64 1) ltac:(ok_data).
sn F_a8ecc D_a8ecc.
sn F_a8ed0 D_a8ed0.
stw F_a8ed4 D_a8ed4 (Z_to_bv 64 886704) (Z_to_bv 64 2) ltac:(ok_data).
sn F_a8ed8 D_a8ed8.
sn F_a8edc D_a8edc.
sn F_a8ee0 D_a8ee0.
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

  (* [comment removed for export] *)
  Lemma tls_c5 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 480) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 886864 ->
    getr regs 10 = tid ->
    getr regs 11 = Z_to_bv 64 1018648 ->
    getr regs 18 = Z_to_bv 64 886664 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 886864 ->
        getr regs' 19 = Z_to_bv 64 0 ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 12; 18; 19; 20; 21]%list) regs regs' ->
        G (mkst regs' (0xa8a78 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1017976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1018616) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1018624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 886880) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 886856) (word_to_le_bytes 8 (Z_to_bv 64 886880))) (Z_to_bv 64 886664) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 1018592) ([Z_to_bv 8 1])) (Z_to_bv 64 886704) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 886696) (word_to_le_bytes 4 tid)) (Z_to_bv 64 886816) (word_to_le_bytes 8 (Z_to_bv 64 1018648))) (Z_to_bv 64 886784) (word_to_le_bytes 8 (Z_to_bv 64 886784))) (Z_to_bv 64 886672) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886680) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886688) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom)) ->
    G (mkst regs (0xa8ee8 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1017976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1018616) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1018624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 886880) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 886856) (word_to_le_bytes 8 (Z_to_bv 64 886880))) (Z_to_bv 64 886664) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 1018592) ([Z_to_bv 8 1])) (Z_to_bv 64 886704) (word_to_le_bytes 4 (Z_to_bv 64 2)))) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H4 H10 H11 H18 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sn F_a8ee8 D_a8ee8.
stw F_a8eec D_a8eec (Z_to_bv 64 886696) tid ltac:(ok_data).
stw F_a8ef0 D_a8ef0 (Z_to_bv 64 886816) (Z_to_bv 64 1018648) ltac:(ok_data).
stw F_a8ef4 D_a8ef4 (Z_to_bv 64 886784) (Z_to_bv 64 886784) ltac:(ok_data).
sn F_a8ef8 D_a8ef8.
ld_step F_a8efc D_a8efc (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_d8b08_8) ltac:(apply bytes_le_to_Z_8).
stw F_a8f00 D_a8f00 (Z_to_bv 64 886672) (Z_to_bv 64 886664) ltac:(ok_data).
stw F_a8f04 D_a8f04 (Z_to_bv 64 886680) (Z_to_bv 64 886664) ltac:(ok_data).
stw F_a8f08 D_a8f08 (Z_to_bv 64 886688) (Z_to_bv 64 0) ltac:(ok_data).
sn F_a8f0c D_a8f0c.
ld_step F_a8f14 D_a8f14 (word_to_le_bytes 8 (Z_to_bv 64 690808)) (Z_to_bv 64 690808) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8f18 D_a8f18 (word_to_le_bytes 8 (pn_w sp0 av ev)) (pn_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8f1c D_a8f1c (word_to_le_bytes 8 s1v) s1v ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8f20 D_a8f20 (word_to_le_bytes 8 (Z_to_bv 64 1018592)) (Z_to_bv 64 1018592) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8f24 D_a8f24 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8f28 D_a8f28 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8f2c D_a8f2c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_a8f30 D_a8f30 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_a8f34 D_a8f34 (0xa8a78 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0Startup3.
Module Ns0Startup4.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Img OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0StartupDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r1ff24_20000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4a000_4b000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4b000_4c000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022.Ns0_code_r58000_59000.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

Section P.
  Variable sp0 : word.
  Variable Jb : word -> option byte.   (* [comment removed for export] *)
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.
  Hypothesis Hal : (bv_unsigned sp0 mod 16 = 0)%Z.

  Local Notation RND := (ed_random rdraw) (only parsing).
  Local Notation CM := (cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw)) (only parsing).

  Lemma Hsp_lo' : (sp_window_lo <= bv_unsigned sp0)%Z.
Proof using Hlo. exact Hlo. Qed.
  Lemma Hsp_hi' : (bv_unsigned sp0 <= sp_window_hi)%Z.
Proof using Hhi. exact Hhi. Qed.
  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof using sp0 Hva. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma rnd_bounds :
    (bv_unsigned sp0 <= bv_unsigned (rnd_w sp0 av ev))%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) + 16 < 2^64)%Z
    /\ (bv_unsigned (rnd_w sp0 av ev) mod 8 = 0)%Z.
Proof using sp0 av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
  destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D & _).
  unfold rnd_w. repeat split; lia.
Qed.

  Lemma rd_rnd : forall J D j n, (j + n <= 16)%nat ->
    rdn SEGS (CM J D) (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + Z.of_nat j)) n = Some (firstn n (skipn j (at_random_bytes RND))).
Proof using sp0 av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
  intros J D j n Hjn.
  destruct (rnd_facts SEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsp_lo' Hsp_hi' Hal) as (A & B & C & D' & E).
  unfold rnd_w. rewrite rdn_cmem_above by (unorm; lia).
  rewrite rdn_wrap_stack_above by (unorm; lia). apply E. exact Hjn.
Qed.

  Lemma rdn_addr : forall segs m (a a' : word) n (r : option (list byte)),
    rdn segs m a' n = r -> a = a' -> rdn segs m a n = r.
Proof using. intros; subst; reflexivity. Qed.

  (* [comment removed for export] *)
  Ltac RD_RND j :=
    eapply rdn_addr; [ rewrite <- (rnd4_eq RND j) by reflexivity; apply (rd_rnd _ _ j 4); cbn; lia
                     | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [reflexivity | symmetry; apply at_self | f_equal; lia] ].

  (* [comment removed for export] *)
  Ltac RD_GUARD :=
    rewrite rdn_cmem_data by region_side;
    lazymatch goal with
    | |- rdn _ (wbytes (wbytes (wbytes ?DD (Z_to_bv 64 ?g) _) _ _) _ _) _ _ = _ =>
        let H := fresh in
        pose proof (rd_guard_at SEGS DD RND g ltac:(lia) ltac:(lia)) as H;
        cbn [Z.add Pos.add Pos.succ] in H; exact H
    end.

  Lemma slli_argc : v_slli (argc_w av) 3 = Z_to_bv 64 (8 * Z.of_nat (length av)).
Proof using sp0 Hva.
  pose proof len_av. unfold argc_w, v_slli. rewrite (u_argcN av Hva).
  f_equal. rewrite Z.shiftl_mul_pow2 by lia. change (2^3)%Z with 8%Z. lia.
Qed.

  (* [comment removed for export] *)
  Lemma fin_c6 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 886864 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 886864 ->
        getr regs' 19 = Z_to_bv 64 0 ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 10; 11; 12; 13; 14; 15]%list) regs regs' ->
        G (mkst regs' (0xa8a80 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690816))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1017976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1018616) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1018624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 886880) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 886856) (word_to_le_bytes 8 (Z_to_bv 64 886880))) (Z_to_bv 64 886664) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 1018592) ([Z_to_bv 8 1])) (Z_to_bv 64 886704) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 886696) (word_to_le_bytes 4 tid)) (Z_to_bv 64 886816) (word_to_le_bytes 8 (Z_to_bv 64 1018648))) (Z_to_bv 64 886784) (word_to_le_bytes 8 (Z_to_bv 64 886784))) (Z_to_bv 64 886672) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886680) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886688) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1018560) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1018564) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1018561) ([Z_to_bv 8 0])) (Z_to_bv 64 886848) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0xa8a78 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1017976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1018616) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1018624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 886880) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 886856) (word_to_le_bytes 8 (Z_to_bv 64 886880))) (Z_to_bv 64 886664) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 1018592) ([Z_to_bv 8 1])) (Z_to_bv 64 886704) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 886696) (word_to_le_bytes 4 tid)) (Z_to_bv 64 886816) (word_to_le_bytes 8 (Z_to_bv 64 1018648))) (Z_to_bv 64 886784) (word_to_le_bytes 8 (Z_to_bv 64 886784))) (Z_to_bv 64 886672) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886680) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886688) (word_to_le_bytes 8 (Z_to_bv 64 0)))) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_a8a30 D_a8a30 (word_to_le_bytes 8 (rnd_w sp0 av ev)) (rnd_w sp0 av ev) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sn F_a8a34 D_a8a34.
sv F_a93ec D_a93ec (Z_to_bv 64 (bv_unsigned sp0 - 432)).
stw F_a93f0 D_a93f0 (Z_to_bv 64 (bv_unsigned sp0 - 424)) (Z_to_bv 64 690816) ltac:(ok_win HJ).
stepb_ft F_a93f4 D_a93f4 ltac:(pin; apply c_eq_0_false; pose proof rnd_bounds; lia).
sv F_a93f8 D_a93f8 (rnd_w sp0 av ev).
sn F_a93fc D_a93fc.
ld_step F_a9400 D_a9400 (word_to_le_bytes 8 (Z_to_bv 64 1018560)) (Z_to_bv 64 1018560) ltac:(rd_img img_c5a78_8) ltac:(apply bytes_le_to_Z_8).
sn F_a9404 D_a9404.
sn F_a9408 D_a9408.
stepiv F_b993c D_b993c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply v_andi_3_aligned; pose proof rnd_bounds as (_ & _ & RB); rewrite <- (Z.mod_mod_divide _ 8 4) by (exists 2%Z; reflexivity); rewrite RB; reflexivity).
stepb_tk F_b9940 D_b9940 ltac:(pin; cond_compute).
sn F_b9a50 D_b9a50.
sn F_b9a54 D_b9a54.
stepb_ft F_b9a58 D_b9a58 ltac:(pin; cond_compute).
sn F_b9a5c D_b9a5c.
stepb_tk F_b9a60 D_b9a60 ltac:(pin; cond_compute).
sn F_b9a98 D_b9a98.
stepb_ft F_b9a9c D_b9a9c ltac:(pin; cond_compute).
ld_step F_b9aa0 D_b9aa0 (rnd4 RND 0) (rnd4w RND 0) ltac:(RD_RND 0%nat) ltac:(apply rnd4_val).
ld_step F_b9aa4 D_b9aa4 (rnd4 RND 4) (rnd4w RND 4) ltac:(RD_RND 4%nat) ltac:(apply rnd4_val).
stw F_b9aa8 D_b9aa8 (Z_to_bv 64 1018560) (rlw RND 0) ltac:(ok_data).
stw F_b9aac D_b9aac (Z_to_bv 64 1018564) (rlw RND 4) ltac:(ok_data).
sn F_b9ab0 D_b9ab0.
sv F_b9ab4 D_b9ab4 (Z_to_bv 64 (bv_unsigned (rnd_w sp0 av ev) + 8)).
sn F_b9ab8 D_b9ab8.
stepb_tk F_b9abc D_b9abc ltac:(pin; cond_compute).
sn F_b9cfc D_b9cfc.
stepb_ft F_b9d00 D_b9d00 ltac:(pin; cond_compute).
sn F_b9d04 D_b9d04.
stepb_ft F_b9d08 D_b9d08 ltac:(pin; cond_compute).
stepret F_b9d0c D_b9d0c (0xa9448 : word) ltac:(pin; first [reflexivity | bveq]).
sn F_a940c D_a940c.
sn F_a9428 D_a9428.
ld_step F_a942c D_a942c (word_to_le_bytes 8 (Z_to_bv 64 1018560)) (Z_to_bv 64 1018560) ltac:(rd_img img_c5a78_8) ltac:(apply bytes_le_to_Z_8).
stw F_a9430 D_a9430 (Z_to_bv 64 1018561) (Z_to_bv 64 0) ltac:(ok_data).
ld_step F_a9434 D_a9434 (guard_bytes RND) (canary_w RND) ltac:(RD_GUARD) ltac:(apply canary_val).
sn F_a9438 D_a9438.
stw F_a943c D_a943c (Z_to_bv 64 886848) (canary_w RND) ltac:(ok_data).
ld_step F_a9440 D_a9440 (word_to_le_bytes 8 (Z_to_bv 64 690816)) (Z_to_bv 64 690816) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_a9444 D_a9444 (Z_to_bv 64 (bv_unsigned sp0 - 416)).
stepret F_a9448 D_a9448 (0xa8a80 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

  (* [comment removed for export] *)
  Lemma fin_c7 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 416) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 886864 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 0 ->
        getr regs' 2 = sp0 ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 886864 ->
        getr regs' 8 = Z_to_bv 64 0 ->
        getr regs' 9 = Z_to_bv 64 0 ->
        getr regs' 10 = Z_to_bv 64 232492 ->
        getr regs' 11 = (argc_w av) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 18 = Z_to_bv 64 0 ->
        getr regs' 19 = Z_to_bv 64 0 ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 6; 8; 9; 10; 11; 12; 18]%list) regs regs' ->
        G (mkst regs' (0xa8c40 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690816))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1017976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1018616) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1018624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 886880) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 886856) (word_to_le_bytes 8 (Z_to_bv 64 886880))) (Z_to_bv 64 886664) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 1018592) ([Z_to_bv 8 1])) (Z_to_bv 64 886704) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 886696) (word_to_le_bytes 4 tid)) (Z_to_bv 64 886816) (word_to_le_bytes 8 (Z_to_bv 64 1018648))) (Z_to_bv 64 886784) (word_to_le_bytes 8 (Z_to_bv 64 886784))) (Z_to_bv 64 886672) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886680) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886688) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1018560) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1018564) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1018561) ([Z_to_bv 8 0])) (Z_to_bv 64 886848) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0xa8a80 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690816))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1017976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1018616) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1018624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 886880) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 886856) (word_to_le_bytes 8 (Z_to_bv 64 886880))) (Z_to_bv 64 886664) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 1018592) ([Z_to_bv 8 1])) (Z_to_bv 64 886704) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 886696) (word_to_le_bytes 4 tid)) (Z_to_bv 64 886816) (word_to_le_bytes 8 (Z_to_bv 64 1018648))) (Z_to_bv 64 886784) (word_to_le_bytes 8 (Z_to_bv 64 886784))) (Z_to_bv 64 886672) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886680) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886688) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1018560) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1018564) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1018561) ([Z_to_bv 8 0])) (Z_to_bv 64 886848) (word_to_le_bytes 8 (canary_w RND)))) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H2 H3 H4 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ ld_step F_a8a38 D_a8a38 (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8a3c D_a8a3c (word_to_le_bytes 8 uid) uid ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stepb_ft F_a8a40 D_a8a40 ltac:(pin; first [apply c_eq_refl | cond_compute]).
ld_step F_a8a44 D_a8a44 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
ld_step F_a8a48 D_a8a48 (zeros 8) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; peel; apply rdn_wbytes_zeros_in; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ltac:(reflexivity).
stepb_ft F_a8a4c D_a8a4c ltac:(pin; cond_compute).
ld_step F_a8a50 D_a8a50 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_a8a54 D_a8a54 ltac:(pin; cond_compute).
ld_step F_a8b34 D_a8b34 (word_to_le_bytes 8 (Z_to_bv 64 691220)) (Z_to_bv 64 691220) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8b38 D_a8b38 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8b3c D_a8b3c (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8b40 D_a8b40 (word_to_le_bytes 8 (Z_to_bv 64 232492)) (Z_to_bv 64 232492) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_a8b44 D_a8b44 (Z_to_bv 64 (bv_unsigned sp0 - 32)).
stepret F_a8b48 D_a8b48 (0xa8c14 : word) ltac:(pin; first [reflexivity | bveq]).
sn F_a8bcc D_a8bcc.
sn F_a8bd0 D_a8bd0.
sn F_a8bd4 D_a8bd4.
sv F_a8bd8 D_a8bd8 (argc_w av).
sv F_a8bdc D_a8bdc (Z_to_bv 64 (bv_unsigned sp0 + 8)).
ld_step F_a8be0 D_a8be0 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8be4 D_a8be4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8be8 D_a8be8 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8bec D_a8bec (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_a8bf0 D_a8bf0 sp0.
stepret F_a8bf4 D_a8bf4 (0xa8c40 : word) ltac:(pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

  (* [comment removed for export] *)
  Lemma fin_c8 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 0 ->
    getr regs 2 = sp0 ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 886864 ->
    getr regs 8 = Z_to_bv 64 0 ->
    getr regs 9 = Z_to_bv 64 0 ->
    getr regs 10 = Z_to_bv 64 232492 ->
    getr regs 11 = (argc_w av) ->
    getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
    getr regs 18 = Z_to_bv 64 0 ->
    getr regs 19 = Z_to_bv 64 0 ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 691140 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 886864 ->
        getr regs' 8 = Z_to_bv 64 784872 ->
        getr regs' 9 = Z_to_bv 64 784864 ->
        getr regs' 18 = Z_to_bv 64 232492 ->
        getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19]%list) regs regs' ->
        G (mkst regs' (0x38b28 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690816))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 691316))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1017976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1018616) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1018624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 886880) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 886856) (word_to_le_bytes 8 (Z_to_bv 64 886880))) (Z_to_bv 64 886664) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 1018592) ([Z_to_bv 8 1])) (Z_to_bv 64 886704) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 886696) (word_to_le_bytes 4 tid)) (Z_to_bv 64 886816) (word_to_le_bytes 8 (Z_to_bv 64 1018648))) (Z_to_bv 64 886784) (word_to_le_bytes 8 (Z_to_bv 64 886784))) (Z_to_bv 64 886672) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886680) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886688) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1018560) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1018564) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1018561) ([Z_to_bv 8 0])) (Z_to_bv 64 886848) (word_to_le_bytes 8 (canary_w RND)))) rom)) ->
    G (mkst regs (0xa8c40 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690816))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1017976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1018616) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1018624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 886880) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 886856) (word_to_le_bytes 8 (Z_to_bv 64 886880))) (Z_to_bv 64 886664) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 1018592) ([Z_to_bv 8 1])) (Z_to_bv 64 886704) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 886696) (word_to_le_bytes 4 tid)) (Z_to_bv 64 886816) (word_to_le_bytes 8 (Z_to_bv 64 1018648))) (Z_to_bv 64 886784) (word_to_le_bytes 8 (Z_to_bv 64 886784))) (Z_to_bv 64 886672) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886680) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886688) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1018560) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1018564) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1018561) ([Z_to_bv 8 0])) (Z_to_bv 64 886848) (word_to_le_bytes 8 (canary_w RND)))) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_a8bf8 D_a8bf8 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
stw F_a8bfc D_a8bfc (Z_to_bv 64 (bv_unsigned sp0 - 8)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_a8c00 D_a8c00 (Z_to_bv 64 (bv_unsigned sp0 - 16)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_a8c04 D_a8c04 (Z_to_bv 64 (bv_unsigned sp0 - 24)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_a8c08 D_a8c08 (Z_to_bv 64 (bv_unsigned sp0 - 32)) (Z_to_bv 64 0) ltac:(ok_win HJ).
stw F_a8c0c D_a8c0c (Z_to_bv 64 (bv_unsigned sp0 - 40)) (Z_to_bv 64 0) ltac:(ok_win HJ).
sv F_a8c10 D_a8c10 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
sv F_a8c14 D_a8c14 (argc_w av).
sn F_a8c18 D_a8c18.
stepiv F_a8c1c D_a8c1c (Z_to_bv 64 (8 * Z.of_nat (length av))) ltac:(gres; pin; imm_norm; apply slli_argc).
sv F_a8c20 D_a8c20 (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat (length av))).
sv F_a8c24 D_a8c24 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
sn F_a8c28 D_a8c28.
sv F_a8b4c D_a8b4c (Z_to_bv 64 (bv_unsigned sp0 - 80)).
stw F_a8b50 D_a8b50 (Z_to_bv 64 (bv_unsigned sp0 - 56)) (Z_to_bv 64 691316) ltac:(ok_win HJ).
stw F_a8b54 D_a8b54 (Z_to_bv 64 (bv_unsigned sp0 - 64)) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(ok_win HJ).
stw F_a8b58 D_a8b58 (Z_to_bv 64 (bv_unsigned sp0 - 72)) (argc_w av) ltac:(ok_win HJ).
sn F_a8b5c D_a8b5c.
stepret F_a891c D_a891c (0xa8ba8 : word) ltac:(pin; first [reflexivity | bveq]).
sn F_a8b60 D_a8b60.
sn F_a8b64 D_a8b64.
ld_step F_a8b68 D_a8b68 (word_to_le_bytes 8 (Z_to_bv 64 784872)) (Z_to_bv 64 784872) ltac:(rd_img img_c5a68_8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8b6c D_a8b6c (word_to_le_bytes 8 (Z_to_bv 64 784864)) (Z_to_bv 64 784864) ltac:(rd_img img_c5a70_8) ltac:(apply bytes_le_to_Z_8).
stepb_ft F_a8b70 D_a8b70 ltac:(pin; cond_compute).
ld_step F_a8b74 D_a8b74 (word_to_le_bytes 8 (Z_to_bv 64 232232)) (Z_to_bv 64 232232) ltac:(rd_img img_bf9a0_8) ltac:(apply bytes_le_to_Z_8).
stepjr F_a8b78 D_a8b78 (0x38b28 : word) ltac:(gres; pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

  (* [comment removed for export] *)
  Lemma fin_c9 : forall G, bwd SEGS G -> forall regs rom (s1v tid : word),
    wfJ sp0 Jb ->
    getr regs 1 = Z_to_bv 64 691140 ->
    getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 80) ->
    getr regs 3 = Z_to_bv 64 67584 ->
    getr regs 4 = Z_to_bv 64 886864 ->
    getr regs 8 = Z_to_bv 64 784872 ->
    getr regs 9 = Z_to_bv 64 784864 ->
    getr regs 18 = Z_to_bv 64 232492 ->
    getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
    getr regs 20 = Z_to_bv 64 0 ->
    getr regs 21 = Z_to_bv 64 0 ->
    getr regs 22 = Z_to_bv 64 0 ->
    getr regs 23 = Z_to_bv 64 0 ->
    getr regs 24 = Z_to_bv 64 0 ->
    getr regs 25 = Z_to_bv 64 0 ->
    getr regs 26 = Z_to_bv 64 0 ->
    getr regs 27 = Z_to_bv 64 0 ->
    (forall regs',
        getr regs' 1 = Z_to_bv 64 691332 ->
        getr regs' 2 = Z_to_bv 64 (bv_unsigned sp0 - 48) ->
        getr regs' 3 = Z_to_bv 64 67584 ->
        getr regs' 4 = Z_to_bv 64 886864 ->
        getr regs' 8 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 9 = (argc_w av) ->
        getr regs' 10 = (argc_w av) ->
        getr regs' 11 = Z_to_bv 64 (bv_unsigned sp0 + 8) ->
        getr regs' 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 18 = Z_to_bv 64 232492 ->
        getr regs' 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)) ->
        getr regs' 20 = Z_to_bv 64 0 ->
        getr regs' 21 = Z_to_bv 64 0 ->
        getr regs' 22 = Z_to_bv 64 0 ->
        getr regs' 23 = Z_to_bv 64 0 ->
        getr regs' 24 = Z_to_bv 64 0 ->
        getr regs' 25 = Z_to_bv 64 0 ->
        getr regs' 26 = Z_to_bv 64 0 ->
        getr regs' 27 = Z_to_bv 64 0 ->
        regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs' ->
        G (mkst regs' (0x38c2c : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690816))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 691316))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 691140))) (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 784872))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1017976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1018616) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1018624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 886880) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 886856) (word_to_le_bytes 8 (Z_to_bv 64 886880))) (Z_to_bv 64 886664) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 1018592) ([Z_to_bv 8 1])) (Z_to_bv 64 886704) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 886696) (word_to_le_bytes 4 tid)) (Z_to_bv 64 886816) (word_to_le_bytes 8 (Z_to_bv 64 1018648))) (Z_to_bv 64 886784) (word_to_le_bytes 8 (Z_to_bv 64 886784))) (Z_to_bv 64 886672) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886680) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886688) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1018560) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1018564) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1018561) ([Z_to_bv 8 0])) (Z_to_bv 64 886848) (word_to_le_bytes 8 (canary_w RND))) (Z_to_bv 64 814544) ([Z_to_bv 8 1]))) rom)) ->
    G (mkst regs (0x38b28 : word) (CM (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (J_aux sp0 av ev uid hw (J_lsm sp0 av Jb)) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690808))) (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 (pn_w sp0 av ev))) (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1v)) (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 (Z_to_bv 64 1018592))) (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 690816))) (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 691316))) (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8)))) (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av))) (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (D_libc sp0 av ev hw) (Z_to_bv 64 1017976) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017992) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1017984) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 1018616) (word_to_le_bytes 8 (Z_to_bv 64 224))) (Z_to_bv 64 1018624) (word_to_le_bytes 8 (Z_to_bv 64 8))) (Z_to_bv 64 886880) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 886856) (word_to_le_bytes 8 (Z_to_bv 64 886880))) (Z_to_bv 64 886664) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 1018592) ([Z_to_bv 8 1])) (Z_to_bv 64 886704) (word_to_le_bytes 4 (Z_to_bv 64 2))) (Z_to_bv 64 886696) (word_to_le_bytes 4 tid)) (Z_to_bv 64 886816) (word_to_le_bytes 8 (Z_to_bv 64 1018648))) (Z_to_bv 64 886784) (word_to_le_bytes 8 (Z_to_bv 64 886784))) (Z_to_bv 64 886672) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886680) (word_to_le_bytes 8 (Z_to_bv 64 886664))) (Z_to_bv 64 886688) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 1018560) (word_to_le_bytes 4 (rlw RND 0))) (Z_to_bv 64 1018564) (word_to_le_bytes 4 (rlw RND 4))) (Z_to_bv 64 1018561) ([Z_to_bv 8 0])) (Z_to_bv 64 886848) (word_to_le_bytes 8 (canary_w RND)))) rom).
Proof using fx sp0 Jb av ev uid hw rdraw Hva Hve Hlo Hhi Hal.
intros G HG regs rom s1v tid HJ H1 H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hk.
pose proof len_av as Hlen. pose proof rnd_bounds as (Hr1 & Hr2 & Hr3). pose proof (u64_range tid) as Htid.
unfold J_aux, J_lsm, D_libc, aux_base, argv_w in *.
eapply HG.
{ sv F_38ae0 D_38ae0 (Z_to_bv 64 (bv_unsigned sp0 - 96)).
stw F_38ae4 D_38ae4 (Z_to_bv 64 (bv_unsigned sp0 - 88)) (Z_to_bv 64 691140) ltac:(ok_win HJ).
stw F_38ae8 D_38ae8 (Z_to_bv 64 (bv_unsigned sp0 - 96)) (Z_to_bv 64 784872) ltac:(ok_win HJ).
sv F_38aec D_38aec (Z_to_bv 64 (bv_unsigned sp0 - 80)).
sn F_38af0 D_38af0.
sn F_38af4 D_38af4.
lb_step F_38af8 D_38af8 (Z_to_bv 8 0) ltac:(rd_img img_c6d90_1).
sn F_38afc D_38afc.
stepb_tk F_38b00 D_38b00 ltac:(pin; cond_compute).
sn F_38b0c D_38b0c.
sn F_38b10 D_38b10.
sn F_38b14 D_38b14.
stw F_38b18 D_38b18 (Z_to_bv 64 814544) (Z_to_bv 64 1) ltac:(ok_data).
sn F_38b1c D_38b1c.
ld_step F_38b20 D_38b20 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rd_img img_c5908_8) ltac:(apply bytes_le_to_Z_8).
stepb_tk F_38b24 D_38b24 ltac:(pin; cond_compute).
ld_step F_38b44 D_38b44 (word_to_le_bytes 8 (Z_to_bv 64 691140)) (Z_to_bv 64 691140) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_38b48 D_38b48 (word_to_le_bytes 8 (Z_to_bv 64 784872)) (Z_to_bv 64 784872) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_38b4c D_38b4c (Z_to_bv 64 (bv_unsigned sp0 - 80)).
stepret F_38b50 D_38b50 (0xa8bc4 : word) ltac:(pin; first [reflexivity | bveq]).
sn F_a8b7c D_a8b7c.
stepb_ft F_a8b80 D_a8b80 ltac:(pin; cond_compute).
ld_step F_a8b84 D_a8b84 (word_to_le_bytes 8 (Z_to_bv 64 691316)) (Z_to_bv 64 691316) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8b88 D_a8b88 (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned sp0 + 8))) (Z_to_bv 64 (bv_unsigned sp0 + 8)) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
ld_step F_a8b8c D_a8b8c (word_to_le_bytes 8 (argc_w av)) (argc_w av) ltac:(rewrite rdn_cmem_win by region_side; rd_hit8) ltac:(apply bytes_le_to_Z_8).
sv F_a8b90 D_a8b90 (Z_to_bv 64 (bv_unsigned sp0 - 48)).
stepret F_a8b94 D_a8b94 (0xa8c74 : word) ltac:(pin; first [reflexivity | bveq]).
sv F_a8c2c D_a8c2c (argc_w av).
sv F_a8c30 D_a8c30 (Z_to_bv 64 (bv_unsigned sp0 + 8)).
sv F_a8c34 D_a8c34 (Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av))).
stepjr F_a8c38 D_a8c38 (0x38c2c : word) ltac:(gres; pin; first [reflexivity | bveq]).
apply mst_refl. }
apply Hk; try (gres; pin; first [reflexivity | f_equal; lia | bveq]).
ra_chain.
Qed.

End P.

End FPX_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0Startup4.
From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.
Module Ns0Startup.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Nodes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Ns0_code_a8c88_a8f38. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0037.DivergeSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlgX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Img OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0StartupDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Startup1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Memset OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Startup2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Startup3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Startup4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r1ff24_20000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r20000_21000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4a000_4b000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4b000_4c000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Ns0_code_a8c88_a8f38.
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1. #[local] Existing Instance PropExec.fx0. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bwd_rz : forall segs scfg model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => srealizes segs scfg (mkCfg st model) K).
Proof using bmK.
intros segs scfg model K Hh Hlazy st st' Hms Hst'. eapply srz_msteps; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition J_main (sp0 : word) (av ev : list (list byte)) (uid hw : word) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 av ev uid hw (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
              (Z_to_bv 64 0xa8a78) (pn_w sp0 av ev) s1v (Z_to_bv 64 0xf8ae0)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0xa8a80)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0xa8c74)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0xa8bc4)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0xbf9e8)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry (sp0 : word) (av ev : list (list byte)) (uid hw : word) (rdraw : EntryDraw) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0xa8c84;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0xd8850;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x38c2c;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev uid hw s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev uid hw rdraw) J (D_main sp0 av ev hw (ed_random rdraw) tid)
}.

Section Assembly.
  Variable scfg : SpuriousCfg.
  Variable sp : word.
  Variables argv envp : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hvsp : valid_sp sp.

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
Proof using Hvsp. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
Proof using Hvsp. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
Proof using Hvsp. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Theorem ref_startup_sec : forall brk mbase lim fs0 stdin0 gid groups net nofile sigmask abt va urnd0 tmp0 K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry sp argv envp uid hw rdraw tid regs mem ->
       srealizes rsegs scfg (mkCfg (mkst regs (0x38c2c : word) mem (seg_rom rsegs))
                             (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim
                                                      (mkProcInput_full argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt va urnd0 tmp0)))) K) ->
    srealizes rsegs scfg (init_config rsegs rpc rph sp brk mbase rdraw lim (mkProcInput_full argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt va urnd0 tmp0)) K.
Proof using bmK scfg sp argv envp uid hw rdraw Hva Hve Hvsp.
intros brk mbase lim fs0 stdin0 gid groups net nofile sigmask abt va urnd0 tmp0 K HK.
pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
pose proof (u64_range sp) as Hsp.
unfold init_config. cbn [cfg_ms cfg_model in_argv in_envp in_uid in_hwcap].
set (model := init_model (segments_reserved rsegs) brk mbase sp lim (mkProcInput_full argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt va urnd0 tmp0)).
assert (Hh : m_halted model = None) by reflexivity.
assert (Hlazy : m_vm_lazy model = []) by reflexivity.
assert (Ht0 : m_tid model = None) by reflexivity.
set (RZ := fun st : machine_state => srealizes rsegs scfg (mkCfg st model) K).
assert (HG : bwd rsegs RZ) by (apply bwd_rz; [exact Hh | exact Hlazy]).
rewrite init_mkst.
replace (Z_to_bv 64 (Z.of_N rpc)) with (0x38ae0 : word) by (apply bv_eq; reflexivity).
rewrite cmem_init. fold (regs_init sp).
destruct (p1_run sp argv envp uid hw rdraw Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
  as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
eapply srz_msteps; [exact Hh | exact Hlazy | exact R1 |].
assert (A1' : getr regs1 1 = (0xa8994 : word)) by (rewrite A1; apply bv_eq; reflexivity).
destruct (memset304_run regs1 (cmem sp (wrap_mem RPH sp argv envp uid hw rdraw) (J1 sp argv J0) (fun _ => None))
  (seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0xa8994 : word) A1')
  as [regs2 [mem2 (R2 & M2 & G2)]].
{ unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
{ exact A10. } { exact A11. } { exact A12. }
{ rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
  replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
  symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
{ rewrite u_Z2bv by lia. lia. }
{ apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; apply wfJ_const | region_side | region_side]. }
eapply srz_msteps; [exact Hh | exact Hlazy | exact R2 |]. subst mem2.
rewrite wbytes_cmem_win by region_side.
carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
carry G2 A3 (3:reg) B3.
change (srealizes SEGS scfg (mkCfg ?st model) K) with (RZ st).
with_strategy opaque [wbytes srealizes] (eapply (p3_run sp argv envp uid hw rdraw) with (G := RZ)); try side Hva Hve HG.
{ unfold J1; repeat apply wfJ_wbytes; apply wfJ_const. }
intros regs3 C1 C2 C10 C18 G3.
carry G3 B3 (3:reg) C3. carry G3 B8 (8:reg) C8.
assert (Cz : forall r : reg, In r [5; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
{ intros r Hr. rewrite (G3 r), (G2 r); [apply Az; exact Hr | |];
  clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
  repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
pose proof (Cz 19 ltac:(in_list)) as Z19. pose proof (Cz 20 ltac:(in_list)) as Z20.
pose proof (Cz 21 ltac:(in_list)) as Z21. pose proof (Cz 22 ltac:(in_list)) as Z22.
pose proof (Cz 23 ltac:(in_list)) as Z23. pose proof (Cz 24 ltac:(in_list)) as Z24.
pose proof (Cz 25 ltac:(in_list)) as Z25. pose proof (Cz 26 ltac:(in_list)) as Z26.
pose proof (Cz 27 ltac:(in_list)) as Z27.
change (J1 sp argv J0) with (J_lsm sp argv J0).
with_strategy opaque [wbytes srealizes] (eapply (tls_c1 sp J0 argv envp uid hw rdraw) with (G := RZ) (s1v := getr regs3 9) (tid := Z_to_bv 64 0)); try side Hva Hve HG.
intros regs4a; intros.
with_strategy opaque [wbytes srealizes] (eapply (tls_c2 sp J0 argv envp uid hw rdraw) with (G := RZ) (tid := Z_to_bv 64 0)); try side Hva Hve HG.
intros regs4b; intros.
with_strategy opaque [wbytes srealizes] (eapply (tls_c3 sp J0 argv envp uid hw rdraw) with (G := RZ) (tid := Z_to_bv 64 0)); try side Hva Hve HG.
intros regs4c; intros.
with_strategy opaque [wbytes srealizes] (eapply (tls_c4 sp J0 argv envp uid hw rdraw) with (G := RZ) (tid := Z_to_bv 64 0)); try side Hva Hve HG.
intros regs4; intros.
unfold RZ at 1.
eapply (rz_set_tid SEGS scfg regs4 (0xa8ee4 : word) _ (seg_rom SEGS) model K W_a8ee4 F_a8ee4 E_a8ee4);
  [exact Hh | exact Hlazy | assumption | exact Ht0 |].
intros tid Htid.
replace (v_addi (0xa8ee4 : word) 4) with (0xa8ee8 : word) by (apply bv_eq; reflexivity).
set (model' := with_tid tid model).
assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted; exact Hh).
assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy; exact Hlazy).
set (RZ' := fun st : machine_state => srealizes rsegs scfg (mkCfg st model') K).
assert (HG' : bwd rsegs RZ') by (apply bwd_rz; [exact Hh' | exact Hlazy']).
change (srealizes SEGS scfg (mkCfg ?st model') K) with (RZ' st).
with_strategy opaque [wbytes srealizes] (eapply (tls_c5 sp J0 argv envp uid hw rdraw) with (G := RZ')); try side Hva Hve HG'.
intros regs5; intros.
with_strategy opaque [wbytes srealizes] (eapply (fin_c6 sp J0 argv envp uid hw rdraw) with (G := RZ')); try side Hva Hve HG'.
intros regs6; intros.
with_strategy opaque [wbytes srealizes] (eapply (fin_c7 sp J0 argv envp uid hw rdraw) with (G := RZ')); try side Hva Hve HG'.
intros regs7; intros.
with_strategy opaque [wbytes srealizes] (eapply (fin_c8 sp J0 argv envp uid hw rdraw) with (G := RZ')); try side Hva Hve HG'.
intros regs8; intros.
with_strategy opaque [wbytes srealizes] (eapply (fin_c9 sp J0 argv envp uid hw rdraw) with (G := RZ')); try side Hva Hve HG'.
intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
unfold RZ'. apply (HK tid regs9). { exact Htid. }
split; try assumption.
- intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
- eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
  + unfold J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. apply wfJ_const.
  + unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. with_strategy opaque [wbytes] reflexivity.
Qed.

End Assembly.

(* [comment removed for export] *)
Theorem ref_startup : forall scfg sp brk mbase (rdraw : EntryDraw) lim inp K,
  valid_sp sp -> valid_brk rsegs brk -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     main_entry sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw tid regs mem ->
     srealizes rsegs scfg (mkCfg (mkst regs (0x38c2c : word) mem (seg_rom rsegs))
                           (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
  srealizes rsegs scfg (init_config rsegs rpc rph sp brk mbase rdraw lim inp) K.
Proof using bmK.
intros scfg sp brk mbase rdraw lim [argv envp fs0 stdin0 uid gid groups net nofile sigmask hw abt va urnd0 tmp0] K Hsp Hbrk Hva Hve HK.
cbn [in_argv in_envp in_uid in_hwcap] in *.
exact (ref_startup_sec scfg sp argv envp uid hw rdraw Hva Hve Hsp brk mbase lim fs0 stdin0 gid groups net nofile sigmask abt va urnd0 tmp0 K HK).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem RPH sp0 av ev uid hw rdraw) a n.
Proof using ME.
intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply rdn_cmem_above; assumption.
Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem RPH sp0 av ev uid hw rdraw a.
Proof using ME.
intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply cmem_at_above. exact Ha.
Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : forall (a : word),
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
Proof using ME.
intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
rewrite cmem_at_win by (unfold in_win, win_lo; lia). apply HJ. unfold in_win, win_lo. lia.
Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
Proof using ME.
intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply store_ok_cmem_win; [exact HJ | unfold win_lo; lia | lia].
Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 av ev hw (ed_random rdraw) tid a.
Proof using ME.
intros a Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply cmem_at_data. unfold win_lo. exact Ha.
Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 av ev hw (ed_random rdraw) tid) a n.
Proof using ME.
intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply rdn_cmem_data. unfold win_lo. exact Ha.
Qed.
End Consumers.

End FPX_1.

End Ns0Startup.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv.
Module Ns0StartupFacts.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.RunEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0StartupDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Startup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RPH := Plain.M.phdrs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition D_main_cells : list (Z * nat) :=
  [(0xd8780%Z, 8%nat); (0xf8ae8%Z, 8%nat); (0xf8b48%Z, 8%nat); (0xf8b10%Z, 8%nat); (0xf8ad8%Z, 8%nat); (0xf8ad0%Z, 8%nat); (0xf8878%Z, 8%nat); (0xf8888%Z, 8%nat); (0xf8880%Z, 8%nat); (0xf8af8%Z, 8%nat); (0xf8b00%Z, 8%nat); (0xd8860%Z, 8%nat); (0xd8848%Z, 8%nat); (0xd8788%Z, 8%nat); (0xf8ae0%Z, 1%nat); (0xd87b0%Z, 4%nat); (0xd87a8%Z, 4%nat); (0xd8820%Z, 8%nat); (0xd8800%Z, 8%nat); (0xd8790%Z, 8%nat); (0xd8798%Z, 8%nat); (0xd87a0%Z, 8%nat); (0xf8ac0%Z, 4%nat); (0xf8ac4%Z, 4%nat); (0xf8ac1%Z, 1%nat); (0xd8840%Z, 8%nat); (0xc6dd0%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0xfa000)%Z.

(* [comment removed for export] *)
Definition djw (P : Prop) : Prop := P.

Lemma range_disjoint_djw : forall a n c,
  range_disjoint_b a n c = true ->
  djw (a + Z.of_nat n <= fst c \/ fst c + Z.of_nat (snd c) <= a)%Z.
Proof using.
intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Section Facts.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main sp0 av ev hw (ed_random rdraw) tid.
  Local Notation RND := (ed_random rdraw) (only parsing).

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
Proof using Hva. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  Lemma D_main_miss : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs (D_main sp0 av ev hw (ed_random rdraw) tid) (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof using sp0 av ev hw rdraw tid.
intros segs a n Hb.
pose proof (u64_range tid). pose proof (u64_range hw).
unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
end.
repeat match goal with
| H : range_disjoint_b _ _ _ = true |- _ =>
    apply range_disjoint_djw in H; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ] in H
| H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
| H : true = true |- _ => clear H
end.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
repeat (rewrite rdn_wbytes_out by
  (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; imm_norm; unorm;
   lazymatch goal with
   | |- (?A \/ ?B) => match goal with H : djw _ |- _ => exact H end
   | |- _ => lia
   end)).
reflexivity.
Qed.

  Ltac hitD :=
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
    pose proof len_av;
    peel; first [ apply rdn_wbytes_hit8; unorm; lia
                | match goal with |- rdn _ (wbytes _ ?a ?bs) ?a _ = _ =>
                    rewrite <- (length_N_to_le_bytes 4) at 1; apply rdn_wbytes_hit; rewrite length_N_to_le_bytes; unorm; lia end ].

  (* [comment removed for export] *)
  Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 0xd87a8) 4 = Some (word_to_le_bytes 4 tid).
Proof using sp0 av ev hw rdraw tid.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0xf8ac0) 8 = Some (word_to_le_bytes 8 (canary_w RND)).
Proof using sp0 av ev hw rdraw tid.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
rewrite canary_bytes.
lazymatch goal with
| |- rdn _ (wbytes (wbytes (wbytes ?DD _ _) _ _) _ _) _ _ = _ =>
    pose proof (rd_guard_at segs DD RND 0xf8ac0 ltac:(lia) ltac:(lia)) as HG;
    cbn [Z.add Pos.add Pos.succ] in HG; exact HG
end.
Qed.

  (* [comment removed for export] *)
  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0xf8b10) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
Proof using sp0 av ev hw rdraw tid Hva.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.

  (* [comment removed for export] *)
  Lemma D_main_hwcap : forall segs,
    rdn segs D (Z_to_bv 64 0xf8b48) 8 = Some (word_to_le_bytes 8 hw).
Proof using sp0 av ev hw rdraw tid Hva.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.

  (* [comment removed for export] *)
  Lemma D_main_environ : forall segs,
    rdn segs D (Z_to_bv 64 0xd8780) 8 = Some (word_to_le_bytes 8 (envp_w sp0 av)).
Proof using sp0 av ev hw rdraw tid Hva.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). pose proof len_av. subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.

  (* [comment removed for export] *)
  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0xd8788) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xd8788)).
Proof using sp0 av ev hw rdraw tid.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.

  (* [comment removed for export] *)
  Lemma D_main_locale : forall segs,
    rdn segs D (Z_to_bv 64 0xd8820) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf8b18)).
Proof using sp0 av ev hw rdraw tid.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.

  (* [comment removed for export] *)
  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0xd8840) 8 = Some (word_to_le_bytes 8 (canary_w RND)).
Proof using sp0 av ev hw rdraw tid.
intros segs. pose proof (u64_range tid). pose proof (u64_range hw). subst D.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.


  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rdn_pointwise_ov : forall segs m n (a : word) bs,
    (forall j, (j < n)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None) ->
    (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
    rdn segs m a n = Some bs ->
    forall j, (j < n)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof using.
intros segs m n.
induction n as [|n IH]; intros a bs Hdef Hnw Hr j Hj; [lia|].
cbn [rdn] in Hr. pose proof (u64_range a) as Ha.
pose proof (Hdef 0%nat ltac:(lia)) as H0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0.
destruct (m a) as [b|] eqn:Hm; [|exfalso; apply H0; reflexivity].
destruct (rdn segs m (a + 1) n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
destruct j as [|j].
+ rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hm.
+ cbn [nth]. assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
  replace (bv_unsigned a + Z.of_nat (S j))%Z with (bv_unsigned (a + 1) + Z.of_nat j)%Z by lia.
  apply (IH (a + 1) rest); [ | lia | exact Hr' | lia].
  intros k Hk. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat k)%Z with (bv_unsigned a + Z.of_nat (S k))%Z by lia.
  apply Hdef. lia.
Qed.

  Ltac d_cover :=
    repeat first
      [ rewrite wbytes_inside by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia); discriminate
      | rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; unorm; lia) ].

  Ltac cover8 :=
    let i := fresh "i" in let Hi := fresh "Hi" in
    intros i Hi; pose proof (u64_range tid); pose proof (u64_range hw); pose proof len_av; subst D;
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
    assert (C : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%Z) by lia;
    destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    lazymatch goal with |- _ (Z_to_bv 64 ?z) <> None => let c := eval vm_compute in z in change z with c end;
    d_cover.

  Lemma D_cover_guard : forall i, (0 <= i < 8)%Z -> D (Z_to_bv 64 (0xf8ac0 + i)) <> None.
Proof using sp0 av ev hw rdraw tid Hva. cover8. Qed.
  Lemma D_cover_canary : forall i, (0 <= i < 8)%Z -> D (Z_to_bv 64 (0xd8840 + i)) <> None.
Proof using sp0 av ev hw rdraw tid Hva. cover8. Qed.
  Lemma D_cover_hwcap : forall i, (0 <= i < 8)%Z -> D (Z_to_bv 64 (0xf8b48 + i)) <> None.
Proof using sp0 av ev hw rdraw tid Hva. cover8. Qed.

  Ltac pt8 Hcov Hrd :=
    let i := fresh "i" in let Hi := fresh "Hi" in
    intros i Hi;
    lazymatch goal with |- D (Z_to_bv 64 (?a + i)) = Some _ =>
      pose proof (rdn_pointwise_ov SEGS D 8 (Z_to_bv 64 a) _
        ltac:(intros j Hj; rewrite u_Z2bv by lia; apply Hcov; lia)
        ltac:(rewrite u_Z2bv by lia; lia) (Hrd SEGS) (Z.to_nat i) ltac:(lia)) as Hp;
      rewrite u_Z2bv, Z2Nat.id in Hp by lia; exact Hp
    end.

  Lemma D_guard_pt : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0xf8ac0 + i)) = Some (nth (Z.to_nat i) (word_to_le_bytes 8 (canary_w RND)) (Z_to_bv 8 0)).
Proof using sp0 av ev hw rdraw tid Hva. pt8 D_cover_guard D_main_guard. Qed.
  Lemma D_canary_pt : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0xd8840 + i)) = Some (nth (Z.to_nat i) (word_to_le_bytes 8 (canary_w RND)) (Z_to_bv 8 0)).
Proof using sp0 av ev hw rdraw tid Hva. pt8 D_cover_canary D_main_canary. Qed.
  Lemma D_hwcap_pt : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0xf8b48 + i)) = Some (nth (Z.to_nat i) (word_to_le_bytes 8 hw) (Z_to_bv 8 0)).
Proof using sp0 av ev hw rdraw tid Hva. pt8 D_cover_hwcap D_main_hwcap. Qed.

  (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.

  Lemma main_entry_rdn_image : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs mem (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
Proof using Hlo ME.
intros segs a n Hb.
assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0xfa000)%Z).
{ unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
  by (rewrite stack_max_size_val; unorm; lia).
apply D_main_miss. exact Hb.
Qed.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0xd87a8) 4 = Some (word_to_le_bytes 4 tid).
Proof using Hlo ME.
intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
  by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0xf8ac0) 8 = Some (word_to_le_bytes 8 (canary_w RND)).
Proof using Hlo ME.
intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
  by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
Qed.
End Facts.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0StartupFacts.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.
Module Ns0MainEntry.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MuslStrlen.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.RunEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0StartupDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Startup OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0StartupFacts.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Lemma D_main_none : forall sp0 av ev hw rnd tid (i : Z),
  valid_argv av -> (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main sp0 av ev hw rnd tid (Z_to_bv 64 i) = None.
Proof using.
intros sp0 av ev hw rnd tid i.
intros Hva Hlo Hhi Hb.
pose proof (u64_range tid) as Ht. pose proof (u64_range hw) as Hhw.
unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
end.
repeat match goal with
| H : range_disjoint_b _ _ _ = true |- _ =>
apply range_disjoint_djw in H; cbn [fst snd] in H
| H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
| H : true = true |- _ => clear H
end.
assert (Hui : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; lia).
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
Time repeat (rewrite OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit.wbytes_outside;
[ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
| rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
reflexivity.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_high : forall (a : word), (0xfa000 <= bv_unsigned a)%Z -> seg_rom RSEGS a = None.
Proof using.
intros a Ha. unfold seg_rom. unfold memory_read.
cbn -[bv_unsigned Z.leb Z.ltb Z.add Z.sub N.leb N.ltb N.add bv_extract Z.of_N Z.to_N].
cbn [Z.of_N].
repeat (lazymatch goal with
| |- context [((?lo <=? bv_unsigned a)%Z && ?c)%bool] =>
replace c with false by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r
end).
reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_pointwise_inv : forall segs m n (a : word) bs,
  (forall j, (j < n)%nat -> seg_rom segs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = None) ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn segs m a n = Some bs ->
  forall j, (j < n)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof using.
intros segs m.
intros n.
induction n as [|n IH]; intros a bs Hseg Hnw Hr j Hj; [lia|].
cbn [rdn] in Hr. pose proof (u64_range a) as Ha.
pose proof (Hseg 0%nat ltac:(lia)) as H0. rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0.
destruct (m a) as [b|] eqn:Hm.
- destruct (rdn segs m (a + 1) n) as [rest|] eqn:Hr'; [|discriminate]. injection Hr as <-.
destruct j as [|j].
+ rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned. exact Hm.
+ cbn [nth]. assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
replace (bv_unsigned a + Z.of_nat (S j))%Z with (bv_unsigned (a + 1) + Z.of_nat j)%Z by lia.
apply (IH (a + 1) rest); [ | lia | exact Hr' | lia].
intros k Hk. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat k)%Z with (bv_unsigned a + Z.of_nat (S k))%Z by lia.
apply Hseg. lia.
- rewrite H0 in Hr. discriminate.
Qed.

Section MainEntry.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Definition p0 : word := cat_argv_ptr sp0 av ev 0.
  Definition p1 : word := cat_argv_ptr sp0 av ev 1.
  Definition auxvp : word := auxv_w sp0 av ev.
  Definition rnd : word := at_random_ptr sp0 av ev.

  (* [comment removed for export] *)
  Definition vals0 : list word := [sp0; p0; p1; auxvp; rnd; tid] ++ junk_vals regs.
  Definition blobs0 : list (list byte) :=
    [a0s ++ [Z_to_bv 8 0]; path ++ [Z_to_bv 8 0]; word_to_le_bytes 8 (canary_w (ed_random rdraw)); word_to_le_bytes 8 hw].
  Definition E0 : env := Env (vals_ev vals0) (blobs_ev blobs0).

  Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

  Definition sr_main : list expr :=
    [ELit 0; ELit 0xa8c84; spx (-48); ELit 0x10800; ELit 0xd8850; EVar 11; EVar 12; EVar 13;
     spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x38c2c; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-8388608)) 8388608;
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000400000; KRange (EVar 4) 0x7fff80000000 0x800000400000;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 160;
     KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 4) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 4) 8;
     KWord (SA (EVar 3) 0) 8 (ELit 3); KWord (SA (EVar 3) 8) 8 (ELit 0x10040);
     KWord (SA (EVar 3) 16) 8 (ELit 4); KWord (SA (EVar 3) 24) 8 (ELit 56);
     KWord (SA (EVar 3) 32) 8 (ELit 5); KWord (SA (EVar 3) 40) 8 (ELit 10);
     KWord (SA (EVar 3) 48) 8 (ELit 16); KBlob (SA (EVar 3) 56) (ELit 8) 3;   (* [comment removed for export] *)
     KWord (SA (EVar 3) 64) 8 (ELit 6); KWord (SA (EVar 3) 72) 8 (ELit 4096);
     KWord (SA (EVar 3) 80) 8 (ELit 11); (* [comment removed for export] *)
     KWord (SA (EVar 3) 96) 8 (ELit 12); (* [comment removed for export] *)
     KWord (SA (EVar 3) 112) 8 (ELit 23); KWord (SA (EVar 3) 120) 8 (ELit 0);
     KWord (SA (EVar 3) 128) 8 (ELit 25); KWord (SA (EVar 3) 136) 8 (EVar 4);
     KWord (SA (EVar 3) 144) 8 (ELit 0); KWord (SA (EVar 3) 152) 8 (ELit 0)
     (* [comment removed for export] *)].

  Definition kn_image : list kentry :=
    [KWr (SA (ELit 0) 0xc6000) 0x34000;
     KImg 0x10000 0xc6dd0;
     KImg 0xc6dd1 0xd8780; KImg 0xf8858 0xf8878;
     KWord (SA (ELit 0) 0xd8788) 8 (ELit 0xd8788);
     KWord (SA (ELit 0) 0xd87a8) 4 (EVar 5);
     KImg 0xd87b4 0xd8800; KImg 0xd8808 0xd8820; KWord (SA (ELit 0) 0xd8820) 8 (ELit 0xf8b18); KImg 0xd8828 0xd8840;
     KBlob (SA (ELit 0) 0xd8840) (ELit 8) 2;                       (* [comment removed for export] *)
     KImg 0xd8850 0xd8860; KImg 0xd8868 0xd88d8; KImg 0xf8890 0xf8ab8; KImg 0xf8ab8 0xf8ac0;
     KBlob (SA (ELit 0) 0xf8ac0) (ELit 8) 2;                       (* [comment removed for export] *)
     KImg 0xf8ac8 0xf8ad0;
     KImg 0xf8ae1 0xf8ae8; KWord (SA (ELit 0) 0xf8ae8) 8 (EVar 3);
     KImg 0xf8af0 0xf8af8; KImg 0xf8b08 0xf8b10; KWord (SA (ELit 0) 0xf8b10) 8 (ELit 4096);
     KImg 0xf8b18 0xf8b48; KBlob (SA (ELit 0) 0xf8b48) (ELit 8) 3 (* [comment removed for export] *); KImg 0xf8b50 0xf8c58; KImg 0xf8c58 0xfa000;
     KRange (EVar 5) 1 4194303;
     KImg 0 0x1000 (* [comment removed for export] *)].

  (* [comment removed for export] *)
  Definition kn_main : list kentry := kn_stack ++ kn_auxv ++ kn_image.
End MainEntry.

Definition all_regs : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof using.
intros n Hn.
destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

Lemma regs_ok_by_index : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i all_regs 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof using.
intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot].
reflexivity.
- pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Section MainEntryProofs.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv uid hw rdraw tid regs mem.

  Let E := E0 sp0 a0s path envv hw rdraw tid regs.

  Lemma sp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Proof using sp0 Hvsp. exact (proj1 Hvsp). Qed.
  Lemma sp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Proof using sp0 Hvsp. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma sp_al : (bv_unsigned sp0 mod 16 = 0)%Z.
Proof using sp0 Hvsp. exact (proj2 (proj2 Hvsp)). Qed.

  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid] ++ junk_vals regs) (Z_to_bv 64 0).
Proof using sp0 a0s path envv hw rdraw tid regs. intros n. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
Proof using sp0 a0s path envv hw rdraw tid regs.
intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 sp0 a0s path envv; p1 sp0 a0s path envv; auxvp sp0 a0s path envv; rnd sp0 a0s path envv; tid] + i)%nat.
rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
Proof using sp0 a0s path envv hw rdraw tid regs. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv uid hw rdraw tid regs mem.
  Let E := E0 sp0 a0s path envv hw rdraw tid regs.

  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ rewrite (spx_val sp0 a0s path envv hw rdraw tid regs)
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk sp0 a0s path envv hw rdraw tid regs (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ _ _ ME); f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ _ _ ME); cbn; tauto
                | idtac ].

  Theorem main_regs_ok : regs_ok E sr_main regs.
Proof using sp0 a0s path envv uid hw rdraw tid regs mem Hvsp Htid ME.
pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
apply regs_ok_by_index.
intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
Qed.
End MainRegs.

Section KnowProofs.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv uid hw rdraw tid regs mem.
  Let E := E0 sp0 a0s path envv hw rdraw tid regs.

  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
Proof using sp0 Hvsp. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z.
Proof using sp0 Hvsp. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z.
Proof using sp0 Hvsp. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0.
Proof using sp0 a0s path envv hw rdraw tid regs. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 sp0 a0s path envv.
Proof using sp0 a0s path envv hw rdraw tid regs. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 sp0 a0s path envv.
Proof using sp0 a0s path envv hw rdraw tid regs. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp sp0 a0s path envv.
Proof using sp0 a0s path envv hw rdraw tid regs. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rnd sp0 a0s path envv.
Proof using sp0 a0s path envv hw rdraw tid regs. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid.
Proof using sp0 a0s path envv hw rdraw tid regs. reflexivity. Qed.

  Lemma know_stack : know_ok RSEGS E mem kn_stack.
Proof using sp0 a0s path envv uid hw rdraw tid regs mem Hva Hve Hvsp ME.
pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
unfold kn_stack, know_ok.
repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
- split; [lia | exact Hal].
- lia.
- split; [lia|]. intros d m Hd Hm.
apply (main_entry_store_ok_win sp0 av envv uid hw rdraw tid regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by lia.
pose proof (read_argc_w RSEGS RPH sp0 av envv uid hw rdraw Hva) as Hr. unfold wmem in Hr.
rewrite (Hr Hve) by (unfold sp_window_hi; lia).
rewrite n_to_le_8_spec. reflexivity.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv uid hw rdraw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(subst av; cbn; lia)) as Hr.
unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv uid hw rdraw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat ltac:(subst av; cbn; lia)) as Hr.
unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (read_argv_null RSEGS RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hr.
rewrite w_add_nat in Hr. subst av. change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
rewrite <- (rdn_wmem_stack RSEGS RPH sp0 [a0s; path] envv uid hw rdraw) in Hr by (try rewrite u_small by lia; lia).
unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
Qed.

  Lemma auxvp_eq : auxvp sp0 a0s path envv = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
Proof using sp0 a0s path envv. unfold auxvp, auxv_w, auxv_off. subst av. cbn [length]. f_equal. lia. Qed.

  Lemma auxvp_u : bv_unsigned (auxvp sp0 a0s path envv) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + 160 <= 2240000)%Z.
Proof using sp0 a0s path envv uid hw rdraw Hva Hve Hvsp.
pose proof kp_lo. pose proof kp_hi.
pose proof (auxv_off_bound RPH sp0 rdraw av envv uid hw) as Hb.
pose proof (lay_bsb_len RPH sp0 rdraw av envv uid hw Hva Hve) as Hl.
rewrite auxvp_eq. rewrite u_small by lia. lia.
Qed.

  Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rnd sp0 a0s path envv))%Z
    /\ (bv_unsigned (rnd sp0 a0s path envv) + 16 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (rnd sp0 a0s path envv) mod 8 = 0)%Z
    /\ (forall j n, (j + n <= 16)%nat ->
          rdn RSEGS (stack_to_mem sp0 (entry_stack_image RPH sp0 av envv uid hw rdraw))
              (Z_to_bv 64 (bv_unsigned (rnd sp0 a0s path envv) + Z.of_nat j)) n
          = Some (firstn n (skipn j (at_random_bytes (ed_random rdraw))))).
Proof using sp0 a0s path envv uid hw rdraw Hva Hve Hvsp.
pose proof kp_lo as HLO. pose proof kp_hi as HHI.
pose proof (lay_bsb_len RPH sp0 rdraw av envv uid hw Hva Hve) as Hl.
destruct (rnd_facts RSEGS RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) kp_al)
as (A & B & C & D & F).
unfold rnd. subst av. repeat split; try assumption; try lia.
Qed.

  Lemma auxv_word_at : forall j, (j < 20)%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8 (nth j (auxv_words RPH (rnd sp0 a0s path envv) uid hw) (Z_to_bv 64 0))).
Proof using sp0 a0s path envv uid hw rdraw tid regs mem Hva Hve Hvsp ME.
intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
destruct auxvp_u as [Hu Hb].
rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv uid hw rdraw) as Hw. unfold wmem in Hw.
rewrite Hw by (rewrite u_small by lia; lia).
replace (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j))
with (sp0 + nat_to_word (auxv_off av envv + 8 * j)) by (rewrite w_add_nat; f_equal; lia).
rewrite (read_auxv_word RSEGS RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_hi; lia) j Hj).
rewrite n_to_le_8_spec. unfold rnd. reflexivity.
Qed.

  Ltac kw_auxv j :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      replace k with (8 * Z.of_nat j)%Z by reflexivity end;
    rewrite (auxv_word_at j) by lia; unfold auxv_words; cbn [nth]; try reflexivity.

  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
Proof using sp0 a0s path envv uid hw rdraw tid regs mem Hva Hve Hvsp ME.
pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
unfold kn_auxv, know_ok.
repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
rewrite ?ke0, ?ke3, ?ke4; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4;
try rewrite Hau; try lia.
- split; [lia|].
destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
by (unfold auxv_off; subst av; cbn [length]; lia).
apply Z_mod_mult.
- kw_auxv 0%nat. - kw_auxv 1%nat. - kw_auxv 2%nat. - kw_auxv 3%nat. - kw_auxv 4%nat. - kw_auxv 5%nat.
- kw_auxv 6%nat.
-
rewrite u_small by lia. split; [lia|].
split; [subst E; unfold E0; cbn [eb blobs_ev blobs0 nth]; rewrite length_N_to_le_bytes; reflexivity|].
pose proof (auxv_word_at 7 ltac:(lia)) as Hr.
intros i Hi. subst E; unfold E0; cbn [eb blobs_ev blobs0 nth].
unfold auxv_words, auxv_entries in Hr. cbn [flat_map fst snd app nth] in Hr. rewrite Hau in Hr.
pose proof (rdn_pointwise_inv RSEGS mem 8 (Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv) + 8 * Z.of_nat 7)) _
ltac:(intros j Hj; rewrite u_small by lia; apply seg_rom_high; rewrite u_small by lia; lia)
ltac:(rewrite u_small by lia; lia) Hr (Z.to_nat i) ltac:(lia)) as Hp.
rewrite u_small, Z2Nat.id in Hp by lia.
replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv) + 56 + i)%Z
with (bv_unsigned sp0 + Z.of_nat (auxv_off av envv) + 8 * Z.of_nat 7 + i)%Z by lia.
exact Hp.
- kw_auxv 8%nat. - kw_auxv 9%nat. - kw_auxv 10%nat. - kw_auxv 12%nat.
- kw_auxv 14%nat. - kw_auxv 15%nat. - kw_auxv 16%nat. - kw_auxv 17%nat. - kw_auxv 18%nat. - kw_auxv 19%nat.
Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvp : forall segs,
    rdn segs (D_main sp0 av envv hw (ed_random rdraw) tid) (Z_to_bv 64 0xf8ae8) 8
    = Some (word_to_le_bytes 8 (auxvp sp0 a0s path envv)).
Proof using sp0 a0s path envv hw rdraw tid Hvsp.
intros segs.
pose proof (u64_range tid). pose proof (u64_range hw). pose proof kp_lo. pose proof kp_hi.
unfold auxvp, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0xc6000) 0x34000 = true.
Proof using. vm_compute. reflexivity. Qed.

  Lemma range_disjoint_sub : forall lo n c i, range_disjoint_b lo n c = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> range_disjoint_b i 1 c = true.
Proof using.
intros lo n [c w] i H Hlo Hhi. unfold range_disjoint_b in *. cbn [fst snd] in *.
apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
Qed.

  Lemma missb_sub : forall lo n i, D_main_missb lo n = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> D_main_missb i 1 = true.
Proof using.
intros lo n i H Hlo Hhi. unfold D_main_missb in *.
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply Z.leb_le in H2. apply Z.leb_le in H3.
apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
apply forallb_forall. intros c Hc. apply (range_disjoint_sub lo n); [|lia|lia].
apply (proj1 (forallb_forall _ _) H1). exact Hc.
Qed.

  (* [comment removed for export] *)
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0xfa000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
Proof using sp0 a0s path envv uid hw rdraw tid regs mem Hva Hvsp ME.
intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
assert (Hlo0 : (0 <= lo)%Z).
{ unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
apply Z.leb_le in Hb. exact Hb. }
cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
rewrite (main_entry_mem_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
apply (D_main_none sp0 av envv hw (ed_random rdraw) tid i Hva); [lia | lia |].
apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.
  (* [comment removed for export] *)
  Ltac kblob8 L :=
    unorm; rewrite ?Z.add_0_l; repeat split; try lia;
    try (subst E; unfold E0; cbn [eb blobs_ev blobs0 nth]; rewrite length_N_to_le_bytes; reflexivity);
    intros i Hi; subst E; unfold E0; cbn [eb blobs_ev blobs0 nth];
    rewrite (main_entry_mem_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    apply L; lia.

  Lemma know_image : know_ok RSEGS E mem kn_image.
Proof using sp0 a0s path envv uid hw rdraw tid regs mem Hva Hvsp Htid ME.
pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
unfold kn_image, know_ok.
repeat apply Forall_cons; try apply Forall_nil;
try kimg;
cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
rewrite ?(u_small 0) by lia; cbn [Z.add].
- split; [lia|]. intros d m Hd Hm.
eapply (store_ok_window RSEGS mem (Z_to_bv 64 0xc6000) (Z_to_bv 64 (0xc6000 + d)) 0x34000 m 0xc6000 0xfa000);
[reflexivity | reflexivity | cbn; lia | apply wseg_data | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
- kw_data (D_main_self sp0 av envv hw rdraw tid).
- kw_mem (main_entry_tid sp0 av envv uid hw rdraw tid Hlo regs mem ME).
- kw_data (D_main_locale sp0 av envv hw rdraw tid).
- kblob8 (D_canary_pt sp0 av envv hw rdraw tid Hva).
- kblob8 (D_guard_pt sp0 av envv hw rdraw tid Hva).
- kw_data D_main_auxvp.
- kw_data (D_main_pagesize sp0 av envv hw rdraw tid Hva).
- kblob8 (D_hwcap_pt sp0 av envv hw rdraw tid Hva).
- lia.
Qed.


  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
Proof using sp0 a0s path envv uid hw rdraw tid regs mem Hva Hve Hvsp Htid ME.
unfold kn_main, know_ok.
apply Forall_app; split; [apply know_stack|].
apply Forall_app; split; [apply know_auxv | apply know_image].
Qed.

  (* [comment removed for export] *)
  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr sp0 av envv k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr sp0 av envv k))%Z
    /\ (bv_unsigned (cat_argv_ptr sp0 av envv k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z.
Proof using sp0 a0s path envv uid hw rdraw tid regs mem Hva Hve Hvsp ME.
intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
pose proof (lay_bsb_nw RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
destruct (argv_ptr_bounds_at sp0 av envv Hva Hve ltac:(unfold sp_window_hi; lia) k Hk') as [B1 B2].
pose proof (u_cat_argv_ptr RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
pose proof (struct_av_bound RPH sp0 rdraw av envv uid hw Hva Hve) as Hsb.
pose proof (total_arg_bytes_firstn_le k av) as Hf.
pose proof (argv_str_len av Hva k Hk') as Hlen.
repeat split.
- rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by lia.
pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv uid hw rdraw) as Hw. unfold wmem in Hw. rewrite Hw by lia.
apply read_argv_cstr_k; [exact Hk' | exact Hnw].
- exact B1.
- lia.
- exact Hlen.
Qed.

  (* [comment removed for export] *)
  Lemma main_str_fits : entry_stack_fits sp0 av envv -> forall k, (k < 2)%nat ->
    (bv_unsigned (cat_argv_ptr sp0 av envv k) + Z.of_nat (length (nth k av [])) + 17 <= 0x800000000000)%Z.
Proof using sp0 a0s path envv uid hw rdraw Hva Hve Hvsp.
intros Hfit k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
assert (Hk' : (k < length av)%nat) by (subst av; cbn; lia).
pose proof (u_cat_argv_ptr RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
pose proof (bsb_len_lower RPH sp0 av envv uid hw rdraw) as Hlow.
pose proof (total_arg_bytes_firstn_le (S k) av) as Hmono.
pose proof (total_arg_bytes_firstn_S av k Hk') as Hstep.
pose proof (build_stack_bytes_within_span RPH sp0 av envv uid hw rdraw) as Hspan.
unfold entry_stack_fits, sp_window_hi in Hfit. lia.
Qed.

  (* [comment removed for export] *)
  Lemma main_auxv : forall j, (j < 20)%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp sp0 a0s path envv) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8 (Z_to_bv 64 (nth j
        [3; Z.of_N (ph_addr RPH); 4; Z.of_N (ph_ent RPH); 5; Z.of_N (ph_num RPH); 16; bv_unsigned hw; 6; 4096;
         11; bv_unsigned uid; 12; bv_unsigned uid; 23; 0; 25; bv_unsigned (rnd sp0 a0s path envv); 0; 0]%Z 0%Z))).
Proof using sp0 a0s path envv uid hw rdraw tid regs mem Hva Hve Hvsp ME.
intros j Hj. rewrite (auxv_word_at j Hj). unfold auxv_words, auxv_entries. cbn [flat_map fst snd app].
do 20 (destruct j as [|j]; [cbn [nth]; rewrite ?Z_to_bv_bv_unsigned; reflexivity|]). lia.
Qed.

  Lemma main_auxv_rng :
    (0 <= bv_unsigned sp0)%Z /\ (bv_unsigned sp0 + 40 <= bv_unsigned (auxvp sp0 a0s path envv))%Z
    /\ (bv_unsigned (auxvp sp0 a0s path envv) + 160 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (auxvp sp0 a0s path envv) mod 8 = 0)%Z
    /\ (bv_unsigned sp0 + 2240000 < 2 ^ 64)%Z
    /\ (0 <= bv_unsigned uid < 2 ^ 64)%Z
    /\ (bv_unsigned sp0 <= bv_unsigned (rnd sp0 a0s path envv))%Z
    /\ (bv_unsigned (rnd sp0 a0s path envv) + 16 <= bv_unsigned sp0 + 2240000)%Z.
Proof using sp0 a0s path envv uid hw rdraw Hva Hve Hvsp.
pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal. pose proof (u64_range uid) as Hu.
destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3 & Hr4).
assert (Hoff : (40 <= Z.of_nat (auxv_off av envv))%Z) by (unfold auxv_off; subst av; cbn [length]; lia).
repeat split; try lia.
rewrite Hau. destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
by (unfold auxv_off; subst av; cbn [length]; lia).
apply Z_mod_mult.
Qed.
End KnowProofs.

End FPX_1.

End Ns0MainEntry.
Module Ns0Exit_run2.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
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
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.LibAtomic OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0ExitBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4b000_4c000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4d000_4e000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4e000_4f000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022.Ns0_code_r58000_59000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0xa933c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0xae984)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0xa933c ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0xc6cc0 wp1 rp1 ->
  file_clean mem 0xc6bd0 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0xae974 : word) mem rom)
                 (mkst regs' (0xa8fe0 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0058 ()) ["FPX_1"] "h07__arithh14__x1h21Hh36__sat3h46__sat4h51bh68__varmaph75__with84__ffh91nh:4__p1h;1zh<2gHh=1oh>5regs'h?2Hah@1xhA2b1hB2b2hC1mhD1yhE3F1lhF4F1rehG4F1rphH4F1wbhI4F1wphJ3F2lhK4F2rehL4F2rphM4F2wbhN4F2wphO4GerrhP3GinhQ3GnlhR4GoflhS4GouthT3HrahU3Hs0hV3HsphW3SOKhX4SPhihY4SPlohZ4codeh[3memh\4regsh]3romh^3rp1h_3rp2h`2spha3wp1hb3wp2p%0p%1p%2p%3p%4p%5p%6p%7p%8p%9p%:p%;p%<p%=p&0p&1p;1p;3p;2p;4p;5p;=p;6p;:p;Bp;<p;?p;>p;Ap;7p;8p;9p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9g002PR1p4p7210g003<R2p4p710R3p8p1003Zp4p710P3p8p10045p4p710g004TR3p4p710p8g0050j1ZTg0077j1~Tg007Zj32Tg005Oj1=Tg00:gj1fTg00;Ej2^Tg0064j1;Tg006Yk10KTg0084R4j20Tg008Pk11uTg008nk20dTg009GR5j25Tg009dk41nTg00:GR6k10hTg00<gk11_Tg00?hk31[Tg00;ak21WTg00@ok11UTg00?4k21:Tg00=Jk11QTg00>5k51NTg00@Lk317Tg05?\j2RTg00Iik20eTg00AMk110Tg00BOk10~Tg00GSk30DTg00H6k30OTg00ICk11ej2VTg00Hck21cTg00G1k11FTg00Kfk20HTg00Mbj2bTg00Lnj2DTg00DMk208Tg00NJk21=Tg00O2k31<Tg00Aok10NTg00Bok21;Tg00CMk11TTg00Ckk21STg00Dgk219Tg00ESk418Tg00FEk11PTg00Tlk209Tg00K<j2XTg00OVj4YTg05CWk20=Tg0JPEk11OTg05HNk11KTg0>1@k20zTg05DLk200Tg00<Dk215Tg014ck11ITg00cMj3@Tg05>Fk20yTg01:dk20xTg05[bj1tTg05WSk11HTg0JQ7k21vTg05GEk214TP1j29Tg00WOj2ETg00>YS00j2sTg00XAj58Tg00ZMk30vTg00\<j3QTg00]ak313Tg00^bk21ETg0JR>k41DTg00aVk41tTg0JSAk11rTg00eej2zTg00kRm=0BTg00V8j2NTP2j6<Tg01JUm:0sTg01NhmB0rTg05`Fm<12Tg05N0m<0lTg00U^j2:Tg08RQj6FTg01EOk61lTP3j6?Tg0JTGm?1kTg08PTm>0TTg01;_m>11Tg08QMk50qTg05XPlArTg05Dnk10gTg0=_Dm>1jTg00f?k20iTg00gom>1ATg05U[mA1@Tg0JU<m>1?Tg00mCk40@Tg0JV5k10oTg01<`k21dTg01A]k40}Tg00dek41bTg05cnk31`Tg01B[k40PTg01CFk70QTg01Cjm<1^Tg01B8k31aTg01FWk80|Tg01HNmB1]Tg01DOk31hTg01Dnk41\Tg01G;k30ETg01I4m<1iTg00hhk41ZTg05dQk40cTg0JW6k31mTg01IYk30mTg01LIk11YTg01MIk81oTg01Mfk71XTg08^bk71GTg08_Fm91sTg01Qbk71VTf0R3#Z#Zp>1w%Z3#Z#Z#Zp>1g%Z3#Z#Z#Z#Z#Z#Z#Zp>1R%Z3#Z#Z#Z#Z#Z#Z#Z#Z#Z#Z#Z#Z#Z#Z#Zp>0Lg01R^R2f3R1f2R7'Xf1R8/X332p=Ig01S<R9/03p=\20823p=>A2283p=B21523p=[B1`283p>0]%;3#=p>1>%=3#=#=#fp=P%=3#=#=#=#=#=#=#=p>0f%=3#=#=#=p>0>P7g01SZS01g01T9S02Q02g01TYS03P2P8g01U9R:P3H0Pg01U`R;K0Qp=S1R83,07p=dg01V@R<P2P2P2P6P6f5R6f4R=P1P7P8P3N<1^p>0n%=3#;#=#;#;#;#=#;#=#=#;#;p>0:%;3#=#=#fp=W%=3#fp>0w%=3#;#=#;p=k%=3#;#=#;#;#;#=#;#;#=#;#;p>02%=3#;#;#;p>01%;3#;p>0S%;3#=#=#=p=x%;3#=#;#=p>0R%;3#;#;#=p>0u%=3#=#;#;p>0t%;3#;#;#;p=p%=3#=#;#=p=w%;3#;#=#;#;#=#;#;p>1B%;3#=#=#=#;#;#=#;p={%;3#=#=#;p>07%;3#;#;#;#;#;#;#;p>0\%;3#;#=#;p>0k%;3#=#;#;p>0_%=3#=#=#;p=i%;3#;#=#=p>0I%=3#;#;#=p>0<g01XFR>:0D83p=CB1a283p=`P2P8g01V_R?P3H0Pp>0^P=Q01Q02Q02Q03P1P7P8Q01Q02Q02Q03P3P;K0QL0|p>0U1578/03p=c%f3>0D8>p>0b10=11578/03':p=lP2P2P2P2P2P2P5P3P8P7P5P1P=P6f6R5f7R@f8RAf9S04NB1]p=g%=3#=p>0j%=3#=#f>0D8>p>0G%=3#;#=#;#;#;#=#;p>0?g01WFRBg01WfRC723p>0ZB1h293p>0{P7P8Q03P3H1\p>06%=3#;#=#=p>0MP6Q01Q02Q02Q03P=P1P7Q01Q02Q02Q03P2P8P:P3H0PP;K0QL0|p>0520i83=2BCp>0320x39p>0Y1D39p>0W%=3#;p>1M%;3#;#=#;#=#=#;#;p>1L%=3#;#=#;#;#;#=#;#=#;#=#=p=v%;3#;#=#;#=#;#=#=p>1J&0N3:0E78p>16P7Q01Q02Q02Q03P2P8P?P3H0PP;K0Qp=nP2P5P6P=P1A@783E<p>0FP2P2P4P@P4P5P6P=P1P7P8P3N<1ip=3P2P@P5P6P=P1P7H1ZP8P3E<p=41D839Q17p=jg01ZFR4P7P8P3H0cp=LP4P61517,V=P8H0c=253p>0C10171083':p=]B0E6=1P7P8P3H0@p=U&0N3:0E78:0E=1p=_&0N3:0E78:0E=1:0E56p=qB0E783:0E=1p=1P<P=P1P7P8P3E<p=7P5P6P=B1m178P3D8p=}1E56=2@=1E78=213'sp=|B0m4561E17=2=8/s3'sp>041E17=2=8/s3p>1qB0m478/s3p>1CB0m483p>1p&1Y3-08Bp=mB0D178=2=3p=OP6P=P1P7P8D8>0m43p=H1583,V7p>0JP7Q01Q02Q02Q03P2P8g01XbP3H0PP;K0Qp>0;1R78/53p>0aP2P5P6P=P1P7P8P3L1op>0AP@AQ56=P1P7P8D8>0m43p=eP2P=P1P7P8P3E<p=A1583,07p>0`P4P6P=P1P7P8P3K1Xp>0[1X839227p=aP4P=1D17P8H0c=263p=hP4P1P7P8H0c=2=3p=u1083,:7p=6P@Q01Q02Q02Q03P5P6P=Q01Q02Q02Q03P1Q01Q02Q02Q03P2P7P:P8H0PP;K0QP3K1GL0|p=J1R78,01/:3p=KP4P@P5P6P=P1P7P8P3N91sp=GP@P5P6P=P4P1P7P8H0cP3E<p=oP2P8P:P3H0Pp>0XP1Q01Q02Q02Q03P7Q01Q02Q02Q03P8P;K0QP3K1Gp>0VP@P4P5P6P=H0cP1P7P8P3E<p=y1078/:3p=Tg01YfS0592B3p>0p1X78=223p>1fP4P6P=P1P7P8P3K1Vp=Mg024A#ZS06#Z$1wR;$1gR:$1R$0L$0L$0L$0L$0L$0L$0L$0LP<g025ER?%~3RD%~8REP7P8P7P3CIRF%~1?278RG[]B]A]9RHp-0RIg024`RJ#=RK#fRL,^9PI%\LPI%;KRM$0KRN#~P01083RO$1uXD2X@220dOO^D2^@2P2P2g025c1583H1nRO#>XC2X921BOO^C2^92&0h3RO#>X@<1BOO^@<&0h:P2&0h;P2%=KRK#fRP#[&1_2RQ%=KS07#=RR#=S08#=RS$0KRT#~P0Q07$0KS09#~P0PFPIQ00P8\G%~=?217\3%~6?2=1\8B1[178P3n2001000000120000000aXBEXADX9?PH21W2JRHQ08#fR?#[+0]PQ%fRRD#[PQ&1URS0:#[PQ&1>KS0;#PRK#[PQ%fSRR#\PI21:LRP2&1Q2RE%=SS0<#=$0f$0f$0fRS$0>$0f#PRG#[7SHPEQ01Q02Q02Q03I1NRF%[LS0=>172TPQQ07#fRU#[PQ%;JRV#=RW#=RX#=RY#fRZ#[-0]HPQ%fSRS?d3K1R8?#\[^12PIfHS0>$0hP2AdS3K1R8K#\[^12PIAdS3K1R8Z#\[^12PIP3X@2R[P[fDS0?P:PU%>UJ0nP[fCS0@O1P[PUO1'B&0:J$0>#WS0A#>Q0AQ0A'B%=MR\#=R]$0wR^#[-0]HPQAdS3K1R8^#\[^12PI%=J#k$0wS0B%fXS0C+0eP2&02J$01#PS0D#>Q0DQ0D'B%;J$0S#x$0R$0u$0t#fR_#>1B__Q06$0hS0E,5_P2%fJR`,5_P2%[_PQ%pJ#w$0>#k#PRa#>1BaafNS0F,5aP215aUP2%[aPQ%pJ#w$0>$0t#PRb#>1BbbfRS0G,5bP215bUP2%[bPQQ0C-0eZP2%xJ$1B#k#PRc#>1BccfWS0H,5cP215cUP2%[cPQ%{J$0R$07#WRd#>1BddfZS0I,5dP215dPP2P[P[f^S0JP;PP%>PJ0nP[f\S0KO1P[PPO1'B%[dPQ21:L?P2%;VS0L$0SS0M#;$0SRV#;$0SS0N#;#p$0\$0\S0O#fS0P#[PQ%{J$07$0k#PRe#>1BeefbS0Q,5eP215eUP2%[ePQ%{J$07#p#PRf#>1BffffS0R,5fP215fUP2%[fPQ%{J$07$07#PRg#>1BggfjS0S,5gP215gUP2%[gPQ%{J$07$0R#PRh#>1BhhfnS0T,5hP215hUP2%[hPQ%{J$07$01#PRi#>1BiifrS0U,5iP215iUP2%[iPQ%{J#x$0_#WRj#>1BjjfuS0V,5jP215jPP2%[jPQ%{J$01#p#PRk#>1BkkfzS0W,5kP215kUP2%[kPQ%{J#x#i#PRl#>1Bllf~S0X,5lP215lUP2%[lPQ%{J$01$0_#PRm#>1Bmmp+01CS0Y,5mP215mUP2%[mPQ%{J$01$0I#PRn#>1Bnnp+01GS0Z,5nP215nUP2%[nPQ%kJ#w$0<$01#WS0[#>Q0[Q0['B&0KXRX#~P0%;\S0\$0KS0]#~P0%;WS0^$0KS0_#~P0&0K]S0`#~P0p+01KS0a$10P0p+01LS0b$0~P01CNLR]B0DN9>RW60ONPBp+01OS0c$10P0&1eTp+01QS0d^;2p+01RS0e\2P0p+01NRo-0]HPQp+01MS0f-0]HPQQ0b,^9PIQ0f#\PIp+01]S0gp+01VRp+1cP0p+01TRqQ0b'`PQPEQ0cQ02$1FRrPEp+01US0h00^oI0UPF103G1R8?p+01SRo'^[^12PIQ0f=c3oX;2PI^;2Rs%>o1Boo103G1R8K?cKp[^12PI103G1R8Kp+01WRt'^[^12PIPEQ0hPrPEQ0e00^qI0UPF103G1R8Zp+01YRu'^[^12PIQ0h,`qPQ1CN`Rv>0ONWPB&0wYRY#[-0]HRH/`tPQPEp+01ZRwPrPE20^HuI0UPF103G1R8Yp+01^S0i'^[^12PIPEp+01\S0jPrPEQ0ep+01[S0k+0^I0UPF103G1R8^p+01`S0l'^[^12PIQ0j,`qPQ20bN\R\>0ONWPB1CNURx>0ONWPB%;MS0m-0bNRM>0ONWPBPqP3P3p+01oS0nP_DlX;2PsP[P[P[p+021S0oP_P_Q0hQ0EP`P[P[p+020S0pQ06P`%>`J0nM:gP[PqO1/Bo%[`,`oPQQ0hp+01fS0q'0PIp+023S0rp+01hS0s5c3X;2Ps103G1R8Zp+01jS0t7cU[^12PI103G1R8?p+01kS0u7cU[^12PI103G1R8^p+01lS0v7cU[^12PI103G1R8Yp+01mS0w7cU[^12PIQ0w9c3UX;2PsPwP3P3p+029S0xPaDlX;2PsP[P[P[p+02;S0yPaPaQ0kQ0xPUp+01eS0zM:gP[PwO1/BuQ0v,`uPQQ0kQ0p'0PIPwP3P3p+02=S0{PbDlX;2PsP[P[P[p+02?S0|PbPbQ0kQ0{PUp+01iS0}M:gP[PwO1/BuQ0p,`uPQQ0kp+024S0~'0PIPuP3P3p+02AS10PcDlX;2PsP[P[P[p+02CS11PcPcPwQ10PUQ0wM:gP[PuO1p+01XR`'BQ0~,``PQp+028S12,0wPIPuP3P3p+02ES13PdDlX;2PsP[P[P[p+02GS14PdPdPwp+02DS15PPPtM:gP[PuO1/B`Q15,`tPQQ14Q0{5c3X;2PsQ0kQ0{'0PIPtP3P3p+02JS16PeDlX;2PsP[P[P[p+02LS17PePeP`Q16PUp+026S18M:gP[PtO1/BpQ0{,`pPQQ10,0`PIPtP3P3p+02NS19PfDlX;2PsP[P[P[p+02PS1:PfPfP`Q19PUp+02:S1;M:gP[PtO1/BpQ10,`pPQQ13,0`PIPtP3P3p+02RS1<PgDlX;2PsP[P[P[p+02TS1=PgPgP`Q1<PUp+02>S1>M:gP[PtO1/BpQ13,`pPQp+02IS1?,0`PIPtP3P3p+02VS1@PhDlX;2PsP[P[P[p+02XS1APhPhP`Q1@PUp+02BS1BM:gP[PtO1/BpQ1?,`pPQp+02MS1C,0`PIPtP3P3p+02ZS1DPiDlX;2PsP[P[P[p+02\S1EPiPiP`Q1DPUp+02FS1FM:gP[PtO1/BpQ1C,`pPQp+02QS1G,0`PIPtP3P3p+02^S1HPjDlX;2PsP[P[P[p+02`S1IPjPjP`p+02]S1JPPQ0pM:gP[PtO1/BpQ1J,`pPQp+02US1K,0`PIPtP3P3p+02bS1LPkDlX;2PsP[P[P[p+02dS1MPkPkP`Q1LPUQ19M:gP[PtO1/BpQ1K,`pPQp+02YS1N,0`PIPtP3P3p+02fS1OPlDlX;2PsP[P[P[p+02hS1PPlPlP`Q1OPUQ1<M:gP[PtO1/BpQ1N,`pPQQ1J,0`PIPtP3P3p+02jS1QPmDlX;2PsP[P[P[p+02lS1RPmPmP`Q1QPUQ1@M:gP[PtO1/BpQ1J,`pPQp+02aS1S,0`PIPtP3P3p+02nS1TPnDlX;2PsP[P[P[p+030S1UPnPnP`Q1TPUQ1DM:gP[PtO1/BpQ1S,`pPQp+02eS1V,0`PIQ1TPo[P0Q0e$10P01VT9R0-0H:Po%{J$07#x#PS1W,VTRy-0H:Pq%{J$01$0R#PS1X,VTRz-0H:Q0hQ0P,VTS1Y-0H;PpQ0[,VTS1Z-0H:PtQ0A,VTS1[-0H:P`&0jV-0GXS1\,bXP2%=J$0_$0R$0?-0GTS1]/DPp+037S1^p+038S1_$1FPu208`uA2`uu%[S=SEtPF21=LRp+03DS1`p+035S1aPu[[p+03ES1bp+036S1cPw[[PIQ1bg0285S1dB1<LR8UW?Q1bQ1dPw[]?p+03FS1eQ1dQ0k[]?PI&0?J#w#p#PS1f,CTS1g/DPp+03?S1h1CXUS1i,bXP2g027IRR$0NRV&0~RRR21;28R{&1T2R|Q0jQ03-1SER}P3P7208BCS1j21937$0Zd&0{8H18RCb8b6b7X1221;23$0{$1PR~>06Ew^12p+01_S1kp+03<S1l'`PQPEp+03:S1mPrPEQ0lp+039S1n+0^I0UPFPVPRP{P|PuP}PCb8b6b7X12B06E~t^12&0?J#w#p#WS1o,CTS1p/DPQ1bB0DX9>S1q,bXP2&0:J$0>#PS1r,CTS1s/DPp+03GS1tQ1sQ0]Q0]Q08#;$0S+0GS1u'b+09p+03HS1vQ1[,XTP2&02J$0t#WS1w,CTS1x/DPp+03JS1yp+03RS1zp+03KS1{PvQ1[CYQ0z&02J$0M#PS1|,CTS1}/DPp+03LS1~PVPRP{P|Q0gP}PCb8b6b7X12Q0k:06E~^12PVPRP{P|Q0jP}PCb8b6b7X12B06E~w^12&02J$0M#WS20,CTS21/DPp+03OS22Q0`Q0`Q0B'CS0B'bQ0C+0eP2&02J#k#PS23,CTS24/DPp+03QS25Q24p+03=S26+0=Q1z&0jJ#p#PRQ,CXS27,bXP2&02J#k#WS28,CTS29/DPp+03TS2:p+03\S2;p+03US2<P\%pJ#i$0_#k#PS2=,VTS2>CYQ0nQ2>/DQp+03VS2?&02J$0<#PS2@,CTS2A/DPp+03WS2Bp+03_S2Cp+03XS2DPx%pJ#w$0>$0M#PS2E,VTS2FCYp+022S2G&02J$0<#WS2H,CTS2I/DPp+03YS2JQ2IQ0]Q0]Q0m#;RQ#=#i#k+0GS0m'b+09p+03ZS2KQ0D,VTS2L,XTP2&01J$0M$0I#i#PS2M,CTS2N/DPQ2;Q2N%pJ$0wS2OQ0C+0e+0=p+03]S2PQ09/V9S09$1Op+03^S2Q&01J$0M$0I#i#WS2R,CTS2S/DPQ2Cp+03gS2Tp+03`S2UPM%pJ$0>$0I#i#PS2V,VTS2WCYQ1;p+03hS2Xp+03aS2YPvQ2LCYQ0yp+03iS2Zp+03bS2[P\Q2FCYp+02<S2\Q2W&0jJ$1B#fS2]'Dp+03cS2^1VT_S2_,XTP2PEQ2;PrPEp+025S2`p+03[S2aJ05PFPEQ2PPrPEQ0|Q2;J05PFPEQ2QPrPEQ0pQ2PJ05PFPEQ2CPrPEQ18Q2QJ05PF1XT0P2&01J$0M$0I#w#PS2b,CTS2cQ0_Q0_Q0M$0j+0GS0M'b+09p+03jS2dp+042S2ep+03kS2fQ0^-0bNS0^P0CYQ1320300PIQ0D,CTS2g,XTP2Q2g$0Yp+03nS2hQ2g/DPp+03oS2iQ2F/DUp+040S2j1VTaS2k,XTP2&02J$01#WS2l,CTS2m/DPQ2ep+04:S2np+043S2oP\Q2kCYQ1C&02J#x#PS2p,CTS2q/DPp+044S2r1CXDS2s,bXP2&02J#x#WS2t,CTS2u/DPp+046S2vQ0A,CTS2w,XTP2Q2w$0Yp+048S2xQ2w/DPp+049S2yQ2k$0WQ2n&0:J#i#PS2z,CTS2{/DPp+04;S2|p+04CS2}p+04<S2~PxP0CYQ1@&0:J#i#WS30,CTS31/DPp+04=S32Q31Q2Z+0=p+04>S33&0:J#w#PS34,CTS35/DPp+04?S36p+04GS37p+04@S38P\%pJ#i$0t#i#WS39,VTS3:CYQ1DQ3:%;J$1M#i#WS3;'Dp+04AS3<1VTbS3=,XTP2&0:J#w#WS3>,CTS3?Q0_Q0_Q0\+0GS0\'b+09Q2}Q0`Q0`/CZS3@'bQ0C+0eP2&0:J$0k#PS3A,CTS3B/DPp+04ES3CQ3BQ2^+0=p+04FS3D&0:J$0k#WS3E,CTS3F/DPQ37p+04OS3Gp+04HS3HP\%xJ$1L$0k#PS3I,VTS3JCYQ1LQ3J&0SJ#x#PS3K'Dp+04IS3L1VTcS3M,XTP2&0:J$0u#PS3N,CTS3O/DPp+04KS3Pp+04SS3Qp+04LS3RPxPyCYQ1OQ1Y$1Kp+04MS3S&0:J$0u#WS3T,CTS3U/DPp+04NS3VQ07#;S07#WS3W,CXS3X,bXP2Q3W,Dyp+04PS3Y1VTdS3Z,XTP2Q1Y,XTP2Q0_Q0_Q0C'CS3['bP2p+04[S3\p+04TS3]P\Q0O$0\$0\$0\$0\#fS0O,VTS3^CYQ1TQ3^00z0$0ZPI%vJ$0>#WS3_,CTS3`/DPp+04VS3a1CX^S3b,bXP21Dy^p+04XS3c1VTeS3d,XTP2%vJ#i#PS3e,CTS3f/DPp+04ZS3g1VTfS3h,XTP2Q0_Q0_/CZS3i'bP2%vJ$0M#WS3j,CTS3k/DPp+04]S3l1DyUp+04^S3m1VTgS3n,XTP2%vJ#k#PS3o,CTS3p/DPp+04`S3q1DyDp+04aS3r1VThS3s,XTP2%vJ#x#WS3t,CTS3u/DPp+04cS3vQ3uQ3<+0=p+04dS3w%vJ$07#PS3x,CTS3y/DPp+04eS3zp+04mS3{p+04fS3|P\%xJ$1J#x#WS3},VTS3~CYp+03@S40Q3~&0jJ$0u#WS41'Dp+04gS421VTiS43,XTP2%vJ$07#WS44,CTS45/DPp+04iS46p+051S47p+04jS48PxPzCYQ1`%vJ$0R#PS49,CTS4:/DPp+04kS4;Q3W,Dzp+04lS4<1VTjS4=,XTP2%vJ$0I#PS4>,CTS4?/DPp+04nS4@1Dz^p+04oS4A1VTkS4B,XTP2%vJ$0I#WS4C,CTS4D/DPQ471VTlS4E,XTP2&0?J#k$0>#PS4F,CTS4G/DPp+053S4H1DzUp+054S4I1VTmS4J,XTP2&0?J#k$0>#WS4K,CTS4L/DPp+056S4M1DzDp+057S4N1VTnS4O,XTP2&0?J#k#i#PS4P,CTS4QQ0_Q0_Q0<+0bS0<'b+09p+059S4R&0?J$0<#i#PS4S,CTS4T/DPp+05:S4U&0?J$0<#i#WS4V,CTS4W/DPp+05;S4Xp+05CS4Yp+05<S4ZPvQ1ZCYQ2?&0?J$0<#w#PS4[,CTS4\/DPp+05=S4]Q0[,CTS4^,XTP2Q4^$0Yp+05?S4_Q4^/DPp+05@S4`%kJ#w$0<#x#PS4a,CTS4b/DPp+05AS4cQ4bQ0]Q0]Q0N#w$0<+0GS0N'b+09p+05BS0]%kJ#i#p$0_#PS4d,CTS4e/DPQ4Yp+05KS4fp+05DS4gPv%kJ#w$0<#x#WS4h,VTS4iCYQ2Q%kJ#i#p$0_#WS4j,CTS4k/DPp+05ES4l&1>QS4m#fS4n,D0p+05FS4oQ2dQ4oQ09Q4o416+00p+02HS4pQ2fQ4p+00Q1?p+03lS4qQ4p+00Q16p+03mS4rQ4p+00p+02KS4sQ2hQ4p+00Q17Q4rQ15+08Q4rQ15Q1532PEQ11PrPE21529RQp+05JS4tJ05PFPEQ4lPrPEQ2\Q4gJ05PFPEQ13PrPEPQQ4qJ05PFPVPRP{P|p+02@S4uP}PCb8b6b7X12Q1>:06E~^12PEQ14PrPEPQQ4lJ05PFPEQ4pPrPEPQPHJ05PFPEQ1?PrPEPQQ4`J05PFQ0lQ0E'5P2PVPR&1I2RFP|Q4]9SEQP}PCb8b6b7%\_P3b0Q16Q1?Q1?Q4pPVPRPFP|Q4_p+05OS4v5nEP}PCb8b6b7Q4v,^_P3b0b3b45@_p+01aS4w/B_p+05US4xQ1<+0yP<PVPRP{P|Q0zP}PCb8b6b7X12p+01cS4y:06E~^12PVPRP{P|Q0zP}PCb8b6b7X12Q4y:06E~^12p+05XS0zQ1=+0yP<PVPRP{P|Q0qP}PCb8b6b7X12p+01dS4z:06E~^12PVPRP{P|Q0qP}PCb8b6b7X12Q4z:06E~^12Q1jQ0ldQ0lQ2gQ14+0xp+05]S0qQ3<Q1N+00p+02_S4{Q2wQ1?+0xp+05_S4|Q1kp+05cS4}'5P2PVPRPFP|Q4l9SEQP}PCb8b6b7%\aP3b0Q1@Q1KQ1KQ1=PVPRPFP|p+05GS4~p+05[S505nEP}PCb8b6b7Q50,^aP3b0b3b45@aQ0l/Ba%t0Q1L$1HQ0}'BQ0dp+05fS51'5P2PVPRPFP|Q4g9SEQP}PCb8b6b7%\bP3b0Q1NQ1AQ1Ap+02WS52PVPRPFP|Q4op+05^S535nEP}PCb8b6b7Q53,^bP3b0b3b45@bQ0e/BbQ0ap+05hS54'5P2PVPRPFP|Q4c9SEQP}PCb8b6b7%\cP3b0p+02[S55Q1DQ1DQ1NPVPRPFP|Q4Yp+05`S565nEP}PCb8b6b7Q56,^cP3b0b3b45@cQ0b/Bcp+01Fp+05iS57'5P2PVPRPFP|p+05>S589SEQP}PCb8b6b7%\dP3b0Q1JQ1EQ1EQ55PVPRPFP|Q4`p+05bS595nEP}PCb8b6b7Q59,^dP3b0b3b45@dQ0Z/BdQ1YQ0PQ4],^3X;221=L?p+062S5:%\?Q58,^9[[Q5:Q1dB1<L?8UW?Q5:Q1dQ4_#\[]?PVPRPFP|Q4_Q0=Q08$0K61725nEP}PCb8b6b7Q0PQ58'^P3b0b3b4Q0ZQ0PPVPRPFP|Q4]9SEQP}PCb8b6b7Q0P#\P3b0Q1HQ1JQ1JQ1EPVPRPFP|Q4_Q4}5nEP}PCb8b6b7Q0PQ4}'^P3b0b3b4K0F+1vQ1O$1HQ0Z'Bp+05jS0PQ3^Q0f32PI&0:J#p#PS0f,CTS0=p+01HS08+09p+05kS1dQ1jQ0ZdQ0Zp+01DS0Zp+060S5;'5P2PVPRPFP|Q589SEQP}PCb8b6b7%\eP3b0p+02cS5<Q1LQ1LQ1SPVPRPFP|Q4`Q545nEP}PCb8b6b7Q54,^eP3b0b3b45@ep+01ES5=/BeQ0ZQ5:'5P2PVPRPFP|Q4Z9SEQP}PCb8b6b7%\fP3b0Q1VQ1MQ1MQ5<PVPRPFP|Q58Q0P5nEP}PCb8b6b7Q0P,^fP3b0b3b45@fQ5=/Bf%vJ#i#WS5>,CTS5?Q5=+09p+061S5@Q0Yp+065S5A'5P2PVPRPFP|Q4X9SEQP}PCb8b6b7%\gP3b0Q1Pp+02gS5BQ5BQ1OPVPRPFP|Q4]p+05mS5C5nEP}PCb8b6b7Q5C,^gP3b0b3b45@gQ0Z/Bgp+01BS5Dp+067S5E'5P2PVPRPFP|Q4R9SEQP}PCb8b6b7%\hP3b0Q1Qp+02iS5FQ5FQ1PPVPRPFP|Q4Xp+05oS5G5nEP}PCb8b6b7Q5G,^hP3b0b3b45@hQ0Y/Bh%vJ#k#WS5H,CTS5Ip+01JS5J+09p+066S5KQ0Xp+06:S5L'5P2PVPRPFP|p+058S5M9SEQP}PCb8b6b7%\iP3b0p+02mS5NQ1RQ1Rp+02kS5OPVPRPFP|Q4UQ5:5nEP}PCb8b6b7Q5:,^iP3b0b3b45@ip+01@S5P/Bif{S5Qp+06;S5R'5P2PVPRPFP|Q4M9SEQP}PCb8b6b7%\jP3b0p+02oS5SQ1TQ1TQ5NPVPRPFP|Q5Mp+064S5T5nEP}PCb8b6b7Q5T,^jP3b0b3b45@jf|S5U/Bj%vJ$0R#WS5V,CTS5W009`Q5RQ5Qp+06?S5X'5P2PVPRPFP|p+055S5Y9SEQP}PCb8b6b7%\kP3b0p+032S5Zp+031S5[Q5[Q1UPVPRPFP|Q4NQ5E5nEP}PCb8b6b7Q5E,^kP3b0b3b45@kQ5U/BkQ5Qp+06AS5\'5P2PVPRPFP|Q4H9SEQP}PCb8b6b7%\lP3b0p+034S5]p+033S5^Q5^Q5ZPVPRPFP|Q5Yp+069S5_5nEP}PCb8b6b7Q5_,^lP3b0b3b45@lQ5U/Bl%vJ$0k#PS5`,CTS5a009qp+06@S5bQ5Qp+06DS5c'5P2PVPRPFP|p+052S5d9SEQP}PCb8b6b7%\mP3b0Q1^Q1cQ1cQ1aPVPRPFP|Q4Ip+06<S5e5nEP}PCb8b6b7Q5e,^mP3b0b3b45@mQ5U/BmQ0Wp+06FS5f'5P2PVPRPFP|p+050S5g9SEQP}PCb8b6b7%\nP3b0Q1nQ1_Q1_Q1^PVPRPFP|Q5dp+06>S5h5nEP}PCb8b6b7Q5h,^nP3b0b3b45@nQ5Q/Bnp+04hS5ip+03AS5j+00Q1eQ4^Q1U+0xQ5fPVPRP{P|flS5kP}PCb8b6b7X12RLQ0S:06E~^12RPPLPPPLPPPVPRP{P|fkS5lP}PCb8b6b7X12RPfiS5m:06E~^12R~PPP~PPP~p+03NS5nQ22fvS5o723W=Q5nPI]=Q1Z-14:fgS5p=2<:Q0Sp+06GS5q'0PIQ1[-14:Q0R=2<:Q1zp+03SS5rfyS5s723W=Q1zPI]=faS5tp+06JS5u'0PIf_S5vp+06KS5w'0PIQ2<Q2?Q5Q723W=Q2<PI]=Q5vp+06MS5x'0PIQ2BQ2DQ5Q723W=Q2BPI]=Q5vp+06OS5y'0PIp+06VS5zp+06bS5{P3PTQ3^Q2\Q0O#>PTQ3^PTQ2\CIdO4b2f]S0Of[S5|p+06QS5}'0PIQ0Ip+06RS5~'0PIfXS60p+06SS61'0PIQ0Hp+06TS62'0PIQ2QQ2CQ0Z723W=Q2QPI]=fVS63Q5z'0PIfUS64p+06WS65'0PIfSS66p+06X'0PIQ0Gp+06YS67'0PIfPS68p+06ZS69'0PIfOS6:p+06[S6;'0PIp+03eS6<p+03fS6=Q6:723W=Q6<PI]=P_Q0E,53S0Ep+06^R~'0X;2Q5xp+06]RP'0Q42P[p+06kS6>Q5xp+06LS6?Q46PPPPQ4UG3Q2KQ2JQ2JQ2DPVPRPFP|Q4<p+06_RP5SEP}PCb8b6b7Q46P3b0b3b4Q5[Q5PG4fES6@eQ6@PaQ42Q5u/0~Q3mP[p+06lS6AQ5up+06IS6BQ3qP~P~Q4XG3Q2aQ2KQ2KQ2JPVPRPFP|Q3vp+06`S6C5SEP}PCb8b6b7Q3qP3b0b3b4Q1VftS6DG4Q0@eQ0@PbQ5iQ5q/0PQ3\P[p+06mS6EQ5qQ5fQ3lPPPPQ4ZG3Q2;Q2aQ2aQ2KPVPRPFP|Q3qp+06aS6F5SEP}PCb8b6b7Q3lP3b0b3b4Q1KQ0UG4Q0@eQ0@PcQ46p+06CS6GQ6C'0Q3cP[p+06nS6HQ6Gp+06BS6IQ3gQ6CQ6CQ4]G3Q2PQ2;Q2;Q2aPVPRPFP|Q3lQ5{5SEP}PCb8b6b7Q3gP3b0b3b4Q19fqS6JG4fBRPePPPdp+04US6KQ5bQ6F'0Q3]P[p+06oS6LQ5bQ5Xp+04WS6MQ6FQ6FQ58G3Q2QQ2PQ2PQ2;PVPRPFP|Q3gp+06cS6N5SEP}PCb8b6b7Q3aP3b0b3b4Q4pfpS6OG4fAS6PeQ6PPeQ4;Q5LQ5{'0p+04QS6QP[p+070S6RQ5LQ5_Q3QQ5{Q5{Q4_G3Q2CQ2QQ2QQ2PPVPRPFP|Q3ap+06dS6S5SEP}PCb8b6b7Q3QP3b0b3b4Q10Q5lG4f@R~eP~PfQ4<Q5EQ6N'0Q3VP[p+071S6TQ5EQ5KQ3YQ6NQ6NQ4`G3Q2UQ2CQ2CQ2QPVPRPFP|Q3Qp+06eS6U5SEP}PCb8b6b7Q3YP3b0b3b4Q4uQ0SG4P~eP~PgQ3{Q5TQ6S'0Q3PP[p+072S6VQ5Tp+063S6WQ3SQ6SQ6SQ4cG3Q2YQ2UQ2UQ2CPVPRPFP|Q3Yp+06fS6X5SEP}PCb8b6b7Q3SP3b0b3b4Q0{fhS6YG4P~eP~PhQ4@Q5@Q6U'0Q3HP[p+073S6ZQ5@Q5;p+04JS6[Q6UQ6UQ0]G3Q2[Q2YQ2YQ2UPVPRPFP|Q3Sp+06gS6\5SEP}PCb8b6b7Q6[P3b0b3b4Q0yQ5pG4P~eP~PiQ4Ap+05nS6]Q6X'0Q3CP[p+074S6^Q6]Q5CQ37Q6XQ6XQ4YG3Q2^Q2[Q2[Q2YPVPRPFP|Q6[p+06hS6_5SEP}PCb8b6b7Q37P3b0b3b4Q18feS6`G4f?RLePLPjQ3\Q1dQ6\'0p+04BS6aP[p+075S6bQ1dQ0Pp+04DS6cQ6\Q6\Q4gG3p+03dS6dQ2^Q2^Q2[PVPRPFP|Q37p+06iS6e5SEP}PCb8b6b7Q6cP3b0b3b4Q2GfdS6fG4PLePLPkQ47Q54Q6_'0Q36P[p+076S6gQ54p+05gS6hQ3<Q6_Q6_Q4lG3Q6<Q6dQ6dQ2^PVPRPFP|Q6cp+06jS6i5SEP}PCb8b6b7Q3<P3b0b3b4Q0pQ0QG4PLePLPlQ5dp+05eS6jQ6e'0Q2~P[p+077S6kQ6jp+05dS6lQ33Q6eQ6eQ4oG3Q6=Q6<Q6<Q6dPVPRPFP|Q3<Q6>5SEP}PCb8b6b7Q33P3b0b3b4Q0nQ5tG4PLePLPmQ4HQ59Q6i'0Q2yP[p+078S6mQ59p+05aS6nQ2|Q6iQ6iQ4~G3Q2TQ6=Q6=Q6<PVPRPFP|Q33Q6A5SEP}PCb8b6b7Q2|P3b0b3b4Q0wQ5vG4PLePLPnQ4IQ4|Q6>'0Q2vP[p+079S6oQ4|Q53Q2xQ6>Q6>p+05HS6pG3Q2XQ2TQ2TQ6=PVPRPFP|Q2|Q6E5SEP}PCb8b6b7Q2xP3b0b3b4Q0uQ0JG4PLePLQ6^,9N1E3]Q6b1E8xQ6g1E7vQ6kP1P]P7Q2eCjQ6m,9NQ2|Q2_Q065L3Q2|Q2k=L8:Q2~Q3==L7:Q32Q3M=L1:Q33Q43=L=:Q36Q38Q0s72=PIQ3<Q0s72=PIQ6aQ0}72=PIQ2}Q0}72=PIQ6cQ0}72=PIQ3Cf:S6qPTQ1WQ3WP;Q0}K0CPIQ3Df;S6rPTQ1XQ3WP;Q0tK0CPI1s17S3WPI1s63PI1s@3PIQ3Pp,2fxRFQ6@Q1]P~P3D8g028QS6sp+07KS6t1XT3P21R3DP21R8KP21R7ZP21R1?P21R=^P21R6YP21VT6p+07SS6u1VT6p+07TS6v1VT6p+07US6w1VT6p+07VS6x1VT6p+07WS6y1VT6p+07XS6z15AUP2Q6rp+07LS6{'5P2f<S6|/5KP2Q6|p+07_S6}'5P2f=S6~/5UP2f>S70#>Q70Q70'BQ70p+07bS71'5P2%>L1BLLQ70/5UP2p+07eS72,5~P2Q6P/5UP2%>P1BPPp+07hS73,5PP2Q0@#>Q0@Q0@'Bp+07OS74fGS75'0PIQ74Q0>'0PIp+07QS76Q0>'0PIQ76fIS77'0PIQ6uQ77'0PIQ6ufJS78'0PIQ6wQ78'0PIQ6wfKS79'0PIQ6uQ6:'0PIQ6uQ68'0PIQ6wQ68'0PIQ6wfQS7:'0PIQ6yQ7:'0PIQ6yQ0G'0PIp+07YS7;Q0G'0PIQ7;Q66'0PIQ6yQ0H'0PIQ6yQ60'0PIQ7;Q60'0PIQ7;fYS7<'0PIp+07[S7=Q7<'0PIQ7=Q0I'0PIp+07]S7>Q0I'0PIQ7>Q5|'0PIp+07ZS7?Q5v'0PIQ7?f`S7@'0PIp+07\S7AQ7@'0PIQ7AQ5t'0PIp+07^S7BQ5t'0PIQ7BQ0Q'0PIp+07`S7CQ0Q'0PIQ7CfcS7D'0PIQ7BQ5p'0PIQ7BQ6Y'0PIQ7CQ6Y'0PIQ7CQ5m'0PIQ71Q5m'0PIQ71Q0S'0PIp+07dS7EQ0S'0PIQ7EQ5l'0PIQ6}foS7F'0PIQ6}Q6O'0PIp+07aS7GQ6O'0PIQ7GQ6J'0PIp+07cS7HQ6J'0PIQ7HQ0U'0PIQ72Q0U'0PIQ72fsS7I'0PIQ7HfwS7J'0PIQ7HfxS7K'0PIQ72Q7K'0PIQ72Q5s'0PIp+07gS7LQ5s'0PIQ7LQ0W'0PIp+07iS7MQ0W'0PIQ7MQ5Q'0PIQ7LQ5P'0PIQ7Lp+01AS7N'0PIQ7MQ7N'0PIQ7MQ5D'0PIp+07kS7OQ5D'0PIQ7OQ0Y'0PIp+07mS5DQ0Y'0PIQ5DQ0Z'0PIQ7OQ08'0PIQ7Op+01IS08'0PIQ5DQ08'0PIQ5DQ5J'0PIp+07oS08Q5J'0PIQ08Q0a'0PIp+081S5JQ0a'0PIQ5JQ0b'0PIQ08p+01P'0PIQ08Q0d'0PIQ5JQ0d'0PIQ5JQ0e'0PIp+083S0dQ0e'0PIQ0d/0oPIp+085S0e/0oPIQ0e/0qPIQ0d/0`PIQ0d/0uPIQ0e/0uPIQ0e/0wPIp+087S0b/0wPIQ0bQ0k'0PIp+089S0aQ0k'0PIQ0aQ0j'0PIQ0bQ0l'0PIQ0bQ4w'0PIQ0aQ4w'0PIQ0ap+01bRu'0PIp+08;S4w/0uPIQ4wQ4y'0PIp+08=S0jQ4y'0PIQ0jQ4z'0PIQ4wQ0s'0PIQ4wQ0}'0PIQ0jQ0}'0PIQ0jQ0t'0PIp+08?S0}Q0t'0PIQ0}Q0u'0PIp+08AS0tQ0u'0PIQ0tQ0v'0PIQ0}Q0p'0PIQ0}Q0o'0PIQ0tQ0o'0PIQ0tQ2G'0PIp+08CRuQ2G'0PIQ0r,0uPIp+08ES0uQ0r'0PIQ0uQ0~'0PIQ12,0uPIQ0x,0uPIQ0uQ0x'0PIQ0uQ1;'0PIp+08GS0sQ1;'0PIQ0sQ0y'0PIp+08IS4zQ0y'0PIQ4zQ2\'0PIQ1@Q1;Q6;40vp+09_S4yp+08DS7P[Q1EQ1;7Q]p+09`S7Q,9NQ1>Q0:'Dp+09aS7Rp+09iS7Sp+09bS7TP]Q2\CYp+08<S7UQ0{,XTP2Q1>/DUp+09dS7VQ0yp+09]S7W'0PIQ0yp+09^S7X'0PIP[P[P[p+09lS7YQ1?Q1?Q1?#>p+09YS7ZPKP[P[p+09kS7[p+0:2S7\PK%>KJ0nM:gP[Q0{O1RuQ2\'BQ15,XTP2Q15,XTP2P[P[P[p+09oS7]Q4sQ4sQ2\p+09mS7^PUQ7ZM:gP[Q1>O1Q0{'BQ13$0WQ7[P[P[P[p+0:1S7_Q17Q17Q2\Q7]PUp+09[S7`M:gQ11,BuQ14Q0:'DQ7^p+0:5S7ap+09nS7bP]Q1FCYp+08HS7cQ14,XTP2Q4p/DUp+0:0S7dQ16,XTP2P[P[P[p+0:7S7eQ1GQ1GQ1>Q7aPUQ7RM:gP[Q4uO1Q0|'BQ4s$0Wp+0:3S7fP[P[P[p+0:9S7gQ1<Q1<Q1>Q7ePUp+09cS7hM:gP[Q0|O1Q11'BQ1?/0_PIQ1?/0_PIQ4sQ7]'0PIQ4sQ7d'0PIQ16/0_PIQ1G/0_PIQ17Q7f'0PIp+02SS7ip+0:4S7j'0PIQ4s/0_PIQ4s/0_PIQ1CQ7e'0PIQ1Cp+0:8S7k'0PIQ17/0_PIQ1G/0_PIQ19p+0:;S7l'0PIQ7ip+0:<S7m'0PIQ7iQ5<'0PIQ1GQ1V'0PIQ1=Q1V'0PIQ52Q5B'0PIQ1S/DDp+0:IS7nQ1H/0aPIQ1H/0aPIQ1J/0aPIQ1M/0aPIQ1E/0aPIQ1E/0aPIQ55/0aPIQ1I/0aPIQ1O/0bPIQ1O/0bPIQ1V/0bPIQ1R/0bPIQ1M/0bPIQ1M/0bPIQ5</0bPIQ1P/0bPIQ1T/0cPIQ1T/0cPIQ5N/0cPIQ5]/0cPIQ1R/0cPIQ1R/0cPIQ5O/0cPIQ1U/0cPIQ1c/0dPIQ1c/0dPIQ1a/0dPIQ1l/0dPIQ5]/0dPIQ5]/0dPIQ5^/0dPIQ1_/0dPIp+03>S7o/0ePIQ7o/0ePIQ26/0ePIQ1`/0ePIQ1l/0ePIQ1l/0ePIp+03;S7p/0ePIQ40/0ePIQ1e/0fPIQ1e/0fPIQ1b/0fPIQ1~/0fPIQ1`/0fPIQ1`/0fPIp+03CS7q/0fPIQ1v/0fPIQ5n/0gPIQ5n/0gPIp+03MS7r/0gPIQ2:/0gPIQ1~/0gPIQ1~/0gPIQ1{/0gPIp+03PS7s/0gPIQ2?/0hPIQ2?/0hPIQ2</0hPIQ2;/0hPIQ2:/0hPIQ2:/0hPIQ5r/0hPIQ2D/0hPIQ2Q/0iPIQ2Q/0iPIQ2P/0iPIQ6d/0iPIQ2;/0iPIQ2;/0iPIQ2a/0iPIQ2U/0iPIQ6=/0jPIQ6=/0jPIQ6</0jPIQ4q/0jPIQ6d/0jPIQ6d/0jPIQ2^/0jPIQ2X/0jPIQ2h/0kPIQ2h/0kPIQ4r/0kPIQ2r/0kPIQ4q/0kPIQ4q/0kPIQ2f/0kPIQ2j/0kPIQ2v/0lPIQ2v/0lPIp+045S2f/0lPIQ2~/0lPIQ2r/0lPIQ2r/0lPIQ2o/0lPIQ2x/0lPIQ33/0mPIQ33/0mPIQ32/0mPIQ6c/0mPIQ2~/0mPIQ2~/0mPIQ2|/0mPIQ38/0mPIQ3D/0nPIQ3D/0nPIQ3C/0nPIQ3R/0nPIQ6c/0nPIQ6c/0nPIQ2}/0nPIQ3H/0nPIQ3GP3P3p+0<>S38p+04\S2;DlX;2PsQ3GQ3\'0PIQ3SQ3l'0PIQ3YQ3l'0PIQ6Kp+04_S7t'0PIQ3QQ3m'0PIQ3VQ3r'0PIQ3]Q3q'0PIQ3GQ3v'0PIQ6MQ3r'0PIQ3GQ3z'0PIQ3cQ3v'0PIQ6KQ42'0PIp+04YS7uP3P3p+0<KS7vQ5iDlX;2PsQ7uQ42'0PIQ6MQ46'0PIQ3rQ46'0PIQ3cQ4;'0PIQ3lQ48'0PIQ3cQ3{'0PIQ3zQ4<'0PIQ3mQ4A'0PIQ48/DDp+0<PS3cp+0<XS7wp+0<QS7xP]Q4@CYp+0:kS7yQ1LQ1[7Qvp+0<RS7z,9Np+0<SS7{Q3{Q1L32PIQ1M/E]p+0<TS7|Q1V/Evp+0<US7}P[p+0<\S7~Q4<Q4;Q4{p+0<NS80Q80Q7yG3Q1SQ1I+0dQ4{p+0<IS81'5P2Q4{p+0<[S82'5P2Q5F/Exp+0<YS83p+09VS84p+05QS85Q5Y413Q85Q5O+1EQ1Pp+0<^S86'5P2Q1Rp+09ES877QvQ7~,9Np+0<]S88Q5YQ1I32PIQ1Jp+0<aS89'5P2Q1Ip+0<bS8:'5P2Q5[Q2_Q063LQ7Rp+07=S8;Q1P'0PIP[p+0<hS8<Q4MQ5YQ1Pp+0<ZS8=Q8=p+0;7S8>G3Q55Q1D+0dp+07?S8?Q1U'0RuPIP[p+0<jS8@Q5YQ4XQ1PQ7~Q7~p+0;9S8AG3Q1NQ1A+0dp+07AS8BQ1M'0PIP[p+0<lS8CQ4IQ4HQ1MQ86Q86p+0;;S8DG3Q52Q1@+0dp+07CRoQ1P'0PIP[p+0<nS8EQ4HQ4NQ1Mp+0<`S8FQ8Fp+0;=S8GG3Q1KQ1=+0dp+0<iS8HQ0]Q5F32PIQ8@Q4gQ1G32PIQ1lQ2k;L:Q7Yp+07<S8IQ5^'0PIQ8;Q1m'0PIp+07>S8JQ5N'0PIPuPIQ5jQ3=;L:Q7_Q8JQ1_'0PIQ8?Q1h'0PIp+07@S8KQ5Z'0PIQ8BQ1a'0PIQ1eQ3M;L:p+0:6S8LQ8BQ26'0PIp+07BS8MQ1`'0PIQ1^,0oPIp+07DS8NQ1m'0PIQ1{Q3Z;L;Q7lQ8Np+03BS8O'0PIp+07ES8Pp+03IS8Q'0PIp+07FRuQ1l'0PIp+07GS8RQ1h'0PIQ7sQ3d;L:p+0:@S8SQ1t,0oPIQ8NQ5n'0PIQ8PQ5j'0PIQ1`,0uPIQ2<Q3h;L:p+0:ES8PQ1~,0uPIQ8RQ5r'0PIp+07HRuQ1e'0PIp+07IRoQ8Q'0PIQ2KQ3n;L:p+0:JS8RQ25,0uPIQ2D,0oPIp+07JS8TQ1{'0PIQ6tQ5n'0PIQ2CQ3s;L:p+0:OS8UQ6tQ2?'0PIQ6{Q2P'0PIp+07MS6tQ7s'0PIp+07NRuQ5r'0PIQ6dQ43;L:p+0:TS7sQ6tQ2a'0PIQ2[,0uPIQ74Q2<'0PIp+07PRuQ2D'0PIQ2ZQ4=;L;p+0:YS74Q2U,0uPIQ76Q2T'0PIp+07RS6tQ2K'0PIQ6uQ2P'0PIQ2hQ4B;L:p+0:^S8VQ6tQ6<'0PIQ6uQ4q'0PIQ6vQ2C'0PIQ6wQ2['0PIQ2oQ4E;L:p+0:cS2CQ6wQ2d'0PIQ6xp+041S2d'0PIQ6yQ6d'0PIQ6zQ2T'0PIQ2xQ4J;L:p+0:hS8WQ6yQ2i'0PIQ6zQ2v'0PIQ7;Q2Z'0PIQ7?Q4q'0PIQ32Q4O;L:p+0:mS4qQ7?Q2r'0PIQ7=Q2|'0PIQ7AQ2h'0PIQ7>Q2d'0PIp+0>1S2hQ6?Q3232PIQ2ep+0=kS2Z7cOX9<PI^9<RuQ2fp+0=lS2i7cOX9<Pup+0>4S8XQ5};2qPIQ2vQ61'BPIQ2fp+06US8Y'BPIQ6cQ65'BPIQ36Q67'BPIQ3<Q6;'BPIQ5~9Q`]p+0>:S8Z,9Np+0>;S8[Q8Y72tPIp+0><S8\Q6b72tPIp+0>5S8],0pPIp+0>>S8^Q0hQ6m32PIQ0g/E]p+0>?S0hp+0>8S8_,0`PIp+0>9S8`,0pPIQ8Z,0qPIQ8[,0qPIQ3C,0pPIQ0gp+04RS8a'0PIQ0iQ3C'0PIp+0>KS0i,53Q37PwP3C]X;2PsQ0lQ3L'0PIp+0>MS0g,53Q3PQ0kP3C]X;2PsQ1kQ3L'0PIQ0lQ3R'0PIQ6PQ2>7Q\p+0>LS0l,9Np+0<gS1kQ3\Q1k$0NPoP]Q05-08BRoEUQ6PeQ6PQ0vP]Q70p+0;HS05Cjp+0>NS0k,9Np+0>OS8bQ6e72LPIQ6@/E]p+0>PfFRs/Evp+0>QS8cQ75/Exp+0>RS8dQ0>Q24p+0;3S8e+0=7Q\p+0>SS8f,9NQ2F9Q@xp+0>TS8g,9Np+0>US8hQ6E72=PIp+0>VS8iQ1[72=PIp+0>WS8jQ7672=PIQ6r/E\p+0>XS76Q2F9Q=\p+0>Y,9Np+0=4S8kQ2;Q8kp+0;?S8lQ8kQ5iQ8kD_Q6xP]PoEUP=eP=Q70PxP7p+0;8S8mCjp+0>[S8n,9Np+0>\S8oQ2>721PI1EAxp+0>]Q2L9Q=vp+0>^S8p,9NQ6qP\P8p+0;IS8qCjp+0>_Rw,9Np+0>`S8rQ2F727PIQ8m9Q@vp+0>aS8s,9NQ2W9Q1Mp+0>bS8t,9NQ2NQ0`Q0`Q2O'CS2O'bQ0C+0e+0=9Q=Mp+0>cS0C,9NQ0^=Q80p+0>dS0`,9NQ0^Q8>5Q7p+0>eS8u,9N1E1Mp+0>fS8vQ2k9Q7\p+0>gS8w,9Np+0>hQ2W728PIQ0^,E=p+0>iS8x1E6vp+0>jRp1E5xp+0>kS8yQ1[9Q=vp+0>l,9Np+0>mS8z?210PIp+0>nS8{Q2L721PIQ6qP\P1p+0;_S8|Cjp+0>oS8},9Np+0?0S8~Q2F72=PIQ04/E]p+0?1S90p+0?2S91Q8T723PI1E5]p+0?3S8Tp+0?4S92Q6{723PIp+0?5S6{20H:3S93p+0=YS94p+0?>S95p+0?7S96PxP8CYp+0=QS97p+0??S98p+0?8RqP\P7CYp+0=RS9920yq7P<p+0=]S9:0001p+0<;S9;p+05LS9<Q6w<0v=p+0?;S9=p+0=`S9>[214:5A2<7:Q38p+0<?S9??231W=Q38PI]=Q6yp+0<9S9@60v7Q95p+0=cS9A[p+05PS9BQ7;613AQ9B01E1Q2_Q065L=p+0<AS9CQ2k=L6:p+0<BS9DQ3==L5:p+0<CS9EQ3M=L@:p+0<DS9FQ3Z=LA;p+0<ES9GQ04Q3d;L:p+0<FS9HQ6qQ3h;L:p+0<GS9IQ6rQ3n;L:p+0<HS9JQ6|Q3s;L:Q81Q6~Q43;L:p+0<JS9KQ70Q4=;L;Q7vQ4B=LL:p+0<LS9LQ4E=L~:p+0<MS9MQ6PQ4J;L:Q80Q4O=LP:p+0<OS9NQ0@p+07jS9O;L:Q3cQ6PQ73Q7740vp+0?PRqQ8][Q2_Q065LPQ7zQ0@Q2k;L:Q7{Q0?Q3=;L:Q7|Q6@Q3M;L:Q7}Q3Z=Ls;p+0<VS9PQ75Q3d;L:p+0<WS9QQ0>Q3h;L:Q7wQ77Q3n;L:Q83Q78Q3s;L:Q8=Q79Q43;L:Q82fLS9RQ4=;L;Q7~fMS9SQ4B;L:Q88Q0FQ4E;L:Q86Q6:Q4J;L:p+0<_S9TQ68Q4O;L:Q8FQ7:Q4w;L:Q89Q0GQ4w;L:Q8:Q6`Q0K7Qxp+0?bS9U,9NQ0j9Q3]p+0?cS9V,9N1E8]p+0?dS9WAQ8x0p+0?eS9X,9NP1P]P8p+0;aS9YCjp+0?fS9Z,9Np+0?gS9[Q0}727PI1E=vp+0?hS9\1E6\p+0?iS9]Q3:9Q=\p+0?jS9^,9Np+0?kS9_Q1[727PIp+0?lS9`Q2k727PI1E@xp+0?mS9aQ31Q80+0=9QA\p+0?nS9b,9NAQ=x0p+0?oS9c,9Np+0@0R`?270PI1E5\p+0@1S9dQ3J9Q7\p+0@2S9e,9Np+0@3S9fQ3:728PI1E=xp+0@4S9gQ3BQ9Y+0=9Q6\p+0@5S9h,9NAQ1xyp+0@6S9i,9Np+0@7S9j?270PI1E6\p+0@8S9kQ3^9Q7\p+0@9S9l,9Np+0@:S9mQ3J728PI1E=xp+0@;S9nQ8|9Q6\p+0@<S9o,9Np+0@=S9p?28yPI1E=\p+0@>S9q1E6xp+0@?S9rp+0>ZS9sp+0;dS9tQ9sp+0;hS9uQ9sp+0<4S9vQ9sp+0<0S9wQ9sQ9vQ9sp+06NS9xQ9sQ7KQ9sp+0<eS9yQ9sp+0<=S9zQ9sQ9GQ9sQ3cQ9sQ9NQ9sQ80Q9sQ7wQ9sQ82Q9sQ6IQ9sQ9yQ9sQ9xQ9sFqD1D1D1D1D1D1D1p+09<S9{PxPoEUP7eP7p+0@AS9|Q3^727PIp+0@BS9}?27yPIp+0@CS9~Q93Q8wp+0@LS:0p+0@ES:1P\P8CYPwp+0@MRwp+0@FS:2PMP7CYQ8r200p7p+0=HS:3p+0=IS:4p+09?S:5PTQ1WP^P:P3K0CPIp+0=JS:6p+09@S:7PTQ1WQ0L#PS0LP:P8K0CPIp+0=KS:8p+0=LS:9?231W=Q:8PI]=Q:9p+0=MS::?23=W=Q:9PI]=AQP\AQ:0,9NQ049Q3M19Nw1E8xp+0@NRpp+0@ORt?23yPI1E7\p+0@PS:;1E1Mp+0@QS:<1E=xp+0@RS:=p+0@SS:>?27LPIp+0@TS:??27~PIp+0@US:@?27yPIp+0@VS:Ap+09NS:BQ1WQ0@P3H1DPI20H:8S:CQ9=p+0@`S:Dp+0@YS:EP\P7CYQ8Tp+0@aS:Fp+0@ZS:GPMP1CYQ92Q950007p+0=\S:HQ9:p+09SS:IPTQ1WPUP:P3K0CPIp+0=^S:Jp+09TS:KPTQ1WPDP:P8K0CPIp+0=_S1WQ9>?231W=Q1WPI]=Q9>p+0=aS:L?23=W=Q9>PI]=Q3WPIQ75/s3PIQ77/s3PIQ6@Q6|7Q\p+0@cS3W,9NQ6~9Q3Mp+0@dS:M,9N1E8xp+0@eS:NQ3~9Q8\p+0@fS:O,9Np+0@gS:P?28yPI1E1\p+0@hS:Q1E=Mp+0@iS:RQ3uQ9P+0=9Q6\p+0@jRu,9NAQ=xzp+0@kS:S,9Np+0@lS:TQ6@721PIp+0@mS:U?21sPI1E@\p+0@nS:VQ3^9Q1\p+0@oS:W,9Np+0A0S:XQ3~728PI1E6xp+0A1S:YQ7}9Q5\p+0A2S:Z,9Np+0A3S:[?28zPI1E=\p+0A4S:\1E6xp+0A5S:]Pqp+0<<S:^Pqp+0<@S:_PqQ79PqQ9RPqQ5vPqQ7@PqQ7zPqQ8=PqQ86PqQ8@Pqp+0<fS:`PqQ8@PqQ8NPqQ0nPqp+0=[S:aPqp+0=3S:bPqp+0=;S:cPqp+0=FS:dPqp+0=ES:ePqp+0=DS:fPqp+0=NS:gPqQ97PqQ6mPqQ:aPqQ8NPqD_D1D1D1D1D1D1D1D1D1D1D1Q7\PxPoEUP7eP7p+0A7S8NQ3^727PIp+0A8S:h?27zPIp+0A9S:iQ93p+0?]S93p+0ABS:jp+0A;S:kP\P8CYp+0?US:lp+0ACS:mp+0A<S:nPMP7CYp+0?VS:op+0?`S:p0007Q8^Q0hQ7aPTQ1XP^P:P3K0CPIp+0>@S:qQ8LPTQ1XQ0LP:P8K0CPIp+0>AS:rp+0>BS:s?231W=Q:rPI]=Q:sp+0>CS:t?23=W=Q:sPI]=AQP\AQ:j,9NQ049Q3MQ:m,9N1E8xp+0ADS:up+0AES:v?23zPI1E7\p+0AFS:w1E1Mp+0AGS:x1E=xp+0AHS:yp+0AIS:z?27LPIp+0AJS:{?27~PIp+0AKS:|?27zPIp+0ALS:}p+0:DS:~Q1XQ0@P3H1DPIQ:CQ9dp+0AVS:Cp+0AOS;0P\P7CYQ9]p+0AWS;1p+0APS;2PMP1CYQ9^Q9g0007Q8dQ8fQ7nPTQ1XPUP:P3K0CPIQ8gQ8RPTQ1XPDP:P8K0CPIQ8hQ8i?231W=Q8hPI]=Q8iQ8j?23=W=Q8iPI]=P`p+0A]S1XQ:CQ07-0bNS07Q4n,VTS8dCYP`Q1XQ:CPMQ1GCYP`Q9DP`Q19P`Q5YP`p+02OS;3P`Q9KP`P6P`P5P`Q77P`Q78P`p+0=2S;4P`Q7~P`Q8FP`Q5lP`Q5kP`Q5PP`Q7NP`Q;4P`p+0=:S;5P`p+0=>S;6P`Q:6P`Q:dP`Q:6P`Q7EP`Q;3P`Q8[P`p+0=SS;7P`Q:aP`p+0=fS;8P`p+0=eS;9P`p+0=dS;:P`p+0=nS;;P`Q2hP`Q6zP`Q8[P`Q7EP`FqD1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1&0~`1s=1PIQ0>/s3PIQ78/s3PIQ6~9Qs\p+0AZS;<,9NQ709Q3Mp+0A[S;=,9N1E8xp+0A\S;>Q1Z9Q8vQ1X,9Np+0A^S;??28zPI1E1\p+0A_S;@1E=Mp+0A`S;A1E6]p+0AaS;BQ1J9Q=xp+0AbS;C,9Np+0AcS;D?21sPIp+0AdS;EQ75721PIp+0AeS;Fp+0:?S;G721PI1EA]p+0AfS;HQ:~9Q=]p+0AgS;I,9Np+0AhS;Jp+0:BS;K728PI1E5]p+0AiS;LQ1V9Q7\p+0AjS;M,9NPAP]P8Q;8Cjp+0AkS;N,9Np+0AlS;Op+0:FS;P727PI1E6vp+0AmS;Q1E5xp+0AnS;RQ4i9Q=vp+0AoS;S,9Np+0B0S;TQ1Z727PIQ04P\P7Q8nCjp+0B1S8n,9Np+0B2S;UQ5N721PIQ8:9QAvp+0B3S;V,9NQ5S9Q=Mp+0B4S;W,9N1E6\p+0B5S;XQ07Q8d5Q8p+0B6S;Y,9NP@PMP8Q8sCjp+0B7S;Z,9Np+0B8S;[Q5^727PIP=Q071E=WQ4n,CXS;\,bXCjp+0B9S;],9NPFP1%kJ#i#p$0I#PS;^,CTS;_Q1Dp+0:aS;`D8Q6s1E=\p+0B;S6sQ07,E6p+0B<S;a1E5]p+0B=S;bp+0B>S;cQ1n727PIp+0B?S;dQ8d727PIp+0B@S;ep+0:]S;f727PI1s83PIp+0BBS;gQ8Gp+0:_S;h32p+0BCS;iQ8GQ7o32p+0BDS;jQ8GQ1Z32p+0:gS;k,0Sp+0:jS;l/0Gp+0?<S;mQ9=Q9=p+0?:S;nQ9Tp+0@GS;oP3p+0:nS;pP1O2b0b3b4Q0bp+0?=S;qQ;mQ;mQ9=Q9TQ;oP3p+0:oS;rP=O2b0b3b4p+084S;sQ95Q;qQ;qQ;mp+0<dS;tp+0@KR=P3p+0;0S;uP6O2b0b3b4Q0tQ98Q95Q95Q;qQ;tP=P3p+0;1S0tP5O2b0b3b4p+08>S;vQ7yQ9vQ;cP3Q;uP5O2b0p+0?@S;wQ98Q98Q95Q;mQ:MP3p+0;2S;xP@O2b0b3b43@Q6cQ;pp+0<3S;yQ;bP3Q0tP@O2b0p+0?AR@Q;wQ;wQ98Q8EQ:FP3Q8ePAO2b0b3b43@Q2}Q;pQ;yQ;bP3Q;xPAO2b0p+0?BS;zP@P@Q;wQ9=Q:DP3p+0;4S;{Q04O2b0b3b43@Q3CQ;up+0<5S;|Q;dP3Q8eQ04O2b0p+0?CS04Q;zQ;zP@p+0=0S;}Q3WP3p+0;5S;~Q6qO2b0b3b43@Q3CQ4qQ9vAdS3K1R8Y#\[^12S<0P3Q;{Q6qO2b0p+0?DS6qQ04Q04Q;zQ92p+0@]S<1P3p+0;6S<2Q6rO2b0b3b43@Q6[Q;xp+0<7S<3p+0BAS<4P3Q;~Q6rO2b0p+0?ES6rQ6qQ6qQ04Q;4Q:NP3Q8>Q6|O2b0b3b43@Q37Q;uQ;|Q;bP3Q<2Q6|O2b0p+0?FS6|Q6rQ6rQ6qQ6{Q<1P3Q8mQ6~O2b0b3b43@Q3PQ;{Q9@Q;iP3Q8>Q6~O2b0p+0?GS6~Q6|Q6|Q6rQ8kQ:PP3Q8AQ70O2b0b3b43@Q3LQ;{Q9@Q;iP3Q8mQ70O2b0p+0?HS70Q6~Q6~Q6|P@Q:OP3p+0;:S<5PLO2b0b3b43@Q3PQ;{Q9zp+0BGS<6P3Q8APLO2b0p+0?IS<7Q70Q70Q6~Q6rQ:UP3Q8DP~O2b0b3b43@Q3SQ;{Q9@Q<4P3Q<5P~O2b0p+0?JS<8Q<7Q<7Q70p+0?9S<9Q:FP3p+0;<S<:Q6PO2b0b3b43@Q3GQ;{Q9;Q<0P3Q8DQ6PO2b0p+0?KS6PQ<8Q<8Q<7Q9=Q:MP3Q8GPPO2b0b3b43@Q6QQ<2Q9;Q;iP3Q<:PPO2b0p+0?LS<;Q6PQ6PQ<8Q9=Q3WP3p+0;>S<<Q0@O2b0b3b43@Q6QQ<2Q9zQ<0P3Q8GQ0@O2b0p+0?MRPQ<;Q<;Q6PQ;qQ:OP3Q8lQ0?O2b0b3b43@Q3QQ<5Q9?p+0BIS0@P3Q<<Q0?O2b0p+0?NS0?PPPPQ<;Q6~Q:TP3p+0;@S<=Q6@O2b0b3b43@Q6QQ<5Q9Ep+0BMS<>P3Q8lQ6@O2b0p+0?OS6@Q0?Q0?PPQ6PQ:[P3p+0;AS<?PsO2b0b3b43@Q3QQ<5Q9?Q<6P3Q<=PsO2b0PqQ6@Q6@Q0?Q98Q:PP3p+0;BS<@Q75O2b0b3b43@Q6KQ<5Q9CQ<0P3Q<?Q75O2b0p+0?QS75PqPqQ6@P@PuP3p+0;CS<AQ0>O2b0b3b43@Q6MQ<<Q9EQ<>P3Q<@Q0>O2b0p+0?RS0>Q75Q75PqQ6PQ:XP3p+0;DS<BQ77O2b0b3b43@Q6KQ<<Q9Ip+0BQS6KP3Q<AQ77O2b0p+0?SS77Q0>Q0>Q75Q6@Q8NP3p+0;ES<CQ78O2b0b3b43@Q6MQ<<Q9Ep+0BKS6MP3Q<BQ78O2b0p+0?TS78Q77Q77Q0>Q04Q:SP3p+0;FS<DQ79O2b0b3b43@Q7uQ<<Q9GQ<0P3Q<CQ79O2b0Q:lQ78Q78Q77Q6rQ:VP3p+0;GS79Q9RO2b0b3b43@Q3\Q<@Q9IQ6KP3Q<DQ9RO2b0Q:oQ:lQ:lQ78Q6@Q:\P3Q05Q9SO2b0b3b43@Q7uQ<@Q7vp+0BUS9RP3Q79Q9SO2b0p+0?WS9SQ:oQ:oQ:lQ77Q:kP3Q8qQ0FO2b0b3b43@Q3\Q<@Q9Ip+0BOS<EP3Q05Q0FO2b0p+0?XS0FQ9SQ9SQ:oQ6~Q:WP3p+0;JS<FQ6:O2b0b3b43@Q3lQ<@Q81Q<0P3Q8qQ6:O2b0p+0?YS6:Q0FQ0FQ9SQ<7Q:ZP3p+0;KS<GQ68O2b0b3b43@Q7tQ<DQ7vQ9RP3Q<FQ68O2b0p+0?ZS68Q6:Q6:Q0FQ77Q:hP3p+0;LS<HQ7:O2b0b3b43@Q3lQ<DQ9Np+0BYRsP3Q<GQ7:O2b0p+0?[S7:Q68Q68Q6:Q9Sp+0A?S<IP3p+0;MS<JQ0GO2b0b3b43@Q7tQ<DQ7vp+0BSS<KP3Q<HQ0GO2b0p+0?\S0GQ7:Q7:Q68Q6PQ:[P3p+0;NS<LQ66O2b0b3b43@Q3rQ<DQ9MQ<0P3Q<JQ66O2b0Q93Q0GQ0GQ7:PPp+0A6S66P3p+0;OS<MfTRPO2b0b3b43@Q3vQ<FQ9NPsP3Q<LPPO2b0p+0?^S<NQ93Q93Q0GQ9SQ:nP3p+0;PS<OQ64O2b0b3b43@Q3rQ<FQ7{p+0B]S<PP3Q<MQ64O2b0p+0?_S64Q<NQ<NQ93Q7:Q:mP3p+0;QS<QQ63O2b0b3b43@Q3vQ<FQ9Np+0BWS<RP3Q<OQ63O2b0Q:pQ64Q64Q<NQ6@Q8NP3p+0;RS63Q0HO2b0b3b43@Q3zQ<FQ7xQ<0P3Q<QQ0HO2b0p+0?aS0HQ:pQ:pQ64Q75p+0A:S<SP3p+0;SS<TQ60O2b0b3b43@Q42Q<LQ7{Q<PP3Q63Q60O2b0Q9UQ0HQ0HQ:pQ7:p+0A@S60P3p+0;TS<UQ7<O2b0b3b43@Q3zQ<LQ9Qp+0BaS<VP3Q<TQ7<O2b0Q9VQ9UQ9UQ0HQ64Q:xP3p+0;US7<Q0IO2b0b3b43@Q42Q<LQ7{p+0B[S<WP3Q<UQ0IO2b0Q9WQ9VQ9VQ9UQ77Q:kP3p+0;VS0IQ5|O2b0b3b43@Q46Q<LQ7}Q<0P3Q7<Q5|O2b0Q9XQ9WQ9WQ9VQ:lp+0A>S5|P3p+0;WS<XQ0KO2b0b3b43@Q4;Q63Q9QQ<VP3Q0IQ0KO2b0Q9ZQ9XQ9XQ9WQ64Q:uP3p+0;XS0KQ0OO2b0b3b43@Q46Q63Q82p+0BeS<YP3Q<XQ0OO2b0Q9[Q9ZQ9ZQ9XQ9VQ:|P3p+0;YS0OQ0JO2b0b3b43@Q4;Q63Q9Qp+0B_S<ZP3Q0KQ0JO2b0Q9\Q9[Q9[Q9ZQ9SQ<IP3p+0;ZS0JQ5vO2b0b3b43@Q3{Q63Q83Q<0P3Q0OQ5vO2b0Q9]Q9\Q9\Q9[Q6:Q:jP3p+0;[S5vQ7@O2b0b3b43@Q4AQ0IQ82Q<YP3Q0JQ7@O2b0Q9^Q9]Q9]Q9\Q9VQ:yP3p+0;\S7@Q5tO2b0b3b43@Q3{Q0IQ9Tp+0BiS<[P3Q5vQ5tO2b0Q9_Q9^Q9^Q9]Q9[Q;0P3p+0;]S5tQ0QO2b0b3b43@Q4AQ0IQ82p+0BcS<\P3Q7@Q0QO2b0Q9`Q9_Q9_Q9^Q7:Q:mP3p+0;^S0QQ7DO2b0b3b43@Q47Q0IQ88Q<0P3Q5tQ7DO2b0Q9aQ9`Q9`Q9_Q93Q:wP3Q8|Q6fO2b0b3b43@Q4HQ0JQ9TQ<[P3Q0QQ6fO2b0Q9bQ9aQ9aQ9`Q9[Q:}P3p+0;`S6fQ6`O2b0b3b43@Q47Q0Jp+0<cS7Dp+0BmS<]P3Q8|Q6`O2b0Q9cQ9bQ9bQ9aQ9_p+0ASS<^P3Q9YQ0RO2b0b3b43@Q4HQ0JQ9Tp+0BgS<_P3Q6fQ0RO2b0P`Q9cQ9cQ9bQ64Q:xP3p+0;bS9bQ5pO2b0b3b43@Q5YQ0JQ89Q<0P3Q9YQ5pO2b0Q9dP`P`Q9cQ0HQ:{P3p+0;cS5pQ6YO2b0b3b43@Q4NQ0QQ7DQ<]P3Q9bQ6YO2b0Q9eQ9dQ9dP`Q9_Q;2P3Q9tQ5mO2b0b3b43@Q5YQ0QQ1kp+0C1S6YP3Q5pQ5mO2b0Q9fQ9eQ9eQ9dQ9cQ;1P3p+0;eS5mQ0SO2b0b3b43@Q4NQ0QQ7Dp+0BkS<`P3Q9tQ0SO2b0Q9gQ9fQ9fQ9eQ9VQ:|P3p+0;fS0SQ5lO2b0b3b43@Q4RQ0QQ9yQ<0P3Q5mQ5lO2b0Q9hQ9gQ9gQ9fQ9Xp+0ANS5lP3p+0;gS<aQ5kO2b0b3b43@Q4XQ9bQ1kQ6YP3Q0SQ5kO2b0Q9iQ9hQ9hQ9gQ9cp+0ATS<bP3Q9ufmS<cO2b0b3b43@Q4RQ9bp+0<kS<dp+0C5S<eP3Q<aQ<cO2b0Q9jQ9iQ9iQ9hQ9fQ;=P3p+0;iS<fQ0TO2b0b3b43@Q4XQ9bQ1kp+0BoS<gP3Q9uQ0TO2b0Q9kQ9jQ9jQ9iQ9[Q;0P3p+0;jS0TQ7FO2b0b3b43@Q4]Q9bQ8HQ<0P3Q<fQ7FO2b0Q9lQ9kQ9kQ9jQ9]p+0ARS7FP3p+0;kS<hQ6OO2b0b3b43@Q4_Q0SQ<dQ<eP3Q0TQ6OO2b0Q9mQ9lQ9lQ9kQ9fp+0AXS6OP3p+0;lS<iQ6JO2b0b3b43@Q4]Q0Sp+0<oS<jp+0C9S<kP3Q<hQ6JO2b0Q9nQ9mQ9mQ9lQ9jQ;@P3p+0;mS6JQ0UO2b0b3b43@Q4_Q0SQ<dp+0C3S<lP3Q<iQ0UO2b0Q9oQ9nQ9nQ9mQ9_Q<^P3p+0;nS9mQ7IO2b0b3b43@Q4cQ0Sp+0<mS0UQ<0P3Q6JQ7IO2b0Q9pQ9oQ9oQ9nQ9aQ:CP3p+0;oS7IQ6DO2b0b3b43@Q4YQ0TQ<jQ<kP3Q9mQ6DO2b0Q9qQ9pQ9pQ9oQ9jQ;>P3Q9wQ0VO2b0b3b43@Q4cQ0TQ:bp+0C=S9oP3Q7IQ0VO2b0Q9rQ9qQ9qQ9pQ9nQ;DP3p+0<1S6DQ5oO2b0b3b43@Q4YQ0TQ<jp+0C7S<mP3Q9wQ5oO2b0p+0@@RPQ9rQ9rQ9qQ9cQ;1P3p+0<2S9qQ7JO2b0b3b43@Q4lQ0Tp+0=1S5oQ<0P3Q6DQ7JO2b0Q9|PPPPQ9rQ9dQ;<P3Q;yQ7KO2b0b3b43@Q4~Q9mQ:bQ9oP3Q9qQ7KO2b0Q9}Q9|Q9|PPQ9nQ;AP3Q9vQ5sO2b0b3b43@Q4lQ9mp+0=7S7Kp+0CAS<nP3Q;yQ5sO2b0Q9~Q9}Q9}Q9|Q9rQ;IP3Q;|Q0WO2b0b3b43@Q4~Q9mQ:bp+0C;S<oP3Q9vQ0WO2b0p+0@DRPQ9~Q9~Q9}Q9fQ;=P3p+0<6S9}Q5QO2b0b3b43@p+05IS<pQ9mp+0=5S<qQ<0P3Q;|Q5QO2b0Q:1PPPPQ9~Q9hQ;?P3Q<3Q5UO2b0b3b43@Q4fQ9qQ7KQ<nP3Q9}Q5UO2b0Q:2Q:1Q:1PPQ9rQ;EP3p+0<8S5Uf}RPO2b0b3b43@Q<pQ9qQ:cp+0CES<rP3Q<3PPO2b0Q;oQ:2Q:2Q:1Q9~Q;NP3Q9@Q0XO2b0b3b43@Q4fQ9qQ7Kp+0C?S:1P3Q5UQ0XO2b0p+0@HS<sQ;oQ;oQ:2Q9jQ;@P3p+0<:S:2Q5PO2b0b3b43@p+05MS<tQ9qp+0=9S<uQ<0P3Q9@Q5PO2b0p+0@IS<vQ<sQ<sQ;oQ9lQ;CP3Q9;Q7NO2b0b3b43@Q4vQ9}Q:CQ:Bp+09MS7NQ6NQ5Qp+09\S9lP1G4Q4leQ4lQ9}Q;1p+09KS<wp+09JS<xQ5{Q5QQ7hP1G4Q4leQ4lP:Q4xQ9}Q6Op+09HS<yp+09GS<zQ6FQ:0P=P=p+0@JRPp+0=oS<{Q;1P3Q38Q0ZO2b0b3b4Q84P1G4Q4leQ;;Q7KD7Q4xQ;;O1P:Q4xQ9}p+0AYS0ZQ87p+09DS<|Q6CPwQ:0Q:0P=Q<{Q;1P3Q9?Q5=O2b0b3b4Q7ZP1G4Q4leQ3GQ3RD7Q4xQ3GO1P4Q3cQ;|p+0CdH1t$0ZQ7x$1rQ00Q9LQ9EQ1aQ4up+0C^S5=,9NRsQ9GPFP3Q;_Q9PQ9FQ3gQ9HF}p+0C_S6CP3P\Q3gQ6CP3Q07Q8dQ6CP3P]Q:^G|K04X>s'z[[P3Q80Q9HQ00Q9NQ9JQ1nQ15p+0Cb,9NRsQ81PFP3Q;_Q8=Q9JQ3mQ9KF}p+0CcS<}P3P\Q3mQ<}P3Q07Q8dQ<}P3P]Q:_G|K04X>s'z[[P3Q7xQ7vQ00Q7zQ9MQ26Q4pp+0CfS<~,9NRsQ9MPFP3Q;_Q86Q9Lp+04bS=0Q80F}p+0CgR~P3P\Q=0P~P3Q07Q8dP~P3P]Q9FG|K04X>s'z[[P3Q7|Q3cQ00Q7}Q7|Q5jQ17p+0CjRs,9NRLQ7xPFP3Q;_Q8:Q3cQ3|Q7zF}p+0CkRAP3P\Q3|PAP3Q07Q8dPAP3P]Q9JG|K04X>L'z[[P3Q9QQ9QQ1`Q00Q7wQ1mQ1:p+0Cn,9NRLQ7}PFP3Q;_Q:`Q7|Q48Q9PF}p+0CoR5P3P\Q48P5P3Q07Q8dP5P3P]Q9LG|K04X>L'z[P3Q8=Q26Q00Q2DQ1hQ1=p+0D2,9NRLQ83PFP3Q;_Q8@Q7wQ4@Q8=F}p+0D3S=1P3P\Q4@Q=1P3Q07Q8dQ=1P3P]Q3cG|K04X>L'z[P3Q2KQ8OQ00Q2aQ1`Q1Ap+0D6S=2,9NRLQ88PFP3Q;_Q8EQ7~Q5dQ86F}p+0D7S=3P3P\Q5dQ=3P3Q07Q8dQ=3P3P]Q7|G|K04X>L'z[P3Q2PQ1tQ00Q1~Q1{Q1Ep+0D:,9NRLQ89PFP3Q;_Q;4Q8FQ4MQ8:F}p+0D;R6P3P\Q4MP6P3Q07Q8dP6P3P]Q7wG|K04X>L'z[P3Q5nQ5nQ4{Q00Q8<Q1=p+0D>S=4,9NRLQ9yPFP3Q;_p+0=6S=5Q;tQ4UQ:`F}p+0D?S=6P3P\Q4UQ=6P3Q07Q8dQ=6P3P]Q7~G|K04X>L'zP3Q8@Q52Q00Q5^Q1Np+0DBS=7,9NRLQ8HPFP3Q;_Q;5Q8<Q58Q8@F}p+0DCS=8P3P\Q58Q=8P3Q07Q8dQ=8P3P]Q8FG|K04X>L'zP3Q1aQ1EQ00Q1cQ1Hp+0DFS=9,9NRLQ0UPFP3Q;_Q;6Q8CQ0]Q8EF}p+0DGS=:P3P\Q0]Q=:P3Q07Q8dQ=:P3P]Q;tG|K04X>L'zP3Q1_Q1SQ00Q5BQ1Op+0DJS00,9NRLQ5oPFP3Q;_p+0=BS=;Q;}Q4oQ;4F}p+0DKS=<P3P\Q4oQ=<P3Q07Q8dQ=<P3P]Q8<G|K04X>L'zP3Q5FQ5Fp+0DMS==,9NS=>Q=>Q8kPFP3Q;_Q4@Q<qD8p+0DNRLP3P\Q<pPLP3Q07Q8dPLP3P]Q<dG|I1qS=?41CW>Q14Q:bQ11+1pQ0|Q2\'sQ:bPFPB19NLQ<gQ:4Q:en0100000020000Q:wQ:fQ8kD8Q11Q90PFP4Q:4Q1]Q:fQ8kg0JX7R6P]P]Q1\g0JYA%m6g0JZKN=0BQ=<p+0DWR6P3PTQ1gQ:xQ1f#>PTQ1gPTQ:xCIdO4b2Q==PTQ1fP>Q1f,NTdQ:wDOPLQ1gPFp+0=GS1fP3Q:dQ=5Q13EHX5LPLQ<dPFQ:8P]P3Q0:CjQ1gQ:dQ=5Q13EHX5LQ5op+0DOS1]Q8HQ0::0JT332X;2PLp+0BnS=@Q=@Q8EQ5oQ0:'5Q:vPVPRP{P|Q<gp+0DLS=A'`:0;ELP}PCb8b6b7X121R3?Q0::0a3D'B^12P3Q:bO1b0K0AQ<d,XTQ5oPVPRP{P|PEQ:xPrPEPQQ<gJ05P}PCb8b6b7X12AdS3K1R8D#\[^12P3Q:bQ1;O2b0Q:mQ:jQ:jp+0AAS=BPVPRP{P|PEQ00PrPEQ6Yp+0DIS=C+0^I0UP}PCb8b6b7X12103G1R8DQ00'^[^12P3Q<qQ0yO2b0b3b4K0FQ7OeQ7OQ1]Q8HQ1]PFQ:9P]P3Q1gQ1fQ7KQ1FGeW5PFQ;hQ1gQ:dQ=5D8PFQ;hQ60p+0:`S=DQ=5D8Q13Q8TPFP4Q;hQ1gQ:dQ=5g0J[UP]PvQ1iQ8@Q1Zg0J\_Pog0J]iQ5:Q5cp+0DPS1gQ8@Q1gp+0DQS=EQ=B,D3Q8C32W5Q;}Q=EB0JT3UQ8C32X;2Q1gp+0C0S=FQ=FQ1kQ5oQ:xPVPRP{P|p+0BlS=GQ=:60;EP}PCb8b6b7X121R3?S=H/5US=I1R3Z'B^12P3Q<qO1S=Jb0K0AQ;fQ2`DAQ1gp+0:\S=KQ<d32ep+07lS=LP3E<b<Q<[Q;fQ<[$0NQ:8PvPoEUQ6GeQ6GQ1gQ:4Q1gQ=EQ1Z723W5Q2\Q7OP3E<b<P4Q:dQ<dQ8@p+0DZS=MP:Q5oQ<Yp+0:ZS=NQ74Q7MQ:uQ:mQ:mQ:jQ8`Q<YP3Q=5Q2\O2b0b3b4p+0:WS=OQ0rG4Q6IeQ6`Q5oQ=O,03X;2Q;}Q;4/03X;2PVPRP{P|Q<gQ=95SEP}PCb8b6b7X121R3KS6`1R3ZRG'0^12P3Q8kO1S=Pb0p+0:VS=QQ2GDAQ=OQ0rDAQ=OQ=Q'0eQ;}p+0DSS=RQ7M5c3X;2Q5oQ;tQ=780`3X;2Q7DQ9y'0Q8:Q;t'0P[p+0DUS=SQ7DQ8:p+0:US=TQ9yQ;tp+0:XS=UG3PVPRP{P|p+0BbS=VQ605SEP}PCb8b6b7X12Q6`/5K9cGU^12Q=Pb0Q=OQ0rG4Q=QQ2GDAQ7LQ73'0eN:0sNB0rQ==p+0DYS=PP3PTQ1pQ=BQ1o#>PTQ1pPTQ=BCIdO4b2Q1]PTQ1oP>Q1o,NTdQ60DOQ1gQ1pQ1gPFQ;`P3p+0:bS1op+0=8S6`Q14EHW5PFQ=DQ1pQ;`Q7KD8PFQ=DQ:kQ4lQ7KD8Q1FQ92PFP4Q=DQ1pQ;`Q7Kg0J_3P]PxQ1qQ8@Q4fg0J`=Pog0JaGQ6Wp+06ES1pQ=EQ<dQ=Ep+0DRS=WQ:n,D3Q8C32W5Q5oQ=W1539S=X,VTQ8C32X;2Q=EQ6YQ6YQ5o/59Q5oQ:yPVPRP{P|Q=E/`QQ=E60;EP}PCb8b6b7X121R3?RG/59/BG^12P3Q=5O1b0K0AQ8VQ5oQ8Zp+0DDS=YP3Q=5Q0{O2b0Q:wQ:vQ:vQ:uQ:jp+0BjS=ZP3Q6`Q1>O2b0b3b4K0FQ=EQ=QQ<d32eQ5DP3E<b<Q=ZQ8VQ=Z$0NQ:9PxPoEUQ6IeQ6IQ=EQ:8Q=EQ=WQ<t723W5Q1>Q73P3E<b<P:Q1fQ;`Q8@p+07fS=[P4Q1fQ8CQ8@p+0D[S=\P:Q;4p+0BfS=]p+0:[S=^Q=NQ9OQ:vQ:uQ:uQ:mQ8ZQ=]P3Q7KQ0{O2b0b3b4Q=UQ2GG4Q6GeQ0RQ;4Q8V,03X;2Q;}Q:b/03X;2PVPRP{P|Q=FQ1g5SEP}PCb8b6b7X121R3KRGQ=H'0^12Q=Jb0Q;fQ2`DAQ=UQ2GDAQ=UQ;f'0eQ;}p+0DTS=HQ9O5c3X;2Q;4Q8:Q=880`3X;2Q89Q:`'0Q1kQ9y'0P[p+0DVS0RQ89Q1kQ7sQ:`Q9yQ74G3PVPRP{P|Q=GQ=B5SEP}PCb8b6b7X12Q=I@0`GK^12Q=Jb0Q=UQ2GG4Q;fQ2`DAQ72Q7M'0eN:0sJ0[NB0rPLQ=MP3PTQ1sQ:nQ1r#>PTQ1sPTQ:nCIdO4b2Q1gPTQ1rP>Q1r,NTdQ:kDOQ=EQ1sQ=EPFQ1oP3Q4~Q<uQ4pEHW5PFQ;`Q1sQ4oQ6`D8PFPBQ=W,9Np+0B`S1rQ;`Q72n0100000020000Q:iQ4oQ6`D8Q14Q6{PFP4Q;`Q1sQ4oQ6`g0JbQRGPvQ1ug0Jc[%mGg0JdeN<12Q1]Q=\P3PTQ1xQ<SQ1w#>PTQ1xPTQ<SCIdO4b2Q=EPTQ1wP>Q1w,NTdQ:iDOQ=WQ1xQ=WPFQ7LP3Q6pQ;5Q1?EHW5Q1gp+0D\S1wP3PTQ1[Q:np+0DAS1uQ<SQ:n7aTdO4b2Q=WQ1[Q:k32Q=RQ1[Q=RPFp+0:dS1sPvP3Q1xQ<pQ:cQ16GeW5PFQ5JQ1xQ6pQ;5D8PFPBQ=H,9NQ<eQ5JQ5An0100000020000Q:iQ6pQ;5D8Q1?Q96PFP4Q5JQ1xQ6pQ;5g0JeoRGP]P]Q1\g0Jg9%mGg0JhCN=0BQ=Ep+0D]S1\P3PTQ1}Q<SQ1|#>PTQ1}PTQ<SCIdO4b2Q=RPTQ1|P>Q1|,NTdQ:iDOQ=HQ1}Q=HPFQ5EP3Q4tp+0=<S1|Q4sEHW5Q=@Q:iQ=@Q1oQ=@416p+0=PS1xP]PoEUQ5AeQ5AQ=SQ<jQ=SPFQ;sP]P3Q;2CjQ1}Q4fp+0==S96Q17EHW5Q<qQ0RQ8EQ0::0JT332X;2Q=SQ<eQ<eQ:bQ<qQ0:'5Q:}PVPRP{P|Q=SQ=R'`:0;EHP}PCb8b6b7X121R3YQ0::0a3?'B^12P3Q;5O1b0K0AQ1oQ<qQ8^p+0DHS0:P3Q;5Q10O2b0Q:{Q:zQ:zQ:yQ:wQ=@P3Q1|Q1BO2b0b3b4K0FQ73eQ73Q0RQ8EQ0RPFQ0eP]P3Q1}Q9<Q;6Q1CGeW5PFQ6?Q1}Q4fQ96D8PFQ6?Q<SQ6pQ96D8Q17Q;nPFP4Q6?Q1}Q4fQ96g0JiMP]PvQ1iQ<jQ1[g0JjWPog0Jkap+05lS1}Q5@P6Q<jp+0DXRGQ:y,D3Q5o32X56Q<qB0JT3UQ5o52GX;2P6Q<mQ<mQ:`Q=5Q5lPVPRP{P|p+0BhS17Q=:60;EP}PCb8b6b7X121R3YS6{/5US=J1R3^'B^12P3Q1|O1S=Ib0K0AQ=UQ12DAQ=OQ;}526eQ5EP3E<b<Q=FQ=UQ=FQ:kQ=FQ1sQ=FD_Q99PvPoEUQ5;eQ5;P6Q1[Q1[92G3X56Q1[-086Q5KP3E<b<P:Q;kQ4fQ<jQ4~P:Q::Q;kQ<jQ=LP4Q::Q;4Q<jp+0DaS=_P:Q6`Q=GQ;`Q=Dp+080S=`Q:|Q:{Q:{Q:zQ:qQ=GP3Q96Q11O2b0b3b4Q8VQ18G4Q6BeQ5kQ6`Q=Q,03X;2Q<qQ<u/03X;2PVPRP{P|p+0C6S5kQ=95SEP}PCb8b6b7X121R3KS=a1R3^S=b'0^12P3Q:cO1S=cb0Q=TQ2`DAQ8VQ18DAQ8VQ=T'0eQ<qQ=MQ=`5c3X;2Q6`Q9yQ=C80`3X;2Q;tQ8C'0Q7DQ<d'0P[Q1wQ;tQ7DQ7sQ8CQ<dQ;hG3PVPRP{P|Q=VQ:x5SEP}PCb8b6b7X12Q=bQ=a/5K7cU^12Q=cb0Q8VQ18G4Q=TQ2`DAQ73Q08'0eN:0sJ0[J0[NB0rQ=Hp+0D`S=cP3PTQ21Q:kQ20#>PTQ21PTQ:kCIdO4b2Q0RPTQ20P>Q20,NTdQ<SDOP6Q21PFQ9xP3Q4tp+0=?S20Q19EHX56PFQ5xQ21Q<pQ;6D8PFQ5xQ:hQ4NQ;6D8Q1CQ9=PFP4Q5xQ21Q<pQ;6g0JlkP]PxQ1qQ<jp+05RS21g0Jn5Pog0Jo?Q5CQ5:PGQ;}Q=PQ:m,D3Q5o32X5GQ=5Q=PQ=X,VTQ5o32X;2PGp+0C8S=XQ=XQ=5/59Q=5Q;0PVPRP{P|1`HQ>0;EHRQP8Q1j219Q8$0Zd&0{3H18b6b7X12Q1|O1K0AQ74Q=5p+0>=S1jQ<0P3Q96Q15O2b0p+0AMS9=Q:}Q:}Q:|p+0A=S1CQ=]P3Q20Q13O2b0b3b4K0FQ=TQ;}52Gep+068S=bP3E<b<Q6YQ74Q6YQ:nQ6Yp+0:eS=aQ6YD_Q;7PxPoEUQ5;eQ5;PGQ99Q=Pp+05TS=d723X5GQ13Q5KP3E<b<P:Q9<Q<pQ<jQ7FQ9<Q;}413P:Q8WQ9<Q<jQ6pP:Q:gQ8WQ<jQ5DP4Q:gQ:bQ<jp+0DbS=eP:Q<uQ<]Q1oQ;`Q5JQ:}Q:|Q:|Q:{Q:rQ<]P3Q;6Q15O2b0b3b4Q;hQ2`G4Q5ueQ<cQ<uQ74,03X;2Q<qQ;5/03X;2PVPRP{P|Q<m=SEHP}PCb8b6b7X121R3KRQQ6{'0^12Q=Ib0Q=UQ12DAQ;hQ2`DAQ;hQ=U'0eQ<qQ=\Q5J5c3X;2Q<uQ7DQ0080`3X;2Q8:Q0U'0Q:`Q8C'0P[Q1\Q8:Q:`p+0:SS6{Q0UQ8CQ=DG3PVPRP{P|Q17Q:y5SEP}PCb8b6b7X12Q=J@0`QK^12Q=Ib0Q;hQ2`G4Q=UQ12DAQ73Q=`'0eN:0sJ0[J0[J0[NB0rQ=SQ=_P3PTQ24Q:iQ23#>PTQ24PTQ:iCIdO4b2P6PTQ23P>Q23,NTdQ:hDOPGQ24PFQ5yP3Q4Rp+0=@S23Q;3EHX5GPFQ9xQ24Q5MQ20D8PFPBQ=P,9NQ1rQ9xQ5An0100000020000Q8NQ5MQ20D8Q19Q;mPFP4Q9xQ24Q5MQ20g0K0IRQP\Q0Bg0K1S%mQg0K2]N<0lQ0RQ=eP3PTQ29Q:hQ28#>PTQ29PTQ:hCIdO4b2PGPTQ28P>Q28,NTdQ8NDOQ=PQ29Q=PPFQ5EP3Q4Up+0=AS28Q1:EHW5P6p+0DcS24P3PTQ2>Q:hQ2=#>PTQ2>PTQ:hCIdO4b2Q=PQ2>Q8N32Q=MQ2>Q=MPFQ5}P\P3Q29Q4XQ=;Q1GGeW5PFQ5hQ29Q4UQ28D8PFPBQ=\,9NQ<VQ5hQ5Gn0100000020000Q66Q4UQ28D8Q1:Q95PFP4Q5hQ29Q4UQ28g0K3gRQPxP\Q27g0K51%mQg0K6;N=0BPGp+0DdS27P3PTQ2AQ8NQ2@#>PTQ2APTQ8NCIdO4b2Q=MPTQ2@P>Q2@,NTdQ66DOQ=\Q2AQ=\PFQ5@P3Q4Zp+0=CS2@Q1<EHW5Q<eQ66Q<eQ;fQ<eQ60Q<ep+0:iS29Q<eFqp+0=WS1:P\PoEUQ5GeQ5GQ1wQ2>Q1wPFQ5\PxP3Q<SCjQ2AQ4]Q:fQ7iEHW5Q=Mp+0DfS2>P3PTQ2FQ8NQ2E#>PTQ2FPTQ8NCIdO4b2Q1wQ2FQ6632Q1\Q2FQ1\PFQ6IPxP3Q2AQ58Q:eQ1=GeW5PFQ5_Q2AQ4]Q:fD8PFPBp+0D^S1=,9NQ<YQ5_Q6]n0100000020000Q66Q4]Q:fD8Q7iP@PFP4Q5_Q2AQ4]Q:fg0K7ERQP\PxQ1qg0K8O%mQg0K9YN=0BQ=\p+0DgS=\P3PTQ2IQ8NQ2H#>PTQ2IPTQ8NCIdO4b2Q1\PTQ2HP>Q2H,NTdQ66DOQ1=Q2IQ1=PFQ5;P3Q4_Q:dQ1KEHW5Q=XQ66Q=XQ:iQ=XQ=DQ=XQ:mQ=Xp+0:lS2HQ=XD_D1p+0=ZS2APxPoEUQ6]eQ6]p+0D_S7iQ2FQ7iPFQ5eP\P3Q:{CjQ2IQ4`Q1fQ1@EHW5Q7iQ2FQ7iPFQ5eP\P3Q2IQ4`Q1fQ1@GeW5PFQ5KQ2IQ4_Q:dD8PFPBQ=c,9NQ=@Q5KQ6]n0100000020000Q:]Q4_Q:dD8Q1KQ04PFP4Q5KQ2IQ4_Q:dg0K:cRQPvQ0mg0K;m%mQg0K=7N<12Q1\p+0DiS0mP3PTQ2NQ66Q2M#>PTQ2NPTQ66CIdO4b2Q7iPTQ2MP>Q2M,NTdQ:]DOQ=cQ2NQ=cPFQ5;P3Q4cQ:3Q52EHW5Q1=p+0DjS2MP3PTQ2LQ:hQ=<Q66Q:h7aTdO4b2Q=cQ2LQ8N32Q=_Q2LQ=_PFQ5_PvP3Q2NQ0]Q:4Q1AGeW5PFQ6WQ2NQ4cQ:3D8PFPBQ=e,9NQ<_Q6WQ6]n0100000020000Q:]Q4cQ:3D8Q52Q6rPFP4Q6WQ2NQ4cQ:3g0K>ARQPMQ2Og0K?K%mQg0K@UN<0lQ7ip+0DkS2OP3PTQ2SQ66Q2R#>PTQ2SPTQ66CIdO4b2Q=_PTQ2RP>Q2R,NTdQ:]DOQ=eQ2SQ=ePFQ5;P3Q4YQ:6Q1NEHW5Q=cp+0DlS2RP3PTQ2WQ66Q2V#>PTQ2WPTQ66CIdO4b2Q=eQ2WQ:]32Q24Q2WQ24PFQ5KPMP3Q2SQ4gQ:8Q1DGeW5PFQ5@Q2SQ4YQ:6D8PFPBQ27,9NQ0^>0ONWQ5@Q6]n0100000020000Q:\Q4YQ:6D8Q1NQ6~PFP4Q5@Q2SQ4YQ:6g0KA_Q0^PMQ2],CXRQQ09g0KBiPog0KD3Q9oQ:[Q9oQ:ZQ9oQ:YQ9oQ:kQ9oQ5|Q9oQ=aQ9oQ:yQ9oQ0tQ9oFqD1D1Q1WPMPoEUQ1deQ1dQ27Q2WQ27Q;HQ4lP31bXQQ06Q0?EhW5Q=ep+0DnS2WP3PTQ2_Q:ZPLQ:YQ:Z7aTdO4b2Q27Q2_Q:Y32p+0DeS09Q2_Q09Q;IQ4oP3Q06Q6@DuW5Q;HQ4gp+0>HS2]Q;HQ4xQ2]Q;HQ0eQ2]Q;HQ:aQ2]Q7JQ0eQ;BQ:HQ23Q2_Q06P:Q0eQ4q/5OS4YQ:Z36X9<P_Q0EQ4qQ;vP3C]X;2Q:dQ=ZQ8EQ=D':Q0UQ;h':Q8EQ=DQ0UQ;hP[Q2OQ==Q=AQ<[Q:dQ:dQ7KG3P[Q2OQ<uQ6`Q7yP_P_PLG3EFPVPRP{P|PEQ;@PrPEPEQ=GQ1\PEQ01Q02Q02Q03P1J1lR1GJP}PCb8b6b7X12X:IAdS3KS03Q1]P8PZP7CK[^12^:IP3Q=DQ:6Q1GO3b0Q2HQ1BG4Q:YQ;wDAQ;sQ0jQ:Y36eQ98p+0>GS0jD7p+0>0RQP:Q4YQ1='0X9<Q:dQ=]Q8VQ;fQ0dQ;<Q0ZQ0ZQ6OQ;wQ<_P3Q:9Q1<O2S1<b0b3b4Q2HQ1BG4Q8YeQ98Q0jD7GGE<Q4xQ4|Q<2Q20Q2_Q06P:Q0dQ8e/5OS8YQ:Z36X9<P_Q0EQ8eQ4wP3C]X;2Q:eQ=ZQ8CQ=K':Q<dQ=^':Q8CQ=KQ<dQ=^P[Q2OQ==Q=AQ<[Q:eQ:eQ<qG3P[Q2OQ=5Q1|Q29P_P_PLG3EFPVPRP{P|PEQ;@PrPEPEQ=GQ2>P1GJP}PCb8b6b7X12X:IQ03Q1]P8P?P7CK[^12^:IP3Q=KQ:6Q1GO3b0Q;xQ10G4Q:YQ;wDAp+082S=Kp+08:Q:Y36ep+05\S=5p+05YS=^D7PQP:Q8YQ1='0X9<Q:eQ=]Q=NQ74Q5JQ;<Q0ZQ0ZQ6OQ98Q=]Q1<b0b3b4Q;xQ10G4Q62eQ=5Q=^D7GGE<Q4gQ;Ap+05ZS62Q;6Q2_Q06P:Q5JQ=a/5OS8YQ:Z36X9<P_Q0EQ=ap+088S4wP3C]X;2Q:fQ=ZQ8@Q=U':Q8HQ=O':Q8@Q=UQ8HQ=OP[Q2OQ==Q=AQ<[Q:fQ:fQ5oG3P[Q2OQ:bQ;4Q2CP_P_PLG3EFPVPRP{P|PEQ;@PrPEPEQ=GQ0RP1GJP}PCb8b6b7X12X:IQ03Q1]P8P^P7CK[^12^:IP3Q=UQ:6Q1GO3b0Q1sQ4uG4Q:YQ;wDAQ=`Q0bQ:Y36eQ;mp+0>ES2CD7PQP:Q8YQ1='0X9<Q:fQ=]Q=QQ=TQ08Q;<Q0ZQ0ZQ6OQ;qQ<YQ1<b0b3b4Q1sQ4uG4Q61eQ;mQ2CD7GGE<Q4lQ2_Q06Q4|p+05WS;qQ96Q2_Q06P:Q08Q;k/5OS06Q:Z36X9<P_Q0EQ;kQ0bP3C]X;2Q2@Q=ZQ8<Q7s':Q1kQ6{':Q8<Q7sQ1kQ6{P[Q2OQ==Q=AQ<[Q2@Q2@Q<jG3P[Q2OQ;}Q8kQ;`P_P_PLG3EFPVPRP{P|PEQ;@PrPEPEQ=GPHP1GJP}PCb8b6b7X12X:IQ03Q1]P8PYP7CK[^12^:IP3Q7sQ:6Q1GO3b0p+0:fR_Q0|G4Q:YQ;wDAp+07nS1Gp+086S03Q:Y36eQ=5Q=^D7PQP:Q06Q1='0X9<Q2@Q=]p+0:RS06p+0:QS1=Q5DQ;<Q0ZQ0ZQ6OQ;mp+0BdQ1<b0b3b4P_Q0|G4Q5~eQ=5Q=^D7GGGoQ:ZP3E?b2Q6]P3E<b<N?1kQ=_p+0DmR_P3PTQ2cQ:]Q2b#>PTQ2cPTQ:]CIdO4b2Q24PTQ2bP>Q2b,NTdQ:\DOQ27Q2cQ27PFQ5;P3Q4lQ:9Q55EHW5Q=eQ2WP3PTP0Q8N20829Q:TQ8N7aTdO4b2Q27Q66720Q09P0Q09PFQ5TQ0^P3Q2cQ4oQ::Q1EGeW5PFQ5@Q2cQ4lQ:9D8PFQ5@Q:SQ4lQ:9D8Q55Q<7PFP4Q5@Q2cQ4lQ:9g0KE=Q0^PWQ0Mg0KFGPog0KGQQ:1PuQ:1Q:]Q:1Q:\Q:1Q:[Q:1Q1CQ:1Q60Q:1Q;kQ:1Q:{Q:1Q8eQ:1D_D1D1D1Q:LQ0^PoEUQ54eQ54Q2>P0Q2>Q6W/EW-033W5Q;nQ5CP3E<b<N>0TQ24p+0DoS24P3PT&01J#k$0f#PR9,CTS0^Q:T%>9PTQ0^PTQ:TCIdO4b2Q09PTP9P>1NT9dQ:SDOQ2>Q0^Q2>PFQ6WP3Q4~Q:gQ1JEHW5PFQ5:Q0^Q4oQ::D8PFQ5:Q<9Q4oQ::D8Q1EQ<8PFP4Q5:Q0^Q4oQ::g0KH[PvQ1qQ2gg0KIePog0KJop+0C@S4oQ:SQ4oQ66Q4oQ:]Q4oQ:\Q4oQ5|Q4oQ=BQ4oQ8WQ4oQ:|Q4oQ;{Q4oD_D1D1D1p+0=bS0^PvPoEUQ54eQ54Q=\Q2LQ=\p+0DhS<8Q2g723W5Q09p+0E1S1JP3PTQ2LQ2gQ=WQ1CQ:S'BdO4b2Q5CP3E<b<N>11Q27p+0E0S27P3PTQ2gQ;nQ=EQ;n9auTdO4b2Q2>Q0DP>Q0D,NTd60DTR9Q<932Q=\Q2gQ=\PFQ5TP3Q6pp+0=OS<9Q1HEHW5Q09Q1JP3PTQ2gPuQ=WQ:S?aTudO4b2Q=\Q2gQ=\e$0Y729PFQ5TQ2gQ6pQ<9D8PFPBQ0m,9NQ=FQ5TQ57n0100000020000Q:RQ6pQ<9D8Q1HQ<;PFP4Q5TQ2gQ6pQ<9g0KL9R9P\PxQ1ig0KMC%m9g0KNMN=0BQ2>p+0E2S2gP3PTQ2mPuQ2l#>PTQ2mPTPuCIdO4b2Q<8PTQ2lP>Q2l,NTdQ:RDOQ0mQ2mQ0mPFQ1dP3Q4tQ97Q1IEHW5p+0CCS2lQ:VQ2lQ:iQ2lQ:hQ2lQ8NQ2lQ=BQ2lQ:uQ2lQ7yQ2lQ5lQ2lQ8>Q2lD_D1D1D1Q;9PxPoEUQ57eQ57Q2MQ2FQ2MPFQ5EP\P3Q;=CjQ2mQ4fQ99Q1SEHW5Q<8p+0E4S<8P3PTQ2kQ:SQ1gQ:S9auTdO4b2Q2MQ2k;2uQ2OQ2kQ2OPFQ=bP\P3Q2mQ9<Q;7Q1LGeW5PFQ5TQ2mQ4fQ99D8PFPBQ2R,9Np+0C:S1HQ5TQ5Gn0100000020000Q:RQ4fQ99D8Q1SQ6@PFP4Q5TQ2mQ4fQ99g0KOWPvP]Q1iQ;HQ1[g0KPaPog0KQkQ<rQ:QQ<rQ:XQ<rQ:kQ<rQ<SQ<rQ:iQ<rQ:mQ<rQ:wQ<rQ4qQ<rQ;2Q<rQ8AQ<rFqD1D1D1p+0=gS4fP]PoEUQ57eQ57Q2RQ:fQ2RQ;RQ<tP3Q1XP:Q98EhW5Q:6Q:dB0JT3U52_X;2Q2Rp+0CLS2mQ2mQ:8Q:cQ;DPVPRP{P|Q1wQ9o60;EP}PCb8b6b7X121R3^B0a3YU'B^12P3Q97O1b0K0AQ4qQ:6Q8cQ<0P3Q97Q1AO2b0Q;BQ;AQ;AQ;@p+0AQS1AQ1HP3Q;7Q1NO2b0b3b4K0FQ0deQ0dP_Q:dQ;Sp+05NS1N?L3:S1wQ;w32X5_Q;RQ4|Q:dP:Q;RQ;SQ;w723W=P4Q59Q:dQ1[Q:9Q<[Q1@Q2HQ1FDAQ2HQ097cUeI0qQ<tQ:d;L:Q6hQ4|Q:eQ:dP:P:Q69Q;r/5OR9Q4q36X9<Q:9Q1J,53S=FQ;rQ0}P3C]X;2Q:8Q1|P3Q=FQ::C]X;2Q=UQ=O':Q=QQ=T':Q=UQ=OQ=QQ=TP[p+0E3S=FQ:cQ;5Q7yQ:8Q:8Q7KG3P[Q=FQ6`Q1|Q29Q:9Q:9Q<uG3EFPVPRP{P|PEPEQ<k00XHp+0C>S<uQ1\5SEH0VP}PCb8b6b7X121R3^S1\/5U1R3YS1|Q1|PUQ1\Dl^12P3Q99O1b0Q;pQ13G4Q2HQ1FDAQ67Q;vQ2H36eQ6lQ6nD7Q:9Q=@Q8VQ;fQ0bQ1@Q2HQ1FG4Q6;eP:Q2>,09X9<Q:8Q=@Q=NQ74Q0eQ1KQ;pQ13G4Q69eQ6lQ6nD7GGGyQ4qP3E?b2Q1dP3E<b<Q1[#tMArQ0mp+0E5S2>P3PTQ2qPuQ2p#>PTQ2qPTPuCIdO4b2Q2OPTQ2pP>Q2p,NTdQ:RDOQ2RQ2qQ2RPFQ5@P3Q<tp+0=TS2pQ5<EHW5PFQ5;Q2qQ9<Q;7D8PFPB19N_Q<lQ5;Q4Un0100000020000Q:QQ9<Q;7D8Q1LPqPFP4Q5;Q2qQ9<Q;7g0KS5PxP]Q1qQ51Q6hg0KT?Pog0KUIp+0CFS9<Q1AQ9<Q:RQ9<Q:YQ9<Q:nQ9<Q:kQ9<Q<SQ9<Q:uQ9<Q:xQ9<Q;pQ9<Q1AQ9<Q<5Q9<D_D1D1D1D1p+0=hS2qP]PoEUQ54eQ54P_Q:eQ;SQ1NP3Q6OP:Q6lEhX5_P_Q:eQ;SQ1wQ6l32X5_P4Q4|Q:eQ54Q:8Q<[Q1KQ;pQ13DAQ;pQ097cUeI0qQ;lQ:e$0gE<Q0PP3E<b<Q6h#tMArQ2Mp+0E6S2MP3PTQ2uQ:RQ2t#>PTQ2uPTQ:RCIdO4b2Q2RPTQ2tP>Q2t,NTdQ:QDOP_Q2uPFQ4ZP3Q1Np+0=US1NQ1MEHX5_PFQ4XQ2uQ<tQ2pD8PFPBQ2W,9Np+0COS2tQ4XQ4Nn0100000020000Q:PQ<tQ2pD8Q5<Q75PFP4Q4XQ2uQ<tQ2pg0KVSR9P]P]Q2sg0KW]%m9g0KXgN=0BQ2Op+0E7S2OP3PT&02J$07#PS<t,CTR9Q:QQ<t#>PTP9PTQ:QCIdO4b2P_PTQ<tP>Q<t,NTdQ:PDOQ2WP9Q2WPFQ4RP3Q4vp+0=VS4vQ1VEHW5p+0CHS<tQ6hQ<tQ<^Q<tQ:SQ<tQ:[Q<tQ5|Q<tQ1CQ<tQ:nQ<tQ:wQ<tQ:zQ<tQ;uQ<tQ<^Q<tQ<:Q<tFqD1D1D1D1p+0=jS2uP]PoEUQ4NeQ4NQ24Q1fQ24PFQ58P]P3Q:SCjP9Q9BQ1:Q1OEHW5Q::Q27Q:6B0JT3D32X;2Q24Q2tQ2tQ<9Q::/5DQ;HPVPRP{P|Q24Q2W,`H60;EP}PCb8b6b7X121R3?B0a3YD'B^12P3Q2pO1b0K0AQ;uQ::Q8gQ<0P3Q2pQ55O2b0Q;EQ;DQ;DQ;CQ<bQ9oP3Q4vQ1EO2b0b3b4K0FQ0eeQ0eQ27Q:6Q27PFQ4_P]P3P9Q85p+0=XS85Q5BGeW5PFQ4]P9Q9BQ1:D8PFQ4]P@Q9BQ1:D8Q1OQ78PFP4Q4]P9Q9BQ1:g0KZ1PvQ1qQ2wg0K[;Pog0K\Ep+0CJS9BQ<<Q9BQ57Q9Bp+0AUS1OQ9BQ:UQ9BQ:]Q9BQ60Q9BQ<IQ9BQ5|Q9BQ:yQ9BQ:|Q9BQ;xQ9BQ1OQ9BQ<<Q9BD_D1D1D1D1D1Q2iPvPoEUQ5YeQ5YQ1JQ1[Q1JQ2gQ2w723W5Q24p+0E;S55P3PTQ1[Q2wQ=cQ0ZQ:S'BdO4b2Q4RP3E<b<N>11Q2Wp+0E:S2WP3PTQ2wQ;zQ7iQ;z9auTdO4b2Q27Q0AP>Q0A,NTd60DTR9;2@Q1JQ2wQ1JPFQ4_P3Q21Q94Q1PEHW5Q24Q55P3PTQ2wPuQ=cQ:S?aTudO4b2Q1JQ2wQ1Je$0Y729PFQ4_Q2wQ21Q94D8PFPBQ=F,9NQ<kQ4_Q4]n0100000020000Q:RQ21Q94D8Q1PQ:oPFP4Q4_Q2wQ21Q94g0K]OPxP\Q1qQ;UP0g0K^YPog0K_cQ2mQ<=Q2mQ1dQ2mQ;1Q2mQ:WQ2mQ8NQ2mQ:jQ2mQ=BQ2mQ60Q2mQ:{Q2mQ9=Q2mQ;{Q2mQ;1Q2mQ<=Q2mD_D1D1D1D1D1Q;;P\PoEUQ4MeQ4MQ=FQ2kQ=FQ;XQ=dP3Q;?P:Q0GEhW5Q1Jp+0E=S2wP3PTQ2kPuQ=PQ:[?aTudO4b2Q=FQ2kQ:R32Q<8Q2kQ<8Q;YQ4xP3P:Q93DuW5Q;XQ21Q8fQ;XQ4}Q8fQ;XQ0aQ8fQ;Xp+0=iS=cQ8fQ0YQ0aQ;TQ2ZQ<9Q2kP:P:Q0aQ<:/5OS0AQ:\36X9<Pap+0E8S0a,53S7iQ<:p+08MS1[P3C]X;2Q1NQ<gQ<qQ=N':Q8kQ74':Q<qQ=NQ8kQ74P[Q2WPGP6Q=@Q1NQ1NQ:dG3P[Q2WQ:3Q1fQ<5PaPaQ=PG3EFPVPRP{P|PEQ;RPrPEPEQ6YQ2RP1GJP}PCb8b6b7X12X:IAdS3KR9Q=MP8PZP7CK[^12^:IP3Q=NQ94Q1IO3b0Q8DQ4sG4Q:[Q04DAQ4wp+08LS=NQ:[36eQ0?Q8iD7Q8^P:Q0A/0_X9<Q1NQ<eQ4qQ2Hp+08BS2RQ;LQ;JQ;JQ;IQ6@Q5kP3Q:aQ1SO2S5kb0b3b4Q8DQ4sG4Q6SeQ0?Q8iD7GGE<Q4}Q6]Q<CQ:gQ2kP:P:Q4wQ<@/5OS6SQ:\36X9<PaQ7iQ<@p+08JS<0/03S753TX;2Q2pQ<gQ:bQ=U':Q;4Q=O':Q:bQ=UQ;4Q=OP[Q2WPGP6Q=@Q2pQ2pQ:fG3P[Q2WQ:eQ:8Q8mPaPaQ=PG3EFPVPRP{P|PEQ;RPrPEPEQ6YQ2>P1GJP}PCb8b6b7X12X:IQ=MP8P?P7CK\9^12^:IP3Q=UQ94Q1IO3b0Q<?Q16G4Q:[Q04DAQ0bQ4zQ:[36eQ1dQ54D7Q8^P:Q6S/0_X9<Q2pQ<eQ29Q8Wp+08@S=UQ;LQ;JQ;JQ;IQ0?Q<eQ5kb0b3b4Q<?Q16G4Q6NeQ1dQ54D7GGE<Q21Q;SQ57Q::Q2kP:P:Q0bQ;{/5OS21Q:\36X9<PaQ7iQ;{Q0sP3C]X;2Q;7Q<gQ5oQ=Q':S0sQ;}Q=T':S6NQ5oQ=QQ;}Q=TP[Q2WPGP6Q=@Q;7Q;7Q23G3P[Q2WQ=;Q28Q;xPaPaQ=PG3EFPVPRP{P|PEQ;RPrPEPEQ6YQ09P1GJP}PCb8b6b7X12X:IQ=MP8P^P7CK\9^12^:IP3Q=QQ94Q1IO3b0Q8eQ1?G4Q:[Q04DAQ03p+08FS09Q:[36eQ6PQ8gD7Q8^P:Q21/0_X9<Q;7Q<eQ=aQ1sQ;vQ;LQ;JQ;JQ;IQ<;p+0C4Q5kb0b3b4Q8eQ1?G4Q5{eQ6PQ8gD7GGE<Q=dQ2kP:Q6]Q51Q:9Q2kP:P:Q03Q<2/5OS2kQ:\36X9<PaQ7iQ<2Q09P3C]X;2Q99Q<gQ<jQ7s':S7iQ8EQ6{':S8gQ<jQ7sQ8EQ6{P[Q2WPGP6Q=@Q99Q99Q;6G3P[Q2WQ20Q2@Q;uPaPaQ=PG3EFPVPRP{P|PEQ;RPrPEPEQ6YPHP1GJP}PCb8b6b7X12X:IQ=MP8PYP7CK\9^12^:IP3Q7sQ94Q1IO3b0Q;~Q4pG4Q:[Q04DAQ0eQ0uQ:[36eQ1dQ54D7Q8^P:Q2k/0_X9<Q99Q<eQ;`Q=DQ7UQ;LQ;JQ;JQ;IQ6PQ<lQ5kb0b3b4Q;~Q4pG4Q6FeQ1dQ54D7GGGoPuP3E?b2Q4UP3E<b<Q;wMArQ27p+0E<S6FP3PTQ2{PuQ2z#>PTQ2{PTPuCIdO4b2Q2gPTQ2zP>Q2z,NTdQ:RDOQ=FQ2{Q=FPFQ4_P3Q=dQ:aQ1QEHW5PFQ58Q2{p+05SR9Q2AD8PFQ58Q:QP9Q2AD8Q5FQ9SPFP4Q58Q2{P9Q2Ag0K`mPxPWQ0_Q0;$0S+0Gg0Kb7Pog0KcAp+0CMS0;Q:PQ0;Q<?Q0;Q1}Q0;Q6OQ0;Q:XQ0;Q:hQ0;Q:mQ0;Q:jQ0;Q=BQ0;Q:|Q0;Q5lQ0;Q;~Q0;Q6OQ0;Q<?Q0;FqD1D1D1D1D1Q<{PxPoEUQ4HeQ4HQ<8P0Q<8Q4`/EW-033W5Q70Q4NP3E<b<N>1jQ1JQ2wP3PTQ31Q:RQ30#>PTQ31PTQ:RCIdO4b2Q=FPTQ30P>Q30,NTdQ:QDOQ<8Q31Q<8PFQ4`P3Q4xQ:HQ5OEHW5PFQ4_Q31Q=dQ:aD8PFPBQ2>,9Np+0C<S30Q4_Q4Mn0100000020000Q:PQ=dQ:aD8Q1QQ0FPFP4Q4_Q31Q=dQ:ag0KdKR9P\Q0Bg0KeU%m9g0Kf_N<0lQ2gp+0E>R9P3PTQ35Q:QQ34#>PTQ35PTQ:QCIdO4b2Q<8PTQ34P>Q34,NTdQ:PDOQ2>Q35Q2>PFQ5MP3p+05VRaQ9:Q1REHW5Q=Fp+0E?S34P3PTQ3:Q:QQ39#>PTQ3:PTQ:QCIdO4b2Q2>Q3:Q:P32Q2MQ3:Q2MPFQ0]P\P3Q35Q;qQ:JQ5NGeW5PFQ4ZQ35PaQ9:D8PFPBQ2O,9NQ9oQ4ZQ4Nn0100000020000Q:PPaQ9:D8Q1RQ68PFP4Q4ZQ35PaQ9:g0KgiPxP\Q3;,CXS3;Q;YP0g0Ki3Pog0Kj=p+0CPRaQ:OPaPuPaQ<BPaQ5GPaQ;=PaQ:[PaQ:kPaQ:wPaQ:vPaQ:uPaQ5lPaQ1APaQ8mPaQ;=PaQ<BPaD_D1D1D1D1D1D1p+0>2S35P\PoEUQ4HeQ4HQ2OQ3:Q2OQ;]Q0zP3Q3;,bXP:Q:pEhW5Q2>p+0EAS3;P3PTQ3=Q:PQ=PQ:OQ:P7aTdO4b2Q2OQ3=Q:O32Q0aQ3=Q0ap+0B:S3:Q=^P3P:Q0HDuW5Q;]Q4xQ8jQ;]Q51Q8jQ;]Q4wQ8jQ;]Q2iQ8jQ0YQ4wQ;WQ<{Q;7Q3=P:P:Q4wQ<=/5OS8jQ:P36X9<PbQ6F,53S4wQ<=p+08QS1R/03S393TX;2Q94Q<gQ0sQ6NQ5oQ=QQ;}Q=TP[P9PGP6Q=@Q94Q94Q:6G3P[P9Q:9Q:8Q<<PbPbQ=PG3EFPVPRP{P|PEQ;UPrPEPEQ6YQ27P1GJP}PCb8b6b7X12X:IAdS3KS27Q=MP8PZP7CK[^12^:IP3Q=QQ9:Q1MO3b0Q8lQ4sG4Q:OQ6qDAQ0bp+08PS=QQ:O36eQ0>Q9sD7Q:rP:Q8jQ1J'0X9<Q94Q<kQ0tQ;uQ09Q;QQ;OQ;OQ;NQ77Q1HP3Q1WQ1VO2S1Vb0b3b4Q8lQ4sG4Q6_eQ0>Q9sD7GGE<Q51Q5:Q8qQ99Q3=P:P:Q0bQ<D/5OS6_Q:P36X9<PbQ4wQ<Dp+08NS1H/03S=T3TX;2Q85Q<gQ7iQ8gQ<jQ7sQ8EQ6{P[P9PGP6Q=@Q85Q85Q:3G3P[P9Q:4Q<9Q<:PbPbQ=PG3EFPVPRP{P|PEQ;UPrPEPEQ6Yp+0E9S6{P1GJP}PCb8b6b7X12X:IQ27Q=MP8P?P7CK[^12^:IP3Q7sQ9:Q1MO3b0Q<CQ16G4Q:OQ6qDAQ03Q1[Q:O36eQ5GQ1}D7Q:rP:Q6_Q1J'0X9<Q85Q<kQ4qQ2HQ7PQ;QQ;OQ;OQ;NQ0>Q<kQ1Vb0b3b4Q<CQ16G4Q6\eQ5GQ1}D7GGE<Q4xQ;VQ5CQ97Q3=P:P:Q03Q8m/5OS4xQ:P36X9<PbQ4wQ8mp+08KS6\P3C]X;2Q1:Q<gQ0UQ06':S0>Q8CQ1=':S7sQ0UQ06Q8CQ1=P[P9PGP6Q=@Q1:Q1:Q:fG3P[P9Q:dQ:eQ<2PbPbQ=PG3EFPVPRP{P|PEQ;UPrPEPEQ6YQ0mP1GJP}PCb8b6b7X12X:IQ27Q=MP8P^P7CK[^12^:IP3Q06Q9:Q1MO3b0Q8>Q1?G4Q:OQ6qDAQ0eQ<0Q:O36eQ6@Q76D7Q:rP:Q4xQ1J'0X9<Q1:Q<kQ29Q8WQ2RQ;QQ;OQ;OQ;NPqQ=XQ1Vb0b3b4Q8>Q1?G4Q6XeQ6@Q76D7GGE<Q0zQ3=P:Q5:Q0PQ1xQ3=P:P:Q0eQ<5/5OS3=Q:P36X9<PbQ4wQ<5Q753TX;2Q4vQ<gQ<dp+0:PS4w':S75Q8@Q8U':S6XQ<dQ4wQ8@Q8UP[P9PGP6Q=@Q4vQ4vQ=;G3P[P9Q2@Q1fQ;{PbPbQ=PG3EFPVPRP{P|PEQ;UPrPEPEQ6YPHP1GJP}PCb8b6b7X12X:IQ27Q=MP8PYP7CK[^12^:IP3Q4wQ9:Q1MO3b0Q8AQ4pG4Q:OQ6qDAQ;sQ4zQ:O36eQ5GQ1}D7Q:rP:Q3=Q1J'0X9<Q4vQ<kQ=aQ1sQ=UQ;QQ;OQ;OQ;NQ6@Q<mQ1Vb0b3b4Q8AQ4pG4Q6UeQ5GQ1}D7GGGoQ:PP3E?b2Q4MP3E<b<Q6qMArQ<8p+0E@S6UP3PTQ3?Q:QQ3>#>PTQ3?PTQ:QCIdO4b2Q2MPTQ3>P>Q3>,NTdQ:PDOQ2OQ3?Q2OPFQ4RP3Q0zQ1WQ1TEHW5PFQ5MQ3?Q;qQ:JD8PFQ5MQ:MQ;qQ:JD8Q5NQ7:PFP4Q5MQ3?Q;qQ:Jg0KkGPxPWQ0\g0KlQPog0Km[p+0CQS;qQ:SQ;qQ:PQ;qQ:SQ;qQ<CQ;qQ5;Q;qQ;>Q;qQ:\Q;qQ:nQ;qQ:xQ;qQ:wQ;qQ:vQ;qQ;0Q;qQ7FQ;qQ8AQ;qQ;>Q;qQ<CQ;qFqD1D1D1D1D1D1p+0>3S3?PxPoEUQ5geQ5gQ0aP0Q0aQ4U/EW-033W5Q<;Q4IP3E<b<N>0TQ2>Q3;P3PTQ3BQ:NQ3A#>PTQ3BPTQ:NCIdO4b2Q2OPTQ3AP>Q3A,NTdQ:MDOQ0aQ3BQ0aPFQ4UP3Q=^Q9>Q5SEHW5PFQ4RQ3BQ0zQ1WD8PFPBQ6{,9NQ4oQ4RQ4Hn0100000020000Q3WQ0zQ1WD8Q1TQ0GPFP4Q4RQ3BQ0zQ1Wg0KneRbP\Q3@g0Koo%mbg0L19N<0lQ2Mp+0EBRbP3PTQ3FQ:MQ3E#>PTQ3FPTQ:MCIdO4b2Q0aPTQ3EP>Q3E,NTdQ3WDOQ6{Q3FQ6{PFQ5YP3Q62Q:LQ1UEHW5Q2Op+0ECS3EP3PTQ3JQ:MQ3I#>PTQ3JPTQ:MCIdO4b2Q6{Q3JQ3W32Q2WQ3JQ2WPFQ4ZP\P3Q3FQ50Q0^Q5[GeW5PFQ5MQ3FQ62Q:LD8PFPBQ55,9NQ<nQ5MQ4In0100000020000Q3WQ62Q:LD8Q1UQ<NPFP4Q5MQ3FQ62Q:Lg0L2CPxP\Q3K,CXS3KQ;]Pyg0L3MPog0L4Wp+0CTS62p+0@bS3FQ62Q:VQ62PuQ62Q:VQ62Q05Q62Q6WQ62Q;@Q62Q8NQ62Q<IQ62Q:{Q62Q:zQ62Q:yQ62Q7FQ62Q1OQ62Q<:Q62Q;@Q62Q05Q62D_D1D1D1D1D1D1D1p+0>6S3IP\PoEUQ5geQ5gQ55Q3JQ55Q;bQ=5P3Q3K,bXP:Q9VEhW5Q6{p+0EES3KP3PTQ3MQ3WPGQ3FQ3W7aTdO4b2Q55Q3MQ3F32Q6FQ3MQ6FQ;cQ0qP3P:Q9WDuW5Q;bQ0zQ76Q;bQ57Q76Q;bQ0bQ76Q;bQ<{Q76Q0YQ0bQ;[Q3?Q1:Q3MP:P:Q0bQ<B/5OS0YQ3W36X9<PcQ6U,53S0bQ<Bp+08US3J/03S3B3TX;2Q9:Q<gQ0>Q7sQ0UQ06Q8CQ1=P[PbP6Q0RQ=@Q9:Q9:Q:gG3P[PbQ1xQ<9Q<@PcPcPGG3EFPVPRP{P|PEQ;YPrPEPEQ6YQ<8P1GJP}PCb8b6b7X12X:IAdS3KS<8Q=PP8PZP7CK[^12^:IP3Q06Q:LQ1PO3b0Q<AQ4sG4Q3FQ6|DAQ03p+08TS06Q3F36eQ:oQ8pD7p+0>DS1=P:Q0YQ2>'0X9<Q9:Q9oQ;~Q;{Q<0Q8nQ;TQ;TQ;SQ9SQ<uP3Q9AQ5FO2S9Sb0b3b4Q<AQ4sG4Q6AeQ:oQ8pD7GGE<Q57Q5KQ<JQ4vQ3MP:P:Q03Q<F/5OS4sQ3W36X9<PcQ0bQ<Fp+08RS03P3C]X;2Q:HQ<gQ75Q6XQ<dQ4wQ8@Q8UP[PbP6Q0RQ=@Q:HQ:HQ:9G3P[PbQ::Q;7Q<=PcPcPGG3EFPVPRP{P|PEQ;YPrPEPEQ6YQ2wP1GJP}PCb8b6b7X12X:IQ<8Q=PP8P?P7CK[^12^:IP3Q4wQ:LQ1PO3b0Q8qQ16G4Q3FQ6|DAQ0eQ1RQ3F36eQ6WQ5;D7Q1=P:Q4sQ2>'0X9<Q:HQ9oQ0tQ;uQ7cQ8nQ;TQ;TQ;SQ:oQ9oQ9Sb0b3b4Q8qQ16G4Q6>eQ6WQ5;D7GGE<Q0zQ;ZQ5@Q1NQ3MP:P:Q0eQ0AQ3W36X9<PcQ0bQ<:p+08OS0eP3C]X;2Q:aQ<gQ8Hp+0:NS0z':Q8<p+0:MS16':Q8HQ0zQ8<Q16P[PbP6Q0RQ=@Q:aQ:aQ:3G3P[PbQ:6Q:4Q<5PcPcPGG3EFPVPRP{P|PEQ;YPrPEPEQ6YP_P1GJP}PCb8b6b7X12X:IQ<8Q=PP8P^P7CK[^12^:IP3Q0zQ:LQ1PO3b0Q8DQ1?G4Q3FQ6|DAQ;sQ1HQ3F36eQ77Q8oD7Q1=P:Q0AQ2>'0X9<Q:aQ9oQ4qQ2HQ09Q8nQ;TQ;TQ;SQ78Q30Q9Sb0b3b4Q8DQ1?G4Q6ieQ77Q8oD7GGE<Q=5Q3MP:Q5KQ6]Q2pQ3MP:P:Q;sQ<</5OS3MQ3W36X9<PcQ0bQ<<Q=T3TX;2Q2AQ<gQ1kp+0:LS0b':S=TQ:`p+0:KR_':S6iQ1kQ0bQ:`P_P[PbP6Q0RQ=@Q2AQ2AQ:dG3P[PbQ1fQ:8Q8mPcPcPGG3EFPVPRP{P|PEQ;YPrPEPEQ6YPHP1GJP}PCb8b6b7X12X:IQ<8Q=PP8PYP7CK[^12^:IP3Q0bQ:LQ1PO3b0Q8GQ4pG4Q3FQ6|DAQ0dQ1[Q3F36eQ6WQ5;D7Q1=P:Q3MQ2>'0X9<Q2AQ9oQ29Q8WQ7PQ8nQ;TQ;TQ;SQ77Q<oQ9Sb0b3b4Q8GQ4pG4Q6eeQ6WQ5;D7GGGoQ3WP3E?b2Q4HP3E<b<%tyMArQ0ap+0EDRGP3PTQ3OQ:MQ3N#>PTQ3OPTQ:MCIdO4b2Q2WPTQ3NP>Q3N,NTdQ3WDOQ55Q3OQ55PFQ4MP3Q=5Q9AQ5ZEHW5PFQ5YQ3OQ50Q0^D8PFQ5YQ:DQ50Q0^D8Q5[Q64PFP4Q5YQ3OQ50Q0^g0L5aPxPWQ0\g0L6kPog0L85Q4;Q4@Q6FPyQ6FQ4N/EW-0i3$0pW5Po20iy0$0pdQ47P3E<b<N>1AQ6{Q3KP3PTQ3UQ:FQ3T#>PTQ3UPTQ:FCIdO4b2Q55PTQ3TP>Q3T,NTdQ:DDOQ6FQ3UQ6FPFQ4NP3Q0qQ;:Q5^EHW5PFQ4MQ3UQ=5Q9AD8PFPBQ2w,9Np+0CDS5^Q4MQ5gn0100000020000p+0@^S0qQ=5Q9AD8Q5ZQ:pPFP4Q4MQ3UQ=5Q9Ag0L9?P\PxQ3XQ;]Q1Yg0L:IPog0L;SQ4<Q4AQ2wPyQ2wQ;dQ53P3p+0@_S3UP;Q9VEhW5Q55p+0EGRcP3PTQ3ZQ0qQ0RQ<1Q0q7aTdO4b2Q2wQ3ZQ<132P9Q3ZQ;eQ4|P3P;Q9WDuX59Q;dQ=^Q76Q;dQ0PQ76Q;dQ;sQ76Q;dQ8]Q3ZP;Q76Q5PQ;sQ3:Q8]Q94Q3ZP;P:Q;sQ6_Q0q36X9<PdQ3;,53S;sQ<Dp+08WS5P/03S763TX;2Q1WQ<]Q=TQ6iQ1kQ0bQ:`P_P[PGQ=SQ=HQ=GQ1WQ1WQ1xG3P[PGQ99Q97Q<BPdPdQ0RG3EFPVPRP{P|PEQ;[PrPEPEQ<gQ2MP1GJP}PCb8b6b7X12X:IAdS3KR_P6P8PZP7CK[^12^:IP3Q0bQ9AQ1QO3b0Q<CQ1?G4Q<1Q6|DAQ0dp+08VS0bQ<136eQ0FQ8rD7Q2CP:Q6_Q2O'0X9<Q1WQ:1Q8>Q<2Q=NQ;VQ;UQ;UQ8nQ6:Q4oP3Q;9Q5OO2S5Ob0b3b4Q<CQ1?G4Q6HeQ0FQ8rD7GGGyQ0PQ=bQ<MQ85Q3ZP;P:Q0dQ<H/5OS1?Q0q36X9<PdQ;sQ<HQ06/03S0d3TX;2Q:JQ<]Q9yQ8R':Q;tQ7n':Q9yQ8RQ;tQ7nP[PGQ=SQ=HQ=GQ:JQ:JQ:gG3P[PGQ<9Q1NQ<@PdPdQ0RG3EFPVPRP{P|PEQ;[PrPEPEQ<gQ34P1GJP}PCb8b6b7X12X:IP6P8P?P7CK\_^12^:IP3Q8RQ9AQ1QO3b0Q<GQ4pG4Q<1Q6|DAQ=Kp+08SS8RQ<136eQ5AQ5:D7Q2CP:Q1?Q2O'0X9<Q:JQ:1Q8eQ;xQ<0Q;VQ;UQ;UQ8nQ0FQ:1Q5Ob0b3b4Q<GQ4pG4Q6EeQ5AQ5:D7GGE<Q=^Q;]Q6WQ1:Q3ZP;P:Q=KQ3MQ0q36X9<PdQ;sQ<<Q393TX;2Q9:Q<]Q7Dp+0:HS39':Q8:p+0:GS=^':S6EQ7DQ39Q8:Q=^P[PGQ=SQ=HQ=GQ9:Q9:Q:6G3P[PGQ:9Q:8Q<:PdPdQ0RG3EFPVPRP{P|PEQ;[PrPEPEQ<gQ24P1GJP}PCb8b6b7X12X:IP6P8P^P7CK\_^12^:IP3Q39Q9AQ1QO3b0Q8GQ14G4Q<1Q6|DAQ5JQ=QQ<136eQ:lQ8pD7Q2CP:Q3MQ2O'0X9<Q9:Q:1Q;rQ;pQ7cQ;VQ;UQ;UQ8nQ:oQ<uQ5Ob0b3b4Q8GQ14G4Q6AeQ:lQ8pD7GGE<Q53Q3ZP;Q=bQ5;Q4vQ3ZP;P:Q5JQ8jQ0q36X9<PdQ;sQ<=Q=QP3C]X;2Q:HQ<]Q89Q;P':S;sQ8FQ8P':S3ZQ89Q;PQ8FQ8PP[PGQ=SQ=HQ=GQ:HQ:HQ:3G3P[PGQ:4Q::Q<5PdPdQ0RG3EFPVPRP{P|PEQ;[PrPEPEQ<gPHP1GJP}PCb8b6b7X12X:IP6P8PYP7CK\_^12^:IP3Q;PQ9AQ1QO3b0Q8lQ1FG4Q<1Q6|DAQ=`Q0eQ<136eQ5AQ5:D7Q2CP:Q8jQ2O'0X9<Q:HQ:1Q7yQ;lQ09Q;VQ;UQ;UQ8nQ:lQ9oQ5Ob0b3b4Q8lQ1FG4Q6>eQ5AQ5:D7GGGoQ0qP3E?b2Q5dP3E<b<Q04NA1@Q2Wp+0EFS6>P3PTQ0=Q3UQ0f#>PTQ0=PTQ3UCIdO4b2Q6FPTQ0fP>Q0f,NTdQ0qDOQ2wQ0=Q2wPFQ5dP3Q53Q;9Q5]EHW5Q8hQ04P9Q3^PFQ4RP\P3Q0=Q4|Q;8Q1aGeX59PFQ5YQ0=Q53Q;9D8PFQ5YQ04Q53Q;9D8Q5]Q9UPFP4Q5YQ0=Q53Q;9g0L<]P\PWQ3[g0L=gPog0L?1p+0CXR_Q:GP_Q3FP_Q:OP_Q:ZP_Q:VP_Q:ZP_Q<HP_Q5EP_Q;DP_Q:kP_Q:mP_Q5lP_Q9=P_Q:}P_Q:CP_Q0ZP_Q<=P_Q;DP_Q<HP_D_D1D1D1D1D1D1D1D1Q8ZP\PoEUQ3{eQ3{Q34Q3^Q34Q4N/EW-0z3$0ZW5Q04Q47P3E<b<N>1?Q6Fp+0EHR_P3PTQ3`Q6qQ3_#>PTQ3`PTQ6qCIdO4b2P9PTQ3_P>Q3_,NTdQ04DOQ34Q3`Q34PFQ4NP3Q56Q4fQ1cEHW5PFQ4MQ3`Q4|Q;8D8PFPBQ6U,9Np+0CGS3_Q4MQ3vn0100000020000Q:EQ4|Q;8D8Q1aQ9VPFP4Q4MQ3`Q4|Q;8g0L@;P\PxQ3bQ4;Q4<g0LAEPog0LBOp+0CYR6p+0@[S3`P6Q3WP6Q:PP6Q:[P6Q:WP6Q:[P6Q<JP6Q=bP6Q;EP6Q:nP6Q:uP6Q;0P6Q5lP6Q9=P6Q;1P6Q;<P6Q<?P6Q;EP6Q<JP6D_D1D1D1D1D1D1D1D1Q8[PxPoEUQ3{eQ3{Q6UPyQ6UQ;gQ6nP3Q:GP:Q48EhW5P9p+0EJR6P3PTQ3dQ:EQ=Wp+0@XRdQ:E7aTdO4b2Q6UQ3d;2dQ3;Q3dQ3;Q;iQ59P3P:Q4;DuW5Q;gQ50Q42Q;gQ1}Q42Q;gQ=KQ42Q;gQ8_Q3dP:Q42Q0XQ=KQ;bQ8_Q:HQ3dP:P:Q=KQ8q/5OS0XQ:E36X9<PeQ3K,53S=KQ8qp+08ZS3F/03S533TX;2Q0^Q<`Q6EQ;sQ8:Q=^Q89Q;PP[PcQ=EQ1gQ=ZQ0^Q0^Q;7G3P[PcQ1NQ2pQ79PePeQ=WG3EFPVPRP{P|PEQ6sPrPEPEQ<]Q6{P1GJP}PCb8b6b7X12X:IAdS3KS6{Q=RP8PZP7CK[^12^:IP3Q=^Q;8Q5NO3b0Q05Q4pG4PdQ04DAQ5Jp+08YS=^;6deQ7:Q0CD7Q0jP:Q0XQ2W'0X9<Q0^p+0CBS;PQ<5Q8AQ0eQ;YQ;XQ;XQ;WQ0GQ2lP3Q2qQ1TO2S89b0b3b4Q05Q4pG4Q6TeQ7:Q0CD7GGGyQ1}Q5RQ63Q:aQ3dP:P:Q5JQ<M/5OS0CQ:E36X9<PeQ=KQ<MQ763TX;2Q:LQ<`Q3ZQ9TQ:~':Q8FQ8PQ9TQ:~P[PcQ=EQ1gQ=ZQ:LQ:LQ97G3P[PcQ99Q85Q<CPePeQ=WG3EFPVPRP{P|PEQ6sPrPEPEQ<]PbP1GJP}PCb8b6b7X12X:IQ6{Q=RP8P?P7CK[^12^:IP3Q8PQ;8Q5NO3b0Q<LQ14G4PdQ04DAQ=`Q0b;6deQ=bQ5AD7Q0jP:Q0CQ2W'0X9<Q:LQ;PQ<2Q;~Q1[Q;YQ;XQ;XQ;WQ7:Q;PQ89b0b3b4Q<LQ14G4Q6ReQ=bQ5AD7GGE<Q50Q;aQ5KQ2AQ3dP:P:Q=`Q<?/5OS14Q:E36X9<PeQ=KQ<?Q0d3TX;2Q9>Q<`Q86p+0:CS=`':Q88Q;K':Q86Q=`Q88Q;KP[PcQ=EQ1gQ=ZQ9>Q9>Q::G3P[PcQ<9Q:gQ8lPePeQ=WG3EFPVPRP{P|PEQ6sPrPEPEQ<]Q2gP1GJP}PCb8b6b7X12X:IQ6{Q=RP8P^P7CK[^12^:IP3Q=`Q;8Q5NO3b0Q<=Q1FG4PdQ04DAQ08Q8R;6deQ0FQ8sD7Q0jP:Q14Q2W'0X9<Q9>Q;PQ;xQ0tQ6\Q;YQ;XQ;XQ;WQ6:Q<nQ89b0b3b4Q<=Q1FG4Q6LeQ0FQ8sD7GGE<Q6nQ3dP:Q5RQ6WQ94Q3dP:P:Q08Q<A/5OS3dQ:E36X9<PeQ=KQ<AQ8RP3C]X;2Q1WQ<`Q7~p+0:AS<`':Q82Q8S':S=KQ7~Q<`Q82Q8SP[PcQ=EQ1gQ=ZQ1WQ1WQ:8G3P[PcQ:9Q1xQ8GPePeQ=WG3EFPVPRP{P|PEQ6sPrPEPEQ<]PHP1GJP}PCb8b6b7X12X:IQ6{Q=RP8PYP7CK[^12^:IP3Q<`Q;8Q5NO3b0Q<@Q13G4PdQ04DAQ1GQ03;6deQ=bQ5AD7Q0jP:Q3dQ2W'0X9<Q1WQ;PQ;pQ4qQ4zQ;YQ;XQ;XQ;WQ0FQ4oQ89b0b3b4Q<@Q13G4Q6HeQ=bQ5AD7GGGoQ:EP3E?b2Q47P3E<b<Q4<#tMArQ2wp+0EIS6HP3PTQ3fQ:GQ3e#>PTQ3fPTQ:GCIdO4b2Q34PTQ3eP>Q3e,NTdQ:EDOQ6UQ3fQ6UPFQ3zP3Q6nQ2qQ1^EHW5PFQ3wQ3fQ56Q4fD8PFPBQ3;,9NQ9<Q3wQ3vn0100000020000Q:AQ56Q4fD8Q1cQ9WPFP4Q3wQ3fQ56Q4fg0LCYPMPxQ0L,CXS3fQ4<Q3{g0LDcPog0LEmp+0CZS3eQ4;Q3ep+0@\S89Q3eQ:MQ3eQ:QQ3eQ:\Q3eQ:XQ3eQ:\Q3eQ<LQ3eQ5_Q3eQ;FQ3eQ1CQ3eQ:vQ3eQ;2Q3eQ;0Q3eQ5lQ3eQ6OQ3eQ;=Q3eQ<@Q3eQ;FQ3eQ<LQ3eFqD1D1D1D1D1D1D1D1Q8\PxPoEUQ3reQ3rQ3;PyQ3;Q;iQ59P3Q3f,bXS4oP:Q4;EhW5Q34p+0EKReP3PTQ3hQ0L,DyS0FQ1]p+0@WS4zQ0F7aTdO4b2Q3;Q3hQ0F32PbQ3hQ;jQ4}P3P:Q4<DuX5bQ;iQ50Q42Q;iQ1}Q42Q;iQ1GQ42Q;iQ8`Q3hP:Q42Q5QQ1GQ;cQ8`Q9:Q3hP:P:Q1GQ4s;6dX9<PfQ6>,53S1GQ<Fp+08[S4q/03S3d3TX;2Q9AQ17Q=KQ8=Q;G':Q82Q8SQ8=Q;GP[P_PLQ==Q<_Q9AQ9AQ2pG3P[P_Q4vQ1NQ05PfPfQ1]G3EFPVPRP{P|PEQ;aPrPEPEQ=ZQ2WP1GJP}PCb8b6b7X12X:IAdS3KS;GQ1gP8PZP7CK[^12^:IP3Q8SQ4fQ1TO3b0Q8qQ13G4Q4zQ;zDAQ5DQ3FQ4z36eQ0GQ0`D7Q0jP:Q4sQ55'0X9<Q9AQ2lQ8DQ<5Q=QQ;ZQ;YQ;YQ;XQ93Q5^P3Q=cQ5SO2S5Sb0b3b4Q8qQ13G4Q6VeQ0GQ0`D7GGGyQ1}Q5eQ<TQ:HQ3hP:P:Q5DQ<O/5OS13;6dX9<PfQ1GQ<Op+08XS5D/03S4s3TX;2Q0^Q17Q83p+0:>S8S':Q7wp+0:=S82':Q83Q8SQ7wQ82P[P_PLQ==Q<_Q0^Q0^Q99G3P[P_Q;7Q94Q<DPfPfQ1]G3EFPVPRP{P|PEQ;aPrPEPEQ=ZQ3EP1GJP}PCb8b6b7X12X:IQ;GQ1gP8P?P7CK[^12^:IP3Q8SQ4fQ1TO3b0Q<MQ15G4Q4zQ;zDAQ=LQ5PQ4z36eQ5_Q5KD7Q0jP:Q13Q55'0X9<Q0^Q2lQ8>Q<2Q1HQ;ZQ;YQ;YQ;XQ0GQ2lQ5Sb0b3b4Q<MQ15G4Q6TeQ5_Q5KD7GGE<Q50Q;bQ5EQ:aQ3hP:P:Q=LQ6S;6dX9<PfQ1GQ<@Q3B3TX;2Q:LQ17Q9QQ7m':Q9PQ7l':Q9QQ7mQ9PQ7lP[P_PLQ==Q<_Q:LQ:LQ:gG3P[P_Q1xQ<9Q<=PfPfQ1]G3EFPVPRP{P|PEQ;aPrPEPEQ=ZQ=FP1GJP}PCb8b6b7X12X:IQ;GQ1gP8P^P7CK[^12^:IP3Q7mQ4fQ1TO3b0Q<?Q11G4Q4zQ;zDAQ7OQ06Q4z36eQ6:Q8tD7Q0jP:Q6SQ55'0X9<Q:LQ2lQ8eQ;xQ=NQ;ZQ;YQ;YQ;XQ68Q;PQ5Sb0b3b4Q<?Q11G4Q6ReQ6:Q8tD7GGE<Q59Q3hP:Q5eQ5TQ2AQ3hP:P:Q7OQ0Y;6dX9<PfQ1GQ<BQ0d3TX;2Q9>Q17Q7}p+0::S1G':S0dQ7|Q7g':S3hQ7}Q1GQ7|Q7gP[P_PLQ==Q<_Q9>Q9>Q:9G3P[P_Q::Q97Q<<PfPfQ1]G3EFPVPRP{P|PEQ;aPrPEPEQ=ZPHP1GJP}PCb8b6b7X12X:IQ;GQ1gP8PYP7CK[^12^:IP3Q1GQ4fQ1TO3b0Q<AQ1BG4Q4zQ;zDAQ9OQ8RQ4z36eQ5_Q5KD7Q0jP:Q0YQ55'0X9<Q9>Q2lQ;rQ;pQ<0Q;ZQ;YQ;YQ;XQ6:Q<nQ5Sb0b3b4Q<AQ1BG4Q6LeQ5_Q5KD7GGGoQ0FP3E?b2Q3vP3E<b<Q3{#tMArP9P6P3PTQ5?Q4zQ5>#>PTQ5?PTQ4zCIdO4b2Q6UPTQ5>P>Q5>,NTdQ:ADOQ3;Q5?Q3;PFQ3zP3Q59Q=cQ1_EHW5PFQ3wQ5?Q6nQ2qD8PFQ3wQ;wQ6nQ2qD8Q1^Q9XPFP4Q3wQ5?Q6nQ2qg0LG7P\PMQ3ig0LHAPog0LIKp+0C[RfQ4;PfQ4<PfQ<1PfQ:NPfQ:RPfQ:]PfQ:YPfQ:]PfQ<MPfQ5LPfQ;HPfQ5|PfQ:wPfQ1APfQ;2PfQ;0PfQ0ZPfQ;>PfQ<APfQ;HPfQ<MPfD_D1D1D1D1D1D1D1D1D1Q1jP\PoEUQ3meQ3mPbQ4AQ=0-033X5bp+0C\RfQ4<PfQ3{PfQ0qPfQ:OPfPuPfQ66PfQ:ZPfQ66PfQ<OPfQ5RPfQ;IPfQ<IPfQ:xPfQ7FPfQ1APfQ;2PfQ;<PfQ1XPfQ<BPfQ;IPfQ<OPfFqD1D1D1D1D1D1D1D1D1RfQ8^PMPoH0@Q3meQ3mQ3EQ5gQ3EQ470033W5Q5g$0oQ=0P3E<b<Q=0P3E<b<N>0TQ34PeP3PTQ3kP@Q3j#>PTQ3kPTP@CIdO4b2Q3;PTQ3jP>Q3j,NTdQ;wDOPbQ3kPFQ3|P3Q4}Q2uQ1nEHX5bPFQ3zQ3kQ59Q=cD8PFPBQ3E,9NQ9BQ3zQ3Gn0100000020000Q:@Q59Q=cD8Q1_Q9ZPFP4Q3zQ3kQ59Q=cg0LJUP\PxQ1iQ3gQ2;g0LK_Pog0LLiPfQ8^PxPoH0@Q3leQ3lQ3EPyQ3Ep+0BERfQ6lP3Q;WP:Q7uEhW5Q3;p+0EMS7uP3PTQ3nQ:AQ==Q:@Q:A7aTdO4b2Q3EQ3nQ:@32PGQ3np+0BFS3kQ6jP3P:Q3gDuX5GPfQ=5Q3aPfQ5CQ3aPfQ7OQ3aPfQ8[Q3nP:Q3aQ5sQ7OQ;eQ8[Q1WQ3nP:P:Q7OQ1?Q:A36X9<Pg153_S7OQ<Hp+08]S3j/03S:O3TX;2Q;9Q=]Q0dQ3hQ7}Q1GQ7|Q7gP[P6Q=AQ=<Q<YQ;9Q;9Q4vG3P[P6Q85Q1:Q<FPgPgQ==G3EFPVPRP{P|PEQ;cPrPEPEQ17Q6FP1GJP}PCb8b6b7X12X:IAdS3KS7gPLP8PZP7CK[^12^:IP3Q1GQ=cQ1UO3b0Q<GQ11G4Q:@P@DAQ9Op+08\S1GQ:@36eQ<NQ8vD7Q2]P:Q1?Q2w'0X9<Q;9Q<rQ8GQ<:Q03Q;]Q;[Q;[Q;ZQ64Q9<P3Q2ZQ5[O2S03b0b3b4Q<GQ11G4Q6^eQ<NQ8vD7GGGyQ5CQ5hQ7<Q:JQ3nP:P:Q9OQ63/5OS8vQ:A36X9<PgQ7OQ63Q533TX;2Q;:Q=]Q7{Q7k':Q7zQ7e':Q7{Q7kQ7zQ7eP[P6Q=AQ=<Q<YQ;:Q;:Q2pG3P[P6Q1NQ:aQ05PgPgQ==G3EFPVPRP{P|PEQ;cPrPEPEQ17Q3KP1GJP}PCb8b6b7X12X:IQ7gPLP8P?P7CK[^12^:IP3Q7kQ=cQ1UO3b0Q<QQ1BG4Q:@P@DAQ7MQ=^Q:@36eQ5RQ=bD7Q2]P:Q8vQ2w'0X9<Q;:Q<rQ8AQ8mQ=QQ;]Q;[Q;[Q;ZQ<NQ<rQ03b0b3b4Q<QQ1BG4Q6ZeQ5RQ=bD7GGE<Q=5Q;dQ5_Q9:Q3nP:P:Q7MQ0YQ:A36X9<PgQ7OQ<BQ763TX;2Q9AQ=]Q7xQ8L':Q3cQ7a':Q7xQ8LQ3cQ7aP[P6Q=AQ=<Q<YQ9AQ9AQ1xG3P[P6Q99Q97Q<@PgPgQ==G3EFPVPRP{P|PEQ;cPrPEPEQ17Q2>P1GJP}PCb8b6b7X12X:IQ7gPLP8P^P7CK[^12^:IP3Q8LQ=cQ1UO3b0Q<AQ10G4Q:@P@DAQ73Q0bQ:@36eQ7:Q0`D7Q2]P:Q0YQ2w'0X9<Q9AQ<rQ;~Q;{Q1HQ;]Q;[Q;[Q;ZQ0GQ5^Q03b0b3b4Q<AQ10G4Q6VeQ7:Q0`D7GGE<Q6lQ3nP:Q5hQ5KQ:HQ3nP:P:Q73Q6_Q:A36X9<PgQ7OQ<DQ0bP3C]X;2Q0^Q=]Q9NQ7j':Q80Q7f':S=]Q9NQ7jQ80Q7fP[P6Q=AQ=<Q<YQ0^Q0^Q:gG3P[P6Q<9Q;7Q<=PgPgQ==G3EFPVPRP{P|PEQ;cPrPEPEQ17PHP1GJP}PCb8b6b7X12X:IQ7gPLP8PYP7CK[^12^:IP3Q7jQ=cQ1UO3b0Q<CQ4uG4Q:@P@DAQ7LQ3JQ:@36eQ5RQ=bD7Q2]P:Q6_Q2w'0X9<Q0^Q<rQ0tQ;uQ=NQ;]Q;[Q;[Q;ZQ7:Q2lQ03b0b3b4Q<CQ4uG4Q6TeQ5RQ=bD7GGGoQ:AP3E?b2Q3rP3E<b<Q2;#tMArQ6Up+0ELS6TP3PTQ3pQ:AQ3o#>PTQ3pPTQ:ACIdO4b2PbPTQ3oP>Q3o,NTdQ:@DOQ3EQ3pQ3EPFQ6QP3Q6lQ2ZQ1mEHW5PFQ3YQ3pQ4}Q2uD8PFPB19NGp+0CIS3oQ3YQ3Gn0100000020000Q:>Q4}Q2uD8Q1nQ9[PFP4Q3YQ3pQ4}Q2ug0LN3PMPxQ2sQ3\Q3lg0LO=Pog0LPGp+0C]RgQ3gPgQ3{PgQ4@PgQ3UPgQ:PPgQ:SPgQ8NPgQ:[PgQ8NPgQ<QPgQ5ePgQ;JPgQ60PgQ:yPgQ<^PgQ7FPgQ1APgQ;=PgQ;?PgQ<CPgQ;JPgQ<QPgFqD1D1D1D1D1D1D1D1D1Q0hPxPoEUQ3ReQ3RPGPyQ3kQ6jP3Q60P:Q3gEhX5GPbp+0ENRyP3PTQ3sQ:?Q00Q:>Q:?7aTdO4b2Q3sQ:>52GQ3KQ3sQ3KQ<6Q51P3P:Q3\DuW5Q3kQ=5Q3aQ3kQ5CQ3aQ3kQ7LQ3aQ3kQ8\Q3sP:Q3aQ5sQ7LQ<4Q8\Q9>Q3sP:P:Q7LQ<J/5OS5sQ:?36X9<PhQ6H,53S7LQ<Jp+08^S3a/03S3p3TX;2Q;8Q<\Q=]Q9MQ7\':Q80Q7fQ9MQ7\P[PeQ=CQ0:Q=VQ;8Q;8Q1:G3P[PeQ94Q85Q<GPhPhQ00G3EFPVPRP{P|PEQ;dPrPEPEQ<YQ2wP1GJP}PCb8b6b7X12X:IAdS3KRgQ=<P8PZP7CK[^12^:IP3Q7fQ2uQ5[O3b0Q<HQ4uG4Q:>Q;wDAQ=[Q3jQ:>36eQ64Q8wD7Q2]P:Q5s/09X9<Q;8Q9<Q<<Q8GQ8RQ3:Q;]Q;]Q;[Q:pQ3_P3Q2iQ5ZO2S5Zb0b3b4Q<HQ4uG4Q6beQ64Q8wD7GGGyQ5CQ5XQ0IQ1WQ3sP:P:Q=[Q<T/5OS8wQ:?36X9<PhQ7LQ<TQ3d3TX;2Q;9Q<\Q9LQ7_':Q7vQ7d':Q9LQ7_Q7vQ7dP[PeQ=CQ0:Q=VQ;9Q;9Q1NG3P[PeQ4vQ:HQ8qPhPhQ00G3EFPVPRP{P|PEQ;dPrPEPEQ<YQ6>P1GJP}PCb8b6b7X12X:IQ=<P8P?P7CK\g^12^:IP3Q7_Q2uQ5[O3b0Q63Q0|G4Q:>Q;wDAQ72Q3FQ:>36eQ5eQ5_D7Q2]P:Q8w/09X9<Q;9Q9<Q<5Q8AQ1RQ3:Q;]Q;]Q;[Q64Q9<Q5Zb0b3b4Q63Q0|G4Q6^eQ5eQ5_D7GGE<Q=5Q;eQ5LQ:JQ3sP:P:Q72Q<C/5OS5LQ:?36X9<PhQ7LQ<CQ4s3TX;2Q;:Q<\Q9KQ7]':S4sQ81Q7b':S=5Q9KQ7]Q81Q7bP[PeQ=CQ0:Q=VQ;:Q;:Q97G3P[PeQ;7Q99Q<APhPhQ00G3EFPVPRP{P|PEQ;dPrPEPEQ<YQ2MP1GJP}PCb8b6b7X12X:IQ=<P8P^P7CK\g^12^:IP3Q7]Q2uQ5[O3b0Q<BQ1>G4Q:>Q;wDAQ7EQ5PQ:>36eQ0GQ8uD7Q2]P:Q5L/09X9<Q;:Q9<Q<2Q;~Q0eQ3:Q;]Q;]Q;[Q93Q<rQ5Zb0b3b4Q<BQ1>G4Q6ZeQ0GQ8uD7GGE<Q6jQ3sP:Q5XQ5EQ9:Q3sP:P:Q7EQ79/5OS3sQ:?36X9<PhQ7LQ79Q763TX;2Q9AQ<\Q9JQ7^':S7LQ9IQ7Y':S76Q9JQ7^Q9IQ7YP[PeQ=CQ0:Q=VQ9AQ9AQ<9G3P[PeQ1xQ2pQ<?PhPhQ00G3EFPVPRP{P|PEQ;dPrPEPEQ<YPHP1GJP}PCb8b6b7X12X:IQ=<P8PYP7CK\g^12^:IP3Q7^Q2uQ5[O3b0Q<DQ0{G4Q:>Q;wDAQ7HQ0bQ:>36eQ5eQ5_D7Q2]P:Q3s/09X9<Q9AQ9<Q;xQ0tQ1[Q3:Q;]Q;]Q;[Q0GQ5^Q5Zb0b3b4Q<DQ0{G4Q6VeQ5eQ5_D7GGGoQ:?P3E?b2Q3GP3E<b<Q3l#tMArQ3;Q7uP3PTQ5IQ:?Q5H#>PTQ5IPTQ:?CIdO4b2Q3EPTQ5HP>Q5H,NTdQ:>DOPGQ5IPFQ6QP3Q6jQ2iQ7pEHX5GPFQ3YQ5IQ6lQ2ZD8PFQ3YQ95Q6lQ2ZD8Q1mQ9\PFP4Q3YQ5IQ6lQ2Zg0LQQP\PMQ3ig0LR[Pog0LSeQ5=Q3gQ5=Q3\Q5=Q4@Q5=Q4AQ5=Q:DQ5=Q:QQ5=Q:TQ5=Q:hQ5=Q:\Q5=Q:hQ5=Q63Q5=p+06=S3gQ5=Q;LQ5=Q=BQ5=Q:zQ5=Q<bQ5=Q<^Q5=Q7FQ5=Q;>Q5=Q;@Q5=Q<DQ5=Q;LQ5=Q63Q5=D_D1D1D1D1D1D1D1D1D1D1Q:qP\PoEUQ3HeQ3HQ3KQ7tQ3KQ3S-033W5Q6CQ3\Q6CQ2;Q6CQ4AQ6CQ5gQ6CQ:FQ6CQ:RQ6CQ:UQ6CQ:iQ6CQ:]Q6CQ:iQ6CQ<TQ6CQ5hQ6CQ;MQ6CQ:jQ6CQ:{Q6CQ1OQ6CQ<bQ6CQ<^Q6CQ1XQ6CQ;AQ6CQ79Q6CQ;MQ6CQ<TQ6CD_D1D1D1D1D1D1D1D1D1D1Q:rPMPoEUQ3HeQ3HQ6>Q3qQ6>Q3r0033W5Q3q$0oQ3SP3E<b<Q3SP3E<b<N>0TPbPyP3PTQ3uQ98Q3t#>PTQ3uPTQ98CIdO4b2PGPTQ3tP>Q3t,NTdQ95DOQ3KQ3uQ3KPFQ8aP3Q51p+0=mS51Q1lEHW5PFQ6QQ3uQ6jQ2iD8PFPBQ6>,9NQ0;Q6QQ3Pn0100000020000Q:=Q6jQ2iD8Q7pQ9]PFP4Q6QQ3uQ6jQ2ig0LToR9P\Q3@g0LV9%m9g0LWCN<0lQ3Ep+0EOR9P3PTQ3yQ:>Q3x#>PTQ3yPTQ:>CIdO4b2Q3KPTQ3xP>Q3x,NTdQ:=DOQ6>Q3yQ6>PFQ3SP3Q6hQ;;Q26EHW5PGp+0EPRgP3PTQ3~Q:>Q3}#>PTQ3~PTQ:>CIdO4b2Q6>Q3~Q:=32PcQ3~PFQ3]P\P3Q3yQ54Q<{Q7oGeX5cPFQ6QQ3yQ6hQ;;D8PFPB19N_p+0CNS3]Q6QQ3Rn0100000020000Q:=Q6hQ;;D8Q26Q9_PFP4Q6QQ3yQ6hQ;;g0LXMPxP\Q41,CXS41PfPzg0LYWPog0LZap+0CaRhQ:<PhQ3lPhQ3mPhQ47PhQ5dPhQ3WPhQ:SPhQ:WPhQ:kPhQ8NPhQ:kPhQ7<PhQ5bPhQ;OPhQ:uPhQ:}PhQ;1PhQ:CPhQ1OPhQ;@PhQ;CPhQ8qPhQ;OPhQ7<PhFqD1D1D1D1D1D1D1D1D1D1Q:tP\PoEUQ37eQ37P_Q3~p+0BJS3~Q57P3Q41,bXP:Q9cEhX5_Q6>p+0ERRXP3PTQ43Q:=Q00Q:<Q:=7aTdO4b2Q43Q:<52_Q6HQ43Q6HQ6MQ0PP3P:P`DuW5Q3~Q4|Q8oQ3~Q5;Q8oQ3~Q=[Q8oQ3~Q8[Q8oQ0cQ=[PfQ:qQ;:Q43P:P:Q=[Q<Q/5OS0cQ:=36X9<PiQ7u,53S=[Q<Qp+08bS8o/03S413TX;2Q2uQ<\Q4sQ=5Q9KQ7]Q81Q7bP[P9Q=CQ0:Q=VQ2uQ2uQ:aG3P[P9Q9:Q:HQ<MPiPiQ00G3EFPVPRP{P|PEQ;iPrPEPEQ<YQ3;P1GJP}PCb8b6b7X12X:IAdS3KS3;Q=<P8PZP7CK[^12^:IP3Q7]Q;;Q1aO3b0Q<OQ4uG4Q:<P@DAQ72p+08aS7]Q:<36eQ9VQ8yD7Q0iP:Q0c/0bX9<Q2uQ9BQ<@Q<?Q5PQ;cQ;bQ;bQ;aQ9Wp+0CKS9WP3PQQ1cO2S1cb0b3b4Q<OQ4uG4Q6oeQ9VQ8yD7GGE<Q5;Q6GQ0JQ9AQ43P:P:Q72Q<X/5OS4uQ:=36X9<PiQ=[Q<Xp+08_S72P3C]X;2Q=cQ<\Q7LQ76Q9JQ7^Q9IQ7YP[P9Q=CQ0:Q=VQ=cQ=cQ94G3P[P9Q2AQ9>Q<JPiPiQ00G3EFPVPRP{P|PEQ;iPrPEPEQ<YP6P1GJP}PCb8b6b7X12X:IQ3;Q=<P8P?P7CK[^12^:IP3Q7^Q;;Q1aO3b0Q0IQ0|G4Q:<P@DAQ7EQ3aQ:<36eQ5bQ3gD7Q0iP:Q4u/0bX9<Q=cQ9BQ<<Q8GQ3JQ;cQ;bQ;bQ;aQ9VQ9BQ1cb0b3b4Q0IQ0|G4Q6meQ5bQ3gD7GGE<Q4|Q;jQ5hQ0^Q43P:P:Q7EQ0XQ:=36X9<PiQ=[Q8qQ1GP3C]X;2Q2qQ<\Q9HQ7[':Q9Gp+09jS7E':Q9HQ7[Q9GQ7EP[P9Q=CQ0:Q=VQ2qQ2qQ1NG3P[P9Q1:Q4vQ79PiPiQ00G3EFPVPRP{P|PEQ;iPrPEPEQ<YQ2WP1GJP}PCb8b6b7X12X:IQ3;Q=<P8P^P7CK[^12^:IP3Q7[Q;;Q1aO3b0Q05Q1>G4Q:<P@DAQ7HQ4qQ:<36eQ:pQ8xD7Q0iP:Q0X/0bX9<Q2qQ9BQ<5Q8AQ8RQ;cQ;bQ;bQ;aQ0HQ3oQ1cb0b3b4Q05Q1>G4Q6keQ:pQ8xD7GGE<Q57Q43P:Q6GQ5RQ:LQ43P:P:Q7HQ<G/5OS43Q:=36X9<PiQ=[Q<GQ3d3TX;2Q4fQ<\Q9FQ7S':S=[Q9Ep+09hS3d':S8xQ9FQ7SQ9EQ3dP[P9Q=CQ0:Q=VQ4fQ4fQ;7G3P[P9Q2pQ85Q<CPiPiQ00G3EFPVPRP{P|PEQ;iPrPEPEQ<YPHP1GJP}PCb8b6b7X12X:IQ3;Q=<P8PYP7CK[^12^:IP3Q7SQ;;Q1aO3b0Q<FQ0{G4Q:<P@DAQ71Q3FQ:<36eQ5bQ3gD7Q0iP:Q43/0bX9<Q4fQ9BQ<2Q;~Q1RQ;cQ;bQ;bQ;aQ:pQ<tQ1cb0b3b4Q<FQ0{G4Q6geQ5bQ3gD7GGGoQ:=P3E?b2Q6[P3E<b<%tzMArQ3Kp+0EQRiP3PTQ45Q:>Q44#>PTQ45PTQ:>CIdO4b2PcPTQ44P>Q44,NTdQ:=DOP_Q45PFQ3VP3Q57PQQ1hEHX5_PFQ3SQ45Q54Q<{D8PFQ3SPtQ54Q<{D8Q7oQ9`PFP4Q3SQ45Q54Q<{g0L[kPxPWQ0_Q4m#=+0bg0L]5Pog0L^?Q6aQ3CQ6HPzQ6HQ3G/EW-0i3$0pW5Po20iz0$0pdQ3HP3E<b<N>1AQ6>PXP3PTQ4:Q:;Q49#>PTQ4:PTQ:;CIdO4b2P_PTQ49P>Q49,NTdPtDOQ6HQ4:Q6HPFQ3GP3Q0PQ2hQ40EHW5PFQ3VQ4:Q57PQD8PFPB19N6Q;qQ3VQ37n0100000020000PpQ57PQD8Q1hQ9aPFP4Q3VQ4:Q57PQg0L_IP\PxQ3XQ3kQ1Yg0L`SPog0La]Q2}Q3DP6Pzp+0BLS1YQ1dP3Q:TP;P`EhX56P_p+0ETR0P3PTQ4=PtQ0:AapTtdO4b2Q4==26pPeQ4=Q<>Q1}P3P;Q9dDuX5eQ1YQ56Q8uQ1YQ5@Q8uQ1YQ7HQ8uQ1YQ:sQ4=P;Q8uQ5QQ7HQ<6Q:sQ;8Q4=P;P:Q7HQ8w;6tX9<Pj153yS7HQ<Tp+08dS5Q/03S8u3TX;2Q2iQ<VQ=[Q8xQ9FQ7SQ9EQ3dP[PiQ=:Q=9Q1rQ2iQ2iQ9:G3P[PiQ1WQ:JQ<QPjPjQ0:G3EFPVPRP{P|PEPfPrPEPEQ<\Q3EP1GJP}PCb8b6b7X12X:IAdS3KS3dQ=CP8PZP7CK[^12^:IP3Q7SPQQ1^O3b0Q63Q1>G4PpP@DAQ71p+08cS7S;6peQ9XQ8zD7Q0lP:Q8w/0GX9<Q2iQ2mQ<BQ<AQ=^Q;eQ;dQ;dQ;cQ9ZQ0;P3Q35Q1_O2S9Eb0b3b4Q63Q1>G4p+07;S9FeQ9XQ8zD7GGGyQ5@Q1pQ7@Q;9Q4=P;P:Q71Q0O/5OS8z;6tX9<PjQ7HQ0OQ7]/03S713TX;2Q2ZQ<VQ9Dp+09gS8x':Q9Cp+09fS=[':Q9DQ8xQ9CQ=[P[PiQ=:Q=9Q1rQ2ZQ2ZQ:aG3P[PiQ:HQ0^Q<MPjPjQ0:G3EFPVPRP{P|PEPfPrPEPEQ<\Q6TP1GJP}PCb8b6b7X12X:IQ3dQ=CP8P?P7CK[^12^:IP3Q8xPQQ1^O3b0Q0KQ0{G4PpP@DAQ7Gp+08`S8x;6peQ6IQ5XD7Q0lP:Q8z/0GX9<Q2ZQ2mQ<=Q8lQ5PQ;eQ;dQ;dQ;cQ9XQ2mQ9Eb0b3b4Q0KQ0{G4p+07:S=[eQ6IQ5XD7GGE<Q56Q3kQ5bQ;:Q4=P;P:Q7GQ43;6tX9<PjQ7HQ<GQ3p3TX;2Q2uQ<VQ:_p+09eS3p':Q9?Q7V':S56Q:_Q3pQ9?Q7VP[PiQ=:Q=9Q1rQ2uQ2uQ1:G3P[PiQ94Q85Q8qPjPjQ0:G3EFPVPRP{P|PEPfPrPEPEQ<\Q6FP1GJP}PCb8b6b7X12X:IQ3dQ=CP8P^P7CK[^12^:IP3Q3pPQQ1^O3b0Q<FQ2\G4PpP@DAQ7CQ3j;6peQ9UQ8yD7Q0lP:Q43/0GX9<Q2uQ2mQ<:Q8DQ3JQ;eQ;dQ;dQ;cQ9VQ9WQ9Eb0b3b4Q<FQ2\G4Q6oeQ9UQ8yD7GGE<Q1dQ4=P;Q1pQ3gQ9AQ4=P;P:Q7CQ5s;6tX9<PjQ7HQ<JQ:O3TX;2Q=cQ<VQ38Q7h':S<VQ9zQ7T':S7HQ38Q7hQ9zQ7TP[PiQ=:Q=9Q1rQ=cQ=cQ1NG3P[PiQ4vQ2AQ79PjPjQ0:G3EFPVPRP{P|PEPfPrPEPEQ<\PHP1GJP}PCb8b6b7X12X:IQ3dQ=CP8PYP7CK[^12^:IP3Q7hPQQ1^O3b0Q<HQ0yG4PpP@DAQ6}Q1G;6peQ6IQ5XD7Q0lP:Q5s/0GX9<Q=cQ2mQ8mQ8>Q8RQ;eQ;dQ;dQ;cQ9UQ9BQ9Eb0b3b4Q<HQ0yG4Q6meQ6IQ5XD7GGGoPtP3E?b2Q3LP3E<b<PqNA1@Pcp+0ESRjP3PTQ5WPtQ5V#>PTQ5WPTPtCIdO4b2Q6HPTQ5VP>Q5V,NTdPpDOP6Q5WPFQ3LP3Q1dQ35Q5jEHX56Q8tPqPeQ3^PFQ6QP\P3Q5WQ1}Q3?Q8OGeX5ePFQ3RQ5WQ1dQ35D8PFQ3RQ;wQ1dQ35D8Q5jQ9cPFP4Q3RQ5WQ1dQ35g0LbgP\PWQ3[g0Ld1Pog0Le;p+0CeR;Q:PP;Q:<P;Q:@P;Q3rP;Q=0P;Q5YP;Q4MP;Q:PP;Q:WP;Q:[P;Q<IP;Q:kP;Q<IP;Q0OP;Q5cP;Q;TP;Q:yP;Q;2P;Q;=P;Q;<P;Q0ZP;Q;DP;Q;HP;Q<JP;Q;TP;Q0OP;FqD1D1D1D1D1D1D1D1D1D1D1Q0jP\PoEUQ6ceQ6cQ6TQ3^Q6TQ3V/EW-0z3$0ZW5PqQ3HP3E<b<N>1?Q6Hp+0EURqP3PTQ4?P@Q4>#>PTQ4?PTP@CIdO4b2PePTQ4>P>Q4>,NTdQ;wDOQ6TQ4?Q6TPFQ3VP3Q5CQ8XQ7qEHW5PFQ3SQ4?Q1}Q3?D8PFPBQ7u,9NQ62Q3SQ2nn0100000020000PpQ1}Q3?D8Q8OP`PFP4Q3SQ4?Q1}Q3?g0LfEP\PxQ3bQ6aQ2}g0LgOPog0LhYQ<~Q:QQ<~Q:=Q<~Q:AQ<~Q=0Q<~Q3vQ<~Q4MQ<~Q4NQ<~Q:QQ<~Q:XQ<~Q:\Q<~Q60Q<~Q:nQ<~Q60Q<~Q0JQ<~Q1pQ<~Q8nQ<~Q:zQ<~Q1AQ<~Q;>Q<~Q;=Q<~Q;<Q<~Q;EQ<~Q;IQ<~Q<LQ<~Q8nQ<~Q0JQ<~FqD1D1D1D1D1D1D1D1D1D1D1Q2]PxPoEUQ6ceQ6cQ7uPzQ7uQ<EQ6]P3Q:PP:Q3<EhW5Pep+0EWR`P3PTQ4BPtQ=:AapTtdO4b2Q7uQ4B;2pPyQ4Bp+0BPS3<Q5GP3P:Q6aDuX5yQ<EQ59Q33Q<EQ6WQ33Q<EQ7GQ33Q<EQ2CQ4BP:Q33Q0WQ7GQ3~Q2CQ=cQ4BP:P:Q7GQ0I/5OS0W;6tX9<Pk153XS7GQ0Ip+08gS:P/03S<~3TX;2Q<{Q1rQ56Q<VQ9?Q7VQ38Q7hP[P0Q=9p+0DES7hQ<ZQ<{Q<{Q9>G3P[P0Q0^Q:LQ<UPkPkQ=:G3EFPVPRP{P|PEp+0BHS38PrPEPEQ=VQ6>P1GJP}PCb8b6b7X12X:IAdS3KS9?Q0:P8PZP7CK[^12^:IP3Q7VQ3?Q1mO3b0Q7<Q0{G4PpP@DAQ7Cp+08fS7V;6peQ9\Q8~D7Q0kP:Q0W/0cX9<Q<{Q2tQ79Q<DQ1GQ;iQ;gQ;gQ<4Q9]PaP3Q8]Q7pO2S<Vb0b3b4Q7<Q0{G4Q8JeQ9\Q8~D7GGGyQ6Wp+06HS8~Q8|Q2qQ4BP:P:Q7CQ7@/5OS56;6tX9<PkQ7GQ7@Q8u3TX;2Q;;Q1rQ7HQ:^Q7R':Q9zQ7TQ:^Q7RP[P0Q=9Q7hQ<ZQ;;Q;;Q:JG3P[P0Q1WQ;9Q63PkPkQ=:G3EFPVPRP{P|PEQ38PrPEPEQ=VP9P1GJP}PCb8b6b7X12X:IQ9?Q0:P8P?P7CK[^12^:IP3Q7TQ3?Q1mO3b0Q5vQ2\G4PpP@DAQ6}Q7S;6peQ1pQ6ID7Q0kP:Q56/0cX9<Q;;Q2tQ<AQ<@Q3FQ;iQ;gQ;gQ<4Q9\Q2tQ<Vb0b3b4Q5vQ2\G4Q8;eQ1pQ6ID7GGE<Q59Q0@Q6GQ4fQ4BP:P:Q6}Q<L/5OS56;6tX9<PkQ7GQ<LQ713TX;2Q51Q1rQ9;Q7Q':Q:2Q4y':Q9;Q7QQ:2Q4yP[P0Q=9Q7hQ<ZQ51Q51Q2AG3P[P0Q:HQ:aQ<HPkPkQ=:G3EFPVPRP{P|PEQ38PrPEPEQ=VQ34P1GJP}PCb8b6b7X12X:IQ9?Q0:P8P^P7CK[^12^:IP3Q7QQ3?Q1mO3b0Q<JQ0yG4PpP@DAQ7BQ8x;6peQ9XQ8{D7Q0kP:Q56/0cX9<Q51Q2tQ8lQ<<Q5DQ;iQ;gQ;gQ<4Q9ZQ3]Q<Vb0b3b4Q<JQ0yG4Q8IeQ9XQ8{D7GGE<Q6]Q4BP:Q8~Q5bQ;8Q4BP:P:Q7BQ13;6tX9<PkQ7GQ<OQ8xP3C]X;2Q2iQ1rQ9@Q7X':Q5UQ7W':S1rQ9@Q7XQ5UQ7WP[P0Q=9Q7hQ<ZQ2iQ2iQ85G3P[P0Q94Q9:Q<FPkPkQ=:G3EFPVPRP{P|PEQ38PrPEPEQ=VPHP1GJP}PCb8b6b7X12X:IQ9?Q0:P8PYP7CK[^12^:IP3Q7XQ3?Q1mO3b0Q<MQ1;G4PpP@DAQ7>Q72;6peQ1pQ6ID7Q0kP:Q13/0cX9<Q2iQ2tQ8DQ<5Q0bQ;iQ;gQ;gQ<4Q9XQ0;Q<Vb0b3b4Q<MQ1;G4Q9FeQ1pQ6ID7GGGoPtP3E?b2Q3HP3E<b<Q2}#tMArP6p+0EVS<VP3PTQ4DPtQ4C#>PTQ4DPTPtCIdO4b2Q6TPTQ4CP>Q4C,NTdPpDOQ7uQ4DQ7uPFQ2~P3Q6]Q8]Q1`EHW5PFQ2|Q4DQ5CQ8XD8PFPB19Nyp+0CSS4CQ2|Q2nn0100000020000Q:0Q5CQ8XD8Q7qQ9dPFP4Q2|Q4DQ5CQ8Xg0LicPMPxQ3fQ2}Q6cg0LjmPog0Ll7P~Q6aP~Q:RP~Q:>P~Q4zP~Q3vP~Q3wP~Q4NP~Q5MP~Q:RP~Q:YP~Q:]P~Q=BP~Q1CP~Q=BP~Q5vP~Q5fP~Q;UP~Q:{P~Q7FP~Q1XP~Q;>P~Q;=P~Q;FP~Q;JP~Q<MP~Q;UP~Q5vP~D_D1D1D1D1D1D1D1D1D1D1D1D1p+0>IS4NPxPoEUQ2xeQ2xPyPzQ3<Q5GP3Q4oP:Q6aEhX5yQ6Tp+0EXRkP3PTQ4EQ0L,DzS0LQ=YQ0L9awTdO4b2Q4EQ0L52yP9Q4EQ6KQ5;P3P:Q2}DuX59Q3<Q59Q33Q3<Q6WQ33Q3<Q7>Q33Q3<p+0>FS3<Q4EP:Q33Q7JQ7>Q6MQ3<Q2uQ4EP:P:Q7>Q4u;6pX9<Pl153jS7>Q<Xp+08h/03S7J3TX;2PQQ<PQ1rQ<3Q9l':Q5UQ7WQ<3Q9lP[PqQ=8Q=7p+0B\S9lPQPQQ:LG3P[PqQ9AQ0^Q7<PlPlQ=YG3EFPVPRP{P|PEQ0@PrPEPEQ<ZPcP1GJP}PCb8b6b7X12X:IAdS3KRcQ7hP8PZP7CK[^12^:IP3Q7WQ8XQ7pO3b0Q0IQ1;G4PwQ;wDAQ7AQ:P;6weQ9]Q90D7Q0kP:Q4u/0_X9<PQPaQ05Q79Q3jQ;jQ;iQ;iQ;gQ9^Q;qP3Q3IQ1lO2S1lb0b3b4Q0IQ1;G4Q8?eQ9]Q90D7GGGyQ6WQ6BQ6fQ=cQ4EP:P:Q7AQ5t/5OS1;;6pX9<PlQ7>Q5tp+08eS7A/03S053TX;2Q<{Q<PQ9}Q7`':Q;|p+09ZS4u':Q9}Q7`Q;|Q4uP[PqQ=8Q=7Q9lQ<{Q<{Q1WG3P[PqQ9>Q;8Q<TPlPlQ=YG3EFPVPRP{P|PEQ0@PrPEPEQ<ZPgP1GJP}PCb8b6b7X12X:IQ7hP8P?P7CK\c^12^:IP3Q7`Q8XQ7pO3b0Q7@Q0xG4PwQ;wDAQ7=Q5Q;6weQ5fQ6GD7Q0kP:Q1;/0_X9<Q<{PaQ<BQ<AQ4qQ;jQ;iQ;iQ;gQ9]PaQ1lb0b3b4Q7@Q0xG4Q8JeQ5fQ6GD7GGE<Q59Q3~Q5cQ2qQ4EP:P:Q7=Q0C;6pX9<PlQ7>Q<MQ413TX;2Q;;Q<PQ9vQ7Z':Q;yp+09XS41':Q9vQ7ZQ;yQ41P[PqQ=8Q=7Q9lQ;;Q;;Q:aG3P[PqQ9:Q:HQ<JPlPlQ=YG3EFPVPRP{P|PEQ0@PrPEPEQ<ZQ6UP1GJP}PCb8b6b7X12X:IQ7hP8P^P7CK\c^12^:IP3Q7ZQ8XQ7pO3b0Q<LQ12G4PwQ;wDAQ7?Q7];6weQ9ZQ8}D7Q0kP:Q0C/0_X9<Q;;PaQ<=Q8lQ=^Q;jQ;iQ;iQ;gQ9[Q2tQ1lb0b3b4Q<LQ12G4Q8;eQ9ZQ8}D7GGE<Q5GQ4EP:Q6BQ5\Q4fQ4EP:P:Q7?Q0c;6pX9<PlQ7>Q<QQ713TX;2Q51Q<PQ9qp+09WS7>':S71Q6DQ84':S4EQ9qQ7>Q6DQ84P[PqQ=8Q=7Q9lQ51Q51Q94G3P[PqQ2AQ:JQ<GPlPlQ=YG3EFPVPRP{P|PEQ0@PrPEPEQ<ZPHP1GJP}PCb8b6b7X12X:IQ7hP8PYP7CK\c^12^:IP3Q7>Q8XQ7pO3b0Q<Op+027S7hG4PwQ;wDAQ7;Q8x;6weQ5fQ6GD7Q0kP:Q0c/0_X9<Q51PaQ<:Q8DQ5PQ;jQ;iQ;iQ;gQ9ZQ3]Q1lb0b3b4Q<OQ7hG4Q8IeQ5fQ6GD7GGGoQ0LP3E?b2Q2nP3E<b<Q6c#tMArPeP`P3PTQ5aPwQ5`#>PTQ5aPTPwCIdO4b2Q7uPTQ5`P>Q5`,NTdQ:0DOPyQ5aPFQ2~P3Q5GQ3IQ1bEHX5yPFQ2|Q5aQ6]Q8]D8PFQ2|Q95Q6]Q8]D8Q1`Q9ePFP4Q2|Q5aQ6]Q8]g0LmAP\PMQ3ig0LnKPog0LoUp+0ChR_Q6aP_Q2}P_PuP_Q:?P_PdP_Q3wP_Q3zP_Q5MP_Q4RP_PuP_Q:ZP_Q66P_Q:jP_Q5|P_Q:jP_Q7@P_Q5qP_Q;VP_Q:|P_Q<^P_Q;?P_Q1XP_Q;>P_Q;HP_Q;LP_Q<OP_Q;VP_Q7@P_FqD1D1D1D1D1D1D1D1D1D1D1D1p+0>JP\PoEUQ2feQ2fP9Q3DQ2y-033X59p+0CiR_Q2}P_Q6cP_Q:SP_Q:@P_Q:EP_Q3zP_Q3|P_Q4RP_Q4UP_Q:SP_Q:[P_Q8NP_Q:mP_Q<IP_Q:mP_Q5tP_Q8~P_Q;WP_Q:}P_Q<bP_Q;@P_Q;?P_Q1XP_Q;IP_Q;MP_Q<QP_Q;WP_Q5tP_D_D1D1D1D1D1D1D1D1D1D1D1D1D1R_Q0iPMPoH0@Q2feQ2fPgQ37Q3H0033X5gQ37$0oQ2yP3E<b<Q2yP3E<b<N>0TQ6TPkP3PTQ4GQ98Q4F#>PTQ4GPTQ98CIdO4b2PyPTQ4FP>Q4F,NTdQ95DOP9Q4GPFQ32P3Q5;p+0>7S32Q1eEHX59PFQ2~Q4GQ5GQ3ID8PFPB19Ngp+0CWQ2~Q6<n0100000020000Q:0Q5GQ3ID8Q1bQ9fPFP4Q2~Q4GQ5GQ3Ig0M0_P\PxQ1iQ2dQ2og0M1iPog0M33P_Q0iPxPoH0@Q2reQ2rPgPzp+0BRR_Q5@P3Q<4P:Q2jEhX5gPyp+0EZRcP3PTQ4JPwQ=7Q:0?aTwdO4b2Q4JQ:052gPiQ4JQ<KQ5:P3P:Q2dDuX5iP_Q4}Q4rP_Q5TQ4rP_Q7?Q4rP_Q2]Q4JP:Q4rQ0VQ7?Q<>Q2]Q2iQ4JP:P:Q7?Q8z;6wX9<Pm153qS7?Q0Op+08jS2j/03S<43TX;2Q35Q<WQ71Q4EQ9qQ7>Q6DQ84P[P`Q1up+0D@R_p+0BZRlQ35Q35Q9AG3P[P`Q;9Q;:Q<XPmPmQ=7G3EFPVPRP{P|PEQ6MPrPEPEQ<PQ6HP1GJP}PCb8b6b7X12X:IAdS3KS84Q=8P8PZP7CK[^12^:IP3Q7>Q3IQ26O3b0Q0KQ12G4Q:0Q98DAQ7;p+08iS7>Q:036eQ9_Q8TD7Q8bP:Q8z/06X9<Q35p+0CRS8zQ<FQ8qQ72Q3kPfPfQ;jQ9`Q4CP3Q8_Q7oO2S72b0b3b4Q0KQ12G4Q8BeQ9_Q8TD7GGGyQ5TQ5wQ9bQ2ZQ4JP:P:Q7;Q8|/5OS8T;6wX9<PmQ7?Q8|Q<~3TX;2Q2hQ<WQ9wp+09US<~':Q7IQ:K':Q9wQ<~Q7IQ:KP[P`Q1uP_PlQ2hQ2hQ:LG3P[P`Q0^Q2qQ7<PmPmQ=7G3EFPVPRP{P|PEQ6MPrPEPEQ<PPXP1GJP}PCb8b6b7X12X:IQ84Q=8P8P?P7CK[^12^:IP3Q<~Q3IQ26O3b0Q0QQ7hG4Q:0Q98DAQ6zQ7VQ:036eQ8~Q1pD7Q8bP:Q8T/06X9<Q2hQ8zQ<DQ<CQ3jQ3kPfPfQ;jQ9_Q8zQ72b0b3b4Q0QQ7hG4Q8KeQ8~Q1pD7GGE<Q4}Q1YQ5fQ2uQ4JP:P:Q6zQ0c;6wX9<PmQ7?Q<QQ8u3TX;2PQQ<WQ9mQ:I':Q6Jp+09RS6z':Q9mQ:IQ6JQ6zP[P`Q1uP_PlPQPQQ9:G3P[P`Q1WQ:JQ<MPmPmQ=7G3EFPVPRP{P|PEQ6MPrPEPEQ<PPbP1GJP}PCb8b6b7X12X:IQ84Q=8P8P^P7CK[^12^:IP3Q:IQ3IQ26O3b0Q<OQ18G4Q:0Q98DAQ6yQ7SQ:036eQ9\Q90D7Q8bP:Q0c/06X9<PQQ8zQ<@Q<?Q4qQ3kPfPfQ;jQ9]Q;qQ72b0b3b4Q<OQ18G4Q8?eQ9\Q90D7GGE<Q5@Q4JP:Q5wQ6GQ=cQ4JP:P:Q6yQ8w;6wX9<PmQ7?Q<TQ7SP3C]X;2Q<{Q<WQ<ip+09QRb':Q<hp+09PS<W':S7?Q<iPbQ<hQ<WP[P`Q1uP_PlQ<{Q<{Q:aG3P[P`Q:HQ9>Q<JPmPmQ=7G3EFPVPRP{P|PEQ6MPrPEPEQ<PPHP1GJP}PCb8b6b7X12X:IQ84Q=8P8PYP7CK[^12^:IP3PbQ3IQ26O3b0Q63Q2`G4Q:0Q98DAQ6xQ8oQ:036eQ8~Q1pD7Q8bP:Q8w/06X9<Q<{Q8zQ<<Q8GQ=^Q3kPfPfQ;jQ9\PaQ72b0b3b4Q63Q2`G4Q8JeQ8~Q1pD7GGGoPwP3E?b2Q2xP3E<b<Q2o#tMArQ7up+0EYRbP3PTQ4LPwQ4K#>PTQ4LPTPwCIdO4b2P9PTQ4KP>Q4K,NTdQ:0DOPgQ4LPFQ2TP3Q5@Q8_Q1tEHX5gPFQ6=Q4LQ5;Q32D8PFPB19Nip+0CVQ6=Q6<n0100000020000PPQ5;Q32D8Q1eQ9gPFP4Q6=Q4LQ5;Q32g0M4=PMPxQ2sQ2eQ2rg0M5GPog0M6QPsQ2dPsQ6cPsQ3CPsQ:TPsQ:APsQ:GPsQ3|PsQ42PsQ4UPsQ4XPsQ:TPsQ:\PsQ:hPsQ:uPsQ60PsQ:uPsQ0QPsQ6BPsQ;XPsQ9=PsQ1OPsQ;APsQ;@PsQ;?PsQ;JPsQ;NPsQ63PsQ;XPsQ0QPsD_D1D1D1D1D1D1D1D1D1D1D1D1D1Q0lPxPoEUQ2[eQ2[PiPzQ<KQ5:P3Q9=P:Q2dEhX5iP9p+0E[RzP3PTQ4OP=Q=6AaPT=dO4b2Q4O=2iPPXQ4Op+0BTQ6WP3P:Q2eDuX5XQ<KQ4}Q4rQ<KQ5TQ4rQ<KQ6xQ4rQ<KQ4NQ4OP:Q4rQ0VQ6xp+0BNS0VQ4NQ51Q4OP:P:Q6xQ0J/5OS4r;6=X9<PnQ<V,53RmQ0Jp+08kP3C]X;2Q3?p+0BXS6xQ7?Q0Tp+09OS7?':Q<hQ<WQ0TQ7?P[PkQ=4p+0D=S7?Q<RQ3?Q3?Q;:G3P[PkQ;8Q;9Q0KPnPnQ=6G3EFPVPRP{P|PEQ1YPrPEPEPlP6P1GJP}PCb8b6b7X12X:IAdS3KRSP_P8PZP7CK[^12^:IP3Q<WQ32Q7oO3b0Q0OQ2`G4PPQ95DAQ6wQ2j;6PeQ9`Q92D7Q8bP:Q4r/0eX9<Q3?Q4CQ<GQ<FQ8xQ<6Q3kQ3kPfQ9aQ62P3Q8`Q1hO2S62b0b3b4Q0OQ2`G4Q8MeQ9`Q92D7GGGyQ5TQ6?Q5pQ2iQ4OP:P:Q6wQ6f/5ORK;6=X9<PnQ6fQ7J5TmX;2Q35Q6xQ<fQ:B':Q9uQ7N':Q<fQ:BQ9uQ7NP[PkQ=4Q7?Q<RQ35Q35Q0^G3P[PkQ9AQ=cQ0IPnPnQ=6G3EFPVPRP{P|PEQ1YPrPEPEPlPjP1GJP}PCb8b6b7X12X:IP_P8P?P7CK\S^12^:IP3Q:BQ32Q7oO3b0Q8|Q0~G4PPQ95DAQ6vQ:P;6PeQ6BQ5fD7Q8bP:10KeX9<Q35Q4CQ79Q<DQ3aQ<6Q3kQ3kPfQ9`Q4CQ62b0b3b4Q8|Q0~G4Q8BeQ6BQ5fD7GGE<Q4}Q<>Q5qQ2ZQ4OP:P:Q6vQ8v;6=X9<PnQ63Q055TmX;2Q2hQ6xQ<ap+09LRK':Q0SQ<w':Q<aPKQ0SQ<wP[PkQ=4Q7?Q<RQ2hQ2hQ:JG3P[PkQ9>Q1WQ<OPnPnQ=6G3EFPVPRP{P|PEQ1YPrPEPEPlQ3EP1GJP}PCb8b6b7X12X:IP_P8P^P7CK\S^12^:IP3PKQ32Q7oO3b0Q<QQ0rG4PPQ95DAQ6uQ5Q;6PeQ9]Q91D7Q8bP:Q8v/0eX9<Q2hQ4CQ<AQ<@Q1GQ<6Q3kQ3kPfQ9^Q8zQ62b0b3b4Q<QQ0rG4Q8KeQ9]Q91D7GGE<Q5:Q4OP:Q6?Q5cQ2uQ4OP:P:Q6uQ<U/5ORK;6=X9<PnQ<UQ8u5TmX;2PQQ6xQ5mQ<x':Q9tp+09IRm':Q5mQ<xQ9tPmP[PkQ=4Q7?Q<RPQPQQ:HG3P[PkQ9:Q:LQ<LPnPnQ=6G3EFPVPRP{P|PEQ1YPrPEPEPlPHP1GJP}PCb8b6b7X12X:IP_P8PYP7CK\S^12^:IP3Q<xQ32Q7oO3b0Q<TQ2GG4PPQ95DAQ6tQ7S;6PeQ6BQ5fD7Q8bP:10KeX9<PQQ4CQ8lQ<<Q3FQ<6Q3kQ3kPfQ9]Q;qQ62b0b3b4Q<TQ2GG4Q8?eQ6BQ5fD7GGGoP=P3E?b2Q6<P3E<b<Q2r#tMArPyPcP3PTQ4QP=Q4P#>PTQ4QPTP=CIdO4b2PgPTQ4PP>Q4P,NTdPPDOPiQ4QPFQ2TP3Q5:Q8`Q1vEHX5iPFQ6=Q4QQ5@Q8_D8PFQ6=Q<sQ5@Q8_D8Q1tQ9hPFP4Q6=Q4QQ5@Q8_g0M7[P\PMQ0<g0M8ePog0M9oPAQ2dPAQ2ePAQ3CPAQ3DPAQ:UPAQ4zPAQ3`PAQ42PAQ5iPAQ4XPAQ4ZPAQ:UPAQ:]PAQ:iPAQ:vPAQ=BPAQ:vPAQ8|PAQ5uPAQ;YPAQ5lPAQ:CPAQ;BPAQ;APAQ;@PAQ;LPAQ;OPAQ<TPAQ;YPAQ8|PAFqD1D1D1D1D1D1D1D1D1D1D1D1D1Q0gP\PoEUQ2QeQ2QPXQ2vQ2^-033X5Xp+0ClRAQ2ePAQ2oPAQ3DPAQ37PAQ:VPAPdPAQ89PAQ5iPAQ46PAQ4ZPAQ4]PAQ:VPAQ66PAQ<SPAQ:wPAQ:jPAQ:wPAQ6fPAQ5wPAQ;ZPAQ;0PAQ;1PAQ;CPAQ;BPAQ;APAQ;MPAQ;QPAQ<UPAQ;ZPAQ6fPAD_D1D1D1D1D1D1D1D1D1D1D1D1D1D1RdQ0kPMPoH0@Q2QeQ2QPjp+047RyQ2x0033X5j&0oyQ2^P3E<b<Q2^P3E<b<N>0TP9PzP3PTQ4TQ<vQ4S#>PTQ4TPTQ<vCIdO4b2PiPTQ4SP>Q4S,NTdQ<sDOPXQ4TPFQ2XP3Q6WQ8ZQ8QEHX5XPFQ2TQ4TQ5:Q8`D8PFPB19NjPhQ2TQ6<n0100000020000Q<sQ5:Q8`D8Q1vQ9iPFP4Q2TQ4TQ5:Q8`g0M;9PvP]Q1iQ0VQ1Zg0M<CPog0M=MPdQ0kP]PoH0@Q2PeQ2PPjQ51Q9RQ5TP3Q;jP:Q98EhX5jQ3?Q<{B0JT3U520X;2PjQ=1Q=1Q8XQ2uQ3~PVPRP{P|B0;E65P}PCb8b6b7X121R3ZB0a3?U'B^12P3Q8_O1b0K0AQ6fQ3?Q;mQ6>P3Q8_Q1hO2b0Q38Q<6Q<6Q3kQ;jPAP3Q8ZQ40O2b0b3b4K0FQ6teQ6tP0Q<{p+0BVRAQ5A?L3:R6Q;w32X50Q9RQ6lQ8rQ9RQ5AQ8rQ9RQ5mQ<{P:Q8rP4Q0iQ<{Q1ZQ8]PaQ7pQ5vQ0rDAQ5vQ6T7cUeI0qQ5AQ9xQ5mQ;;Q<{P:P:Q8KQ9b/5OROQ7@36X9<Q8]153kQ9bQ<43TX;2Q8XQ<xQ<y,:mQ<zp+09FRd':PmQ<yQ<zPdP[PcQ2qQ4fQ0JQ8XQ8XQ;:G3P[PcQ;9Q2ZQ0KQ8]Q8]Q;8G3EFPVPRP{P|PEPE20X~0p+0D0Rd=SEeH0VP}PCb8b6b7X121R3ZRZ/5URm1R3?R9159URfPZC]^12P3Q8`O1RIb0Q9YQ2GG4Q5vQ0rDAQ8?Q7>Q5v36eQ5wQ8~D7Q0nP:Q7u,0OX9<p+01nROQ5wQ8~D7GGGyQ6lQ<EQ6BQ51Q<{P:P:Q8?Q7@76KX9<Q8]Q8;Q3?Q<xQ87Q<|':p+09CRSp+09BR7':Q87Q<|PSP7P[PcQ2qQ4fQ0JQ3?Q3?Q9>G3P[PcQ0^Q:LQ63Q8]Q8]Q;8G3EFPVPRP{P|PEPE20X~Gp+0C`R7=SEeH0VP}PCb8b6b7X12Pm1R3^R^15^URSPZC]^12PIb0Q<TQ0oG4Q5vQ0rDAQ8JQ7VQ5v36eQ9_Q92D7Q0nQ0wGGE<Q5TQ<{P:Q9xQ5fQ2iQ<{P:P:Q8;Q0WQ7@36X9<Q8]Q9FQ35Q<xp+09AR_Q:7':Q:5p+09>R1':P_Q:7Q:5P1P[PcQ2qQ4fQ0JQ35Q35Q:JG3P[PcQ1WQ9AQ<OQ8]Q8]Q;8G3EFPVPRP{P|PEPE20X~HASE;eH0VP}PCb8b6b7X12Pm1R3YRY15YURmPZC]^12PIb0Q7<Q0pG4Q5vQ0rDAQ8IQ7AQ5v36eQ5wQ8~D7Q0nQ0vGGGoQ6fP3E?b2Q2[P3E<b<Q1Z#tMArPgp+0E\RgP3PTQ4WQ<vQ4V#>PTQ4WPTQ<vCIdO4b2PXPTQ4VP>Q4V,NTdQ<sDOPjQ4WPFQ2TP3Q5TQ8[Q1yEHX5jPFQ6=Q4WQ6WQ8ZD8PFPB19N0Q3eQ6=Q2Yn0100000020000Q<sQ6WQ8ZD8Q8QQ9jPFP4Q6=Q4WQ6WQ8Zg0M>WPxP]Q1qQ5xQ9xg0M?aPog0M@kp+0CmRZQ;oPZQ2oPZQ2rPZQ37PZQ3HPZQ:WPZQ:EPZQ<1PZQ46PZQ48PZQ4]PZQ58PZQ:WPZQ8NPZQ:kPZQ:xPZQ:mPZQ:xPZQ9YPZQ6?PZQ;[PZQ;2PZQ6OPZQ;DPZQ;CPZQ;BPZQ;NPZQ;RPZQ7<PZQ;[PZQ9YPZD_D1D1D1D1D1D1D1D1D1D1D1D1D1D1Q8bP]PoEUQ2aeQ2aP0Q;;PAQ5AP3Q;dP:Q5wEhX50P0Q;;Q5w92A6X50Q9RQ4}Q5qQ9RQ6BQ;;P:Q5qP4Q5mQ;;Q5yQ8XPaQ1mQ9YQ2GDAQ9YQ6T7cUeI0qQ4}Q<EQ6BQ51Q;;P:P:Q9FQ9b76KX9<Q8XQ8;Q3?p+09=RKQ9{p+09;RU':p+09:Rap+099R6':Q9{PUPaP6P[PcQ;9Q2ZQ0KQ3?Q3?Q9>G3P[PcQ0^Q:LQ63Q8XQ8XQ;:G3EFPVPRP{P|PEPE20XdGASE70H0VP}PCb8b6b7X12PfP^PSP9C]^12PIb0Q<TQ0oG4Q9YQ2GDAQ=[Q7VQ9Y36eQ9_Q92D7POQ0wGGGyQ5TQ;;P:Q9xQ5fQ2iQ;;P:P:Q=[Q0WQ9b36X9<Q8XQ9FQ35PKp+098R<p+097R:':p+096RSp+095R^':P<P:PSP^P[PcQ;9Q2ZQ0KQ35Q35Q:JG3P[PcQ1WQ9AQ<OQ8XQ8XQ;:G3EFPVPRP{P|PEPE20XdHASE;0H0VP}PCb8b6b7X12PfPYPmP9C]^12PIb0Q7<Q0pG4Q9YQ2GDAQ6oQ7AQ9Y36eQ5wQ8~D7POQ0vGGGoQ0OQ;;$0gE<Q2QP3E<b<Q9x#tMArPip+0E]RiP3PTQ4\Q<vQ4[#>PTQ4\PTQ<vCIdO4b2PjPTQ4[P>Q4[,NTdQ<sDOP0Q4\PFQ2^P3Q5AQ8\Q1{EHX50PFQ2[Q4\Q5TQ8[D8PFPB19NqQ=2Q2[Q2Jn0100000020000Q;oQ5TQ8[D8Q1yQ9kPFP4Q2[Q4\Q5TQ8[g0MB5RjP]P]Q2sg0MC?%mjg0MDIN=0BPXp+0E^RXP3PT&0?J$0<#w#WRJ,CTRjQ<s%>JPTPjPTQ<sCIdO4b2P0PTPJP>1NTJdQ;oDOPqPjPFQ2aP3Q5KQ1jQ1~EHX5qP5Q9xP5Q<vP5Q2fP5Q2vP5Q3LP5Q6[P5Q:YP5Q3`P5Q3UP5Q4;P5Q4<P5Q4_P5Q4`P5Q:YP5Q:iP5Q1CP5Q:zP5Q:vP5Q:zP5Q5pP5Q9xP5Q3:P5Q7FP5Q;<P5Q;FP5Q;EP5Q;DP5Q;QP5Q;TP5Q<XP5Q3:P5Q5pP5FqD1D1D1D1D1D1D1D1D1D1D1D1D1D1Q8cP]PoEUQ2JeQ2JQ<VPQQ<VPFQ6<P]P3Q7FCjPjQ5EQ8^Q7rEHW5Q3IQ8XB0JT3D52`X;2Q<VQ=2Q=2Q8`Q3I/5DQ<>PVPRP{P|Q=3Q<V/`q60;EP}PCb8b6b7X121R3DB0a3?D'B^12P3Q8[O1b0K0AQ5pQ3IQ98Q6HP3Q8[Q8OO2b0Q6MQ3~Q3~Q0@Q<6P5P3Q1jQ7qO2b0b3b4K0FQ6teQ6tP`Q8XPFQ6=P]P3PjQ=bQ0hQ5nGeX5`PFQ2UPjQ5EQ8^D8PFQ2UP@Q5EQ8^D8Q7rQ9nPFP4Q2UPjQ5EQ8^g0MESPvQ1qQ4^g0MF]Pog0MGgp+0D1RjPSPjp+06PRSPjP=PjPyPjQ2xPjQ3PPjQ3RPjQ:[PjQ<1PjQ:FPjQ3{PjQ4@PjQ4cPjQ0]PjQ:[PjQ:kPjQ<IPjQ:|PjQ:xPjQ:|PjQ5mPjPSPjQ;aPjQ<bPjQ;>PjQ;IPjQ;HPjQ;FPjQ;SPjQ;UPjQ0OPjQ;aPjQ5mPjD_D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1Q8fPvPoEUQ2BeQ2BPkQ1ZQ4^92b3X5kQ<Vp+0EbRjP3PTQ1ZQ4^Q=7Q1Z>1fT=dO4b2Q2aP3E<b<N>11Pqp+0EaRqP3PTQ4^Q;zQ1uQ;z9aPTdO4b2Q0[P>Q0[,NTd60DTRS=2`@PkQ4^PFQ2[P3Q5_Q:qQ22EHX5kQ<VPjP3PTQ4^PPQ=7Aa=TPdO4b2Q4^Pke$0Y92kSPFQ2[Q4^Q5_Q:qD8PFPB19NcPhQ2[Q2Dn0100000020000Q<vQ5_Q:qD8Q22Q9pPFP4Q2[Q4^Q5_Q:qg0MI1RhP\PxQ1qg0MJ;%mhg0MKEN=0BP`p+0EcP3PTQ4bPPQ4a#>PTQ4bPTPPCIdO4b2PbPTQ4aP>Q4a,NTdQ<vDOPcQ4bPFQ2KP3Q5RQ:sQ25EHX5cp+0D4R`P6P`Q61P`PpP`Q2nP`Q2|P`Q3VP`Q3GP`Q66P`Q:DP`Q:MP`Q5gP`Q47P`Q4gP`Q4lP`Q66P`Q5|P`Q:jP`Q5lP`Q:{P`Q5lP`Q9uP`Q61P`Q;dP`Q;1P`Q;@P`Q;MP`Q;LP`Q;JP`Q;UP`Q;XP`Q7@P`Q;dP`Q9uP`D_D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1Q8iPxPoEUQ2DeQ2DPzQ5zPFQ6<P\P3Q3kCjQ4bQ5eQ:tQ1zEHX5zPzQ5zPFQ6<P\P3Q4bQ5eQ:tQ1zGeX5zPFQ2YQ4bQ5RQ:sD8PFPB19NgPsQ2YQ2Dn0100000020000Q<vQ5RQ:sD8Q25Q9rPFP4Q2YQ4bQ5RQ:sg0MLORsPvQ0Ng0MMY%msg0MNcN<12Pbp+0EeP3PTQ4ePPQ4d#>PTQ4ePTPPCIdO4b2PzPTQ4dP>Q4d,NTdQ<vDOPgQ4ePFQ2KP3Q3gQ1=Q5rEHX5gPcp+0EfP3PTQ4iQ:0Q4h#>PTQ4iPTQ:0CIdO4b2Q4i=2g=PiQ4iPFQ6dPvP3Q4eQ5hQ2CQ2:GeX5iPFQ2QQ4eQ3gQ1=D8PFPB19NXQ<}Q2QQ2?n0100000020000PPQ3gQ1=D8Q5rQ9|PFP4Q2QQ4eQ3gQ1=g0MOmRvPMP\Q1qg0MQ7%mvg0MRAN=0BPzp+0EgP3PTQ4kP=Q4j#>PTQ4kPTP=CIdO4b2PiPTQ4jP>Q4j,NTdPPDOPXQ4kPFQ2DP3Q5XQ3<Q2<EHX5Xp+0D8RzPPPzQ5zPzPKPzQ65PzQ:=PzQ33PzQ36PzQ8aPzQ3QPzQ<SPzQ:MPzQ:QPzQ4IPzQ5YPzQ6pPzQ<pPzQ<SPzQ:jPzQ:wPzQ7FPzQ5lPzQ7FPzQ<iPzQ65PzQ;iPzQ;=PzQ;DPzQ;RPzQ;QPzQ;OPzQ;YPzQ;]PzQ6fPzQ;iPzQ<iPzD_D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1D1Q9sP\PoEUQ2?eQ2?p+0E_RzQ69PFQ2YPMP3Q3~CjQ4kQ5bQ0jQ2?EHX5zPzQ69PFQ2YPMP3Q4kQ5bQ0jQ2?GeX5zPFQ2aQ4kQ5XQ3<D8PFPBp+0E`RB,9NQ07>0ONWQ2aQ2?n0100000020000PPQ5XQ3<D8Q2<Q9~PFP4Q2aQ4kQ5XQ3<g0MSKRNQ07PWQ;\g0MTU%mNg0MU_N=0BPip+0EiP3PTQ;_P=Q;^#>PTQ;_PTP=CIdO4b2PzPTQ;^P>Q;^,NTdPPDOPBQ;_PFQ2DP3Q5\Q2]Q2BEHX5BPXp+0EjP3PTQ8dP=Q4n#>PTQ8dPTP=CIdO4b2Q8d=2BPPqQ8dPFQ2QQ07P3Q;_Q6IQ4NQ2DGeX5qQ2B-1d4P=P3E?b2P=P3E?b2EMQ69$0WQ69$0gE<Q2KP3E<b<P=P3E?b2EMQ:0P3E?b2PPP3E?b2EMQ5z$0WQ5z$0gE<Q2PP3E<b<PPP3E?b2EMb2Q;zP3E?b2EMP:P3E?b2Q2PP3E<b<Q<sP3E?b2EMQ<vP3E?b2EMQ<vP3E?b2EMQ<vP3E?b2EMP=P3E?b2EMPwP3E?b2EMQ98P3E?b2EMPwP3E?b2EMPtP3E?b2EMP@P3E?b2EMQ:VP3E?b2PtP3E?b2EMQ:;P3E?b2EMQ:>P3E?b2EMQ:>P3E?b2Q:>P3E?b2EMQ98P3E?b2EMQ:?P3E?b2EMQ:AP3E?b2EMP@P3E?b2EMQ4zP3E?b2EMQ:GP3E?b2EMQ6qP3E?b2EMQ:FP3E?b2Q3UP3E?b2EMQ:FP3E?b2EMQ:MP3E?b2EMQ:MP3E?b2Q:MP3E?b2EMQ:NP3E?b2EMQ:QP3E?b2EMQ:QP3E?b2Q:QP3E?b2EMQ:RP3E?b2EMPuP3E?b2EMb2Q;zP3E?b2EMQ=OP3E?b2Q4XP3E<b<Q:QP3E?b2EMQ:RP3E?b2EMPuP3E?b2EMQ:SP3E?b2Q5GP3E<b<PuP3E?b2EMb2Q;nP3E?b2EMQ:TP3E?b2EMQ8NP3E?b2Q:]P3E?b2EMQ66P3E?b2Q66P3E?b2EMQ:hP3E?b2Q66P3E?b2EMQ2F$0WQ2F$0gE<Q5:P3E<b<Q8NP3E?b2EMQ8NP3E?b2Q5TP3E<b<Q8NP3E?b2EMQ:hP3E?b2Q:hP3E?b2EMQ:iP3E?b2EMQ:kP3E?b2EMQ74P3E?b2Q5fP3E<b<Q<SP3E?b2EMQ:nP3E?b2Q<SP3E?b2EMQ:nP3E?b2EMQ=BP3E?b2EMQ8VP3E?b2Q:4Q2\E<Q:xP3E?b2EMQ0|Q2\Q5BQ:4P\PoH0@Q0|eQ0|PLQ<pQ1]Q4t723X5LQ<p-08LQ11P3E<b<Q1>Q0{Q5BQ:4Q07PoH0@Q1>eQ1>PLQ8dQ1]Q8d723X5LQ8d-08LQ1BP3E<b<Q5BQ:4P]PoH0@Q0{eQ0{PLQ<dQ1]Q8C723X5LQ<d-08LQ10P3E<b<H0}H0}H0}H1bQ=>Q=>Q8kPFP3Q;_Q:eQ:bQ<pQ<qF}Q=?41CW>'zeWKWLP8P3O2n2001000000121000000W2WMP8P3O2n2001000000121000000W2WNP8P3O2n2001000000121000000W2WJP8P3O2n2001000000121000000W2WFWGP8P3O2n2001000000121000000W2WHP8P3O2n2001000000121000000W2WIP8P3O2n2001000000121000000W2WEP8P3O2n2001000000121000000W2WOWSP8P3O2n2001000000121000000W2WPP8P3O2n2001000000121000000W2WRP8P3O2n2001000000121000000W2WQP8P3O2n2001000000121000000W2WWaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaWXWYWTWUWVaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW_aaaaaaaaaaaaaaaaaaWbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW^aaaaaaaaaaaaaaaaaaWaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaWZaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW`aW]aaaaaaaaaaaaaaaW[aaaaW\aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaao"). Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0Exit_run2.
Module Ns0Exit_run3.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
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
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.LibAtomic OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0ExitBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Exit_run2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4b000_4c000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4d000_4e000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4e000_4f000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022.Ns0_code_r58000_59000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Ns0Exit_run3 () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z2leC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib7Mh_0058;Ns0ExitBase:file_cleanC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic2ex00C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions5bv_eqC59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7step_ldC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfI47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list01C45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4c_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:SumWalkTac9c_eq_reflC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_tkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftlC49OSSVerify5KrLib8PropExec7v_auipcC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC49OSSVerify5KrLib8PropExec:step_auipcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4v_lwC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0055:SumWalkTac?bytes_le_to_Z_4C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7step_lwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5c_ltsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_blt_tkC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib7Mh_00387WalkTac=wf_getr_chainC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C35stdpp7tactics<f_equal_helpC49OSSVerify5KrLib8PropExec8v_addi_0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9step_addiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec<step_jalr_x0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec=step_jal_linkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9e8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9e8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9e8C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9ecC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_ae9f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_ae9f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_ae9f0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea0cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea10C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea14C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea14C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea18C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea24C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea28C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea2cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea44C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea48C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aea4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aea4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aea4cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aeaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aeaccC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aeaccC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aead0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aead0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aead0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aead4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aead4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aead4C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007W_aead8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007F_aead8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4d000_4e0007D_aead8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9300C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9300C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9300C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a9304C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a9304C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a9304C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8f9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8f9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8f9cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007W_a8fa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007F_a8fa0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0020ENs0_code_r4b000_4c0007D_a8fa0C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xae4d4)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0xa933c ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0xae974 : word) mem rom)
                 (mkst regs' (0xae4d4 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0xc6cc0
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0xaea24
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0xc6cc0
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
ltac2:(KReplay.run1 (kr_tL_Mh_0058 ()) ["FPX_1"] "h06__sat1h16__sat2h27__arithh34__x1h41Hh51bh68__varmaph75__with84__ffh91zh:1nh;4__p1h<2gHh=1oh>5regs'h?1xh@2HahA1yhB4__x2hC2b1hD2b2hE1mhF3F1lhG4F1wbhH4F1wphI4F1wrhJ4GerrhK3GinhL3GnlhM4GoflhN4GouthO3HrahP3Hs0hQ3HsphR2NEhS3SOKhT4SPhihU4SPlohV2WBhW2WPhX6__sat3hY6__sat4hZ4codeh[3memh\4regsh]3romh^2sph_2wbh`2wpp%0p%1p%2p%3p%4p%5p%6p%7p%8p%9p&0p&1p;1p;3p;2p;4p;5p;7p;=p;6p;:p;Bp;<p;?p;>p;Ap;@p;8p;9p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9g002PR1p4p7210g003<R2p4p710R3p8p1003Zp4p710P3p8p10045p4p710g004TR3p4p710p8g0050j1TTg0077j1rTg007Zj32Tg005Oj15Tg00:gj1_Tg00;Ej2XTg0064j13Tg006Yk10GTg0084R4j20Tg008Pk11{Tg008nk20YTg009GR5j24Tg009dk41uTg00:GR6k10`Tg00?4k217Tg00?hk31]Tg00;ak219Tg00<gk11PTg00@ok113Tg00=Jk11LTg00>5k51GTg00@Lk30{Tg05?\j2ITg00Iik20[Tg00AMk10qTg00BOk10vTg00GSk30KTg00H6k30NTg00ICk11jj2OTg00Hck21eTg00G1k116Tg00<Dk21?Tg01F3k71QTg00>YS00j2`Tg00Kfk20@Tg00Mbj2^Tg00Lnj2ETg00DMj2iTg00NJk211Tg00O2k310Tg00Aok10ITg00Bok20sTg00CMk11OTg00Ckk21MTg00Dgk20}Tg00ESk40|Tg00FEk11KTg00Tlk20\Tg00K<j2ZTg00OVj4[Tg05CWk20=Tg0JPEk11ITg00f?k207Tg01:dk20HTg05HNk11ETg05DLj2|Tg014ck11DTg00cMj3@Tg05>Fk20pTg05[bk10RTg05WSk11|Tg05Dnk10oTg05GEk20xTP1j29Tg00WOj2DTg00XAj58Tg00ZMk30mTg00\<j3MTg00]ak30wTg00^bk21CTg00aVk41zTg0JSAk11yTg0MVik30bTg00eek20CTg00kRm=08Tg00V8j2JTP2j6:Tg01JUm:0iTg01NhmB0dTg05`Fm<1@Tg05N0m<0hTg00U^j2CTg08RQj6QTg01EOk61tTP3j6>Tg0JTGm?1sTg08PTm>1>Tg01;_m>1=Tg08QMk51<Tg05XPmA0>Tg0=_Dm>1pTg00gom>1;Tg0JQ7k21mTg05U[mA1lTg0>1@k21:Tg0JU<m>1kTg00mCj4uTg0MX3k20uTg0MXPk21iTg08G1k118Tg05;]k214Tg0MY1k21dTg0MYRk31cTg05fIk31bTg05^Pk21aTg01G;j3~Tg05_hk41`Tg0MZ;k41^Tg0FCam@1_Tg01<`k21\Tg01A]k40BTg00dek41[Tg05cnk31gTg01B[k40OTg01CFk70MTg01Cjm<1ZTg01B8k31hTg01FWk80eTg01HNmB1YTg01DOk31XTg01Dnk41WTg01I4m<1nTg00hhk41oTg05dQk40cTg0JW6k31VTg01IYk30fTg01LIk11UTg01MIk81TTg01Mfk71STg08^bk71BTg08_Fm91RTg08FMk61wTg01Qbk71xTf0R3#T#Tp>1}%T3#T#T#Tp>1f%T3#T#T#T#T#T#T#Tp>1N%T3#T#T#T#T#T#T#T#T#T#T#T#T#T#T#Tp>0Fg01R^R2f3R1f2R7'Zf1R8/Z332p=Hg01S<R9/03p=\1i23p==A2283p=B21?23p=]B1g283p>0U%33#5p>12%53#5p>0_%53#_p>0^%53#5#5#5#5#5#5#5p>0]%53#5#5#5p=z%53#5#5#_p=LP7g01SZS01g01T9R:P:g01TYS02P2P8g01U9R;P3H0Og01U`R<K0Mp=W1I83,07p=kg01V@R=P2P2P2P6P6f5R6f4R>P1P7P8P3N<1Zp>0n%53#3#5#3#3#3#5#3#5#5#3#3p=x%33#5#5#_p=Y%53#3#5#3p>03%53#3#5#3#3#3#5#3#3#5#3#3p=o%53#3#3#3p>01%33#3p>0l%33#5#5#5p>0E%33#5#3#5p>0a%33#3#3#5p>0k%53#5#3#3p>0X%33#3#3#3p=p%53#5#3#5p=v%33#3#5#3#3#5#3#3p>1A%33#5#5#5#3#3#5#3p>0Q%33#5#5#3p>0D%33#3#3#3#3#3#3#3p>0P%33#3#5#3p>0g%53#5#5#3p=qg01XFR?:0K83p=?B1h283p=bP2P8g01V_R@P3H0Op>0VP>Q01P:P:Q02P1P7P8Q01P:P:Q02P3P<K0ML0ep>0Z1478/03p=d%_3>0K8?p=w10>11478/03'Cp>0:P2P2P2P2P2P2P5P3P8P7P5P1P>P6f6R5f7RAf8RBf9RCNB1Yp=lP7Q01P:P:Q02P2P8P@P3H0OP<K0Mp=s%33#3#5#5p>0L%53#3#3#5p>0t%53#3#5#5p=}%53#3#5#3#3#3#5#3p>0~g01WFR@g01WfRD723p>09B1X293p>0rP7P8Q02P3H1Wp=n%33#5#3#3p>1JP6Q01P:P:Q02P>P1P7Q01P:P:Q02P2P8P;P3H0OP<K0ML0ep=t1E39p>0S%53#3p>1H%33#3#5#3#5#5#3#3p>1F%53#3#5#3#3#3#5#3#5#3#5#5p>06P1Q01P:P:Q02P7P8P3L0ep>0z&0I39~78p>0yP2P2P4PAP4P5P6P>P1P7P8P3N<1np=6P2PAP5P6P>P1P7H1oP8P3E:p=71E839M17p=gg01ZFR4P7P8P3H0cp=PP4P1P7P8H0c=2>3p=m1483,O7p>04A~6>1P7P8P3Cup=V&0I39~789~>1p=e&0I39~789~>19~56p>02A~7839~>1p=1A2283$18p=yP5P6P>B1V178P3D8p>0<1D56=2A>1D78=213'`p>0A1D17=2>8/`3p=FB0f478/`3p>0;B0f483p>1v&1U3,i@p=jB0K178=2>3p=NP6P>P1P7P8D8>0f43p=GP7Q01P:P:Q02P2P8g01XbP3H0OP<K0Mp={1I78/43p>0jP2P5P6P>P1P7P8P3L1Tp>0?P2P>P1P7P8P3E:p=APAAM56>P1P7P8D8>0f43p=a1483,07p>0TP4P6P>P1P7P8P3K1Sp>0W1Z839227p=fP4P>1E17P8H0c=263p>001083,C7p=;10171083'Cp=cPAQ01P:P:Q02P5P6P>Q01P:P:Q02P1Q01P:P:Q02P2P7P;P8H0OP<K0MP3K1BL0ep=U1I78,01/C3p=SP=P>P1P7P8P3E:p=<P4PAP5P6P>P1P7P8P3N91Rp=RPAP5P6P>P4P1P7P8H0cP3E:p>05P2P8P;P3H0Op>1rP1Q01P:P:Q02P7Q01P:P:Q02P8P<K0MP3K1Bp>1q1078/C3p=hg01YfS0392@3p>0JP8Q01P:P:Q02P3J1wp>15P4P6P>P1P7P8P3K1xp=Kg024AS04#TS05#T$1}S06$1fR<$1N$0F$0F$0F$0F$0F$0F$0F$0FP=g025ER;%r3RE%r8RFP7P8P7P3CHRG%r1?278RH[]D]C]:RIp-0RJg024`RK#5S07#_S08,X9PJQ08#\PJQ07#3RL$0GRM#rP01083RN$1{XA2X?220YNN^A2^?2P2P2g025c1483H1uRN#=XE2X:21BNN^E2^:2&0`3RN#=X?=1BNN^?=&0`<P2Q06$0`P2Q07#5RO#5RP#5RQ#5S09#5RR$0GRS#rP0&0GPS0:#rP0Q08%_RRT+17P2PGPJQ00P8\H%r>?217\3%r6?2>1\8B1]178P3n2001000000120000000aXDFXCEX:;PI%\TPJ2192KS0;Q09#_RI#]+0U&1P2R;%_QS0<#]P;&13QS0=#]P;&12OS0>$0_S0?$0^RQ#]P;&1L2REQ0;&0_R$0]$0]$0]RR#z$0]#LRF#]3WPEQ01P:P:Q02I1GRHQ08#]S0@>0{2SP;%_PRG#]P;Q0;%3KS0A#5RU#5RV#5RW#_S0B#]+0UP;%_RRR?k3Q1I8I#\[^32PJfGS0C$0`P2AkR3Q1I8Q#\[^32PJAkR3QQ0B,I8#\[^32PJP3X?2RXPXfCS0DP<PG%=GJ0nPXfBS0EO1PXPGO1'B%xK#z#YS0F#=Q0FQ0F'BQ0;%5LRY#5RZ$0^R[#]+0UP;AkR3Q1I8[#\[^32PJ%5K$03$0^R\%_VR]+0[P2%oK$01#LS0G#=Q0GQ0G'B%3K$0l$0E$0a$0k$0X#_R^#=1B^^Q05$0`S0H,4^P2%_KR_,4^P2%]^P;%pK#v#z$03#LR`#=1B``fMS0I,4`P214`GP2%]`P;%pK#v#z$0X#LRa#=1BaafQS0J,4aP214aGP2%]aP;&0EK$1A$03#LRb#=1BbbfUS0K,4bP214bGP2%]bP;&0QK$0a$0D#YRc#=1BccfXS0L,4cP2%_ORO,4cP2%]cP;Q08017IP2Q0A#3S0M$0lRd#3$0lRe$0P$0P$0PS0N#_S0O#]P;&0QK$0D$0g#LRf#=1Bfff_S0P,4fP214fGP2%]fP;&0QK$0D#p#LRg#=1BggfcS0Q,4gP214gGP2%]gP;&0QK$0a#q#LRh#=1BhhfgRi,4hP214hGP2%]hP;&0GVRV#rP0%3URU$0GS0R#rP0&0GZRZ#rP0%3YRj$0GRk#rP0fkS0S$0qP0flS0T$0vP0Q08,?MRlB0KM9?Rm60NMP@foS0U$0qP0&1jSfqS0V^92frRn\2P0fpS0W,X9PJQ0V#\PJQ0;fnRo+0UP;Q0;fmS0X+0UP;f|RpfvS0Y+1eP0Q0T,bnP;PEQ0U&16:RqPEfsS0Z00VoI0ZPH103F1I8IfyRr'X[^32PJQ0X=d3rX92PJ^92Rs%=r1Brr103F1I8Q?dQp[^32PJ103F1I8Qf}S0['X[^32PJPEfuS0\PqPEftRt-0VnI0ZPH103FQ0B,I8p+01@S0]'X[^32PJQ0\,btP;1?M_Ru>0NMmP@Q0;&0^WS0^#]+0US0_fwS0`'bP;PEfzRWPqPEQ0_00VrI0ZPH103FQ0^,I8p+01ES0a'X[^32PJPEPpPqPEf{Rv-0VnI0ZPH103F1I8[p+01GS0b'X[^32PJ1btpP;1wMYRY>0NMmP@1?MGRw>0NMmP@%3LRL,wMRx>0NMmP@1wMUS0c>0NMmP@Q0\P3P3p+01PRUP^I0:X92PsPXPXPXp+01RS0dP^P^Q0YQ0HP_PXPXp+01QS0eQ05P_%=_J0nM:lPXQ0\O1/Bt%]_,btP;Q0Yp+01NS0f'0PJp+01TS0g=d3UX92Ps103FQ0B,I8Q0d7dG[^32PJ103F1I8Ip+01SS0h7dG[^32PJ103F1I8[Q0g7dG[^32PJ103FQ0^,I8p+01US0i7dG[^32PJQ0i9d3GX92PsPvP3P3p+01ZS0jP`I0:X92PsPXPXPXp+01\S0kP`P`PpQ0jPGQ0bM:lPXPvO1/BWQ0f,bWP;p+01XS0l,0pPJPvP3P3p+01^S0mPaI0:X92PsPXPXPXp+01`S0nPaPaPpQ0mPGp+01KS0oM:lPXPvO1/BWQ0d,bWP;Q0k,0pPJPvP3P3p+01bS0pPbI0:X92PsPXPXPXp+01dS0qPbPbPpQ0pPGp+01OS0rM:lPXPvO1/BWp+01VS0s,bWP;Q0n,0pPJPvP3P3p+01fS0tPcI0:X92PsPXPXPXp+01hS0uPcPcPpp+01eS0vPOPXPXp+01gS0wQ06PO%=OJ0nM:lPXPvO1/BW%]O,bWP;Q0q,0pPJPrP3P3p+01jRtPfI0:X92PsPXPXPXp+01lS0xPfPfPWPtPGp+01WS0yM:lPXPrO1fxR_'BQ0m,b_P;Q0u,0WPJPrP3P3p+01nS0zPgI0:X92PsPXPXPXp+020S0{PgPgPWQ0zPGp+01[S0|M:lPXPrO1/B_Q0p,b_P;Q0x,0WPJPEQ01P:P:Q0221?29RyQ0;5WEQ0;Q0v5sEK1QPH%\3S0}p+01oS0~,X3'`%\8Q0{,X8'`[^32PJPvP3P3p+024S10PhI0:X92PsPXPXPXp+026S11PhPhPpQ10PGp+01aS12M:lPXPvO1/BWQ0u,bWP;p+022S13,0pPJp+025S14P_[P0Q0`$0qP01OS9R0-0@<P_&0QK$0D$0E#LS15,OSR_-0@<PrQ06Q0O,OSS16+0@PW&03K$0L$0D$0a#YS17,OSS18-0@<Pv&03K#v$0t$01#Y,OSS19-0@<PpQ0F,OSRs-0@<Q0[%ze,wVS1:,^VP2%5K$12$0k$0D$01#},wSS1;/EOp+02>S1<p+02?S1=$16f~S1>Q0[Q1>'iQ0[Q1>Q1>32Q08011Tp+02IS1?Q1<Q0][[p+02JS1@Q1=p+01ARe[[PJQ1@g0285S1AQ08@10T8UW@Q1@Q1APe[]@p+02KS1BQ1Ap+01BS1C[]@PJ%]RQ1>5WEPH&0~K#v#p#LS1D,?SS1E/EOp+02FS1F1?VGS1G,^VP2g027IS1H$0IRTQ1H$0vRz20s28R{&1O2R|Q1CQ02-1MER}P3P71i@DS1I20}37$09d&0r8H0|RDb8b6b7X3220s23$0r$1KR~Q0]5nE^32p+01CS1Jp+02AS1K'bP;PEQ1KPqPEp+01DS1Lp+02@S1M+0VI0ZPHPTPzP{P|Q1>P}PDb8b6b7X32AnE~p^32&0~K#v#p#YS1N,?SS1O/EOp+02LS1PB0KV9?S1Q,^VP2%xK#z#LS1R,?SS1S/EOp+02NS1TQ1SQ09#3$0L,wkS1U,^k+0\p+02OS1V1ZSsP2%oK$0X#YS1W,?SS1X/EOp+02QS1Yp+02XS1Zp+02RS1[PuPsC[Q0o%oK#}#LS1\,?SS1]/EOp+02SS1^PTPzP{P|Q1JP}PDb8b6b7X32AnE~e^32PTPzP{P|Q1CP}PDb8b6b7X32Q0]9nE~^32%oK#}#YS1_,?SS1`/EOp+02VS1a1?Z\S1b,^Z00[]P2%oK$03#LS1c,?SS1d/EOQ1ZQ1dp+02DS1e+0=p+02YS1f&0_K#p#LR\,?VS1g,^VP2%oK$03#YS1h,?SS1i/EOp+02[S1jp+02bR;p+02\S1kPY%pK#q$1J$03#LS1l,OSS1mC[Q0iQ1m/E\p+02]S1n%oK$0t#LS1o,?SS1p/EOp+02^S1qp+02eS1rp+02_S1sPw%pK#v#z#}#LS1t,OSS1uC[Q0l%oK$0t#YS1v,?SS1w/EOp+02`S1xQ1w&0EL$03#},wkS1y,^k+0\p+02aS1zQ0G,OSS1{,ZSP2&01K#}$0L#q#LS1|,?SS1}/EOp+02cS1~Q1}%pK$0^S2000[]+0=p+02dS21Q0:/O9S0:$1IQ1r&01K#}$0L#q#YS22,?SS23/EOp+02fS24p+02mS25p+02gS26Px%pK#z$0L#q#LS27,OSS28C[Q0np+02nS29p+02hS2:PuQ1{C[Q12p+02oS2;p+02iS2<PYQ1uC[Q0pQ28&0_K$1A#_S2='Ep+02jS2>1OS^S2?,ZSP2PEQ1~PqPEQ0|P;EtPHPEQ21PqPEQ0vQ1~EtPHPEQ1rPqPEQ0sQ21EtPHPEQ24PqPEQ0kQ1rEtPH1ZS0P2&01K#}$0L#v#LS2@,?SS2AQ0RQ0R%zd'wS2B'^+0\p+031S2Cp+038S2Dp+032S2EQ0cP0C[p+01kS2F20700$09PJQ0G,?SS2G,ZSP2Q2G00H9p+035S2HQ2G/EOp+036S2IQ1u/EGp+037S2J1OS`Rd,ZSP2%oK$01#YS2K,?SS2L/EOp+039S2Mp+03@Rkp+03:S2NPYPdC[p+023S2O%oK$0E#LS2P,?SS2Q/EOp+03;S2RQ0<,?VS2S,^VP2%oK$0E#YS2T,?SS2U/EOp+03=S2VQ0F,?SS2W,ZSP2Q2W00H9p+03?S2XQ2W/EOPk&0Sdp+03AS2Y%xK#q#LS2Z,?SS2[/EOp+03BS2\p+03IS2]p+03CS2^PwP0C[p+02<S2_%xK#q#YS2`,?SS2a/EOp+03DS2bQ2ap+030S2c+0=p+03ES2d%xK#v#LS2e,?SS2f/EOp+03FS2gp+03MS2hp+03GS2iPY%pK#q$0X#q#YS2j,OSS2kC[Q1MQ2k%3K$1H#q#YS2l'Ep+03HS2m1OSaS2n,ZSP2%xK#v#YS2o,?SS2pQ0RQ0R&0_j'wS2q'^+0\p+03JS2r%xK$0g#LS2s,?SS2t/EOp+03KS2uQ2tQ0B00[]+0=p+03LS2v%xK$0g#YS2w,?SS2x/EOQ2hp+03TS2yp+03NS2zPY&0EK$1F$0g#LS2{,OSS2|C[p+02GS2}Q2|&0lK$0E#LS2~'Ep+03OS301OSbS31,ZSP2%xK$0k#LS32,?SS33/EOp+03QS34p+03XS35p+03RS36PwP_C[Q1BQ16$1Ep+03SS37%xK$0k#YS38,?SS39/EOQ2y%3P#YS3:,E_p+03US3;1OScS3<,ZSP2%xK#p#LS3=,?SS3>Q0RQ0R/?]S3?'^+0\p+03WS3@p+03^S3AQ35PYQ0N$0P$0P$0P$0P#_S0N,OSS3BC[Q1Y&06K#z#YS3C,?SS3D/EOp+03YS3E1E_[p+03ZS3F1OSfS3G,ZSP2&06K#q#LS3H,?SS3I/EOp+03\S3J1OSgS3K,ZSP2&06K#q#YS3L,?SS3M/EOQ3APEQ0nPqQ0nH0zPH&06K#v#LS3N,?SS3O/EOp+03`S3PQ0?#_S0?,E_p+03aS3Q1OShS3R,ZSP2&06K#v#YS3S,?SS3T/EOp+03cS3Up+03jS3Vp+03dS3WQ0cQ18C[Q1n&06K$0X#LS3X,?SS3Y/EOp+03eS3Z&06K$0X#YS3[,?SS3\/EOp+03fS3]&06K#}#LS3^,?SS3_/EOp+03gRPp+03nS3`p+03hS3a1?M]S3bP0C[Q1zp+03oS3cp+03iS3dPxP0C[P;p+040S3eQ3VPYP_C[Q1~&0S0p+03kS3fp+03lS3gp+03mRj?23_W5Q3gPJ]51ij_A2j__Q3`Q3c?230W5Q3`PJ]5Q3c/i0Q3c?200Q2EQ3cQ0:Q3c40y'|Ptp+033S3h/|tQ2Fp+034S3i/|tQ0xQ2H/|tp+01mS3jQ2I/|tQ0zQ2HQ0t'iQ2HQ0tQ0t32PEQ12PqPEPyp+041S3kEtPHPEQ3`PqPEQ0mPjEtPHPEp+01cS3lPqPEPyQ2EEtPHPTPzP{P|Q0pP}PDb8b6b7X32Q0n9nE~^32PEQ0vPqPEPyQ3`EtPHPEQ0tPqPEPyQ0_EtPHPEQ0wPqPEPyQ3dEtPHQ1CQ0H'4P2Q3jQ0xQ0xQ2FPTPz&1D2RHP|Q3a9WEyP}PDb8b6b7%\^P3b2b0b1Q3jQ0xQ0xQ2FPTPzPHP|Q3ap+048S3m5sEP}PDb8b6b7p+04>S3n,X^P3b2b0b15@^Q1J/B^Q3nQ10+0pP=PTPzP{P|Q0bP}PDb8b6b7X32Q0a9nE~^32PTPzP{P|Q0bP}PDb8b6b7X32Q0a9nE~^32p+04AS3oQ11+0pP=PTPzP{P|p+01HS3pP}PDb8b6b7X32p+01FS3q9nE~^32PTPzP{P|Q3pP}PDb8b6b7X32Q3q9nE~^32Q1IQ1CdQ1CQ2Gp+01iS3r+0Hp+04FS3sQ2]p+02;S3t'|Q1KQ2WQ2F+0Hp+04HS3up+04KS3v,4eP2p+029S3wp+028S3xQ3xp+027S3yPTPzPHP|Q3e9WEyP}PDb8b6b7%\`P3b2b0b1Q3wQ3xQ3xQ3yPTPzPHP|Q3ep+04DS3z5sEP}PDb8b6b7p+04JS3{,X`P3b2b0b15@`Q1C/B`&0R0Q1e$1|Q0o'Bp+04NS3|,4nP2Q2_Q3tQ3tp+02:S3}PTPzPHP|Q3c9WEyP}PDb8b6b7%\aP3b2b0b1Q2_Q3tQ3tQ3}PTPzPHP|Q3cp+04GS3~5sEP}PDb8b6b7p+04MS40,XaP3b2b0b15@aQ0Z/BaQ0Xp+04PS41'4P2Q1<p+02=S42Q42Q2_PTPzPHP|AWEyjP}PDb8b6b7%\bP3b2b0b1Q1<Q42Q42Q2_PTPzPHP|p+04IS439sEjP}PDb8b6b7p+04ORL,XbP3b2b0b15@b1BobfiS44p+04QS45'4P2Q1MQ1=Q1=Q1<PTPzPHP|Q3f9WEyP}PDb8b6b7%\cP3b2b0b1Q1MQ1=Q1=Q1<PTPzPHP|Q3fQ3v5sEP}PDb8b6b7Q45,XcP3b2b0b15@cfjS46/BcffR\p+04TS47'4P2p+02BS48Q1KQ1KQ1MPTPzPHP|AWEyPP}PDb8b6b7%\fP3b2b0b1Q48Q1KQ1KQ1MPTPzPHP|Q409sEPP}PDb8b6b7p+04SS40,XfP3b2b0b15@f1Bifp+04VS49,4\P2Q1ep+02CS4:Q4:Q48PTPzPHP|Q3Z9WEyP}PDb8b6b7%\gP3b2b0b1Q1eQ4:Q4:Q48PTPzPHP|Q3Z=sELP}PDb8b6b7p+04US4;,XgP3b2b0b15@g1BigPTPzP{P|Q44P}PDb8b6b7X32AnE~i^32fdS4<p+04YS4='4P2Q2}Q1FQ1Fp+02ES4>PTPzPHP|Q3W9WEyP}PDb8b6b7%\hP3b2b0b1Q2}Q1FQ1FQ4>PTPzPHP|Q3Wp+04RS4?5sEP}PDb8b6b7p+04XS4@,XhP3b2b0b15@hfeS4A/BhQ18Q2_+0HQ4=&0o0p+04ZS4Bf^S4C;20PTPzP{P|fWS4DP}PDb8b6b7X32S4EQ0K9nE~^32S4FQ4EQ4FQ4EQ4FPTPzP{P|fVS4FP}PDb8b6b7X32S4EfTS4G9nE~^32R~Q4EP~Q4EP~Q1jQ1kfaS4E723W=Q1jPJ]=Q19-0x<fRS4H=2=<Q0Kp+04aS4I'0PJ20x<sQ0J=2=<Q1sQ1xQ4<723W=Q1sPJ]=fLS4<p+04dS4J'0PJfJS4Kp+04eS4L'0PJQ1~?23\X=;PJ^=;Q4Kp+04g'0PJQ21Q1r?23iW=Q21PJ]=Q4Kp+04i'0PJfIS4Mp+04jR~'0PJfHS4Np+04kS4O'0PJQ2:Q2<Q46723W=Q2:PJ]=Q0Cp+04mS4P'0PJP^Q0H,43S0Hp+04oS4Q'0X92Q4@p+04nS4R'0p+03PS4SPXp+055S4TQ4@p+04WS4UQ36Q4RQ4RQ3WG6Q1sQ1qQ1qQ1nPTPzPHP|Q3;=WE~P}PDb8b6b7Q36P3b2b0b1Q14Q4EG7f<S4VeQ4VP`Q4SQ4;Q4Q'0Q2iPXp+056S4WQ4;Q47Q2]Q4QQ4QQ3ZG6Q1xQ1sQ1sQ1qPTPzPHP|Q2vQ4O5WEP}PDb8b6b7Q2]P3b2b0b1Q3rQ4FG7f:R~eP~PaQ34Q4?p+050S4O'0Q2bPXp+057S4XQ4?Q45Q2gQ4OQ4OQ3]G6Q1zQ1xQ1xQ1sPTPzPHP|Q2]p+04l5WEP}PDb8b6b7Q2gP3b2b0b1p+01YS4YQ4GG7P~eP~PbQ36p+051S4Z,0LQ2YPXp+058S4[PLQ3|Q2^Q4ZQ4ZPPG6P;Q1zQ1zQ1xPTPzPHP|Q2gQ4P5WEP}PDb8b6b7Q2^P3b2b0b1Q0hfSS4PG7PCePCPcQ4Wp+053S4\5d3X92p+04LS4]p+052S4^'0p+03>S4_PXp+059S4`Q4]Q3vPkQ4^Q4^Q3aG6Q1~P;P;Q1zPTPzPHP|Q2^Q4R5WEP}PDb8b6b7PkP3b2b0b1Q0fQ4HG7PBePBPfQ2yQ3~Q4\'0Q2RPXp+05:S4]Q3~Q3sQ2VQ4\Q4\Q3dG6Q21Q1~Q1~P;PTPzPHP|Q4Q9WEkP}PDb8b6b7Q2VP3b2b0b1p+01JS3~Q0JG7PBePBPgQ3;Q3zp+054S4a'0Q2DPXp+05;S4bQ3zp+04CS4cQ2NQ4aQ4aQ3VG6Q1rQ21Q21Q1~PTPzPHP|Q2VQ4O5WEP}PDb8b6b7Q2NP3b2b0b1p+01IS4dfPS4eG7PBePBPhp+03VS4fQ3oQ4T'0Q3hPXp+05<S4gQ3op+04@Q2HQ4TQ4TQ3fG6Q24Q1rQ1rQ21PTPzPHP|Q2DQ4Z5WEP}PDb8b6b7Q2HP3b2b0b1Q0afNS4hG7PAePAQ4[,9M1D3lQ4`1D8wQ4]1D7uQ4bQ0A,wMS0A,D1Q4g1?MOS4i,D>p+05=S4jP6PlP>Q2CCgp+05>S4k,9MQ2NQ2?Q055P3Q2NAP8d<Q2RQ2n=P7<p+03<S4lQ31=P1<Q2VQ4_P>&0QK$0D$01#L,OSP<Q3s&0QK$01$0a#L,OS-0@<'|DmPJQ2XQ0a72>PJQ0a92k>PJQ2YQ3q72>PJQ2\Q3q72>PJQ2^PCQ15Q3:604SQ06Q3qDmPJQ2bP~Q15Q0?604SP<Q3qDmPJ1`75PJ1`>3PJ1`53PJQ2]p,2fxROfFS3sQ1;f?S4mP3D8g028QS4np+05PS4o1ZS3P2Q0<,I3P21I8QP21I7IP2Q0B,I1P21I>[P2Q0^,I6P21OS6p+05XS4p1OS6p+05YS4q1OS6p+05ZS4r1OS6p+05[S4s1OS6p+05\S4t1OS6p+05]S4u14CGP2f;S4vp+05QS4w'4P2Q4V/4QP2Q4vp+05cS4x'4P2Q4V/4GP2f=S4y#=Q4yQ4y'BQ4mp+05fS4z'4P2f@S4{#=Q4{Q4{'Bf>S4|/4GP2Q4{p+05i'4P2fAS4}/4GP2Q0E#=Q0EQ0E'BQ0Ep+05lS4~'4P2Q0D#=Q0DQ0D'Bp+05TS50Q3s'0PJQ50Q0C'0PJp+05VS51Q4M'0PJQ51Q4K'0PJQ4pQ4M'0PJQ4pQ4K'0PJQ4rQ4K'0PJQ4rfKS52'0PJQ4pQ4h'0PJQ4pfOS53'0PJQ4rQ0J'0PJQ4rQ4H'0PJQ4tQ0J'0PJQ4tQ4H'0PJp+05^S54Q4H'0PJQ54Q4P'0PJQ4tQ4F'0PJQ4tQ4D'0PJQ54fYS55'0PJQ54fZS56'0PJp+05`S57Q55'0PJQ57Q56'0PJp+05bS58Q56'0PJQ58f[S59'0PJQ57Q4C'0PJQ57Q0P'0PJQ58Q4E'0PJQ58fbS5:'0PJp+05dS5;Q4E'0PJQ5;Q5:'0PJQ4zQ5:'0PJQ4zQ0Q'0PJQ5;/0\PJQ5;/0iPJQ4zQ44'0PJQ4zQ46'0PJp+05hRiQ44'0PJQ46,0iPJp+05jR\Q46'0PJQ0S,0\PJQ4z/0oPJQ4zQ0U'0PJQ0V,0iPJ10inPJQ0V,0\PJ10\nPJQ4~/0nPJQ4~Q0Z'0PJQ0Y,0\PJQ0`,0\PJQ4~/0rPJQ4~/0WPJp+05nS0`/0rPJQ0`/0WPJp+060S0Y/0WPJQ0Y/0vPJQ0`Q1>'0PJQ0`Q0]'0PJQ0YQ1C'0PJQ0YQ1J'0PJp+062S0ZQ1C'0PJQ0ZQ1J'0PJp+064S0VQ1J'0PJQ0VQ1L'0PJp+01]S0QQ4I80mep+06lS5:Q0Y[Q0vQ1J7Mlp+06mS4E,9MQ3qQ0='Ep+06nS5<p+075S5=p+06oS5>PlQ0aC[PiQ3q,ZSP2Q1CQ5>'0PJQ1Cp+070S5?'0PJPXPXPXp+077S5@PUPU%=Up+06eS5APQPXPXp+076S5Bp+07=S5CPQ%=QJ0nM:lPXQ1LO1Q1J'BQ0o,ZSP2Q3~,ZSP2PXPXPXp+07:S5DQ0eQ0eQ1Jp+078S5EPGQ5AM:lPXQ0aO1RiQ1L'BPXPXPXp+07;S5FQ0hQ0hQ1Cp+079S5GPGp+06fS5HM:lPXQ1JO1Q4d'BQ0fQ0='EQ5Ep+07?S5IQ5GPlp+01LS5JC[Q0Zp+01MS5K,ZSP2Q0f/EGQ5F1ZSUP2PXPXPXp+07AS5LQ0yQ0yQ1LQ5IPGQ5:M:lPXQ3qO1Q0a'BQ0e$0Sp+07>S5MPXPXPXp+07CS5NQ0lQ0lQ1LQ5LPGQ5<M:lQ4d,BiQ0r/0^PJQ0r/0^PJQ0ep+07@S5O'0PJQ0eQ5L'0PJ10U^PJQ0y/0^PJQ0dp+07DS5P'0PJQ4Yp+07ES5Q'0PJQ0e/0^PJQ0e/0^PJQ0hp+07HS5R'0PJQ0hp+07IS5S'0PJQ0d/0^PJQ0y/0^PJQ0gp+07LS5T'0PJQ4Yp+07MS5U'0PJQ4YQ3r'0PJQ0yQ2F'0PJQ0jQ2F'0PJQ0QQ3j'0PJQ0wQ0<'Ep+07TS5VQ0q/0`PJQ0q/0`PJQ3l/0`PJ10t`PJQ0p/0`PJQ0p/0`PJQ12/0`PJQ0t/0`PJQ0x/0aPJQ0x/0aPJQ2F/0aPJQ13/0aPJ10taPJ10taPJQ3r/0aPJQ0z/0aPJQ10/0bPJQ10/0bPJQ2O/0bPJQ3}/0bPJQ13/0bPJQ13/0bPJp+021S5W/0bPJQ11/0bPJQ2_/0cPJQ2_/0cPJQ3t/0cPJQ48/0cPJQ3}/0cPJQ3}/0cPJQ3w/0cPJQ1</0cPJQ1e/0fPJQ1e/0fPJQ4:/0fPJQ1@/0fPJQ48/0fPJQ48/0fPJQ1K/0fPJQ1F/0fPJQ1P/0gPJQ1P/0gPJQ1B/0gPJQ1[/0gPJQ1@/0gPJQ1@/0gPJQ1?/0gPJQ1T/0gPJp+02TS5X/0hPJQ5X/0hPJQ1^/0hPJp+02ZS5Y/0hPJQ1[/0hPJQ1[/0hPJQ1Y/0hPJQ1a/0hPJAMUusp+08MS5Z,9Mp+08NS5[Q21;2UPJQ0d/Dlp+08OS5\Q0h/Dup+08PS5]PXp+08VS5^P;Q1zQ0fQ5\Q5\Q5QG6Q0r-0YUQ0fp+08DS5_'4P2Q0fp+08US5`'4P2Q0y/Dwp+08TS5ap+06JS5bQ2gQ2>40wQ2gQ4Y+1CQ0sp+08XS5c'4P2Q0jp+069S5d7Mup+08WS5e,9MQ5cp+02kS5f;2UPJQ5Kp+08[S5g'4P2p+08\S5h,4UP2p+01_S5iQ2?Q053Pp+06US5jQ0y,0LPJPXp+08bS5kp+02lS5lQ5fQ0yQ5gQ5gp+07QS5mG6Q0oQ3~+0YQ45Q0m'0PJPXp+08dS5nQ5fQ2CQ0lp+08]S5oQ5op+07SS5pG6Q4dQ3p+0YQ40Q0g'0PJPXp+08fS5qQ2>Q2<Q0gp+08_S5rQ5rp+07US5sG6Q0bQ3q+0YQ4;Q0l'0PJPXp+08hS5tQ2<Q25Q0gp+08aS5uQ5up+07WS5vG6Q0aQ1L+0YQ5nQ2DQ4Y32PJp+08eS5wQ2R;2ePJAPtd<p+06`S5xQ3|Q0p'0PJQ0u,0LPJQ41Q0Q'0PJQ45Q0n'0PJQ0~Q2n;P<Q5AQ41Q0w'0PJQ45Q3j'0PJQ4?Q0p'0PJQ40Q0v'0PJQ10Q31;P<p+06jS41Q40Q0x'0PJQ47Q13'0PJQ4;Q0w'0PJQ49/0tPJQ3wQ3<Q063PQ5>Q49Q5W'0PJQ4UQ3y'0PJQ4@Q0x'0PJQ4=Q0~'0PJQ1<Q3G;P<p+074S3|Q4=Q11'0PJQ4BQ2_'0PJp+04[S5yQ5W'0PJp+04\S5zQ10'0PJQ4:Q3K;P<Q5GQ5zQ3t'0PJp+04]S5{Q1K'0PJp+04^S5|Q11'0PJp+04_S5}Q3w'0PJp+02HS5~Q3R;P<Q5MQ5|Q1M'0PJQ5}Q1F'0PJp+04`S60Q3t'0PJQ4IQ1<'0PJQ1=p+03bS61'BPJQ1<Q3W'BPJQ1B/BPPJQ2}/BPPJQ1?Q3V'BPJQ0WQ3Q7Mlp+09NS62,9Mp+09OS63Q0UQ3Z32PJp+09PS64Q0Up+04ES6532PJQ63,0oPJp+09RS0UQ0XQ3u32PJQ0\/Dlp+09SS0\Q0WQ0U'0PJQ0\,0oPJQ0Tp+09TS3u'0PJQ0Tp+09US66'0PJQ1T,0oPJQ1m9M~Yp+09YS67,9Mp+08SS68Q1jQ68$0IQ4?PlQ03,i@RoEVP~eP~Q0[PlPAp+07NS0[Cgp+09[S03,9Mp+09\S69p+042S6:72BPJQ4|/Dlp+09]S6;Q4m/Dup+09^S6<Q4{/Dwp+09_S6=Q4}Q1dQ5G+0=7MYp+09`S6>,9MQ1u9MAwp+09aS6?,9Mp+09bS6@p+045S6A72>PJp+09cS6B?2>sPJp+09dS6CQ4B72>PJQ4v/DYp+09eS6DQ1u9M>Yp+09fS6E,9Mp+08`S6FQ1qQ6FQ5QQ6FQ2:Q6FDeQ5}PlPoEVP>eP>Q4|PwP7Q5MCgp+09hS1q,9Mp+09iS6GQ1m721PJ1DBwp+09jS6HQ1{9M>up+09kS6I,9MP~PYP8p+07OS6JCgp+09lS6K,9Mp+09mS6LQ1u727PJQ5M9MAup+09nS6M,9MQ289M1xp+09oS6N,9MQ1}Q20,?ZS20,^Z00[]+0=9M>xp+0:0S6O,9MQ0c=M80p+0:1S6P,9MQ0cQ5C5M7p+0:2S6Q,9M1D1xp+0:3ReAM7Ydp+0:4S6R,9Mp+0:5S6SQ28728PJQ0c,D>p+0:6S6T1D6up+0:7S6U1D5wp+0:8S6VAM>usp+0:9S6W,9Mp+0::S6X?210PJp+0:;S6YQ1{721PJP~PYP1p+07eS6ZCgp+0:<S6[,9Mp+0:=S6\Q1u72>PJ1DClp+0:>S6]p+0:?S6^Q4?723PJ1D5lp+0:@S6_p+0:AS6`Q47723PJp+0:BS6a20@<3S6bp+09ES6cp+0:JS6dp+0:DS6ePwP8C[p+09=S6fQ6e00p8P=p+09HS6g/|7p+08@S6hQ2uQ5{<0m1p+0:GR;p+09K[20x<6A2=7<Q5{p+08=S6i60m8p+0:IS6jp+09M[Q2zQ6060w5Q2z01C7Q2?Q055P1p+08ERiAP>d<p+08FS6kQ2n=P6<p+08GS6lQ31=P5<p+08HS6mQ3<Q065PAp+08IS6nQ3G=PB<p+08JS6oQ3K=PC<p+08KRWQ3R=P~<p+08LS6pp+04fQ4m60mCp+0:SS6qp+09WS6r[Q2?Q055P~Q5[Q4v?Pd<Q5\Q4VQ2n;P<Q5]Q4yQ31;P<p+08QS6sQ4|Q3<Q063Pp+08RS6tQ4mQ3G;P<Q68Q4{Q3K;P<Q5aQ4}Q3R;P<Q5`Q4HQ4M7Mwp+0:\R\,9MQ4\9M3lp+0:]S6u,9M1D8lp+0:^S6vAM8w0p+0:_S6w,9MP1PlP8Q5VCgp+0:`S6x,9Mp+0:aS6yQ4a727PJ1D>up+0:bS6z1D6Yp+0:cS6{Q2k9M>Yp+0:dS6|,9Mp+0:eS6}?27sPJp+0:fS6~?27dPJ1DAwp+0:gRnQ2ap+08AS70+0=9MBYp+0:hS71,9MAM>w0p+0:iS72,9Mp+0:jS73?270PJ1D5Yp+0:kS74Q2|9M7Yp+0:lS75,9Mp+0:mS76Q2k728PJ1D>wp+0:nS77Q2tQ0B,?ZS78,^Z00[]+0=9M6Yp+0:oS79,9MAM1w_p+0;0S7:,9Mp+0;1S7;?270PJ1D6Yp+0;2S7<Q3B9M7Yp+0;3S7=,9Mp+0;4S7>Q2|728PJ1D>wp+0;5S7?Q5p9M6Yp+0;6S7@,9Mp+0;7S7A?28_PJ1D>Yp+0;8S7B1D6wp+0;9S7CPep+07XS7DPep+07\S7EPep+07gS7FPep+07cS7GPeQ7FPep+04;R]PeQ4APeQ5cPep+080RZPep+088S7HPep+08CS7IPep+08BS7JPeQ70PePWPeQ5[PeQ3kPeQ5cPeP]PeK02D1D1D1D1D1D1D1Q0ZPwPoEVP7eP7p+0;;S7KQ3B727PJp+0;<S7L?27_PJQ0}Q7L,X3'`PJ1OS8p+0;?S7MQ6bQ6ap+0;GS7Np+0;AS7OPxP8C[Q6XQ6e/|8p+09<S7PQ6fQ0VQ15Q0M#LS0M604SP<P3DmPJp+09>S7Qp+09??237W=Q7QPJ]=p+05k,`8PJQ0}p+0;ES7R,X3'`PJ1OS8p+0;HS0}Q6bp+0:KS6bp+0;PS7Sp+0;JS7TPYP8C[p+0:CS7Up+0:MS7V/|8Q6cp+09FS7Wp+06=S7XQ15>04S[P<P3DmPJp+09GS15Q6g?237W=Q15PJ]=P;p+0;TS7Yp+0;NS7ZPu&06K#}#YS7[,OSS7\C[P;p+07VS7]P;Q5sP;Q5VP;p+07ZS7^P;Q4VP;P1P;p+07fS7_P;p+07lS7`P;PZP;p+08;S7aP;p+087S7bP;Q7aP;PLP;PrP;p+08lS7cP;Q5_P;Q6pP;Q5eP;Q5^P;Q5`P;Q5rP;Q5kP;Q65P;Q7cP;PLP;DeD1D1D1D1D1D1D1D1D1D1D1D1&0v;1`7CPJQ4<?MYAQ7S,9MQ4}9M3xp+0;QS7d,9M1D8wp+0;RS7eQ0cQ185M8p+0;SS7f,9MQ7Y?28_PJ1D1Yp+0;US7g1D>xp+0;VS7h1D6wp+0;WS7iAM>Y_p+0;XS7j,9Mp+0;YS7kQ4{721PJp+0;ZS7lQ4K721PJp+0;[S7m?21_PJ1DBwp+0;\S7nAM>x0p+0;]S7o,9MP~PYP8p+09AS7pCgp+0;^S7q,9Mp+0;_S7r?27_PJPAPx1DAmp+09CS7sCgp+0;`S7t,9MQ3b=M10p+0;aS7u,9MP>Q3b1D>mQ6cCgp+0;bS6c,9MQ7\9M8up+0;cS7v,9Mp+07mS7w9M7up+0;dS7x,9MQ0c,D1p+0;eS7yPOP7Q17,?SS7zQ1Jp+06HS7{D8Q4n1D1Yp+0;gS4n1D>xp+0;hQ3b,D6p+0;iS7|1D5up+0;jS7}1DAlp+0;kS7~1DBwp+0;lS80Q0A,DCp+0;mS81Q4i,D~p+0;nS82p+0;oS83Q1872CPJp+0<0S84?2B_PJp+0<1S85?2B0PJp+0<2S86?2B0PJp+0<3RLQ7\72BPJp+0<4RrQ5b72BPJp+0<5S87?2B_PJp+0<6R]Q4172BPJp+0<7S88Q4172BPJ1`83PJ1`13PJ1`63PJ1`A3PJ1`C3PJQ4v/`3PJp+0<>Q5=p+06VS8932p+0<?S8:Q5=Q3j32p+0<@S8;Q5=Q1932p+06^S8<,0Rp+06aS8=/0FQ6QQ6PQ6PQ6Op+082S8>Q6yP3Q5AP1O2b2b0b1p+04hPeQ6QQ6QQ6PQ8>Q6yP3Q5HP>O2b2b0b1Q4LQ8=Q6RPePeQ6QQ7Ep+0<:S4LP3p+06gS8?P5O2b2b0b1Q6RPePeQ6QQ6Np+0;=S8@P3Q8?P6O2b2b0b13@Q2>p+06cS8AQ6SQ6RQ6RPep+07[S8Bp+0<9S8CP3p+06hS8DPAO2b2b0b1Q6SQ6RQ6RPep+08?S8Ep+0;:S8FP3Q8DP5O2b2b0b13@Q2<p+06bS8GQ6TQ6SQ6SQ6RQ8BQ8CP3p+06iS8HPBO2b2b0b1Q6TQ6SQ6SQ6RQ6MQ7CP3Q8HPAO2b2b0b13@Q5fQ5AQ6UQ6TQ6TQ6Sp+07]S8Ip+0<;S8JP3Q41PCO2b2b0b1Q6UQ6TQ6TQ6SQ70Q7LP3Q41PBO2b2b0b13@Q5fQ8GQ6VQ6UQ6UQ6TQ7EAkR3QQ0^,I8#\[^32S8KP3p+06kS8LP~O2b2b0b1Q6VQ6UQ6UQ6Tp+09gS8MQ7@P3Q8LPCO2b2b0b13@Q2cQ8?Q6WQ6VQ6VQ6Up+07_S8Np+0<=S8OP3Q5:Q4vO2b2b0b1Q6WQ6VQ6VQ6UQ7Ip+0;>S8PP3Q5:P~O2b2b0b13@Q25Q5AQ6XQ6WQ6WQ6VQ8IQ8CP3Q4EQ4VO2b2b0b1Q6XQ6WQ6WQ6VQ1qQ7@P3Q4EQ4vO2b2b0b13@Q2CQ8HQ6YQ6XQ6XQ6Wp+07aS4vQ8:P3Q5<Q4yO2b2b0b1Q6YQ6XQ6XQ6WPip+0;@S1qP3Q5<Q4VO2b2b0b13@Q2;Q8DQ6[Q6YQ6YQ6XQ4vQ8:P3Q5>Q4|O2b2b0b1Q6[Q6YQ6YQ6XQ6RQ7MP3Q5>Q4yO2b2b0b13@Q2CQ41Q6\Q6[Q6[Q6YQ6Zp+0<CS4yP3Q5?Q4mO2b2b0b1Q6\Q6[Q6[Q6YQ6Vp+0;FS4VP3Q5?Q4|O2b2b0b13@Q3hQ8HQ6]Q6\Q6\Q6[Q4vQ8OP3p+071S3hQ4{O2b2b0b1Q6]Q6\Q6\Q6[Q6KQ8FP3Q3hQ4mO2b2b0b13@Q2HQ8HQ6^Q6]Q6]Q6\Q7GQ8KP3p+072S4mQ4}O2b2b0b1Q6^Q6]Q6]Q6\Q6MQ8@P3Q4mQ4{O2b2b0b13@Q2JQ8LQ6_Q6^Q6^Q6]Q7GQ8:P3p+073S4{Q0EO2b2b0b1Q6_Q6^Q6^Q6]Q6MQ7LP3Q4{Q4}O2b2b0b13@Q2JQ8LQ6`Q6_Q6_Q6^Q6ZQ8KP3Q3|Q0DO2b2b0b1Q6`Q6_Q6_Q6^Q6OQ7MP3Q3|Q0EO2b2b0b13@Q2MQ5<Q6aQ6`Q6`Q6_Q7Fp+0<EP3Q5=fDR~O2b2b0b1Q6aQ6`Q6`Q6_Q6XQ7RP3Q5=Q0DO2b2b0b13@Q2JQ5?Q7UQ6aQ6aQ6`p+07kRCp+0<IS0DP3Q5BfERBO2b2b0b1Q7UQ6aQ6aQ6`Q6]p+0;LS0EP3Q5BP~O2b2b0b13@Q2MQ5>Q6eQ7UQ7UQ6aQ7FQ4yP3Q5@Q3sO2b2b0b1Q6eQ7UQ7UQ6aQ6QQ1qP3Q5@PBO2b2b0b13@Q2RQ5>p+0:ES4}Q6eQ6eQ7Up+07iS4|Q8KP3Q5EQ0CO2b2b0b1Q4}Q6eQ6eQ7UQ6Rp+0;CS7UP3Q5EQ3sO2b2b0b13@Q2VQ4mp+0:FS3sQ4}Q4}Q6ePCQ0DP3Q5GQ4NO2b2b0b1Q3sQ4}Q4}Q6eQ6]p+0;IS8QP3Q5GQ0CO2b2b0b13@Q2RQ3|P;Q3sQ3sQ4}p+07oS0Cp+0<MS8RP3Q5DQ4MO2b2b0b1P;Q3sQ3sQ4}Q6aQ7SP3Q5DQ4NO2b2b0b13@Q2VQ4{p+0:HRBP;P;Q3sPCp+0<GS4NP3Q5FQ4KO2b2b0b1PBP;P;Q3sQ6Tp+0;DS8SP3Q5FQ4MO2b2b0b13@Q2XQ4{Q6jPBPBP;Q7wQ8KP3p+07<S4MQ52O2b2b0b1Q6jPBPBP;Q6VQ7NP3Q4MQ4KO2b2b0b13@Q2YQ5BQ6dQ6jQ6jPBQ0CQ8RP3Q5CQ4<O2b2b0b1Q6dQ6jQ6jPBQ6ap+0;MS4KP3Q5CQ52O2b2b0b13@Q2XQ5EQ6bQ6dQ6dQ6jp+083S52p+0<QR;P3Q5MQ0IO2b2b0b1Q6bQ6dQ6dQ6jQ3sQ7YP3Q5MQ4<O2b2b0b13@Q2YQ5@p+0:LR~Q6bQ6bQ6dQ0Cp+0<KS4<P3Q5IQ4hO2b2b0b1P~Q6bQ6bQ6dQ6XQ0}P3Q5IQ0IO2b2b0b13@Q2^Q5@Q7VP~P~Q6bp+081S0IQ8KP3Q5OQ53O2b2b0b1Q7VP~P~Q6bQ6[p+0;KS6bP3Q5OQ4hO2b2b0b13@Q2dQ5Dp+0:NRAQ7VQ7VP~Q52P;P3Q5LQ4eO2b2b0b1PAQ7VQ7VP~Q3sQ7dP3Q5LQ53O2b2b0b13@Q2^Q4Mp+0:OS53PAPAQ7VQ7bp+0<US4hP3p+07BS6jQ0JO2b2b0b1Q53PAPAQ7VQ6dQ7jP3Q6jQ4eO2b2b0b13@Q2dQ5Fp+0:PS4eQ53Q53PAQ52p+0<OS7VP3Q5NQ4HO2b2b0b1Q4eQ53Q53PAQ6]Q0EP3Q5NQ0JO2b2b0b13@Q2iQ5Fp+0:QS0JQ4eQ4eQ53p+085S8TQ8KP3Q5PQ4PO2b2b0b1Q0JQ4eQ4eQ53Q6_p+0;OS8UP3Q5PQ4HO2b2b0b13@Q2]Q5Mp+0:RS4HQ0JQ0JQ4eQ7bQ4hP3Q5QQ4GO2b2b0b1Q4HQ0JQ0JQ4eQ6dQ7gP3Q5QQ4PO2b2b0b13@Q2iQ5OQ6qQ4HQ4HQ0JQ7ap+0<YS8VP3p+07FS8WQ0KO2b2b0b1Q6qQ4HQ4HQ0JPAQ7nP3Q8WQ4GO2b2b0b13@Q2]Q5Ip+0:TS8XQ6qQ6qQ4HQ7bp+0<SS8YP3p+07GS8ZQ4FO2b2b0b1Q8XQ6qQ6qQ4HQ6aQ7SP3Q8ZQ0KO2b2b0b13@Q2uQ5Ip+0:US0KQ8XQ8XQ6qp+089S8[Q8KP3Q5RQ4DO2b2b0b1Q0KQ8XQ8XQ6qQ6eQ7fP3Q5RQ4FO2b2b0b13@Q2hQ6jp+0:VR5Q0KQ0KQ8XQ7aQ8VP3Q5SQ0LO2b2b0b1P5Q0KQ0KQ8XPAQ7kP3Q5SQ4DO2b2b0b13@Q2uQ5Pp+0:WS4DP5P5Q0KQ8Ep+0<]S4FP3p+07JS8\Q55O2b2b0b1Q4DP5P5Q0KQ4HQ7tP3Q8\Q0LO2b2b0b13@Q2hQ5Np+0:XS0LQ4DQ4DP5Q7ap+0<WS8]P3p+07KRAQ56O2b2b0b1Q0LQ4DQ4DP5Q3sQ7YP3PAQ55O2b2b0b13@Q30Q5Np+0:YS55Q0LQ0LQ4DQ6iQ8KP3Q5TQ59O2b2b0b1Q55Q0LQ0LQ4DPBQ7iP3Q5TQ56O2b2b0b13@Q34Q8Wp+0:ZRBQ55Q55Q0LQ8EQ4FP3Q5Uf\RAO2b2b0b1PBQ55Q55Q0LQ4HQ7oP3Q5UQ59O2b2b0b13@Q30Q5Rp+0:[S8^PBPBQ55Q7Ip+0<aS8_P3Q0[f]R6O2b2b0b1Q8^PBPBQ55P5Q7xP3Q0[PAO2b2b0b13@Q34Q8ZP\Q8^Q8^PBQ8Ep+0<[S8`P3Q6JQ4CO2b2b0b1P\Q8^Q8^PBQ6dQ7jP3Q6JP6O2b2b0b13@Q37Q8ZQ6uP\P\Q8^Q70Q8KP3p+07PS6dQ0PO2b2b0b1Q6uP\P\Q8^P~Q7mP3Q6dQ4CO2b2b0b13@Q3;P4p+07`S4CQ8Wp+0=9H1z$09Q4v$1yQ00Q7EQ5VQ7GQ0vQ0k40bQ0vQ0QQ0uQ5i'yp+0=6,9MR~Q7DPOP3Q7zp+07hS0kQ5vQ1rp+07YS0PK0<p+0=7S8aP3PYP_Q8aP3PxP0Q8aP3Q3bP0Q8aP3PuQ7\Q8aP3PlQ5UQ8aP3PwP_Q8aP3Q0APCQ8aP3Q4ip+07jS8bL0ADFDFDFDFDFDF40;X>~+0C[[[[P3p+07^S8cQ5vQ00Q8NQ0PQ7FQ3rQ0n40bQ3rQ12Q0xQ3l'yp+0=:,9MR~Q7EPOP3Q7zQ7`Q8BQ2<Q8IK0<p+0=;R6P3PYP_P6P3PxP0P6P3Q3bP0P6P3PuQ7\P6P3PlQ5mP6P3PwP_P6P3Q0AQ0CP6P3Q4ip+07nS2<L0ADFDFDFDFDFDF40;X>~+0C[[[[P3Q4vQ7EQ00p+07bS8dQ8cQ3jQ0q60bCQ3jQ0vQ0{Q0w'yp+0=>S8e,9MR~Q4CPOP3Q7zPZQ8NQ25Q4vK0<p+0=?RAP3PYP_PAP3PxP0PAP3Q3bP0PAP3PuQ7\PAP3PlQ5sPAP3PwP_PAP3Q0AQ52PAP3Q4iQ8>L0ADFDFDFDFDFDF40;X>~+0C[[[[P3p+07dS25Q4vQ00Q6ZQ4|Q0CQ5WQ0u40bQ5WQ3rQ10Q2F'yp+0=B,9MR~Q25POP3Q7zp+084S8fQ7GQ2CQ6ZK0<p+0=CR>P3PYP_P>P3PxP0P>P3Q3bP0P>P3PuQ7\P>P3PlQ0PP>P3PwP_P>P3Q0AQ7bP>P3Q4ip+086S8gL0ADFDFDFDFDFDF40;X>~+0C[[[[P3Q7FQ7`Q8>Q10Q2F40bQ00Q4|Q3lQ14Q3jQ3xQ0~'yp+0=FS8h,9MR~Q0kPOP3Q7zQ7HQ7FQ2HQ4|K0<p+0=GS8iP3PYP_Q8iP3PxP0Q8iP3Q3bP0Q8iP3PuQ7\Q8iP3PlQ8IQ8iP3PwP_Q8iP3Q0AQ7aQ8iP3Q4ip+08:S8jL0ADFDFDFDFDFDF40;X>~+0C[[[P3Q0tQ00PtQ5WQ3wQ5WQ2_Q2O'yp+0=JS8k,9MR~Q7`POP3Q7zp+08<S8lPCQ2MQ7wK0<p+0=KR>P3PYP_P>P3PxP0P>P3Q3bP0P>P3PuQ7\P>P3PlQ4vP>P3PwP_P>P3Q0AQ8EP>P3Q4ip+08>S8mL0ADFDFDFDFDFDF40;X>~+0C[[[P3Q0xQ10Q00Q3yPZQ42Q14Q1MQ3y'yp+0=NS8n,9MR~POP3Q7zQ6hQ0CQ2VQ0IK0<p+0=OS8oP3PYP_Q8oP3PxP0Q8oP3Q3bP0Q8oP3PuQ7\Q8oP3PlQ6ZQ8oP3PwP_Q8oP3Q0AQ7IQ8oP3Q4iQ7JL0ADFDFDFDFDFDF60;ZX>~+0C[[[P3Q3wQ52Q1MQ3xQ4:Q3}'yp+0=QS8p,9MS8qQ8qQ52POP3Q7zQ2;Q8fD8p+0=RR~P3PYP_P~P3PxP0P~P3Q3bP0P~P3PuQ7\P~P3PlQ0kP~P3PwP_P~P3Q0AQ6kP~P3Q4iPiL0ADFDFDFDFDFDFS8r40;W>Q0mQ8>Q0|+1vQ0eQ1L'`Q8>POP@19M~p+0<RS8sQ6nQ7In0100000020000Q7UQ7JQ52D8Q0|p+09LS8tPOP4Q6nQ1;Q7JQ52g0JX7R>PlPlQ1:g0JYA%j>g0JZKN=08Q8np+0=ZS1;P3PSQ1EQ8SQ1D#=PSQ1EPSQ8SCHdO4b4Q8pPSQ1DP?Q1D,JSdQ7UDNP~Q1EPOPiP3Q5_Q8TQ0QEGX5~P~Q8bPOPWPlP3Q0=CgQ1EQ5_Q8TQ0QEGX5~PZp+0=SS1DQ4|Q0=:04S332X92P~P;P;Q2<Q0=,4Zp+0;BS8uQ7OQ1qQ1qQ7MPTPzP{P|Q8sp+0=PS8v'b9{E~P}PDb8b6b7X321I3IQ0<Q0=60j3'B^32P3Q8fO1b2b0b1K0?Q8b,ZSQ7OQ1qQ1qQ7MPTPzP{P|PEQ8uPqPEPyQ8sEtP}PDb8b6b7X32AkR3QQ0<,I8R>#\[^32P3Q8fQ1LO2b2b0b1Q7OQ1qQ1qQ7MPTPzP{P|PEQ8nPqPEQ8sp+0=MS8w+0VI0ZP}PDb8b6b7X32103Fp+0=TS8x,X>[^32P3Q8fQ1JO2b2b0b15@ZDAQ4aeQ4aQ1DQ4|Q1DPOQ6pPlP3Q1EPiQ8gQ0mGaW5POQ89Q1EQ5_Q8TD8POQ89Q8@p+06WS1JQ8TD8Q0QQ62POP4Q89Q1EQ5_Q8Tg0J[UPlPuQ1GQ0kQ19g0J\_Pog0J]iQ3dp+044S1EQ8xQ8bQ8xp+0=UR>Q8P,E3Q8b32W5PZB04S3GQ8b52>X92Q8xQ8YQ8YQ7_Q0CQ8SQ7UQ8uQ8uQ7OPTPzP{P|Q8w9{E;P}PDb8b6b7X321I3IS8y/4GS8zQ0B,I3'B^32P3Q8gO1S8{b2b0b1K0?p+06TS8|Q1>DAQ8xQ8b/EGQ4|32eQ4TP3E:b<p+0<LS8}Q8|Q8}$0IPWPuPoEVp+043S8~eQ8~Q8xQ6nQ8xQ1992>3W5Q1LQ4aP3E:b<P4Q5_Q8bQ0kp+0=]RFP<PZp+0<HS19p+06RS90p+06QS91Q4^Q8uQ7OQ7OQ1qp+08iS92Q19P3Q8TQ1LO2b2b0b1p+06OS93PpG7Q6:eQ4PPZQ93,03X92S4PQ2<Q0I/03X92Q8uQ7OQ7OQ1qPTPzP{P|Q8sp+0=LS945WEP}PDb8b6b7X321I3QS95Q0B,I3S96'0^32P3Q8TO1S97b2b0b1p+06NS98PvDAQ93PpDAQ93Q98'0eQ2<p+0=VS99Q4^5d3X92PZQ7GQ8h80T3X92Q8dQ25'0Q4vQ7G'0PXp+0=XS8hQ8dQ4vp+06MS9:Q25Q7Gp+06PS9;G6Q8uQ7OQ7OQ1qPTPzP{P|Q4NQ7M5WEP}PDb8b6b7X32Q96Q95/4Q7dG^32Q97b2b0b1Q93PpG7Q98PvDAQ4OQ4Z'0eN:0iNB0dQ8vp+0=\RpP3PSQ1OQ8PQ1N#=PSQ1OPSQ8PCHdO4b4Q1DPSQ1NP?Q1N,JSdQ8@DNQ8xQ1OQ8xPOp+06XS1NP3p+06YS97Q7bQ5iEGW5POQ1JQ1OQ1NQ8gD8POQ1JQ7BQ2VQ8gD8Q0mQ63POP4Q1JQ1OQ1NQ8gg0J_3PlPwQ1QQ8bQ2\g0J`=Pog0JaGQ3VQ6AP>PCQ99Q7C,E3Q7`32X5>Q0IQ991439S1O,OSQ7`32X92P>p+0<TS63Q63Q0I/49Q0IQ7RQ8SQ7UQ7UQ8uPTPzP{P|1b>y={E>P}PDb8b6b7X321I3IS96/49Q96'B^32P3Q7bO1b2b0b1K0?Q5jQ0IQ8SQ7UQ7UQ8uQ7cQ8kP3Q7bQ0bO2b2b0b1Q8SQ7UQ7UQ8uQ7MQ8RP3Q7bQ3qO2b2b0b13@DA&0SC=2>CeQ4WP3E:b<Q8RQ5jQ8R$0IQ6pPwPoEVQ6:eQ6:P>PWQ99Q2b723X5>Q3qQ4ZP3E:b<P<PiQ1NQ8bQ4QP4PiPCQ8bp+0=^S4QP<Q0IQ0Dp+06SS8kQ90Q4\Q7UQ8uQ8uQ7Op+08jS96Q0DP3Q8gQ0aO2b2b0b1Q9;PvG7Q8~eQ4GQ0IQ5j,03X92PZQ8>/03X92Q7UQ8uQ8uQ7OPTPzP{P|Q8YQ8x5WEP}PDb8b6b7X321I3QS4GQ8y'0^32Q8{b2b0b1Q8|Q1>DAQ9;PvDAQ9;Q8|'0ePZp+0=WS8yQ4\5d3X92Q0IQ4vQ8i80T3X92Q4CQ6Z'0Q7_Q25'0PXp+0=YS8iQ4CQ7_Q9:Q6ZQ25Q91G6Q7UQ8uQ8uQ7OPTPzP{P|Q1q9WE;P}PDb8b6b7X32Q8zQ4G<0TQ^32Q8{b2b0b1Q9;PvG7Q8|Q1>DAQ4RQ4^'0eN:0iJ0WNB0dQ8pPFP3PSQ1SQ7CQ1R#=PSQ1SPSQ7CCHdO4b4Q8xPSQ1RP?Q1R,JSdQ7BDNP>Q1SPOQ97P3Q2XQ7HQ0nEGX5>POQ1NQ1SQ4_Q7bD8POP@Q99,9MQ4yQ1NQ4Rn0100000020000Q7@Q4_Q7bD8Q5iQ64POP4Q1NQ1SQ4_Q7bg0JbQRvPuQ1Ug0Jc[%jvg0JdeN<1@P~Q4QP3PSQ1XQ7AQ1W#=PSQ1XPSQ7ACHdO4b4P>PSQ1WP?Q1W,JSdQ7@DNQ99Q1XQ99POQ4OP3PkQ8[Q12EGW5Q1Dp+0=_S1WP3PSPsQ7Cp+0=EQ7AQ7C7fSdO4b4Q99Q7B72sQ8yPsQ8yPOp+06[S1UPuP3Q1XQ2YQ8jQ0pGaW5POQ4]Q1XPkQ8[D8POP@Q8h,9Mp+0<XS1SQ4]Q3gn0100000020000Q7@PkQ8[D8Q12Q0UPOP4Q4]Q1XPkQ8[g0JeoRvPlPlQ1:g0Jg9%jvg0JhCN=08Q8xp+0=`S1:P3PSQ1]Q7AQ1\#=PSQ1]PSQ7ACHdO4b4Q8yPSQ1\P?Q1\,JSdQ7@DNQ8hQ1]Q8hPOQ3`P3Q2\Q7aQ3lEGW5P;Q7@Q97>0y;;Q5]PlPoEVQ3geQ3gQ8iQ0CQ8iPOQ4jPlP3Q4KCgQ1]Q2^Q8lQ0qEGW5Q8TQ1;Q7wQ0=:04S332X92Q8iQ1SQ1SQ8>Q8TQ0='4Q8QQ0}Q7NQ7NQ4VPTPzP{P|Q0_Q8iQ8y'b5{EP}PDb8b6b7X32Q0^,I3Q0=:0j3I'B^32P3Q7aO1b2b0b1K0?Q97Q8TQ0}Q7NQ7NQ4Vp+090S0=Q8nP3Q7aQ0oO2b2b0b1Q0}Q7NQ7NQ4VQ7UP;P3Q7aQ3~O2b2b0b13@DAQ4ZeQ4ZQ1;Q7wQ1;POQ4kPlP3Q1]Q2bQ6iQ0vGaW5POp+04<RvQ1]Q2^Q8lD8POPvQ7AQ2YQ8lD8Q0qQ66POP4PvQ1]Q2^Q8lg0JiMPlPuQ1GQ2<Psg0JjWPog0JkaQ3UQ3ap+0=[RvQ2<Q7R,E3=2pZX5vQ8fB04S3G=2pZX92Pvp+0<ZS1]Q1]Q6ZQ8TQ6bQ7TQ8QQ8QQ0}PTPzP{P|Q8RQ8w5{EP}PDb8b6b7X32Q0^,I3S3l/4GS1\1I3['B^32P3Q6iO1S1Xb2b0b1K0?Q91Q1CDAQ9;Q0C52veQ3`P3E:b<Q8YQ91Q8YQ7BQ8YQ1UQ8YDeQ6tPuPoEVPPePPPvPsA2p3sX5v1ivsPjP3E:b<P<Q8<Q2^Q2<PkP<PWQ8<Q2<Q4TP4PWQ0IQ2<p+0=dS5iP<Q7bQ7VQ97Q1NQ4`Q8QQ0}Q0}Q7NQ0=Q7VP3Q8lQ0oO2b2b0b1Q89Q0]G7p+049S4ReQ56Q7bQ4PQ8fQ7H/03X92Q8QQ0}Q0}Q7NPTPzP{P|Q8VQ945WEP}PDb8b6b7X321I3QS941I3[S4P'0^32P3Q8lO1S56b2b0b1Q98Q1>DAQ89Q0]DAQ89Q98'0eQ8fQ4`9d3FX92Q7bQ25Q8w80T3X92Q7G/0CQ8dQ8b'0PXQ1WQ7GQ8dQ9:PCQ8bQ1JG6Q8QQ0}Q0}Q7NPTPzP{P|Q4NQ4V5WEP}PDb8b6b7X32Q4PQ94/4Q7dG^32Q56b2b0b1Q89Q0]G7Q98Q1>DAQ4ZQ4['0eN:0iJ0WJ0WNB0dQ8yp+0=cS0]P3PSQ1`Q7BQ1_#=PSQ1`PSQ7BCHdO4b4Q1;PSQ1_P?Q1_,JSdQ7ADNPvQ1`POQ3nP3Q2^Q8mQ0tEGX5vPOp+04=S1_Q1`Q2\Q6iD8POQ1_Q7?Q2DQ6iD8Q0vp+09VS56POP4Q1_Q1`Q2\Q6ig0JlkPlPwQ1QQ2<Q2]g0Jn5Pog0Jo?Q3WQ3dPpQ0CQ1q,E3=2FZX5pQ8TQ1O,OS=2FZX92PpQ8`Q8`Q8T/49Q8TQ0EQ6bQ7TQ7TQ8QPTPzP{P|Q0_/byQ0_5{ES1OP8Q1IQ1O00}8$09d&0r3H0|b6b7X32Q6iO1b0b1K0?Q90Q8TQ6bQ7TQ7TQ8Qp+08oS1OQ8KP3Q8mQ0fO2b2b0b1Q6bQ7TQ7TQ8QQ8FQ0DP3Q8mQ5KO2b2b0b13@DAQ98Q0C52peQ3cP3E:b<Q63Q90Q63Q7CQ63p+06\S1`Q63DeQ68PwPoEVPPePPPpQ6tQ2u92F3X5pQ5KPjP3E:b<P<Q2bQ2\Q2<Q8UQ2bQ0C40wP<p+06_S63Q2bQ2<Q2YP<Q6pQ63Q2<Q4WP4Q6pQ8>Q2<p+0=eS1_P<Q7Hp+0<PS4Pp+06ZS94Q97Q4]Q7TQ8QQ8QQ0}p+091S8wQ4PP3Q6iQ5JO2b2b0b1Q1JQ1>G7p+04:eQ59Q7HQ90,03X92Q8fQ8[/03X92Q7TQ8QQ8QQ0}PTPzP{P|Q1]Q0_5WEP}PDb8b6b7X321I3QS59Q3l'0^32Q1Xb2b0b1Q91Q1CDAQ1JQ1>DAQ1JQ91'0eQ8fQ4QQ4]5d3X92Q7HQ8dQ8n80T3X92Q4vQ7`'0Q6Z/0CPXQ1:Q4vQ6Zp+06LS8nQ7`PCQ1NG6Q7TQ8QQ8QQ0}PTPzP{P|Q8RQ7N5WEP}PDb8b6b7X32Q1\Q59<0TQ^32Q1Xb2b0b1Q1JQ1>G7Q91Q1CDAQ4ZQ4`'0eN:0iJ0WJ0WJ0WNB0dQ8hQ5iP3PSQ1dQ7@Q1c#=PSQ1dPSQ7@CHdO4b4PvPSQ1cP?Q1c,JSdQ7?DNPpQ1dPOp+04?P3Q2NQ8EQ0wEGX5pPOQ3nQ1dQ2MQ8mD8POP@19MFQ4yQ3nQ3gn0100000020000Q7>Q2MQ8mD8Q0tQ6rPOP4Q3nQ1dQ2MQ8mg0K0IS1dPYQ1bg0K1SQ1d#jg0K2]N<0hQ8iQ1_P3PSQ1iQ7?Q1h#=PSQ1iPSQ7?CHdO4b4PpPSQ1hP?Q1h,JSdQ7>DNPFQ1iPOQ3`P3Q2RQ6hQ0uEGX5FQ1;p+0=fS1hP3PSQ1mQ7?Q1l#=PSQ1mPSQ7?CHdO4b4Q1mQ7>52FQ4QQ1mQ4QPOQ3oPYP3Q1iQ4lQ70Q3rGaW5POQ6AQ1iQ2RQ6hD8POP@Q1W,9Mp+0<DQ6AQ3]n0100000020000Q7=Q2RQ6hD8Q0uQ67POP4Q6AQ1iQ2RQ6hg0K3gS1iPwPYQ1gg0K51Q1i#jg0K6;N=08Pvp+0=gS1iP3PSQ1pQ7>Q1o#=PSQ1pPSQ7>CHdO4b4Q4QPSQ1oP?Q1o,JSdQ7=DNQ1WQ1pQ1WPOQ3aP3Q2VQ7JPtEGW5Q1SQ7=Q1SQ89Q1SQ8@Q1SQ5xQ1SK02Q5ePYPoEVQ3]eQ3]Q1:Q1mQ1:POQ3mPwP3Q7ACgQ1pQ4_Q7IQ2FEGW5PFp+0=iS3mP3PSQ1uQ7>Q1t#=PSQ1uPSQ7>CHdO4b4Q1:Q1uQ7=32p+0=aS1tQ1uQ1tPOQ4RPwP3Q1pQ2XQ5_Q0xGaW5POQ3eQ1pQ4_Q7ID8POP@p+0=bS4R,9MQ19Q3eQ3Zn0100000020000Q7=Q4_Q7ID8Q2FQ69POP4Q3eQ1pQ4_Q7Ig0K7ES1pPYPwQ1Qg0K8OQ1p#jg0K9YN=08Q4Qp+0=jS1pP3PSQ1wQ7>Q1v#=PSQ1wPSQ7>CHdO4b4Q1tPSQ1vP?Q1v,JSdQ7=DNQ4RQ1wQ4RPOPPP3PkPiQ3jEGW5Q8`Q7=Q8`Q7@Q8`Q97Q8`Q1qQ8`Q8AQ8`DeD1p+08ZS1vPwPoEVQ3ZeQ3ZQ0]Q1uQ0]POQ8~PYP3Q7NCgQ1wQ2YQ6kQ0zEGW5Q0]Q1uQ0]POQ8~PYP3Q1wQ2YQ6kQ0zGaW5POPjQ1wPkPiD8POP@Q5i,9MP;PjQ3Zn0100000020000Q7<PkPiD8Q3jQ6<POP4PjQ1wPkPig0K:cS1wPuQ1yg0K;mQ1w#jg0K=7N<1@Q1:p+0=lS1wP3PSQ1}Q7=Q1|#=PSQ1}PSQ7=CHdO4b4Q0]PSQ1|P?Q1|,JSdQ7<DNQ5iQ1}Q5iPOPPP3Q2\Q6lQ0~EGW5Q1tp+0=mS1tP3PSQ1{Q7?Q8oQ7=Q7?7fSdO4b4Q5iQ1{Q7>32Q1_Q1{Q1_POQ3ePuP3Q1}Q2^Q6mQ0{GaW5POQ3VQ1}Q2\Q6lD8POP@Q1h,9Mp+0<JS0{Q3VQ3Zn0100000020000Q7<Q2\Q6lD8Q0~Q6>POP4Q3VQ1}Q2\Q6lg0K>AS1}PxQ20g0K?KQ1}#jg0K@UN<0hQ4Rp+0=nS1}P3PSQ23Q7=Q22#=PSQ23PSQ7=CHdO4b4Q1_PSQ22P?Q22,JSdQ7<DNQ1hQ23Q1hPOPPP3Q2bQ6nQ5WEGW5Q0]p+0=oS22P3PSQ28Q7=Q27#=PSQ28PSQ7=CHdO4b4Q1hQ28Q7<32Q1iQ28Q1iPOPjPxP3Q23Q2dQ6oQ13GaW5POQ3aQ23Q2bQ6nD8POP@p+0=hS27,9MQ4<Q3aQ3Zn0100000020000Q7;Q2bQ6nD8Q5WQ6@POP4Q3aQ23Q2bQ6ng0KA_Q0cPxQ2=,?VS2=Q0:g0KBiPog0KD3p+0<`S0:Q7:Q0:Q79Q0:Q77Q0:Q7BQ0:Q7KQ0:Q8<Q0:Q7RQ0:Q8DQ0:K02D1D1Q5rPxPoEVQ61eQ61Q27Q28Q27Q7vQ2gP3Q2=,^VQ05Q6GJ00W5Q1_p+0>1S2=P3PSQ2?Q79P~Q77Q797fSdO4b4Q27Q2?Q7732Q3mQ2?Q3mQ7xQ2iP3Q05Q6HDmW5Q7vQ2dp+098S28Q7vQ2zQ28Q7vQ4kQ28Q7vp+08YS23Q28Q4AQ4kQ7qQ1vQ8mQ2?Q05P<Q4kQ5A/4NS4AQ793;X:=P^Q0HQ5Ap+05GS28P3CcX92Q5_Q8}Q7wQ97'CQ7`Q1N'CQ7wQ97Q7`Q1NPXQ1}Q8pQ8vQ4<Q5_Q5_Q8gG6PXQ1}Q7HQ7bQ8AP^P^P~G6EQQ7jQ7iQ7iQ7hPTPzP{P|PEQ7lPqPEPEQ4PQ0]PEQ01P:P:Q02P1J1tR:GUP}PDb8b6b7X32X;JAkR3QS02P>P8Q0BP7CS[^32^;JP3Q1UPWQ0|O3b2b0b1p+06dS1UQ5JG7Q77Q03DAQ4jp+05FQ773;ep+09ZS01p+097S1ND<Q92P<Q4AQ27'0X:=Q5_Q19Q1JQ89Q4gQ7jQ7iQ7iQ7hQ03Q0DP3PWQ0jO2S4Ab2b0b1Q1UQ5JG7Q65eQ01Q1ND<GRE:Q2zQ4fQ4EQ8EQ2?Q05P<Q4gQ41/4NS65Q793;X:=P^Q0HQ41p+05DP3CcX92PiQ8}Q5j,CCQ8bQ8|'CPCQ5jQ8bQ8|PXQ1}Q8pQ8vQ4<PiPiQ8fG6PXQ1}Q8TQ7aQ8GP^P^P~G6EQQ7jQ7iQ7iQ7hPTPzP{P|PEQ7lPqPEPEQ4PQ1pP:GUP}PDb8b6b7X32X;JQ02P>P8PIP7CS[^32^;JP3Q1JPWQ0|O3b2b0b1Q8HQ0oG7Q77Q03DAQ4bp+05CQ773;eQ2yQ34D<Q92P<Q65Q27'0X:=PiQ19Q8kQ90Q4]Q7jQ7iQ7iQ7hQ01Q19Q4Ab2b0b1Q8HQ0oG7Q3zeQ2yQ34D<GRE:Q2dQ7oQ36Q6iQ2?Q05P<Q4]Q8</4NS3zQ793;X:=P^Q0HQ8<p+05AS65P3CcX92Q7IQ8}Q4|Q91'CQ0kQ9;'CQ4|Q91Q0kQ9;PXQ1}Q8pQ8vQ4<Q7IQ7IPZG6PXQ1}Q8>Q0IQ1`P^P^P~G6EQQ7jQ7iQ7iQ7hPTPzP{P|PEQ7lPqPEPEQ4PPpP:GUP}PDb8b6b7X32X;JQ02P>P8P[P7CS[^32^;JP3Q8kPWQ0|O3b2b0b1p+06]S1`Q3~G7Q77Q03DAQ4`p+05@S8TQ773;eQ6rp+095S8|D<Q92P<Q3zQ27'0X:=Q7IQ19Q93Q98Q4[Q7jQ7iQ7iQ7hp+09XQ4NQ4Ab2b0b1Q1`Q3~G7Q4ceQ6rQ8|D<GRE:Q2gQ2?Q05Q4fQ4SQ8lQ2?Q05P<Q4[Q5x/4NS2?Q793;X:=P^Q0HQ5xQ8TP3CcX92Q7JQ8}Q7FQ9:'CQ7_Q8n'CQ7FQ9:Q7_Q8nPXQ1}Q8pQ8vQ4<Q7JQ7JQ2<G6PXQ1}Q0CQ52Q94P^P^P~G6EQQ7jQ7iQ7iQ7hPTPzP{P|PEQ7lPqPEPEQ4PQ0_P:GUP}PDb8b6b7X32X;JQ02P>P8Q0^P7CS[^32^;JP3Q93PWQ0|O3b2b0b1Q63Q4dG7Q77Q03DAQ4Xp+05?S02Q773;eQ2yQ34D<Q92P<Q2?Q27'0X:=Q7JQ19p+06KS19Q5bQ4WQ7jQ7iQ7iQ7hQ6rp+0<FS6rQ4Ab2b0b1Q63Q4dG7p+04BeQ2yQ34D<GRL05Q79P3E>b4Q3ZP3E:b<N?1sQ5ip+0>0S63P3PSQ2AQ7<Q2@#=PSQ2APSQ7<CHdO4b4Q1iPSQ2@P?Q2@,JSdQ7;DNQ27Q2AQ27POPPP3Q2gPWQ2OEGW5Q1_Q2=P3PSP0Q7>1i29Q72Q7>7fSdO4b4Q27Q7=720Q3mP0Q3mPOQ3fQ0cP3Q2AQ2iQ6pQ10GaW5POQ3aQ2AQ2gPWD8POQ3aQ71Q2gPWD8Q2OQ6CPOP4Q3aQ2AQ2gPWg0KE=Q0cPmQ2Bg0KFGPog0KGQp+0<bS2BPnQ2BQ7<Q2BQ7;Q2BQ7:Q2BQ8FQ2BQ8@Q2BQ5xQ2BQ7NQ2BQ41Q2BDeD1D1D1Q5uQ0cPoEVp+03_S5xeQ5xQ1pP0Q1pQ3V/Dm-073$09W5Q66Q3WP3E:b<N>1>Q1hp+0>2S1hP3PS&01K$03$0]#LR^,?SS2AQ72%=^PSQ2APSQ72CHdO4b4Q3mPSP^P?1JS^dQ71DNQ1pQ2AQ1pPOQ3VP3Q2mQ5ZQ14EGW5POQ3dQ2AQ2iQ6pD8POQ3dQ3uQ2iQ6pD8Q10Q6DPOP4Q3dQ2AQ2iQ6pg0KH[PuQ1QQ2Gg0KIePog0KJop+0<cS2AQ71Q2AQ7=Q2AQ7<Q2AQ7;Q2AQ7KQ2AQ8PQ2AQ8=Q2AQ0}Q2AQ8LQ2ADeD1D1D1Q5kPuPoEVQ5xeQ5xp+0=kS6DQ1{Q6DQ1wQ2G723W5Q27p+0>4S14P3PSQ1{Q2GQ99Q8FQ71'BdO4b4Q3WP3E:b<N>1=Q1ip+0>3S1iP3PSQ2GQ66P>Q669fnSdO4b4Q1pQ0GP?Q0G,JSd60KSR^Q3u32Q6DQ2GQ6DPOQ3fP3Q2]Q5[Q11EGW5Q27Q14P3PSQ2GPnQ99Q71?fSndO4b4Q6DQ2GQ6De00H972^POQ3fQ2GQ2]Q5[D8POP@Q1t,9MQ8YQ3fQ3Pn0100000020000Q6~Q2]Q5[D8Q11Q8MPOP4Q3fQ2GQ2]Q5[g0KL9R^PYPwQ1Gg0KMC%j^g0KNMN=08Q3mp+0>5S3mP3PSQ2LPnQ2K#=PSQ2LPSPnCHdO4b4Q1wPSQ2KP?Q2K,JSdQ6~DNQ1tQ2LQ1tPOQ61P3Q2uQ5]Q3xEGW5p+0<fS2uQ74Q2uQ7@Q2uQ7?Q2uQ7>Q2uQ8PQ2uQ7OQ2uQ1UQ2uQ6bQ2uQ5<Q2uDeD1D1D1Q5wPwPoEVQ3PeQ3PQ1}Q1uQ1}POQ3`PYP3Q7jCgQ2LQ2vQ6sQ3wEGW5Q6Dp+0>7R^P3PSPdQ71Q8xQ719fnSdO4b4Q1}?2dnQ22PdQ22POQ3cPYP3Q2LQ2hQ6tQ3}GaW5POQ3fQ2LQ2vQ6sD8POP@Q63,9MQ4FQ3fQ3]n0100000020000Q6~Q2vQ6sD8Q3wQ6HPOP4Q3fQ2LQ2vQ6sg0KOWPuPlQ1GQ7vPsg0KPaPog0KQkp+0<hS1GQ6}Q1GQ76Q1GQ7BQ1GQ7AQ1GQ7@Q1GQ1qQ1GQ7UQ1GQ5HQ1GQ4KQ1GQ5?Q1GK02D1D1D1p+08gS2LPlPoEVQ3PeQ3PQ63Q7IQ63Q7~Q2zP3Q7lP<Q01J00W5Q6nQ2=B04S3G72iX92Q63p+0<oS01Q01Q6oQ8jQ7tQ7rQ7qQ7qQ7oPTPzP{P|Q4RQ2B5{EP}PDb8b6b7X321I3[Q0^>0j3G'B^32P3Q6tO1b2b0b1K0?Q5HQ6nQ7rQ7qQ7qQ7oQ7sQ8KP3Q6tQ0pO2b2b0b1Q7rQ7qQ7qQ7oQ7ZQ4FP3Q6tQ12O2b2b0b13@DAQ4geQ4gQ2=PiQ2=Q80Q30?P3<S12Q0332W5Q7~Q35?Pi<Q7~Q80Q03723W=P4Q3FPiPsPWQ4<Q0mQ5APUDAQ5AQ227dGeI1<Q2zPiP<Q3AQ35Q5_PiP<P<Q3{Q8D/4NS7oQ5H3;X:=PWQ14,43S0pQ8Dp+05HP3CcX92Q6oQ7aP3Q0pQ6pCcX92Q91Q9;'CQ93Q98'CQ91Q9;Q93Q98PXp+0>6S0pQ8jQ8[Q1UQ6oQ6oQ8gG6PXQ0pQ7bQ7aQ8GPWPWQ7HG6EQQ7tQ7rQ7rQ7qPTPzP{P|PEPEp+0<^S7qQ0_+1rQ2AQ0]5WEH1qP}PDb8b6b7X321I3[S7H/4GQ0^,I3S7aQ7aPGQ7HI0:^32P3Q68O1b2b0b1Q8?Q0rG7Q5APUDAQ43Q28Q5A3;eQ3JQ3ED<PWQ4PQ1JQ89Q8TQ0mQ5APUG7Q3veP<Q7oQ63'0X:=Q6oQ4PQ8kQ90Q4kQ0QQ8?Q0rG7Q3{eQ3JQ3ED<GRL05Q5HP3E>b4Q61P3E:b<&0RsNA0>Q1wp+0>8S1wP3PSQ2QPnQ2P#=PSQ2QPSPnCHdO4b4Q22PSQ2PP?Q2P,JSdQ6~DNQ63Q2QQ63POQ3aP3Q2zQ68Q3tEGW5POPPQ2QQ2hQ6tD8POP@Q2=,9Mp+0<VS2PPPQ2bn0100000020000Q6}Q2hQ6tD8Q3}Q6IPOP4PPQ2QQ2hQ6tg0KS5PwPlQ1Qp+03]S2hQ3Ag0KT?Pog0KUIp+0<iS2QQ7ZQ2QQ6~Q2QQ77Q2QQ7CQ2QQ7BQ2QQ7AQ2QQ7OQ2QQ8SQ2QQ8?Q2QQ7ZQ2QQ3hQ2QDeD1D1D1D1Q5tPlPoEVQ5xeQ5xQ2=Q5_Q2=Q80Q30P3Q7gP<Q3JJ00W5Q2=Q5_Q2=Q80Q12Q3J32W5P4Q35Q5_Q5xQ6oQ4<Q0QQ8?Q0rDAQ8?Q227dGeI1<Q8AQ5_$0oE:Q3QP3E:b<Q3A$0RNA0>Q1tp+0>9S1tP3PSQ2UQ6~Q2T#=PSQ2UPSQ6~CHdO4b4Q63PSQ2TP?Q2T,JSdQ6}DNQ2=Q2UQ2=POQ2gP3Q30Q5aQ2_EGW5POQ2dQ2UQ2zQ68D8POP@Q1h,9Mp+0=2S2_Q2dQ2Yn0100000020000Q6|Q2zQ68D8Q3tQ6KPOP4Q2dQ2UQ2zQ68g0KVSRGPlPlQ2Sg0KW]%jGg0KXgN=08Q1}p+0>:S1}P3PS%oK$0D#LRG,?SS2SQ6}%=GPSQ2SPSQ6}CHdO4b4Q2=PSPGP?1JSGdQ6|DNQ1hQ2SQ1hPOQ2^P3Q4SQ5`Q42EGW5p+0<kRGQ3APGQ7SPGQ71PGQ7:PGQ7KPGQ8FPGQ7CPGQ7UPGQ4VPGQ8HPGQ7SPGQ4{PGK02D1D1D1D1Q96PlPoEVQ2YeQ2YQ1iQ6kQ1iPOQ2mPlP3Q71CgQ2SQ34Q5^Q1<EGW5Q6pQ14Q6oQ0<:04S332X92Q1iQ2_Q2_Q5\Q6pQ0<'4Q7vQ6cQ7uQ7uQ7tPTPzP{P|Q1iQ0_Q1h'b5{EP}PDb8b6b7X321I3IQ0^Q0<60j3'B^32P3Q5`O1b2b0b1K0?Q8HQ6pQ6cQ7uQ7uQ7tQ7WQ8KP3Q5`Q0vO2b2b0b1Q6cQ7uQ7uQ7tQ7dQ0:P3Q5`Q0qO2b2b0b13@DAQ4keQ4kQ14Q6oQ14POQ2]PlP3Q2SQ36Q5eQ1=GaW5POQ2iQ2SQ34Q5^D8POQ2iQ69Q34Q5^D8Q1<Q6NPOP4Q2iQ2SQ34Q5^g0KZ1PuQ1QQ2Wg0K[;Pog0K\Ep+0<mRGQ5=PGQ3PPGQ7ePGQ73PGQ7<PGQ8@PGQ7LPGQ7KPGQ7RPGQ0}PGQ8LPGQ7ePGQ5=PGDeD1D1D1D1D1Q7cPuPoEVQ2XeQ2XQ3mPsQ3mQ0pQ2W723W5Q1hp+0>>S34P3PSPsQ2WQ5iQ7hQ71'BdO4b4Q2^P3E:b<N>1=Q2=p+0>=RsP3PSQ2WQ6;Q0]Q6;9fnSdO4b4Q14Q0FP?Q0F,JSd60KSRGQ6932Q3mQ2WQ3mPOQ2]P3Q37Q5cQ1MEGW5Q1hQ34P3PSQ2WPnQ5iQ71?fSndO4b4Q3mQ2WQ3me00H972GPOQ2]Q2WQ37Q5cD8POP@19M^p+0<\S5iQ2]Q2in0100000020000Q6~Q37Q5cD8Q1MQ6PPOP4Q2]Q2WQ37Q5cg0K]OPwPYQ1QQ83P0g0K^YPog0K_cQ01Q5@Q01Q61Q01Q7YQ01Q75Q01Q7>Q01Q7MQ01Q8PQ01Q8@Q01Q7NQ01Q7TQ01Q4EQ01Q7YQ01Q5@Q01DeD1D1D1D1D1p+08nS01PYPoEVPkePkP^PdQ86Q3;P3Q7mP<Q6UJ00X5^Q14p+0>@S7mP3PSPdPnPFQ7:?fSndO4b4Q6~92^dQ1wPdQ1wPLQ4fP3P<Q6VDmW5Q86Q37Q7sQ86Q3JQ7sQ86p+05BRGQ7sQ86Q2LQ7sQ0WPGQ81Q92Q5ZPdP<P<Q3|/4NS8@Q7;5;GX:=P`p+0>;RG,43S2WQ3|Q51P3CcX92Q68P;Q8fQ8k'CQ52Q90'CQ8fQ8kQ52Q90PXPsPpPvQ4PQ68Q68PiG6PXPsQ6lQ6kQ4mP`P`PFG6EQQ4np+0;fS2iQ2iQ7yPTPzP{P|PEQ7|PqPEPEQ4hQ1hP:GUP}PDb8b6b7X32X;JAkR3QS1hQ1:P8Q0BP7CS[^32^;JP3Q5jQ1vPtO3b2b0b1Q4{Q0iG7Q7:Q6<DAQ65p+05US69Q7:3;eQ6GQ7WD<Q1NP<Q8@/0^X:=Q68Q8]Q5HQ5Ap+05KS8@Q4nQ2iQ2iQ7yQ6HQ1SP3Q1vQ3rO2S3rb2b0b1Q4{Q0iG7Q47eQ6GQ7WD<GRE:Q3JQ3ZQ4MQ5[PdP<P<Q65Q5G/4NS7WQ7;3;X:=P`Q2WQ5Gp+05SS47/03S1S3hX92Q5aP;Q8>Q91'CQ0IQ9;'CQ8>Q91Q0IQ9;PXPsPpPvQ4PQ5aQ5aQ7IG6PXPsQ5_Q6oQ3hP`P`PFG6EQQ4nQ2iQ2iQ7yPTPzP{P|PEQ7|PqPEPEQ4hQ1tP:GUP}PDb8b6b7X32X;JQ1hQ1:P8PIP7CS[^32^;JP3Q8kQ1vPtO3b2b0b1Q5EQ0gG7Q7:Q6<DAQ8Tp+05RS8kQ7:3;eQ3UQ3PD<Q1NP<Q7W/0^X:=Q5aQ8]Q8GQ8=p+05IS0IQ4nQ2iQ2iQ7yQ6GQ8]Q3rb2b0b1Q5EQ0gG7Q40eQ3UQ3PD<GRE:Q37Q80Q3QQ6pPdP<P<Q8TQ4E/4NS80Q7;3;X:=P`Q2WQ4EQ4oP3CcX92Q6tP;Q93,CZS4oQ0CQ98'CS37PZQ93Q0CQ98PXPsPpPvQ4PQ6tQ6tQ8EG6PXPsQ70Q6hQ8LP`P`PFG6EQQ4nQ2iQ2iQ7yPTPzP{P|PEQ7|PqPEPEQ4hQ6DP:GUP}PDb8b6b7X32X;JQ1hQ1:P8P[P7CS[^32^;JP3Q91Q1vPtO3b2b0b1Q5:Q0hG7Q7:Q6<DAQ02p+05OS6DQ7:3;eQ6Ep+09DS6hD<Q1NP<Q80/0^X:=Q6tQ8]Q8<Q1`Q28Q4nQ2iQ2iQ7yQ8MQ2PQ3rb2b0b1Q5:Q0hG7Q4?eQ6EQ6hD<GRE:Q3;PdP<Q3ZQ5xPWPdP<P<Q02Q5>/4NRdQ7;3;X:=P`Q2WQ5>Q6DP3CcX92Q6sP;Q2<Q9:'CS2WQ7wQ8n'CS6hQ2<Q9:Q7wQ8nPXPsPpPvQ4PQ6sQ6sQ6iG6PXPsQ8mQ7JQ8HP`P`PFG6EQQ4nQ2iQ2iQ7yPTPzP{P|PEQ7|PqPEPEQ4hQ0_P:GUP}PDb8b6b7X32X;JQ1hQ1:P8Q0^P7CS[^32^;JP3Q93Q1vPtO3b2b0b1Q5<Q0dG7Q7:Q6<DAQ4kp+05NQ7:3;eQ3UQ3PD<Q1NP<10d^X:=Q6sQ8]Q94Q97p+05EQ4nQ2iQ2iQ7yQ6EQ4hQ3rb2b0b1Q5<Q0dG7Q45eQ3UQ3PD<GRL05PnP3E>b4Q2bP3E:b<Q03NA0>Q1ip+0>?RdP3PSQ2[PnQ2Z#=PSQ2[PSPnCHdO4b4Q0pPSQ2ZP?Q2Z,JSdQ6~DNP^Q2[POQ2]P3Q3;Q1vQ48EGX5^POQ2mQ2[Q2yQ23D8POQ2mQ6}Q2yQ23D8Q1KQ6QPOP4Q2mQ2[Q2yQ23g0K`mPwPmQ0RQ0>$0L'wg0Kb7Pog0KcAp+0=0RtQ6|PtQ5EPtQ3UPtQ7gPtQ76PtQ7?PtQ1qPtQ7MPtQ8PPtQ0}PtQ6bPtQ5<PtQ7gPtQ5EPtK02D1D1D1D1D1Q1OPwPoEVQ2VeQ2VQ1wP0Q1wQ2r/Dm-073$09W5Q6BQ2YP3E:b<N>1pQ14Q7mP3PSQ2aQ6~Q2`#=PSQ2aPSQ6~CHdO4b4P^PSQ2`P?Q2`,JSdQ6}DNQ1wQ2aQ1wPOQ2rP3Q4fQ5gQ4:EGW5POQ2]Q2aQ3;Q1vD8POP@Q1t,9Mp+0<_S4:Q2]Pkn0100000020000Q6|Q3;Q1vD8Q48PePOP4Q2]Q2aQ3;Q1vg0KdKRtPYQ1bg0KeU%jtg0Kf_N<0hQ3mp+0>ARtP3PSQ2fQ6}Q2e#=PSQ2fPSQ6}CHdO4b4Q1wPSQ2eP?Q2e,JSdQ6|DNQ1tQ2fQ1tPOQ2\P3Q3@Q5hQ1eEGW5Q0pp+0>BS2eP3PSQ2kQ6}Q2j#=PSQ2kPSQ6}CHdO4b4Q1tQ2kQ6|32Q1}Q2kQ1}POQ2vPYP3Q2fQ35Q5oQ4>GaW5POQ2gQ2fQ3@Q5hD8POP@19MGQ0:Q2gQ2Yn0100000020000Q6|Q3@Q5hD8Q1eQ6SPOP4Q2gQ2fQ3@Q5hg0KgiPwPYQ2l,?VS2lPLP0g0Ki3Pog0Kj=p+0=3R`Q6{P`PnP`Q5FP`Q3]P`Q7jP`Q7:P`Q7BP`Q7UP`Q8uP`Q7OP`Q6bP`Q7ZP`Q3hP`Q7jP`Q5FP`DeD1D1D1D1D1D1p+092PYPoEVQ2VeQ2VPGQ2kP]Q3EP3Q2l,^VP<Q6YJ00X5GQ1wp+0>DR`P3PSQ2nQ6|PFQ6{Q6|7fSdO4b4Q2nQ6{52Gp+0><S2lQ2nQ2lQ88Q3FP3P<Q6[DmW5P]Q4fQ15P]Q5xQ15P]Q65Q15P]Q96Q15Q0WQ65Q85p+08mS15Q6sQ2nP<P<Q65Q5E/4NS6[Q6|3;X:=Pa143dS65Q5EQ4r/03S2k3hX92Q5eP;Q4oQ37PZQ93Q0CQ98PXPtPpPvQ4PQ5eQ5eQ6nG6PXPtPWQ6oQ5BPaPaPFG6EQQ7~Q7}Q7}Q7|PTPzP{P|PEQ81PqPEPEQ4hQ0pP:GUP}PDb8b6b7X32X;JAkR3QS0pQ1:P8Q0BP7CS[^32^;JP3Q91p+08^RZQ0zO3b2b0b1Q5@Q0iG7Q6{Q6=DAQ8TQ4qQ6{3;eQ6Lp+09JS91D<p+09:S98P<Q6[/0GX:=Q5eQ8`Q41Q8HQ6DQ7~Q7}Q7}Q7|Q6MQ5iP3PZQ3jO2S3jb2b0b1Q5@Q0iG7Q4@eQ6LQ91D<GRE:Q5xQ3dQ5OQ6tQ2nP<P<Q8TQ5C/4NS4@Q6|3;X:=PaQ65Q5Cp+05WS5i/03S6[3hX92Q5cP;Q2WQ6hQ2<Q9:Q7wQ8nPXPtPpPvQ4PQ5cQ5cQ6lG6PXPtQ6mQ5[Q5=PaPaPFG6EQQ7~Q7}Q7}Q7|PTPzP{P|PEQ81PqPEPEQ4hPsP:GUP}PDb8b6b7X32X;JQ0pQ1:P8PIP7CS[^32^;JP3Q93PZQ0zO3b2b0b1Q4MQ0gG7Q6{Q6=DAQ02Q51Q6{3;ePPQ3WD<Q98P<Q4@/0GX:=Q5cQ8`Q5HQ5Ap+05MS93Q7~Q7}Q7}Q7|Q6LQ8`Q3jb2b0b1Q4MQ0gG7Q4UePPQ3WD<GRE:Q4fQ84Q3ZQ5]Q2nP<P<Q02Q3h/4NS4fQ6|3;X:=PaQ65Q3hQ50P3CcX92Q5^P;Q7`Q19'CS4UQ5b,CCS6LQ7`Q19PCQ5bPXPtPpPvQ4PQ5^Q5^Q7IG6PXPtPiQ5_Q5>PaPaPFG6EQQ7~Q7}Q7}Q7|PTPzP{P|PEQ81PqPEPEQ4hQ22P:GUP}PDb8b6b7X32X;JQ0pQ1:P8P[P7CS[^32^;JP3Q9:PZQ0zO3b2b0b1Q5?Q0hG7Q6{Q6=DAQ4kQ47Q6{3;eQ6HQ6gD<Q98P<Q4f/0GX:=Q5^Q8`Q8GQ8=Q8@Q7~Q7}Q7}Q7|Q6IQ1]Q3jb2b0b1Q5?Q0hG7Q49eQ6HQ6gD<GRE:Q3EQ2nP<Q3dQ3UQ5\Q2nP<P<Q4kQ4{/4NS2nQ6|3;X:=PaQ65Q4{Q1S3hX92Q5`P;Q8bp+06IS65'CS1SQ4|Q7{'CS49Q8bQ65Q4|Q7{PXPtPpPvQ4PQ5`Q5`Q70G6PXPtQ7JQ6kQ4EPaPaPFG6EQQ7~Q7}Q7}Q7|PTPzP{P|PEQ81PqPEPEQ4hQ0_P:GUP}PDb8b6b7X32X;JQ0pQ1:P8Q0^P7CS[^32^;JP3Q19PZQ0zO3b2b0b1Q4mQ0dG7Q6{Q6=DAQ4jQ8kQ6{3;ePPQ3WD<Q98P<Q2n/0GX:=Q5`Q8`Q8<Q1`Q0IQ7~Q7}Q7}Q7|Q6HQ8VQ3jb2b0b1Q4mQ0dG7Q4;ePPQ3WD<GRL05Q6|P3E>b4PkP3E:b<Q6=NA0>P^p+0>CS6=P3PSQ2pQ6}Q2o#=PSQ2pPSQ6}CHdO4b4Q1}PSQ2oP?Q2o,JSdQ6|DNPGQ2pPOQ2^P3Q3EPZQ1FEGX5GPOQ2\Q2pQ35Q5oD8POQ2\Q6yQ35Q5oD8Q4>Q6TPOP4Q2\Q2pQ35Q5og0KkGPwPmQ2qg0KlQPog0Km[p+0=4R^Q71P^Q6|P^Q71P^Q4MP^PPP^Q7kP^Q7;P^Q7CP^Q8SP^Q7UP^Q8uP^Q0EP^Q8UP^Q4mP^Q7kP^Q4MP^K02D1D1D1D1D1D1p+093S35PwPoEVQ2NeQ2NQ2lP0Q2lQ2b/Dm-073$09W5Q8MQ4_P3E:b<N>1>Q1wP`P3PSQ2tQ6zQ2s#=PSQ2tPSQ6zCHdO4b4PGPSQ2sP?Q2s,JSdQ6yDNQ2lQ2tQ2lPOQ2bP3Q3FQ5rQ2}EGW5POQ2^Q2tQ3EPZD8POP@19MsQ2AQ2^Q2Vn0100000020000Q6yQ3EPZD8Q1FQ6UPOP4Q2^Q2tQ3EPZg0KneR^PYQ78g0Koo%j^g0L19N<0hQ1tp+0>ER^P3PSQ2xQ6zQ2w#=PSQ2xPSQ6zCHdO4b4Q2lPSQ2wP?Q2w,JSdQ6yDNPsQ2xPOQ2XP3p+03[RaQ6FQ5~EGX5sQ1}p+0>FS2wP3PSQ2|Q6zQ2{#=PSQ2|PSQ6zCHdO4b4Q2|Q6y52sQ34Q2|Q34POQ2gPYP3Q2xQ3JQ5uQ1?GaW5POQ2\Q2xPaQ6FD8POP@19Mdp+0<dS2gQ2\Q4_n0100000020000Q6yPaQ6FD8Q5~Q6WPOP4Q2\Q2xPaQ6Fg0L2CPwPYQ2~,?VRaP]P_g0L3MPog0L4WQ8aQ6xQ8aQ74Q8aPnQ8aQ74Q8aQ5IQ8aQ3VQ8aQ7nQ8aQ7>Q8aQ7LQ8aQ7NQ8aQ4VQ8aQ7RQ8aQ8UQ8aQ7eQ8aQ5=Q8aQ7nQ8aQ5IQ8aDeD1D1D1D1D1D1D1p+096S8aPYPoEVQ2NeQ2NPdQ2|Q4LQ2hP31^VaP<Q6]J00X5dQ2lp+0>HRaP3PSQ31Q6yPFQ6xQ6y7fSdO4b4Q31Q6x52dQ7mQ31Q7mQ8JQ3AP3P<Q6^DmW5Q4LQ3EQ6gQ4LQ61Q6gQ4LQ8TQ6gQ4LQ15Q6gQ0WQ8TQ87Q8wQ5`Q31P<P<Q8TQ4M/4NS8wQ6y3;X:=PbQ6=,43S8TQ4MQ54/03S0W3hX92Q5gP;Q4UQ6LQ7`Q19PCQ5bPXP^PpPvQ4PQ5gQ5gQ5ZG6PXP^Q5\Q5[Q5DPbPbPFG6EQQ83Q82Q82Q81PTPzP{P|PEQ85PqPEPEQ4hQ1}P:GUP}PDb8b6b7X32X;JAkR3QS5bQ1:P8Q0BP7CS[^32^;JP3Q9:Q5kQ13O3b2b0b1Q5FQ0iG7Q6xQ6?DAQ02Q4uQ6x3;eQ6PQ62D<Q6fP<Q8w/0dX:=Q5gQ4:Q5<Q4EQ47Q83Q82Q82Q81Q6QQ0:P3Q5kQ5WO2S5Wb2b0b1Q5FQ0iG7Q5zeQ6PQ62D<GRE:Q61PjQ5PQ5^Q31P<P<Q02Q5L/4NS6QQ6y3;X:=PbQ8TQ5LQ4sP3CcX92Q5hP;Q1SQ49Q8bQ65Q4|Q7{PXP^PpPvQ4PQ5hQ5hPWG6PXP^Q6pQ6tQ5GPbPbPFG6EQQ83Q82Q82Q81PTPzP{P|PEQ85PqPEPEQ4hPtP:GUP}PDb8b6b7X32X;JQ5bQ1:P8PIP7CS[^32^;JP3Q19Q5kQ13O3b2b0b1Q5OQ0gG7Q6xQ6?DAQ4kQ4rQ6x3;eQ3fQ3aD<Q6fP<Q6Q/0dX:=Q5hQ4:Q41Q8HQ4wQ83Q82Q82Q81Q6PQ4:Q5Wb2b0b1Q5OQ0gG7Q5yeQ3fQ3aD<GRE:Q3EPrQ3dQ5aQ31P<P<Q4kQ5=/4NS3EQ6y3;X:=PbQ8TQ5=Q4pP3CcX92Q1vP;Q0kp+06GS4k'CQ7Fp+06FS4r'CQ0kQ4kQ7FQ4rPXP^PpPvQ4PQ1vQ1vQ6lG6PXP^Q6nQ6mQ4{PbPbPFG6EQQ83Q82Q82Q81PTPzP{P|PEQ85PqPEPEQ4hQ1iP:GUP}PDb8b6b7X32X;JQ5bQ1:P8P[P7CS[^32^;JP3Q65Q5kQ13O3b2b0b1Q3|Q0hG7Q6xQ6?DAQ4jQ5iQ6x3;eQ6MQ8tD<Q6fP<Q3E/0dX:=Q1vQ4:Q5HQ5AQ6DQ83Q82Q82Q81Q6NQ7qQ5Wb2b0b1Q3|Q0hG7Q4BeQ6MQ8tD<GRE:Q2hQ31P<PjPPQ68Q31P<P<Q4jQ5@/4NS31Q6y3;X:=PbQ8TQ5@Q6[3hX92Q23P;Q7_p+06ES8T'CS6[Q6Zp+06DR;'CS8tQ7_Q8TQ6ZP;PXP^PpPvQ4PQ23Q23PiG6PXP^Q6kQ6oQ3hPbPbPFG6EQQ83Q82Q82Q81PTPzP{P|PEQ85PqPEPEQ4hQ0_P:GUP}PDb8b6b7X32X;JQ5bQ1:P8Q0^P7CS[^32^;JP3Q4kQ5kQ13O3b2b0b1Q5BQ0dG7Q6xQ6?DAQ4gQ51Q6x3;eQ3fQ3aD<Q6fP<Q31/0dX:=Q23Q4:Q8GQ8=Q93Q83Q82Q82Q81Q6MQ4FQ5Wb2b0b1Q5BQ0dG7Q4=eQ3fQ3aD<GRL05Q6yP3E>b4Q2VP3E:b<&0R_NA0>PGp+0>GRFP3PSQ33Q6zQ32#=PSQ33PSQ6zCHdO4b4Q34PSQ32P?Q32,JSdQ6yDNPdQ33POPkP3Q2hQ5kQ1@EGX5dPOQ2XQ33Q3JQ5uD8POQ2XQ6vQ3JQ5uD8Q1?Q6XPOP4Q2XQ33Q3JQ5ug0L5aPwPmQ2qg0L6kPog0L85Q2HQ2DQ7mP_Q7mQ2Y/Dm-073$0JW5Po207_0$0JdQ2RP3E:b<N>1;Q2lPaP3PSQ39Q6wQ38#=PSQ39PSQ6wCHdO4b4PdPSQ38P?Q38,JSdQ6vDNQ7mQ39Q7mPOQ2YP3Q3Ap+08cS3AQ1BEGW5POPkQ39Q2hQ5kD8POP@19Mtp+0<gS1BPkQ2Nn0100000020000P\Q2hQ5kD8Q1@Q6YPOP4PkQ39Q2hQ5kg0L9?PYPwQ3:,?VRbQ88Q16g0L:IPog0L;SQ2IQ2MPtP_p+0<<S2MQ5xP31^VbQ06Q6^J00X5tQ34p+0>JRbP3PSQ3<Q6uPvQ6u9f\SdO4b4Q3<=2t\Q2eQ3<Q2eQ8OQ3PP3Q06Q6_DmW5Q2MQ3FQ6gQ2MQ3UQ6gQ2MQ4jQ6gQ2MQ35Q3<Q063PQ6gQ0XQ4jQ88Q35Q5eQ3<Q06P<Q4jQ5M/4NS35Q6u3;X:=Pc143`S4jQ5MQ57/03S0X3hX92Q5oQ7VQ6[Q8tQ7_Q8TQ6ZP;PXPFQ1;Q8ip+0<NR;Q5oQ5oQ5\G6PXPFQ6sQ5]Q4MPcPcPvG6EQQ85Q84Q84Q83PTPzP{P|PEPLPqPEPEQ8YQ2lP:GUP}PDb8b6b7X32X;JAkR3QRpQ4QP8Q0BP7CS[^32^;JP3Q4kQ5nQ10O3b2b0b1Q5CQ0hG7P\Q6?DAQ4gp+05_S4k;;\ePeQ64D<Q7QP<Q35/0tX:=Q5oQ8_Q5?Q5>Q69Q85Q84Q84Q83Q6RQ2BP3Q5nQ2OO2S35b2b0b1Q5CQ0hG7Q5|ePeQ64D<GRE:Q3UQ3cQ8WQ5cQ3<Q06P<Q4gQ5N/4NS64Q6u3;X:=PcQ4jQ5NQ4u/03S4g3hX92PZQ7VQ25p+06CS0h'CQ7Gp+06BS2l'CQ25Q0hQ7GQ2lPXPFQ1;Q8iP;PZPZQ5ZG6PXPFQ5[Q5aQ5FPcPcPvG6EQQ85Q84Q84Q83PTPzP{P|PEPLPqPEPEQ8YQ6=P:GUP}PDb8b6b7X32X;JQ4QP8PIP7CS\p^32^;JP3Q8TQ5nQ10O3b2b0b1Q6jQ0dG7P\Q6?DAQ4bQ4t;;\ePjQ3VD<Q7QP<Q64/0tX:=PZQ8_Q5:Q8LQ47Q85Q84Q84Q83PeQ8_Q35b2b0b1Q6jQ0dG7Q5{ePjQ3VD<GRE:Q3FP]Q3fQ5^Q3<Q06P<Q4bQ31Q6u3;X:=PcQ4jQ5@Q2k3hX92Q5hQ7VQ8dp+06AS2k'CQ4vp+06@S3F'CS5{Q8dQ2kQ4vQ3FPXPFQ1;Q8iP;Q5hQ5hQ6nG6PXPFPWQ6oQ5=PcPcPvG6EQQ85Q84Q84Q83PTPzP{P|PEPLPqPEPEQ8YQ3mP:GUP}PDb8b6b7X32X;JQ4QP8P[P7CS\p^32^;JP3Q0hQ5nQ10O3b2b0b1Q5BQ0eG7P\Q6?DAQ4]Q4q;;\eQ6OQ62D<Q7QP<Q31/0tX:=Q5hQ8_Q8DQ8?Q4wQ85Q84Q84Q83Q6PQ0:Q35b2b0b1Q5BQ0eG7Q5zeQ6OQ62D<GRE:Q5xQ3<Q06Q3cQ3dQ5`Q3<Q06P<Q4]Q7WQ6u3;X:=PcQ4jQ5GQ4qP3CcX92Q5gQ7VQ4Cp+06?S4j'CS06Q8Np+06>S3<'CS62Q4CQ4jQ8NQ3<PXPFQ1;Q8iP;Q5gQ5gQ6lG6PXPFQ6mQ6pQ4{PcPcPvG6EQQ85Q84Q84Q83PTPzP{P|PEPLPqPEPEQ8YQ0_P:GUP}PDb8b6b7X32X;JQ4QP8Q0^P7CS\p^32^;JP3Q2kQ5nQ10O3b2b0b1Q5EPUG7P\Q6?DAQ4`Q4p;;\ePjQ3VD<Q7QP<Q7W/0tX:=Q5gQ8_Q1UQ8AQ6DQ85Q84Q84Q83Q6OQ4:Q35b2b0b1Q5EPUG7Q5yePjQ3VD<GRL05Q6uP3E>b4Q4lP3E:b<Q16Q0OQ99,X3X92Q08011I%\IQ8y,X9[\aQ1AQ08@10I8UX@aQ1AQ8h#\[^@aQ85Q84Q84Q83PTPzPHP|Q1;Q0@Q09$0G60{25sEP}PDb8b6b7Q0OQ8i'XP3b2b0b1bXbYQ16,ZSQ0OQ83Q82Q82Q81PTPzPHP|Q8h9WEyP}PDb8b6b7Q0O#\P3b2b0b1Q83Q82Q82Q81PTPzPHP|Q8hQ1}5sEP}PDb8b6b7Q0OQ7m'XP3b2b0b13@DA+1mNA1lPsp+0>IRsP3PSQ3>Q6uQ3=#=PSQ3>PSQ6uCHdO4b4Q7mPSQ3=P?Q3=,JSdP\DNPtQ3>POQ4lP3Q5xQ5nQ1PEGX5tQ34PbP3PSQ3BQ6wQ0N#=PSQ3BPSQ6wCHdO4b4Q3BQ6v52tQ2eQ3BQ2ePOQ2^PYP3Q3>Q3PQ5wp+02MRyGaW5POQ2XQ3>Q5xQ5nD8POQ2XQ8^Q5xQ5nD8Q1PQ6\POP4Q2XQ3>Q5xQ5ng0L<]PYPmQ3?g0L=gPog0L?1P6PBP6Q6xP6Q6|P6Q79P6Q74P6Q79P6Q5NP6Q3`P6Q7tP6Q7BP6Q1qP6Q6bP6Q7TP6Q8QP6Q7fP6Q7hP6Q5GP6Q7tP6Q5NP6DeD1D1D1D1D1D1D1D1Q98PYPoEVQ2JeQ2JQ6=Q3BQ6=Q2Y/Dm-1:3$09W5Q1IQ3B01:0$09dQ2RP3E:b<N>1kPdp+0>KR6P3PSQ3DP\Q3C#=PSQ3DPSP\CHdO4b4Q2ePSQ3CP?Q3C,JSdQ8^DNQ6=Q3DQ6=POQ2YP3Q3QQ5qQ1TEGW5POPkQ3DQ3PQ5wD8POP@19M`p+0<jS2YPkQ1~n0100000020000PBQ3PQ5wD8PyQ6]POP4PkQ3DQ3PQ5wg0L@;PYPw1?V[RyQ2>Q5fg0LAEPog0LBOp+0=<R9Q8^P9Q6yP9Q6}P9Q7:P9Q75P9Q7:P9Q5PP9Q3cP9Q7uP9Q7CP9Q7OP9Q0EP9Q6bP9Q7TP9Q7YP9Q7iP9Q5DP9Q7uP9Q5PP9DeD1D1D1D1D1D1D1D1p+09;PwPoEVQ2JeQ2JP`P_Q8:Q61P31^VyP<Q2>J00X5`Ptp+0>MRyP3PSQ3GQ8^Q8hQ8^9fBSdO4b4Q3G=2`BP^Q3GQ8;Q3UP3P<Q5fDmX5^Q8:Q3JQ2:Q8:Q3ZQ2:Q8:Q4bQ2:Q8:Q8aQ3G;P<Q2:Q0TQ4bQ4LQ8aQ1vQ3GP<P<Q4bQ6QQ8^3;X:=Pf143aR9Q5LQ4x/03S4b3hX92Q6FP;Q5{Q06Q4vQ3FQ4CQ4jPXPbQ8yQ99Q8RQ6FQ6FQ6tG6PXPbQ5aQ68Q5IPfPfQ8hG6EQPrPLPLQ86PTPzP{P|PEP]PqPEPEQ8sPdP:GUP}PDb8b6b7X32X;JAkR3QRdPvP8Q0BP7CS[^32^;JP3Q2lQ2LQ3yO3b2b0b1Q5OQ0dG7PBQ6@DAQ4]Q58;;BeQ6TQ0\D<p+09@RpP<Q6Q/0`X:=Q6FQ2gQ4{Q4mQ4pPrPLPLQ86Q6Up+0<eRcP3Q2LQ11O2S11b2b0b1Q5OQ0dG7Q4IeQ6TQ0\D<GRE:Q3ZQ6:Q5SQ5gQ3GP<P<Q4]Q8W/4NS0dQ8^3;X:=PfQ8WQ0X5h9X92Q5uP;Q62Q8cQ7X'CQ8NQ3<Q8cQ7XPXPbQ8yQ99Q8RQ5uQ5uQ5]G6PXPbQ6sQ5eQ5MPfPfQ8hG6EQPrPLPLQ86PTPzP{P|PEP]PqPEPEQ8sQ2wP:GUP}PDb8b6b7X32X;JPvP8PIP7CS\d^32^;JP3Q3FQ2LQ3yO3b2b0b1Q5QQ0eG7PBQ6@DAQ4`Q4k;;BeQ3ePjD<PpP<Q0d/0`X:=Q5uQ2gQ5>Q5<Q51PrPLPLQ86Q6TQ2gQ11b2b0b1Q5QQ0eG7Q60eQ3ePjD<GRE:Q3JQ8CQ3`Q23Q3GP<P<Q4`Q5D/4NS51Q8^3;X:=PfQ5DQ4g5h9X92Q5rP;Q8Ip+06<S4`'CQ7Ep+06;S0d'CQ8IQ4`Q7EQ0dPXPbQ8yQ99Q8RQ5rQ5rQ6pG6PXPbQ5[Q5ZQ5EPfPfQ8hG6EQPrPLPLQ86PTPzP{P|PEP]PqPEPEQ8sQ1wP:GUP}PDb8b6b7X32X;JPvP8P[P7CS\d^32^;JP3Q3<Q2LQ3yO3b2b0b1Q5GPUG7PBQ6@DAQ4[Q4t;;BePep+09QS3<D<PpP<Q51/0`X:=Q5rQ2gQ8LQ41Q50PrPLPLQ86Q6RQ2AQ11b2b0b1Q5GPUG7Q5}ePeQ3<D<GRE:Q61Q3GP<Q6:Q3gQ5cQ3GP<P<Q4[Q8wQ8^3;X:=PfP9Q4MQ4tP3CcX92PZP;Q8Bp+06:R;'CQ7^Q5d'CR9Q8BP;Q7^Q5dPXPbQ8yQ99Q8RPZPZQ6oG6PXPbPWQ5\Q5BPfPfQ8hG6EQPrPLPLQ86PTPzP{P|PEP]PqPEPEQ8sQ0_P:GUP}PDb8b6b7X32X;JPvP8Q0^P7CS\d^32^;JP3Q4`Q2LQ3yO3b2b0b1Q5FQ0rG7PBQ6@DAQ4XQ4s;;BeQ3ePjD<PpP<Q8w/0`X:=PZQ2gQ8?Q5HQ8kPrPLPLQ86PeQ2BQ11b2b0b1Q5FQ0rG7Q5|eQ3ePjD<GRL05Q8^P3E>b4Q2RP3E:b<Q5f$0RNA0>Q7mp+0>LReP3PSQ3IQ8^Q3H#=PSQ3IPSQ8^CHdO4b4Q6=PSQ3HP?Q3H,JSdPBDNP`Q3IPOQ1rP3Q61Q2LQ1VEGX5`POQ21Q3IQ3QQ5qD8POP@19M^Q2QQ21Q1~n0100000020000Q0LQ3QQ5qD8Q1TQ6^POP4Q21Q3IQ3QQ5qg0LCYPxPwQ0M,?VRdQ3iQ2Hg0LDcPog0LEmp+0==RvQ2>PvP\PvQ6zPvQ6~PvQ7;PvQ76PvQ7;PvQ5QPvQ3ePvQ6cPvQ8FPvQ8uPvQ4KPvQ0EPvQ6bPvQ7gPvQ7jPvQ5FPvQ6cPvQ5QPvK02D1D1D1D1D1D1D1D1Q7PPwPoEVQ1xeQ1xP^P_Q8;Q3UP31^VdP<Q3iJ00X5^Q2ep+0>NS7PP3PSQ3KQ0M,E_RdP>Q55?fSddO4b4Q3K=2^dQ2wQ3KQ2wp+0<AQ3WP3P<Q2HDmW5Q8;Q3JQ2EQ8;Q3ZQ2EQ8;Q4XQ2EQ8;Q1NQ3K;P<Q2EQ44Q4XQ8JQ1NQ5gQ3KP<P<Q4XQ6j/4NRv;;BX:=Pg143sRfQ6jQ5;P3CcX92Q5uQ4<P9Q0Pp+068R9'CQ7^Q5dQ0PP9PXP6Q8xQ1DQ0{Q5uQ5uQ68G6PXP6Q5`Q5aQ5OPgPgP>G6EQQ87PrPrPLPTPzP{P|PEQ88PqPEPEQ7VQ7mP:GUP}PDb8b6b7X32X;JAkR3QR9Q8hP8Q0BP7CS[^32^;JP3Q0dQ5tQ3xO3b2b0b1Q5LQ0rG7Q55Q6?DAQ4WQ4xQ553;eQ6UQ3uD<PpP<10v^X:=Q5uPcQ3|Q4{Q4qQ87PrPrPLQ6VQ2uP3Q5tQ3yO2Rvb2b0b1Q5LQ0rG7p+04bS3yeQ6UQ3uD<GRE:Q3ZQ8~Q8\Q5hQ3KP<P<Q4WQ8Z/4NR;;;BX:=PgPfQ8Zp+05aP3CcX92Q5kQ4<Q7Dp+067S4W'CQ5vp+066S8\'CQ7DQ4WQ5vQ8\PXP6Q8xQ1DQ0{Q5kQ5kQ6sG6PXP6Q6tQ5cQ5IPgPgP>G6EQQ87PrPrPLPTPzP{P|PEQ88PqPEPEQ7VPFP:GUP}PDb8b6b7X32X;JQ8hP8PIP7CS\9^32^;JP3Q5dQ5tQ3xO3b2b0b1Q8WQ0fG7Q55Q6?DAQ4TQ57Q553;eQ3kQ3`D<PpP<10;^X:=Q5kPcQ5?Q5>Q5iQ87PrPrPLQ6UPcPvb2b0b1Q8WQ0fG7Q4IeQ3kQ3`D<GRE:Q3JQ4LQ3cQ1vQ3KP<P<Q4TQ5F/4NS4L;;BX:=PgQ5FQ0W5hfX92Q6FQ4<Q7]p+065R;'CQ5sQ0V'CQ7]P;Q5sQ0VPXP6Q8xQ1DQ0{Q6FQ6FQ5ZG6PXP6Q5\Q5[Q5GPgPgP>G6EQQ87PrPrPLPTPzP{P|PEQ88PqPEPEQ7VQ1tP:GUP}PDb8b6b7X32X;JQ8hP8P[P7CS\9^32^;JP3Q4WQ5tQ3xO3b2b0b1Q5DQ5KG7Q55Q6?DAQ4aQ4uQ553;eQ6RQ0UD<PpP<Q4L/0^X:=Q6FPcQ5:Q8LQ69Q87PrPrPLQ6SQ2gPvb2b0b1Q5DQ5KG7Q60eQ6RQ0UD<GRE:Q3UQ3KP<Q8~PjQ23Q3KP<P<Q4aQ4@;;BX:=PgQ5CQ4g5hfX92Q5rQ4<Q5Vp+063Rf'CRBQ5pQ0Z'CRjQ5VPfQ5pQ0ZPXP6Q8xQ1DQ0{Q5rQ5rPWG6PXP6Q6pQ5]Q5@PgPgP>G6EQQ87PrPrPLPTPzP{P|PEQ88PqPEPEQ7VQ0_P:GUP}PDb8b6b7X32X;JQ8hP8Q0^P7CS\9^32^;JP3P;Q5tQ3xO3b2b0b1Q4MQ5JG7Q55Q6?DAQ4\Q4tQ553;eQ3kQ3`D<PpP<Q4@/0^X:=Q5rPcQ8DQ8?Q47Q87PrPrPLQ6RQ2APvb2b0b1Q4MQ5JG7Q5}eQ3kQ3`D<GRL05PdP3E>b4Q1~P3E:b<Q2H$0RNA0>PtPyP3PSQ3MQ55Q3L#=PSQ3MPSQ55CHdO4b4P`PSQ3LP?Q3L,JSdQ0LDNP^Q3MPOQ1rP3Q3UQ5tp+02PRtEGX5^POQ21Q3MQ61Q2LD8POQ21Q4DQ61Q2LD8Q1VQ6_POP4Q21Q3MQ61Q2Lg0LG7PYPxQ0RQ0B'?g0LHAPog0LIKQ8eQ3iQ8eQ5fQ8eQ6uQ8eQ6{Q8ePnQ8eQ7<Q8eQ77Q8eQ7<Q8eQ8WQ8eQ3kQ8eQ7vQ8eQ7KQ8eQ7UQ8eQ7ZQ8eQ4KQ8eQ0EQ8eQ7hQ8eQ7kQ8eQ4MQ8eQ7vQ8eQ8WQ8eDeD1D1D1D1D1D1D1D1D1Q6fPYPoEVQ1keQ1kQ2wQ29Q2wQ1z-073$0JW5PAQ2HPAQ5lPAQ6vPAQ6|PAQ71PAQ7=PAQ79PAQ7=PAQ8ZPAQ6:PAQ7xPAQ7LPAQ8SPAQ8UPAQ7ZPAQ4KPAQ7iPAQ7lPAQ5CPAQ7xPAQ8ZPAK02D1D1D1D1D1D1D1D1D1RAQ7QPxPoCuQ1keQ1kPFQ2DQ2c0073$0JX5FP@Q2CQ2N+0u&0J3X5@20u83$0JPJQ001y17R1\31y78P8[P7\121i78P3n2001000000120000000aXA2X?21B83R1$1820u78$0J[^A2^?2P3Q2EQ2RQ88P]P]Q87Q1HQ05-142&13K-1d2Q04-14261c261b2g07V<+1a;~TPzP220s27P8PHH1`P|PEQ07-192RHQ0;5{E-15EPqQ0;={EH-15EH0zP}PDb8b6b7X32XB2g01YIRH\11B87PH[[^32^B2P3Q4_Q2HQ46O3b2b0b1O3b4Q2;Q2D+07Q2CQ2NP]Q87Q87PrQ6BQ0DP3Q3iQ46O2b2b0b1P]Q87Q87PrQ6BQ0DP3Q2VQ0SO2b2b0b1H1^E:Q1zP3E:b<Q1zP3E:b<N>1;Q2eQ7PP3PSQ3OQ0LQ3N#=PSQ3OPSQ0LCHdO4b4P^PSQ3NP?Q3N,JSdQ4DDNQ2wQ3OQ2wPOQ24P3Q3WQ92Q1YEGW5POQ1rQ3OQ3UQ5tD8POP@19MFQ2YQ1rQ1~n0100000020000P5Q3UQ5tD8PtQ6`POP4Q1rQ3OQ3UQ5tg0M[9Q0cPwQ0?,?VRtQ2MQ18g0M\CPog0M]MPAQ7QPwPoCuQ1jeQ1jPFP_p+0<BRAQ3ZP31^VtP<Q6eJ00X5FP`p+0>PRtP3PSQ3RQ4DQ1DQ4D9f5SdO4b4Q3R=2F5PaQ3RQ4yQ3]P3P<Q4}DmX5aPAQ2hQ91PAQ3]Q91PAQ4aQ91PAp+099RAQ3R;P<Q91Q46Q4aQ8OPAQ5oQ3RP<P<Q4aQ5P/4NRAQ4D3;X:=Ph1436RVQ5PQ4zP3CcX92Q3AQ4NPBPjQ5VPfQ5pQ0ZPXPyP~Q8pQ6rQ3AQ3AQ5`G6PXPyQ5eQ5^Q6jPhPhQ1DG6EQQ88P]P]Q87PTPzP{P|PEQ8CPqPEPEQ4<Q2eP:GUP}PDb8b6b7X32X;JAkR3QRRQ99P8Q0BP7CS[^32^;JP3P;Q96Q3}O3b2b0b1Q5NQ5KG7P5Q6>DAQ4\p+05e;;5eQ6WQ56D<Q7pP<10AFX:=Q3AQ1BQ5BQ5=Q4sQ88P]P]Q87Q6XQ1GP3Q96Q3wO2RAb2b0b1Q5NQ5KG7Q4JeQ6WQ56D<GRE:Q3]Q6AQ5TPZQ3RP<P<Q4\Q5S/4NRZQ4D3;X:=PhQ5SQ4b5hVX92Q5nQ4Np+07RR;p+061RQ'CQ5mQ0Y'CP;PQQ5mQ0YPXPyP~Q8pQ6rQ5nQ5nQ68G6PXPyQ5aQ1vQ5LPhPhQ1DG6EQQ88P]P]Q87PTPzP{P|PEQ8CPqPEPEQ4<PsP:GUP}PDb8b6b7X32X;JQ99P8PIP7CS\R^32^;JP3PfQ96Q3}O3b2b0b1Q5RQ5JG7P5Q6>DAQ4^Q58;;5eQ8~Q3eD<Q7pP<10ZFX:=Q5nQ1BQ4mQ3hQ4qQ88P]P]Q87Q6WQ1BPAb2b0b1Q5RQ5JG7p+04ceQ8~Q3eD<GRE:Q2hQ2MQ3kQ5hQ3RP<P<Q4^Q4@Q4D3;X:=PhQ5CQ0X5hVX92Q5kQ4NQ6dp+05oRZ'CQ6JQ0`'CQ6dPZQ6JQ0`PXPyP~Q8pQ6rQ5kQ5kQ5\G6PXPyQ6sQ5]Q5FPhPhQ1DG6EQQ88P]P]Q87PTPzP{P|PEQ8CPqPEPEQ4<PGP:GUP}PDb8b6b7X32X;JQ99P8P[P7CS\R^32^;JP3PQQ96Q3}O3b2b0b1Q4MQ0oG7P5Q6>DAQ4ZQ4k;;5eQ6TQ3uD<Q7pP<Q4@/0FX:=Q5kQ1BQ5<Q4EQ5iQ88P]P]Q87Q6UQ2uPAb2b0b1Q4MQ0oG7Q3yeQ6TQ3uD<GRE:Q3ZQ3RP<Q6AQ3cQ5gQ3RP<P<Q4ZQ5I/4NRNQ4D3;X:=PhPVQ5IQ4kP3CcX92Q5uQ4NQ0[p+05mRV'CQ5UQ4~'CQ0[PVQ5UQ4~PXPyP~Q8pQ6rQ5uQ5uQ5ZG6PXPyQ5[Q6tQ5GPhPhQ1DG6EQQ88P]P]Q87PTPzP{P|PEQ8CPqPEPEQ4<Q0_P:GUP}PDb8b6b7X32X;JQ99P8Q0^P7CS\R^32^;JP3PZQ96Q3}O3b2b0b1Q5MQ3~G7P5Q6>DAQ4OQ54;;5eQ8~Q3eD<Q7pP<10NFX:=Q5uQ1BQ41Q8HQ69Q88P]P]Q87Q6TPcPAb2b0b1Q5MQ3~G7Q4IeQ8~Q3eD<GRL05Q4DP3E>b4Q1xP3E:b<Q18$0RNA0>Q6=p+0>OP3PSQ3TQ4DQ3S#=PSQ3TPSQ4DCHdO4b4Q2wPSQ3SP?Q3S,JSdP5DNPFQ3TPOQ1rP3Q3ZQ96Q1[EGX5FPOQ21Q3TQ3WQ92D8POP@19Map+0<nRAQ21Q1fn0100000020000Q8XQ3WQ92D8Q1YQ6aPOP4Q21Q3TQ3WQ92g0M^WRcPYPwQ1Qg0M_a%jcg0M`kN=08P`PtP3PSQ3YQ0KQ3X#=PSQ3YPSQ0KCHdO4b4PFPSQ3XP?Q3X,JSdQ8XDNPaQ3YPOQ1jP3Q3]p+08kRtQ1^EGX5ap+0=AR`Q8XP`Q2JP`Q29P`Q6xP`Q6~P`Q73P`Q7?P`Q7;P`Q7?P`Q5SP`Q1EP`Q2iP`Q8PP`Q4VP`Q7dP`Q7SP`Q8UP`Q7kP`Q7nP`Q5IP`Q2iP`Q5SP`K02D1D1D1D1D1D1D1D1D1PpPwPoEVQ1feQ1fPsP_POQ26PYP3Q81CgQ3YPPQ7cQ5XEGX5sPsP_POQ26PYP3Q3YPPQ7cQ5XGaX5sPOQ1zQ3YQ3]PtD8POP@19MbPAQ1zQ1fn0100000020000Q8XQ3]PtD8Q1^Q6ePOP4Q1zQ3YQ3]Ptg0Mb5RtPxPmQ1Qg0Mc?%jtg0MdIN=08Q2wp+0>RP3PSQ3\Q0KQ3[#=PSQ3\PSQ0KCHdO4b4PsPSQ3[P?Q3[,JSdQ8XDNPbQ3\POQ1jP3Q3aQ15p+02URtEGX5bPbP0POQ1~PxP3Q3\Q3aQ15PtGaX5bPOQ1nQ3\PPQ7cD8POP@19M6Q3b>0NMmQ1nQ1Zn0100000020000Q8XPPQ7cD8Q5XQ4}POP4Q1nQ3\PPQ7cg0MeSRPQ3bPmQ1Qg0Mf]%jPg0MggN=08PFp+0>SP3PSQ3_Q0KQ3^#=PSQ3_PSQ0KCHdO4b4PbPSQ3^P?Q3^,JSdQ8XDNP6Q3_POQ5YP3Q3dQ01Q1aEGX56P6P0POQ1sQ3bP3Q3_Q3dQ01Q1aGaX56POQ5YQ3_Q3aQ15D8POp+02WRbQ6@Q3aQ15D8PtQ3sPOP4Q5YQ3_Q3aQ15g0Mi1PuQ0cQ1QQ18g0Mj;Pog0MkEPop+0=DRtQ6qPtQ4HPtQ0JPtQ4DPtQ2NPtQ2CPtQ6{PtQ72PtQ76PtQ7BPtQ7>PtQ7BPtQ5TPtp+047PtQ7|PtQ7OPtQ8QPtQ7YPtQ7fPtQ7ePtQ7nPtQ7rPtQ6jPtQ7|PtQ5TPtDeD1D1D1D1D1D1D1D1D1D1D1Q7sQ0cPoEVQ1PeQ1PPeQ18Q1892y3X5eQ18,iePbP3E:b<N@1_Pap+0>TP3PSQ7zQ6BQ17#=PSQ7zPSQ6BCHdO4b4P6PSQ17P?Q17,JSdQ6@DNPeQ7zPOQ1fP3Q3VQ1OPbEGX5ePsp+0>UP3PSQ7\P5Q7[#=PSQ7\PSP5CHdO4b4Q7\Q0K52ePyQ7\POQ1nPuP3Q7zQ3fQ0=Q1ZGaX5y21\4bP5P3E>b4Q6BP3E>b4EKQ4eQ6?E:Q0KP3E>b4EKQ53Q6>E:Q0KP3E>b4EK&0S_&0o_E:Q1nP3E:b<Q0KP3E>b4EKQ4DP3E>b4EKQ0LP3E>b4EKQ55P3E>b4EKQ8^P3E>b4EKP\P3E>b4EKQ6wP3E>b4Q6uP3E>b4EKQ6wP3E>b4EKQ6zP3E>b4EKQ6zP3E>b4Q6zP3E>b4EKQ6zP3E>b4EKQ6}P3E>b4EKQ6}P3E>b4Q6}P3E>b4EKQ6~P3E>b4EKPnP3E>b4EKb4Q6;P3E>b4EKQ9;P3E>b4Q2dP3E:b<Q6}P3E>b4EKQ6~P3E>b4EKPnP3E>b4EKQ71P3E>b4Q3]P3E:b<PnP3E>b4EKb4Q66P3E>b4EKQ72P3E>b4EKQ7>P3E>b4Q7<P3E>b4EKQ7=P3E>b4Q7=P3E>b4EKQ7?P3E>b4Q7=P3E>b4EKQ1u$0SQ1u$0oE:Q3dP3E:b<Q7>P3E>b4EKQ7>P3E>b4Q3fP3E:b<Q7>P3E>b4EKQ7?P3E>b4Q7?P3E>b4EKQ7@P3E>b4EKQ7BP3E>b4EKQ90P3E>b4p+046P3E:b<Q7AP3E>b4EKQ7CP3E>b4Q7AP3E>b4EKQ7CP3E>b4EKQ8PP3E>b4EKQ5jP3E>b4Q6nQ1LE:Q8SP3E>b4EKQ0eQ1LQ2OQ6nPYPoCuQ0eeQ0eP~P_Q56Q66Q0|P3E:b<PUQ0aQ2OQ6nPxPoCuPUePUP~P0Q3uQ0\Q0jP3E:b<Q0rQ3qQ2OQ6nQ3bPoCuQ0reQ0rP~P0Q3uQ0\Q4YP3E:b<Q0fQ0bQ2OQ6nPuPoCuQ0feQ0fP~Q7\Q1DQ7\723X5~Q7\,i~Q0lP3E:b<Q5KQ3pQ2OQ6nPlPoCuQ5KeQ5KP~Q0kQ1DQ4|723X5~Q0k,i~Q0yP3E:b<Q5JQ4dQ2OQ6nPwPoCuQ5JeQ5JP~P_Q56Q66Q0sP3E:b<Q0oQ3~Q2OQ6nQ0APoCuQ0oeQ0oP~Q6kQ1DQ6l723X5~Q6k,i~Q0iP3E:b<Q2OQ6nQ4iPoCuQ3~eQ3~P~PiQ1DQ6k723X5~1i~iQ0gP3E:b<H0BH0BH0BH0BH0BH0BH0BH0BH1[Q8qQ8qQ52POP3Q7zQ7IQ8>PkQ8fK0<Q8r40;W>+0CeWRWWWVWIWGP8P3O2n2001000010121000000W4WHP8P3O2n2001000010121000000W4XFCP8P3O2n2001000010121000000W4WJWNP8P3O2n2001000010121000000W4WKP8P3O2n2001000010121000000W4WMP8P3O2n2001000010121000000W4WLP8P3O2n2001000010121000000W4WSaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaWTWUWOWPWQaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaX`2aaaaaaaaX_2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaWZaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaW^aW]aaaaaaaaaaaaaaW[aaaaaaW\aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaao"). Qed.

(* [comment removed for export] *)
Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0xc6cc0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xa933c)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0xc6cc0 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0xc6cb8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xc6bd0)) ->
  file_clean mem 0xc6bd0 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0xaea24 : word) mem rom)
                 (mkst regs' (0xa8fe0 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Exit_run3 ()) ["FPX_1"] "h01Hh11bh22gHh37__arithh44__x1h54__ffh68__varmaph75__with85regs'h92Hah:7__sat33h;7__sat34h<1zh=2b1h>2b2h?1nh@4F1rehA4F1rphB3F2lhC4F2rehD4F2rphE4F2wbhF4F2wphG4GerrhH3Hs0hI3HsphJ3M24hK3M32hL4SPhihM4SPlohN4codehO3memhP4regshQ3romhR3rp1hS3rp2hT2sphU3wp2p%0p&0p;1p;2p;4p;5p;3p;6p;Ap;>p;<p;8p;=p;7p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9g002PR0p4p7210g003<R1p4p710R2p8p1003Zp4p710P2p8p10045p4p710g004TR2p4p710p8g0050j11Tg005Uj12Tg006:j1gTg006Xj1lTP0k20~Tg007;k10CTg007]j1PTg008;j2Ak10|Tg008ak200Tg009=j2NTg009gk10UTg00:Gj1hTg00:fj2XTg00;nj2tTg00<Pk40gTg00=Sj53Tg00>Ej2CTg00?7j35Tg00?Qk209Tg00?kj34Tg00@_R0j2yTg00A:j3xTg00A]j3wTg00BJj26Tg00C>k10VTg00C`j2aTg00D:k30mTP2j68Tg00D^j1`Tg00EblA_Tg00FWj2GTg00G:k20lTg00GZj4?Tg00H:k10STg00HZj2TTP1j6JTg00IBj2}Tg00J4j2eTg00Jfk10ATg00Kgm>0@Tg00L`k20RTg00M@k20QTg00N5j1vTg00O5m<0kTg00Omm>0jTg00Pfk10iTg00QXk20MTg00R5j2rTg00RQk20LTg00S9k30KTg00S]k10hTg00T;k10fTg00TYk10eTg00UDk30JTg00Ugk20dTg00VIk20cTg00W5k30bTg00WTk40aTg00XFk20ITg00Xik30<Tg00Ydk20`Tg00ZkmA0_Tg00[`k20HTg00\Sm>0^Tg00]Lj3UTg00]lj4jTg00^nj2STg00_Kj2|Tg00_hk20{Tg00`Fk20zTg00`ik30:Tg00aLk30\Tg00aok407Tg00bZk80ZTg00c7k10FTg00cmm=06Tg00ddk20ETg00e_m>0tTg00f`m<0sTg00gbk20rTg00h^k40DTg00i9k40qTg00iSk40GTg00jDk30?Tg00k@k70wTg00kdk80xTg00lHk70oTf1R1f0R2g00mDR33xp=:f3R4f2R5/N1/S2'Ap=O1C51=542p=B%22#1#1#1#2#2#1#2p=d%22#1#1#2p=i%22#1#1#1p=c%12#1#1#Pp=D%12#1#1#1p=Y%22#1p={1N51/S2p>0W%12#Pp>0T%12#2#1#2p=Z%12#1#2#1p=p%12#2#2#1p=f%12#2#2#2p=o%22#1#1#Pp=Qf4R6g00m`R7P4P5P1H0G;52p=71X12,t5p=H1|12,A5p=b%22#1#2#1p=z%22#2#2#2#2#2#2#2p=n%22#2#2#2p>0=f5R8P7P6P4P5H0G;51/y2p=V%22#2#2#1p>02%12#2#1#1p>0B%P2=x13p=m%12#1#1#2p>04%22#2#1#1p>0;P8P6P4P5P1D3>0?72p=EA5512,y4p=~1y12,y5p>01%22#2#1#2#1#2#1#1p>0pf6R9?486?445?412p=@A4645?412p=0B0?712p>0ng00oIR:1N451N1235p=91a:2p=<P9P8P6P41C51P2EJp=K%12#2#1#2#2#2#1#2#1#2#1#1p=[Ax451=562p=IP9A4864P5P1P2D3p=>AU864P5P1P2Cjp=Lf7R;1N64/S5,A8749?412p=MP6P4P5P1C?=U82p==g00ogR<g010GS00752p=^1a<2p=uP;A4986P4P5P1D3>0?72p=R%12#1p>0PP6P4P5P1C?=U829U;9p=W%12#1#2#2p>0O%22#2p>08g010gR=0002p=q20I:2p=\P:P1g011EP2H07p>0>P1g011lR>g012KS01Q01g012kS02P2g013KK0wp=]P:P1g013kP2H07p>05AU5129U64p=;%22#2#1#2p>0}%12#2#1#2#2#2#1#2p=s1S45,A69498?412p>0]1S12,A5p>03A5:12p>0[P4P>Q01Q01Q02P5P1P2L0xp>0NP7P5P1P2H0Gp>0y16129445p=k1A129445p>0v1N51=5:2p>0u1N1295:5p>0Y%12#2p>0XP7P8P6P4P5P1P2K0op=Fg014RR8#1R>#2R?#gR@%1>RA#1RB#1RC#1RD#1RE#gRF#lRG+0~RH%gB#lRI$0C\GS03Q03PGP;%P>R>,:@RJPFPFP6%PDRKCOCBPGf8RL%PBRM,:@RN%d8#i#c#DRO,AFRPCB%1ES04#1#Y#Y#Y#Y#Y#YRQ#PS05%{A#DS06:0WF9+001NF;%YQ#Y#Y#DS07+00&0UIRI$0CRQf:R;PFPFPL%28R9#1RR#1RS$0TRTCOg0157#h#h#h#hRU#h#h#h#hRV%Z8#p#f#o#QRW,AFRX,XVS08,tIS09D7PQf;RYPFPFf9RZPKCOPVAHIVLRLD7PQf<AbFOMPVPLD7PQf=RL%PCRC9bFOPVAHIVZD7PQf>RO%d8#i#o#DS0:,AFR[PV%d8#o#z#DR\,AFR],XVS0;,tIS0<D7f?R^P\P;PZH0gP0PQf@RZ%2BRB#QR_9bF\R`PU%29R9#nS0=#2$0=#n#nRa#PRb,AFRc,XUS0>,tIRdD7PQPZ%1?S0?#1S0@$0TS0A9bF\RePVAHIVYRYPQPZ%D9S0B9bF\R9PVPYPQPZAbF\MRYPVAHIV;R;PQPZAbF\CR\PVP;D7EVEVEVp,2fxR;fCRf%18#{$02#z#p$0B,mFRgfBS0CfARhP;P2%Z8$04$0=$0;#DS0D,:FRiQ0CPhD3EEQ0?,m@Rj,C2Rk=5G^PGP21m@BRB%2?R?#2#{S0E#PRl,AFRmCBRnPG1C2JRoPFPFPZPCCOC~401X8H-09HP2PQQ0CP`PUPdD7PQPfPePVAHIVOROPQPfP9PVPOPQPfPYPVAHIVLRLPQPfP\PVPLD7EVEVEVP0PQfDRLPePVAHIV^R^D7PQPLP9PVP^PQPLPYPVPOPQPLP\PVPOD7EVEVP;fGROPgfFR^fER`P;P2PiP^P`D3EEA5GkfPnPGPoPFPFPLPCCOC~401X8H-09HP2PQP^PePVAHIVhRhD7PQPOP9PVQ0C9HIVRePQPOPYPVPhPQPOP\PVPhD7EVEVP0PQfHRhP9PVAHIVfD7PQPhPYPVPePQPhP\PVPeD7EVP;fKRePgfJRffIRpP;P2PiPfPpD3EEA5GkOPnPGPoPFPFPhPCCOC~401X8H-09HP2PQPfP9PVAHIV`R9D7PQPePYPVP9PQPeP\PVP9D7EVP0PQfLR9PYPVAHIV^ROD7PQP9P\PVPOD7P;fOROPgfNRqfMRrP;P2PiPqPrD3EEA5GkePnPGPoPFPFP9PCCOC~401X8H-09HP2PQPqPYPVAHIVhD7PQPOP\PVAHIVpD7PHP;fRRpPgfQR\fPRYP;P2PiP\PYD3EEA5GkqPnPGPoPFPFPOPCCOS0FC~401X8HA4\j9Ro1m@?R?P9Pj%c8$0p#c#QRn,AFRkPNP]F@Pj%na#n#n#n#PS0G,AFRaPjPeD0P?PePjPfD0P?Pf1m@8RsPXD0PNPrPJPFPFPqPCCOS0HD0PjPrPs%Z8#p#f#c#QS0I,AFRtD0P?PrPBPmD0RuP;P\PgPYPOD3RvP;PuPiPYPOD3Rw+0nPGPuPjPrCBS0JPGPuPBPmCBS0KPGPuPJQ0HCBS0L'yS0M'yPvP;P<PHAx@=3Rv9w@jS0NP\Pon0100000020000%PARA,6gS0OPYPOD3Pw&0CG&0VG'aRwP;P7P\PgPYPOg015VPjPN%gSRg/:MS0P1XV9P9g016`g017jRo,a<Rug018JPGPPPQP\162MS0QPV1XVrRx,tID7X1Gg019TRy%l2Rz%l1R{P0%l5?512P4P5P4P1C9R0[P5P1P5P2C9%l4?551[R|%l6?545\0B0m512P2n2001000000120000000W>W=W?R0P|^>{^=z^?yRyP2PF%d8#i#i#DRz,AFR{16PMR|%<zPFP{PFP|C9dO4b0A5G{|PGP{PQPpP2PVAHIVqD7X1GPLP|P2E8b0P\PNPhFK%`9MA_P0PyP2PF%[8#Z#DR|,:FRLQ0O%<|PFPLPFQ0OC9dO4b0PGPFP|P31GF|dQ0ODIPGPLP;fSR|?4jqR{P2PpP\P;A4{?qRzPjPkPNP]PjPaF@PjPrP?PrD0PjP9P?P9D0PsPXPNPOD0PJPFPFPYPCCOS0RPjPOD0PsPtP?POD0PBPmPiPpP\F>S0SEEX1GP;A4pjrR4PLP\PYD3P;P<PHAw@?vS0TP4A44?rR6n010000002000016LAS0UP\PYD3P;P6PjPkPNP]D0PjPaPjP9D0P?P9PjPeD0P?PePsPXD0PNPqPJQ0FD0PjPqPsPtD0P?PqPBPmD0S0VPiP\PYD3PwP;P7P4PLP\PYg01:2P?PN1:gCS0WPxPrg01;<Pug01<F%l@Rx00lGRLPxPGPjPrC?S0X&0SLR6PpPNPuELPGP4PN1CpNCBR4eP4PG1C|NR4PQP|Q0W,TgS0Y,62S0ZPVAHIVOR}D7X1GPGPPPQP|162CS0[PVP}D7X1GP0PyP2PF%d8#i#z#DR},AFR~16PCRP%<}PFP~PFPPC9dO4b0A5G~PPGP~PQfTR~P2PVAHIVYD7X1GP`PPP2E8b0P4PfEJP{PNP2FKb2%`rMA_P0PyP2PF%[8#Z#QR{,:FR4Q0U%<{PFP4PFQ0UC9dO4b0PGPFP{P31GF{dQ0UDIPGP4P;P~PjPOP?POD0R{P2P|PpP;P{PjPkPNP]PjPaF@PjPqP?PqD0PjPrP?PrD0PsPXPNPYD0PJPFPFP\PCPjPYGMPsPtP?PYD0PBPmPiP|PpF>S0\EEX1GP;PzP4PpP\D3P;Pz%2R#gRR1:RTS0]'TS0^,}4S0_PpP\D3Q0SPwP;P7PzP4PpP\g01=PPjP?Q0]g01>ZPug01?dPLPxPGP?PqC?PLPxPGPjPqP6E=P|PjPuELPGPzPjPqCBRzePzPGPOfURzPjPYP?PYD0R4/C?RP,e2#^X1GPLPxPGP?POC?PLPxPGPjPOP6E=P~P?PuELPGP{P?POCBR}eP}PGPY1e\2#^X1G&0AYPPP2EJb2P{PjP2FKb2N>0@P0PyP2PF%[8#c#QRP,:FR}Q0_%<PPFP}PFQ0_C9dO4b0PGPFPPP31GFPdQ0_DIPGP}P;P4P2P~P|P;P4PjPkPNP]PjPaF@PjPOP?POD0PjPqP?PqD0PsPXPNP\D0PJPFPFPpPCPjP\GMPsPtP?P\D0PBPmPiP~P|F>EEX1GP;P{P}P|PpD3P;P<PHQ0NP{Q0@#gR41:4TR4'T%PSS0@+0R-0Q}RS94{jn010000002000016}AS0SP|PpD3Q0\PwP;P7P{P}P|Ppg01@nR{PjP4g01B8%v{#ug01CBN<0kP0PyP2PF%[8#i#DR{,:FR4Q0S%<{PFP4PFQ0SC9dO4b0PGPFP{P31GF{dQ0SDIPGP4P;fVR{PjP\P?P\D0RPPjPSP2PzP~P;A4PjkRP?4N]S0\PjPaPjPYP?PYF@PjPOP?POD0PsPXPNPpD0PJPFPFP|PCPjPpGMPsPtP?PpD0PBPmPiPzP~F>RSGRX1GP0PyP2PFPkQ0@-0RT-0Q}S0`%<nPFPkPFQ0`C9dO4b0Q0`95GkPGPkP;fWRnPjPpP?PpD0R}PjP2P4P{PzP;A4}jkS0a?4N]R}PjPaPjP\P?P\F@PjPYP?PYD0PsPXPNP|D0PJPFPFP~PCPjP|GMPsPtP?P|D0PBPmPiP{PzF>S0bGRX1GP;PPP4PzP~D3P;P<PHAw@NvS0cPPQ0\n0100000020000164AS0\PzP~D3PSPwP;P7PPP4PzP~g01DLPNPj&0P8$02#QR4,:gRSQ0;P]g01EVPug01F`PLPxPGPjPkC?RYPLPxPGP?P\PLPxPGPjP\P6E=E=P{PjPuELPGPPPjPkCBRPePPPGPkPQPn1TgS,62PVQ0<D7X1GP0PyP2PFP[16k4R4Q0:#<PFP[PFP4C9dO4b0A5G[4PGP[PQfXR[P2PVQ0<D7X1GPhP4P2E8b0Q0aPjP2FKb2%`]MA_P0PyP2PF%[8#i#QR4,:FRhQ0\%<4PFPhPFQ0\C9dO4b0PGPFP4P31GF4dQ0\DIPGPhP;P[PjP|P?P|D0PjPkPNP]D0R4P2PnP{P;P4PjPaPjPpP?PpF@PjP\P?P\D0PsPXPNP~D0PJPFPFPzPCPjP~GMPsPtP?P~D0PBPmPiPnP{F>S0aEEX1GP;P}PhP{PzD3P;P}16hAS0<P{PzD3Q0bPwP;P7P}PhP{Pzg01GjPNPvQ0E#1,mRg01I4Pug01J>PLPxPGPNP]C?RhPLPYPLPxPGP?PpPLPxPGPjPpP6E=GWPnPNPuELPGP}PNP]CBR}eP}PGP]fYR}PjP~P?P~D0PjPkPNP]D0RS/Cv,e2=5<oX1GPu1AF=S0E,e]=5<od1C4NS0bP2EJb2N>0jP0PyP2PF%[8#z#DRo,:FRPQ0<%<oPFPPPFQ0<C9dO4b0PGPFPoP31GFodQ0<DIPGPPP;PSP2P[PnP;PSPjPaPjP|P?P|F@PjPpP?PpD0PsPXPNPzD0PJPFPFP{PCPjPzGMPsPtP?PzD0PBPmPiP[PnF>EEX1GP;P4PPPnP{D3P;P<PHQ0NP4&0icRp944jn010000002000116PAS0:PnP{D3Q0aPwP;P7P4PPPnP{g01KHPjPN1:g_RPQ0>Pcg01LRPug01M\PLPhPLPYPLPxPGP?P|PLPxPGPjP|P6E=GWP[PNPuELQ0b=5G]R4eP4PGP]PQP}1TgP,62PUPdD7X1GP0PyP2PF%{8$0O#f#p$08#QRP,AFR416]_R_%<PPFP4PFP_C9dO4b0A5G4_PGP4PQfZR4P2PUPdD7X1GP^P_P2E8b0PSPNP2FKb2P:Pb20M>KRS,r2X<:20L>K1r=>S0b%qK1r=S[[%q>R_g01NfR^B0K>K1UW9%qS\^^9_g01OBRd$0SRU&0UdRd&0h:S0>&0f:RP&0e:Ro%\bS0a%\>S0;%gD60J:+0>']Q02-0doRDP2P5Q00,a<S0020c25#^dB0b:=1H0aR5b5b6b71rbSP2b3b:b;1NFcPUPdQ0>PP20I:=S02Q0a+05,]oPDP5b5b6b7%qbP2b3%PERE-0L>S0dQ0b%qE20M>ERS,r=[[S0bB0K>E1V^X9_S0e%qS\^^9_S0fPUPdQ0>PPQ0aQ0;>0J:FS0;+0>,]oPDP5b5b6b71rbSP2b3b:b;60<bEJ-0`cNA0_P0PyP2PF%[8#z#QRc,:FRbQ0:%<cPFPbPFQ0:C9dO4b0PGPFPcP31GFcdQ0:DIPGPbP;P4PjPzP?PzD0PjPkPNP]D0RcPjPpP2P}P[P;A4cjaRcPjP~P?P~D0PjP|P?P|D0PsPXPNP{D0PJPFPFPnPCPjP{GMPsPtP?P{D0PBPmPiP}P[F>R|GRX1GP0PyP2PFPaPpQ0G#<PFPaPFPpC9dO4b0A5GapPGPaP;f[R_PjP{P?P{D0PjPkPNP]D0R^PjP2PbP4P}P;A4^jaR^?4jzS0GP?PzPjP~P?P~F@PsPXPNPnD0PJPFPFP[PCPjPnGMPsPtP?PnD0PBPmPiP4P}F>R~GRX1GP;PcPbP}P[D3P;PcQ0@,:RRE,TR,}bS0@P}P[D3P|PwP;P7PcPbP}P[g01OnPjPvPEg01Q8Pug01RBPLPxPGPjPaC?REPLPhPLPYPLPxPGP?PzPLPxPGPjPzP6E=E=D;P4PjPuELPGPcPjPaCBRcePcPGPaf\RcPjPnP?PnPjPkF@PNP]PjPaD0Rb/Cv-0H2#^X1GQ00Q0E-0Ha#^dP^PjP2FKb2N>0^P0PyP2PF%[8$0;#DR|,:FR>Q0@%<|PFP>PFQ0@C9dO4b0PGPFP|P31GF|dQ0@DIPGP>P;PbP2P_P4P;A4bj{R|?4?{S00PjPzP?PzD0PsPXPNP[D0PJPFPFP}PCPjP[GMPsPtP?P[D0PBPmPiP_P4F>S0aEEX1GP;P^P>P4P}D3P;P<PHQ0NP^Q0Gn010000002010116>AS0GP4P}D3P~PwP;P7P^P>P4P}g01SLPjPNQ0A,:gR>1XVzPzg01TVPug01U`PLPEPLPhPLPYPLPxPGP?P{PxPGPjP{C?S0>=UL6E=D;P_PNPuELPGP^PNP]CBR^eP^PGP]PQPc1Tg>,62PV1XVnS0g,tID7X1GP0PyP2PF%d8#o$0=#DR>,AFR^Q0A,6]R~%<>PFP^PFP~C9dO4b0A5G^~PGP^PQf]R^P2PV1XV[S0A,tIR>D7X1GP`P~P2E8b0PbPNP2FKb2%`zMA_P0PyP2PF%[8$0;#QRz,:FRbQ0G%<zPFPbPFQ0GC9dO4b0PGPFPzP31GFzdQ0GDIPGPbP;P^PjP[P?P[D0PjPkPNP]D0PjPaPjPnD0RzP2PcP_P;A4z?nR~PjP{P?P{D0PsPXPNP}D0PJPFPFP4PCPjP}GMPsPtP?P}D0PBPmPiPcP_F>S0hEEX1GP;P|PbP_P4D3P;P<PHQ0TP|Q00n010000002010116bAS00P_P4D3Q0aPwP;P7P|PbP_P4g01VjP?PNQ0B,:gRb1XV{P{g01X4Pug01Y>PLQ0>PLPEPLPhPLPYPLPxPGP?PnC?S0>PxPGPjPnC?R`=UL6D;D;PcPNPuELPGP|PNP]CBR|eP|PGP]PQP^1Tgb,62PVP>D7X1GP0PyP2PF%d8#c$04#DR>,AFRbQ0B,6]R|%<>PFPbPFP|C9dO4b0A5Gb|PGPbPQf^RbP2PVAHIV}S0BD7X1GQ0CP|P2E8b0PzPNP2FKb2%`{MA_P0PyP2PF%[8$0}#DRz,:FR|Q00%<zPFP|PFQ00C9dO4b0PGPFPzP31GFzdQ00DIPGP|P;PbPjP}P?P}PjPkF@PNP]PjPaD0PjP[P?P[D0RzP2P^PcP;A4zjnS0CP?PnPsPXPNP4F@PJPFPFP_PCPjP4GMPsPtP?P4D0PBPmPiP^PcF>S0aEEX1GP;P~P|PcP_D3P;P~Q0^,}|S0^PcP_D3Q0hPwP;P7P~P|PcP_g01ZHPjP?Q0]g01[RPug01\\PLQ0>PLP`PLPEPLPhPLPYPLPxPGP?P[C?R`PLPxPGPjP[C?S0>P6D;D;D;P^PjPuELPGP~PjPnCBR~eP~PGP[f_R~PjP4P?P4PjPkF@PNP]PjPaD0PjP}P?P}D0R|/C?R>,e2#^X1GPLP`PLQ0>PLPEPLPhPLPYPLPxPGP?P}C?S0]PxPGPjP}C?S0h=UL6D;D;D;S0iPbP?PuCjPGPzP?P[CBR`eP`PGP}1e42#^X1G&0A}P>P2EJb2PzPjP2FKb2N>0@P0PyP2PF%s8#Z#Y#DR>,:FR`Q0^%<>PFP`PFQ0^C9dO4b0PGPFP>P31GF>dQ0^DIPGP`P;P|P2PbP^P;A4|j[R>?4?[S0jPsPXPNP_D0PJPFPFPcPCPjP_GMPsPtP?P_D0PBPmPiPbP^F>S0kEEX1GP;PzP`P^PcD3P;P<PHQ0NPzQ0Cn010000002010116`AS0CP^PcD3Q0aPwP;P7PzP`P^Pcg01]fPjPNQ0PQ0gPng01_0Pug01`:Q0iPbPNPuCjPGPzPNP]CBRzePzPGP]PQP~Q0P,Tg,62S0iPVQ0BD7X1GP0PyP2PF%{8$0O#Z$02$08#DS0B,AFRz16]MR`Q0B#<PFPzPFP`C9dO4b0A5Gz`PGPzPQf`RzP2PVAHIV4S0BD7X1GPZP`P2E8b0P|PNP2FKb2%`nMA_P0PyP2PF%s8#Z#Y#QR|,:FR`Q0C%<|PFP`PFQ0CC9dO4b0PGPFP|P31GF|dQ0CDIPGP`P;PzPjP_P?P_D0PjPkPNP]D0PjPaPjP4D0P?P4PjP}D0S0gP2P~PbP;Q0g?4?}R|PsPXPNPcD0PJPFPFP^PCPjPcGMPsPtP?PcD0PBPmPiP~PbF>S0aEEX1GP;P>P`PbP^D3P;P<PHQ0TP>Q0jn010000002010116`AS0jPbP^D3Q0kPwP;P7P>P`PbP^g01aDP?PNQ0WQ0AP[g01bNPug01cXPLQ0>PLQ0]PLQ0hPLPEPLPhPLPYPLPxPGP?P4C?S0>PxPGPjP4C?S0A=UL6D;D;D;P~PNPuELPGP>PNP]CBR>eP>PGP]PQPzQ0ZPVQ0BD7X1GP0PyP2PF%d8#o$0;#DS0B,AFR>16]CR`Q0B#<PFP>PFP`C9dO4b0A5G>`PGP>PQfaR>P2PVAHIV_D7X1GPZP`P2E8b0Q0gPNP2FKb2%`[MA_P0PyP2PF%s8#Z$04#DR[,:FR`Q0j%<[PFP`PFQ0jC9dO4b0PGPFP[P31GF[dQ0jDIPGP`P;P>PjPcP?PcPjPkF@PNP]PjPaD0PjP_P?P_D0PjP4P?P4D0R[P2PzP~P;A4[sXS0gPNP^PJPFPFPbPCCOPjP^F@PsPtP?P^D0PBPmPiPzP~F>S0BEEX1GP;P|P`P~PbD3P;P|Q04,mRRZ,TR,}`S04P~PbD3Q0aPwP;P7P|P`P~Pbg01dbPjP?PZg01elPug01g6PLQ0]PLQ0hPLQ0>PLQ0APLPEPLPhPLPYPLPxPGP?P_C?S0hPLPxPGPjP_C?S0]P6D;D;D;D;PzPjPuELPGP|PjP}CBR|eP|PGP4fbR|PjP^P?P^PjPkF@PNP]PjPaD0PjPcP?PcD0PjP_P?P_D0S0a/C?RZ,e2#^X1GPLQ0>PLQ0APLQ0hPLQ0]PLPEPLPhPLPYPLPxPGP?PcC?S0APxPGPjPcC?S0>=UL6D;D;D;D;R`P>P?PuCjPGP[P?P4CBRRePRPGP_1ec2#^X1G&0A_PZP2EJb2P[PjP2FKb2N>0@P0PyP2PF%s8#f$04#DRZ,:FRRQ04%<ZPFPRPFQ04C9dO4b0PGPFPZP31GFZdQ04DIPGPRP;Q0aP2P>PzP;Q0a?4sXS0k?4NbS0lPJPF1NF~RZPCPjPbK0]PsPtP?PbD0PBPmPiP>PzF>S0mEEX1GP;P[PRPzP~D3P;P<PHAw@svS0nP[Q0gn010000002010116RAS0gPzP~D3Q0BPwP;P7P[PRPzP~g01h@PsPJQ0PQ08PXg01iJPug01jTP`P>PJPuCjPGP[PJ1C>JCBR[eP[PG1C|JS08PQP|Q0iPVQ09D7X1GPG1SZKR[,AFS0iPQP|Q0QPVQ09D7X1GP:P[1NFzR`>03FTS0QAbF2M55GX<:P:PG&0|FS0PQ0P1SZTS0B1|[MPG\:Q0P'aS0oPUPd20{:1S0pPPP:20z:8RZ%\T60::g01k^S0q%\K:0::ZRR%\M60\:H07,]oPDP5b5b6b7X4:1S2T1S2KS0r/|M+0[^4:P2P`O1b3L0ZQ0i,NFPUPdQ0pPPPoQ05#\Q06#\:0::Z+05,]oQ01$0VS01Q02005R,]oH0NPDP5b5b6b7X4:S02Q05Q06,S2+001S1KRT#q[^4:S05P2P`P}O2b3Q0dQ0bQ0eQ0fPUPdQ0pPPPoQ07#\-05Z,]oQ01Q0;-0>R,]oH0NPDP5b5b6b7X4:S0;Q07-0021rTS[^4:S07P21NF|RTP4O2b3b:b;60<[EJQ0B,AFQ0i/6M55GR[eP[PGQ0QfcR[@0y2VS0QQ0955QX1GPnB03F`KRn/6MP2E8b0Q08P4EJQ0aPJP2FKb2%`XMA_P0PyP2PF%s8#f$04#QR4,:FRMQ0g%<4PFPMPFQ0gC9dO4b0PGPFP4P31GF4dQ0gDIPGPMP;P[PjPbP?PbD0PjPkPNP]D0PjPaPjP^D0P?P^PjPcD0P?PcPsPXD0S0aP2P|P>P;Q0a?4N~R4PJPFP`PCPjP~K0]PsPtP?P~D0PBPmPiP|P>F>S09EEX1GP;Q0kPMP>PzD3P;P<PHQ0cQ0kQ0ln010000002010116MAR`P>PzD3Q0mPwP;P7Q0kPMP>Pzg01lEPNPJAxg=3RM1XVbPbg01mOPug01nYPLPxPGPsPXC?RSPLQ0hPLQ0]PLQ0APLQ0>PLPEPLPhPLPYPLPxPGP?P^C?S0>PxPGPjP^C?S0A=UL6D;D;D;D;P|PJPuELPGQ0kPJQ08CBR}eP}PG1C[JS08PQP[1TgMR},62S0kPVAHIVzRID7X1GPGPnPQP[162=PVPID7X1GPGPnQ0Q=5QIX1GP{16n=&0FnEJQ08P_EJQ0aPJP2FKb2%`bMA_P0PyP2PF%s8#f#p#DR_,:FRnP`%<_PFPnPFP`C9dO4b0PGPFP_P31GF_dP`DIPGPnP;fdR_PjP~P?P~PjPkF@PNP]PjPaD0PjPbP?PbD0PjP^P?P^D0PsPXPNPzD0R{P2P[P|P;P{PJPFPFP>PCPjPzGMPsPtP?PzD0PBPmPiP[P|F>EEX1GP;P4PnP|P>D3P;P<PHAw@JvP4P4PJ1C4JQ0YCkn010000002010116nARIP|P>D3Q09PwP;P7P4PnP|P>g01ocRnPJPJQ0Wg020m%vn#ug0227N=06P0PyP2PF%s8#f#p#QRn,:FR4PI%<nPFP4PFPIC9dO4b0PGPFPnP31GFndPIDIPGP4P;feRnPjPzP?PzPjPkF@PNP]PjPaD0PjP~P?P~D0PjPbP?PbD0PsPXPNP>D0RQPJ1CQJS0WQ0YCkP2P_P[P;PQPJ1STCS0Y,AFS09PjP>D0PsPtP?P>D0PBPmPiP_P[F>EEX1GPLPxPGPNPzC?PLPSPLQ0>PLQ0APLPxPGP?PbPLPxPGPjPbPLPEPLPhPLPYPLPxPGP?P~C?S0APxPGPjP~C?S0>=UL6D;D;E=GWD;P_PJPuELPGP{PJ1C_JCBR{eP{PG1CnJS0aP;ffR{PjP>P?P>PjPkF@PNP]PjPaD0PjPzP?PzD0PjP~P?P~D0PsPXPNP|D0S08PJQ0ZP4PnP_P;Q081NF[R~>03FCRb74JRQPjP|PsPtP?P|F@PBPmPiPnP_F>S0ZGRX1GPG1STKRT,AFRVP;Q08PJQ0[P4PnP_Q0ZGRX1GP:PTAbF2C95GbX<:P:PGQ0PQ0PQ0Y1|TCQ0oPUPdQ0pPPP:%\CRP:0::ZQ0qB0\:RPH07,]oPDP5b5b6b7X4:1S2CQ0r/|C+0[^4:P2P~O1b3L0Z1NFVQ02Q05P2P~PcO2b3Q0dQ0bQ0eQ0fQ0;Q07P21NFnRcP^O2b3b:b;60<TEJQ0916VC55GRVePVPGPbP;fgRVPjP|P?P|PjPkF@PNP]PjPaD0PjP>P?P>D0PjPzP?PzD0PsPXPNP[D0RTPJP2P4P{PnP;PTPJPFB0WF_CH0vRTPjP[PsPtP?P[F@PBPmPiP{PnF>GRX1GP;PQP4PnP_D3P;PQ1:FWR:00E}R5PnP_D3Q0ZPwP;P7PQP4PnP_g023APsPMP:g024KPug025UPLPxPGPJPbC?PLPxPGPNP|PLPSPLQ0APLQ0>PLPxPGP?PzPLPxPGPjPzPLPEPLPhPLPYPLPxPGP?P>PLPxPGPjP>P6E=GWD;E=GWD;E=P{PsPuELPGPQPsPXCBRQePQPGPXA5G2:X1GP0PyP2PFPXP:%<WRQ1NF:Rz:0uFXdO4b0PTPsP2FKb2N>0tP0PyP2PFP:P5PQB0YzF5dO4b0P31GFWd9xFWRW=5G5PGP:P;fhRTPjP[P?P[D0PjPkPNP]D0PjPaPjP|D0P?P|PjP>D0P?P>PsPXD0PNP_PJB03FcCD0RcP2PVP{P;PcPjP_PsPtP?P_F@PBPmPiPVP{F>R>EEX1GP0PyP2PFP:20E:=RbPQB0YzFbdO4b0P:PGe00E=95GWP;PcP:PVP{D3P;P<PHQ0NPcPcPj1CcNP}Ckn010000002010116:ARWPVP{D3P>PwP;P7PcP:PVP{g026_R:PjPNPMg027i%v:#ug0293N=06P0PyP2PF%Z8#p#f#c#DR:,:FRcPW%<:PFPcPFPWC9dO4b0PGPFP:P31GF:dPWDIPGPcP;fjR:PjPnP?PnD0PjPkPNP]D0PjPaPjP_D0P?P_PjP[D0P?P[PsPXD0PNP{PJPFPFPVPCCOD0R>Pj1C>NRbP}CkP2fiRzPTP;A4>j{R>PsPtP?P{D0PBPmPiPzPTF>RQEEX1GPLPxPGPJPFPFP{PCCOR4C?PLPxPGPNPnPLPSPLPxPGP?P|PLPxPGPjP|PLPxPGP?P[PLPxPGPjP[PLPEPLPhPLPYPLPxPGP?P_PLPxPGPjP_P6E=GWD;E=E=E=GWE=PzPNPuELPGPzPjP_P?P_D0PjPkPNP]D0PjPaPjP[D0P?P[PjP|D0P?P|PsPXD0PNPnPJP4D0PNPnCBR4eP4PGP{P;fkR4PjP{P?P{D0PjPkPNP]D0PjPaPjPnD0P?PnPjP_D0P?P_PsPXD0PNPVPJPFPFPTPCCOD0R_PjQ0kPcP:PzP;P_PjPVPsPtP?PVF@PBPmPiP:PzF>R|GRX1GPGP{P;P_PjP2PcP:PzP|GRX1GP;P>PcPzPTD3P;P<PHQ0nP>16cAR|94>sn0100000020101Q0?#2#gR_Q0=$0P#i#c,m_R_'T,}cR[PzPTD3PQPwP;P7P>PcPzPTg02:=RcPsP_g02;G%vc#ug02<QN<0sP0PyP2PF&0X8$0B#o$02$08#DRc,:FR_P[%<cPFP_PFP[C9dO4b0PGPFPcP31GFcdP[DIPGP_P;flRcPjPVP?PVPjPkF@PNP]PjPaD0PjP{P?P{D0PjPnP?PnD0PsPXPNPTD0PJPFPFPzPCPjPTGMRnPsP|P2P4P:P;A4nstRn?4?TPBPmPiP4P:F>R>GRX1GP0PyP2PFPtP|Q0I#<PFPtPFP|C9dO4b0A5Gt|PGPtP;fmRQPjPTP?PTPjPkF@PNP]PjPaD0PjPVP?PVD0PjP{P?P{D0PsPXPNPzD0PJPFPFP:PCCORDPjPzD0RoPsP2P_PcP4P;A4ostRo?4?zPBPmPiPcP4F>GRX1GP;PnP_P4P:D3P;P<PHQ0TPnPnP?1CnjP}Ckn010000002010116_ARPP4P:D3P>PwP;P7PnP_P4P:g02=[R_P?PjPMg02>e%v_#ug02?oN=06P0PyP2PF&0X8$0B#o$02$08#QR8,:FR_PP%<8PFP_PFPPC9dO4b0PGPFP8P31GF8dPPDIPGP_P;fnR8PjPzP?PzD0PjPkPNP]D0PjPaPjPTD0P?PTPjPVD0P?PVPsPXD0PNP:PJPFPFP4PCCOD0PjP:PsPtD0RMP?1CMjRnP}CkP2PQPcP;A4M?:RMPBPmPiPQPcF>R}EEX1GPLPxPGPsPtC?R>PLPxPGPjPzPLPxPGPJPDPLPxPGPNPzPLPSPLPxPGP?P{PLPxPGPjP{PLPxPGP?PVPLPxPGPjPVPLPEPLPhPLPYPLPxPGP?PTPLPxPGPjPTP6E=GWD;E=E=E=GWE=E=E=PQPjPuELPGPoPjPzCBRoePoPGP:P;foRoPjP:P?P:D0PjPkPNP]D0PjPaPjPzD0P?PzPjPTD0P?PTPsPXD0PNP4PJPFPFPcPCCOD0PjP4PsPtD0RTP?Q0kP_P8PQP;A4T?4PBPmPiP8PQF>RVGRX1GPGP:P;PTP?P2P_P8PQPVGRX1GP;PMP_PQPcD3P;P<PHAw@BvPMPMPB1CMv1:glR@,TgRgCkn010000002010116_ARAPQPcD3P}PwP;P7PMP_PQPcg02A9R_PBPvP@g02BC%v_#ug02CMN=06P0PyP2PFPiPAQ0D#<PFPiPFPAC9dO4b0PGPFQ0DP3Q0D,GFdPADIPGPiP;fpR3PjP4P?P4PjPkF@PNP]PjPaD0PjP:P?P:D0PjPzP?PzD0PsPXPNPcD0PJPFPFPQPCPjPcGMPsPtP?PcD0RzPB1CzvPgCkP2PoP8P;PzPBPmPiPoP8F>RzEEX1GP0PyP2PFPmQ0E/6lRy%<lPFPmPFPyC9dO4b0A5GmyPGPmP;fqPjPcP?PcPjPkF@PNP]PjPaD0PjP4P?P4D0PjP:P?P:D0PsPXPNPQD0PJPFPFP8PCPjPQGMPsPtP?PQD0RQPBP2PiP3PoP;PQPBPmPiP3PoF>GRX1G20r7zPyP2E8b0PAP2E8b0EF16:=&0F:EJPnP2EJb2PPP2E8b0EFP|P2E8b0P[P2E8b0EF16{=&0F{EJPbP2EJb2PWP2E8b0EFb0P5P2E8b0EFB03F~K/6CP2E8b0Q0aP^EJQ0WP2EJb2PIP2E8b0EFP`P2E8b0EFQ0gP2E8b0EFQ04P2E8b0EFQ0jP2E8b0EFQ0CP2E8b0EFQ0^P2E8b0EFQ00P2E8b0EFQ0GP2E8b0EFQ0@P2E8b0EFPpP2E8b0Q0:P2E8b0EFQ0<P2E8b0EFQ0\P2E8b0EFQ0`P2E8b0Q0SP2E8b0EFQ0_P2E8b0EFQ0UP2E8b0EFQ0OP2E8b0EFQ0JQ0MPLPxPGPBPmPLPxPGP?PrPLP>PLQ0XPLPxPGPJQ0HPLPxPGPNPrPLPSPLPxPGP?PfPLPxPGPjPfPLPxPGP?PePLPxPGPjPePLPEPLPhPLPYPLPxPGP?P9PLPxPGPjP9P6E=GWD;E=E=E=GWE=E=D;E=E=R6P\PjPuCjQ0JeQ0JPGPqA5G2OX1G1aGqQ0VPjP2FKb2Q0KQ0LP6P\PBPuCjQ0KeQ0KPGPmA5G2mX1G1aGmQ0VPBP2FKb2P6P\PJPuCjQ0LeQ0LPGQ0FQ0R95G2X1GQ0F,aGQ0VPJP2FKb2H0DH0DH0DH0qWCWDP1P2O2n2001000010121000000W0WEP1P2O2n2001000010121000000W0WFP1P2O2n2011000010121000000W0WBP1P2O2n2011000010121000000W0WGW@WAWKWJWLWMWHWIXSGXUGXRGXNGXTGWQWOWPo"). Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0Exit_run3.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.musl.Mh_0067.
Module Ns0Strnlen.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.musl.Mh_0067. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Frame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.musl.Mh_0067.Ns0MemcpyBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.musl.Mh_0067.Ns0Memchr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r4e000_4f000 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0022.Ns0_code_r58000_59000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Ns0Strnlen () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes3nat02C59OSSVerify5KrLib7Mh_00387CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01C45stdpp9bitvector;definitions;bv_unsignedK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_00387CatExec6wbytesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib7Mh_00385Frame6in_rngC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses9not_morphC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00387StepTac6u_Z2bvC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthc59OSSVerify5KrLib7Mh_0058:Ns0Strnlen5lenW8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Frame>wbytes_outsideC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058:Ns0Strnlen4mem1C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00I69OSSVerify5KrLib4musl7Mh_00679Ns0Memchr5mchrH00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC47Corelib4Init5Peano2ltC69OSSVerify5KrLib4musl7Mh_00679Ns0Memchr<rodata_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02c59OSSVerify5KrLib7Mh_0058:Ns0Strnlen8mem1_outC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib4musl7Mh_00679Ns0Memchr5mchrH01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib7Mh_00385Frame7outsideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk<wbytes_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?mem_grows_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib7Mh_00387SeqExec?rdn_wbytes_hit8C1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses8or_morphC59OSSVerify5KrLib7Mh_00387CatExec>rdn_wbytes_outC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC59OSSVerify5KrLib7Mh_00385Hoare6ret_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4musl7Mh_00679Ns0Memchr2KLC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0056<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6regupdC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib7Mh_00387SeqExec<step_addi_atC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions4BvWfC59OSSVerify5KrLib7Mh_00387WalkTac=wf_getr_chainC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib7Mh_00387StoreOk<store_ok_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec:step_sd_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC49OSSVerify5KrLib8PropExec9step_addiC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4btgtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec=step_jal_linkC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_00306CatSim6msteps01C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8v_addi_0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2ex01c59OSSVerify5KrLib7Mh_0058:Ns0Strnlen4HOK1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Hoare;ret_ok_evenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4musl7Mh_00679Ns0Memchr;ref_memchr0C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC49OSSVerify5KrLib8PropExec4c_eqC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec8c_eq_neqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec;step_beq_ftC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec5v_subC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec;step_sub_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058:Ns0Strnlen5rd_raC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec?bytes_le_to_Z_8C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7step_ldC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058:Ns0Strnlen5rd_s0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058:Ns0Strnlen5rd_s1C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses>eq_equivalenceC47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib7Mh_00387SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387SeqExec<step_jalr_x0C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC59OSSVerify5KrLib7Mh_0056<RefMemcpyLib:runs_transC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC35stdpp7tactics<f_equal_helpK59OSSVerify5KrLib7Mh_00306CatSim6msteps02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C59OSSVerify5KrLib7Mh_0056<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba430C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba430C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba430C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba434C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba434C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba434C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba438C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba438C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba438C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba43cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba43cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba43cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba440C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba440C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba440C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba444C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba444C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba444C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba448C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba448C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba448C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba44cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba44cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba44cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba450C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba450C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba450C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba454C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba454C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba454C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba458C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba458C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba458C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba45cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba45cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba45cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba460C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba460C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba460C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba464C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba464C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba464C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba468C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba468C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba468C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba46cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba46cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba46cC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007W_ba470C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007F_ba470C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0022ENs0_code_r58000_590007D_ba470C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okc59OSSVerify5KrLib7Mh_0058:Ns0Strnlen;strnlen_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00385Frame9frame_modC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058:Ns0Strnlen6frame1C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Section SNL.
  Variable mem : word -> option byte.
  Variables s sp : word.
  Variable buf : list byte.
  Variables K n : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : mchrH mem s buf K n.
  Hypothesis HsK : (0 < bv_unsigned s + K)%Z.
  Hypothesis Hstk : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true.
  Hypothesis Hspr : (0x13898 <= bv_unsigned sp - 32)%Z.
  Hypothesis Hdisj : (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32
                      \/ bv_unsigned sp <= bv_unsigned s)%Z.

  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation W8 v := (word_to_le_bytes 8 v).

  (* [comment removed for export] *)
  Definition mem1 (ra s0 s1 : word) : word -> option byte :=
    wbytes (wbytes (wbytes mem (Z_to_bv 64 (usp - 8)) (W8 ra)) (Z_to_bv 64 (usp - 16)) (W8 s0))
           (Z_to_bv 64 (usp - 24)) (W8 s1).

  Lemma lenW8 : forall v : word, length (W8 v) = 8%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Strnlen ()) ["FPX_1"; "SNL"] "h01vp;1p;2p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210p1003<p4p710R0p8p1003Zp4p710P0p8p10045p4p710p1004Tp4p710p8g0050j11Tg005Uj14Tg0063j12Tg006Vj10Tg0075j23Tg008>#1#1#1#1#1#1#4#2g008c#0#0#0#0#0#0#0#0f0'3W0o"). Qed.

  Lemma mem1_out : forall ra s0 s1 (a : word),
    (bv_unsigned a < usp - 24 \/ usp <= bv_unsigned a)%Z -> mem1 ra s0 s1 a = mem a.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Strnlen ()) ["FPX_1"; "SNL"] "h04__x1h17__arithh24__ffh34__p1h46__sat2h56__sat3h68__varmaph75__with81nh94__x2h:1xh;2Hah<1yh=1zh>1Hh?1ah@1mhA1ohB2rahC2s0hD2s1p&0p;1p;2p;3p;4p;6p;7p;<p;Bp;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210g003<R0p4p710R1p8p1003Zp4p710P1p8p10045p4p710p1004Tp4p710p8g0050j16Tg005Uj1dTg0063j1`Tg009Bj29Tg009lj1<Tg00:Qj1;Tg00:oj28Tg00;LR1j21Tg00;hR2j20Tg00<Dj2aTg00<^j1mTg00=Uk203Tg00>2j24Tg00>Mj1|Tg00>oj2\Tg006Vj17Tg00?Uj2YTg00@]j3gj4XTg00AXj3ITg00B2j2VTg00BLR3j1eTg00Blj3DTg00Cej13Tg00D>R4j22Tg00D[j1HTg00E9j4oTg00E\j6NTg00FEj3MTg00Fnj2lTg00GVj3kTg00H:j1jTg00HZj1iTg00I:j2_Tg00IXk102Tg00J6k401Tg00JTk100Tg00K2j1~Tg00K]j2hTg00L@j3KTg00Lcj7{Tg00MGj1zTg00Mij3[Tg00NLj2yTg00Nnj2xTg00OZj3wTg00P9j4vTg00Pkj4ATg00QVj2fTg00R9j6uTg00R]j3tTg00S@j3RTg00T;j2TTg00T[j1]Tg00UXj6STP0j6FTg00VYj4sTg00WUl<rTg00X:lBqTg00X`l<cTg00YEj4LTg00Z0j7^Tg00ZTj7pTg00[8j6}Tg00[\j8bTf0R0#6#6p=Bg00\@R5/00p==g00\^R6/V0p=:g00]<R7P6P6P6P3P3f5R3f4R8f3R9f2R:f1R;P0M<rp=nP6P6P6P6P6P6P4P0P;P:P4P9P8P3f6R4f7R<f8f9MBqp=PP6P6P1P<P1P4P3P8P9P:P;P0M<cp=O1f60p=CP:g00][R1g00^:R=P=g00^ZR>P6P;g00_:R?P0CLg00_aR@F^p=GP:P1P=P=P>P6P;g00`ARAP0CLP@F^p=EP:P1P=P=P>P;P0Fpp=JP;P1P=P=P>P0E}p=ZP9P1P=P=P>P:P;P0Gbp=UP6P;PAP0CLp=?P8P1P=P=P>P9P:P;P1P=P=P>P0P@F^Gbp=5P6P;P?P0CLp=WP6P8P9P:P;P0EFp=@P7P8P9P:P;P0EFp=>P6P6P2P<P2P4P3P8P9P:P;P0M<cp=Qg008>R4#6R2#BR<#6R?#6R@#6RA#dRB#`RC19B0RDp,2spRE,9BRF%<4#6#B#;RG'8RH'110FD'a%mE%=FRE%;2RD%;ARA+03RI,1F'4%d<#`RJ#|RKp,3memRL%;<R<,8FRM,\BRNg008c#7#7#7#7#7#7#7#7RO/Y3RP3gRQ%;?R?,8FRR,\BRS1YO8RTP:CXRUPLP9O19IK0XAKRVPKPLPNPPP:CXRWPVPKPLP:O1RXPV1VKXAIKXXePWPPPLPNP:PO%e0RL9D9N#3X87PM19B9RW,00%eORV,20RY,1W'4#3X=6RW19B:RZ,0MR[12MVR\,1ZR]'4R^#312M<R_,1ZR`,4[Ra#3P[P]P[P`%H[P0X:6R[11;0#HX<6X:6R`PZPZ%:ZR]P\P_P[P[P[P6P6g00`h12;0Co#:X@6X86RbPMPM%:MPVP<P[P[%:LX:7POP<%:<EnRcM:PRdGOEN9M^a1lDARa115D%=A115I[[R^%=DReg00aLRfAkDA;UW;RA%=I\f^;eReg00ahRf#jRg%ifRfP61_6:P;&026H01Rh&006Ri%~6RjPjP1P=P=P>1h62R21h64Rk%CG5K6Rl5GjAEjk2F{Rm%z=Rn%C<Ro9K6kRp=Ej2A[6poRq9Gj25Jj,ZjCU1yj>RrP0P:g00bTRsg00c4Rt'V1x0:=IstdAw65;CvRtb2b6b7X06X96180G,1;100;'aRs18;<Ru/0:12u<Rv,1:'4g00cTRw[[^06^96P019B3PFP8O3Rxb1b4b5CA19BNRyPaP^PAPePgPf1_6;RzPiPj%B4#<#<#<#6#B#<#B#<#<#6#B#;R4#C%;@R@#C9K6k5EjR{PnPj1f65R5/?pD5PrPtb2b6b7X06180@,04R4%=u[^06P0PFp,4HsprO2R@b1b4b5PaP^PAPep-0R|PgPfPzPiPjPjP1P=P=P>P9Eu%CD=t6BRD9Gjk5JjR>PnPj1WpDD5PrPtb2b6b7X06W3110I,4;Rp11uI[^06^3|P0PEPFP9O3RFb1b4b55RMRED@AD:NV#3e1TJPRP%]3RND>PO12yL/0IX87PM10YIX=6RY10\I10_IP[10;0#HX<6X:6R0P\P_PdPIPI%:IRdGQPaP^PAPePgPfPzPiPjP>PnPj1?qDD5PrPtb2b6b7X06X3|10vI\p^06^3|PFb1b4b5CAPyPED@12yV/0IePPPND>ESEFPUPTPQPSP:POAD9SL#3X87PRPW10RZRU12RVRN,1ZRP'4Ry#312R<RE,1ZRv,4URq#3PUPPPUPv%HUP[P`PZPZP]PNPEP[P[P[PbPRPR%:RPVP<PcM:PRUGOEN9MyqPaP^PAPePgPfPhPiPjPmPn%C?9K6kRk=Ej2A[6koRq9Gj25Jj,ZjCUPrPtb2b6b7X06X9618;?R?/0:12?<Ry,1:'4Pw[\s^06^96Pxb1b4b5CA19BSRvPaP^PAPePgPfPzPiPjP{PnPj1?5kD5PrPtb2b6b7X06%=?\4^06P@b1b4b5PaP^PAPePgPfPzPiPjP>PnPj1WkDD5PrPtb2b6b7X06X3|11?I\p^06^3|PFb1b4b55RRR?D@AD:SV#3e1TJTRk%]8RPD>PO12vL/0IX87PRPY10NI10EIP[P0PNPEPUPIPIPdGQPaP^PAPePgPfPzPiPjP>PnPj1?qDD5PrPtb2b6b7X06X3|10yI\p^06^3|PFb1b4b5CAPvP?D@12vV/0IePkPPD>ESEFAgQSTRT1\BHRS1YO9RQP:CXPQPTPSP:POAD9SL#3X87PHPW10HZRW12HVRT,1ZRP'4Rk#312H<Rv,1ZR?,4WRy#3PWPPPWP?%HWP[P`PZPZP]PTPvP[P[P[PbPHPH%:HPVP<PcM:PRcGOEN9MkyPaP^PAPePgPfPhPiPjPmPnAEjl2A[6loRo9Gj25Jj,ZjCUPrPtb2b6b7X06X9618;GRG/0:12G<R<,1:'4Pw[\s^06^96Pxb1b4b5CA19BSRBPaP^PAPePgPfPzPiPjP{PnPj1?5lD5PrPtb2b6b7X06%=G\4^06P@b1b4b5PaP^PAPePgPfPzPiPjP>PnPj1WlDD5PrPtb2b6b7X06X3|11GI\p^06^3|PFb1b4b55RHRGD@AD:SV#3e1TJQRQ%]9RJD>PO12BL/0IX87PHPY10TI10vIP[P0PTPvPcPIPIPdGQPaP^PAPePgPfPzPiPjP>PnPj1?oDD5PrPtb2b6b7X06X3|10<I\p^06^3|PFb1b4b5CAPBPGD@12BV/0IePQPJD>ESEFP3P8P9P:Cs=IKXeb>W;X?CXDCXCCWBo"). Qed.

  (* [comment removed for export] *)
  Lemma HOK1 : forall ra s0 s1, mchrH (mem1 ra s0 s1) s buf K n.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Strnlen ()) ["FPX_1"; "SNL"] "p'0h04__x1h14__p1h24__x2h37__arithh44__ffh57__sat65h67__sat66h77__sat67h88__varmaph95__with:4cstrh;4__x3h<4__x4h=2Hah>4__p2h?4__x5h@1ohA1HhB2H0hC3HK0i003HK0hD3HKni013HKnhE4Hbufi024HbufhF2HihG4Hn64i034Hn64hH3Hnwi043HnwhI3Hnzi053HnzhJ3Hroi063HrohK4Hwini074HwinhL2HxhM5Hzeroi085HzerohN1ihO1jhP1mhQ2rahR2s0hS2s1hT1xhU1zp&0p;1p;2p;5p;3p;4p;7p;6p;>p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210g003<R0p4p710R1p8p1003Zp4p710P1p8p10045p4p710g004TR1p4p710p8g0050j14Tg005Uj1UTg0063j1STg00<^j1]Tg009Bj2;Tg00:Qj1:Tg00=Uj2kTg00;Lj20Tg00>2j29Tg00d1R2j5PTg00VYj3Hj4nTg00HZj1^Tg00>Mj1\Tg00T;j2~Tg00e4j4ZTg00eej2xTg00AXj3@Tg00D>j27Tg00fGj2sTg00fdj2rTg00BLj1pTg00;hj21Tg00gAj1lTg00>oj2YTg00gaj4OTg00h=j2hTg00Cej1gTg00hUj1TTg00i]j1fTg00jBj2eTg00Fnj2dTg00GVj3cTg00H:j1bTg00I:j2BTg00IXj1aTg00J6j4DTg00JTj1`Tg00K2j1_Tg00K]j2ETg00Mij3NTg00QVj2?Tg00R]k300Tg00MGj1[Tg00NLj2}Tg00B2j2|Tg00Nnj2{Tg00OZj3wTg00P9j4uTg006Vj1CTg00k3j2=Tg00k\j2LTg00lHj3KTg009lj12Tg00L@j3WTg00:oj2ITg00<Dj2GTg00lhj5VTg00mhj7qTP1j6oTg00S@j3mTP0j6QTg00n]l>tTg00YEj4RTg00Z0j7XTg00[\j8vTg00o`j3jTg00ZTj7yTg00Lcj7zTg00R9j6iTf0R0#4#4p=3g00\@R1/10p=5g00\^R3f1R4g00_:P0CRp=AP4g00][R5g00^:R6P6g00^ZR7P0g00_aR8FXp=>f2R9P5P6P6P7P3P4g00`AP0CRP8FXp=8f3R8P5P6P6P7P9P4P0Gvp=6Aj340p=<P9P5P6P6P7P4P0Fyp=FP9P5P6P6P7P4P0Fzp=JP4P5P6P6P7P0Eip=Mg008>R5#4R:#4R;#4R<#3R=#4R>#UR?#SR@p,2spRA#]1;?ARA#5%::RB%:>R>'kRC,0A'9p,1sRD#]1;?DRE#510EC'9p,3HOKp,3memRFPDp,3bufRGp,1KRHp,1nRIDPP2PFPDPGPHPIf6R2f5RJf4RK3HPDPGPHPIDPP0%U<RL#SRM#^RN#\ROg010IRPPFPD1~MGRQCZRR1xNGRN3@17EHRS%:<R<'sRT/r</7<%pQRU,7ERV'110VC%5HPM%lHRWPG1YL1RXCO,;L=@31g00]<1h0WPMP4PGPXCO,;L=@31#g[]O17H</1I10IC%TFfGRLfFRXfE3HRWPDPGPHPIPOPRPPfHRR?HLXPDPQCZ=@O0X@OPPPQPWPFPD%fQRQ%5URD1eS<RP%5S%5<%5T[[RT1dB>R<101B%5>101C[[RS%5BROg00aLRXAcB>4UW=R>%5C\X^=OROg00ahRX#bRI%^XRGP31B39P4%a3RYCD%`3RZ%_3R[1E35R\1E3:R]5N3R^1?3B>003?RB'A,>[%[6R6A8[^BC61}[7R7P0P9g00bTR^g00c4R_'|1{09=@^_dAw314CuR_b4b8b9X03X231704/0C1749/1C[^03^23P0PUPEf;O3b3b5b6b7b:1;?0R^,1E10^V'9fIR^PRPLP4PQPDPPPTP<PSP>POg008cRV#CR`#CRa#CRb#CRc,=31=3bRb1=3`'<'<g0122R`'L%Cc,=31=3VRV,<b'</L`=KXI5KXPGP3P31B3KP9PYCDRcP4P31B3JP8PYCDCDPZP[%25RY,E3Rd=8[\%2:,E39N3dR:,A\,>[5F[P6P[%:=R=,?39W3]Re98[:A8[]d5J[P6P[1?31R:1E3;9N3d'A,>[RdP6%4Y#3#:RY,?39W3],A\,>[R;A8[]\5J[C6C6C6P7P_b4b8b9X03X23X;3X<3X?31190179K,00'9178J1I9=R='11198'G17KJ,01R11IKY,08R]11K8'G[[[^03^23^;3^<3^?3P0PUPHPEPA1;?2PJp,5Hdisjp,3HsKRUO8b3b5b6b7b:DVWLXT@FqPNf8RNEof7RfP2PJPKP8P9P4%35#2#2#2#4#3#2#4#3#3#3#:Rg/10Rh%35#2#2#2#4#3#2#3#2#2#4#3#:R5,00Ri'9%\MRjPF1Y?4RFO1%[M9@j0X@jP9P4P0O2P^PRPLPFCnP^PRPLPFP3P41IAY,0011A0'GXU3PQPDPPPTP<PSP>POp-0RY1=3a/<V,<b/L`=KXIPGP3PcP41B38CDPZP[1M[21?35Rc,A\,>[RX5F[P6P[A8[ceP6P[PdP61M[f9J[;C6C6C6P7P_b4b8b9X03X23X;3X<3X1YW>19Ki115=1G]N\1[[^03^23^;3^<3^1Y^>YP011A211g2R1PHPEPAP2PJp,4HsprPUO9b3b5b6b7b:1;?FPQPDPPPTP<PSP>POPIPG1B34RFPZP[1?3g=8[\1M[8Rg5F[P6A8[:\C6P7P_b4b8b9X03X1Y19h4%54[^03^1YP01025P2PJO3b3b5b6b7b:PQPDPPPTP<PSP>POPIPGPFPZP[AF[gXP61A\B,>[C6P7P_b4b8b9X03X1Y194i104C[^03^1YP0P1P2PJO3b3b5b6b7b:5m4EQDVEQWFXN3%TWeM>tWJWGWDWIWMWCWHWKWEPNPfP2PJPKP8P9P4P0O9n5000001000000191102107104100108105101103106bPbBbAXS@XR@WQo"). Qed.

  Lemma frame1 : forall ra s0 s1, frame_mod mem (mem1 ra s0 s1) [(Z_to_bv 64 (usp - 32), 32%Z)].
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Strnlen ()) ["FPX_1"; "SNL"] "h04__x1h12Hah27__arithh34__ffh46__sat2h56__sat3h68__varmaph75__with84__p1h94__x2h:1ah;1Hh<2H0h=2_Hh>2rah?2s0h@2s1hA1zp;1p;2p;4p;3p;6p;7p;5p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210g003<R0p4p710R1p8p1003Zp4p710P1p8p10045p4p710p1004Tp4p710p8g0050j11Tg005Uj1MTg0063j1JTg00<^j1sTg009Bj2:Tg00;hj20Tg00:Qj16Tg00=Uj2[Tg00;Lj22Tg00>2R1j29Tg012^j2STg00:oj27Tg00>oj2=Tg013>j4qTg00H:j1OTg00lHj3jTg013^j2FTg00>Mj1`Tg00VYj4Dj3^Tg00AXj3>Tg014Xj2]Tg00Blj3LTg00Cej1?Tg00D>j2BTg00Fnj2ZTg00GVj3YTg00HZj1XTg00I:j2KTg00IXj1WTg00J6j4VTg00JTj1UTg00K2j1TTg00K]j2ITg00QVj2;Tg00L@j3ATg00Mij3RTg00[8j6rTg00MGj1pTg009lj15Tg00Lcj7oTg00NLj2lTg00B2j2kTg00Nnj2iTg00OZj3hTg00P9j4gTg00<Dj2fTg00lhj5eTg00R9j6aTg00R]j3bTg00S@j3cTP0j7dTg006Vj13Tg00?Uj2ETg00@]j3GTg015Vj3HTg016Wj5NTg017[j4_Tg00YEj4PTg00Z0j7mTg00ZTj7nTg00[\j8\Tf0R0#1#1p=8g00\^R2f1R3g00`AP0CPp=@P3g00][R4g00^:R5P5g00^ZR6P0g00_aFmp=4P2P3g00_:P0CPp=<f2R7P4P5P5P6P3P0Fnp=Qf3R8P4P5P5P6P7P3P0G\p=Cg008>R9#1R:#8R;#1R<#1R=#1R>#MR?#JR@p,2spRA#sg00\@RB1:?ARA'0RC%6:RD%6>R>'[RE,2A'91S@2RFP@P2%6=R=,7ARG,=?RHP=Cq%OFRF3j,F0RI%M;#J#`RJf5RKf4RLP8P3CDp,3memRMP3O13>[^:@A^873,]MRNP1AL3H=#?1F3Ff6R1PKPLP7CDPMP7O15>JP0AL8H=#?1FLFP2PG1:?1RL,001B0=,2L'9#?f;f:RLf9RFf7ROCDPMPOO15>J]1XA21:?KRK,0G1BG=,2K'9#?PLPFf8P11ZD>R112BD10B>12BE[[RL10BDRKg00aLRJAYD>3UW1R>10BE\J^1KRKg00ahRJ#ORO%XJRJP21K27P3%W2CV%U2RP%T2RQPQP4P5P5P61I2:R:1;2=RR5A2RS1I29RT'@,4QAR2SR,<T,4Q5QQEr%p5RSPQP4P5P5P6%59#1#8#6RU,;29A2:,<T,4Q1@:T,4QFoCC1lQ6R:P0P7g00bTRVg00c4RW'k1i07=>VWdAh2B3CgRWb3b6b7X02X92173=RV/001BV=,20'9g00cT[177U,231073'f[^02^92P0PA1:?FP8O3b2b4b5DeW11:?HP1PLP>PKPOPJ1K23RHPPPQ%89#5#5#5#1#8#5#8#5#5#1#8#6R9,;2AA2TRRR'@,4QPS1;2B/@R,4QCCP:PWb3b6b7X02170=,0910BV[^02P0PAp,4HsprO2b2b4b5P1PLP>PKp-0RKPOPJPHPPPQPQP4P5P5P6P8Ea1;2D=b2?RD,<T,4Q5QQPS1<RD,4QCCP:PWb3b6b7X02W8120E,9312VE[^02^8KP0PCPAPFO3b2b4b55cGP3FdW=W1P3P0O2n2001000000121000000X<IX:@PM%6;,7A,=?R;g008c#3#3#3#3#3#3#3#3RI/E8R85GMR0%6<,7A,=?R<1EI7R73GRG17AU,=?R?1EI3RI5GGPMP0PGAH8M;AH70<DNAHIG?DNPNeC_b;X@@X?@W>o"). Qed.

  (* [comment removed for export] *)
  Lemma rd_ra : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 8)) 8 = Some (W8 ra).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Strnlen ()) ["FPX_1"; "SNL"] "h04__x1h14__p1h27__arithh34__ffh46__sat2h56__sat3h68__varmaph75__with81nh91zh:1xh;2Hah<1Hh=1mh>1oh?2rah@2s0hA2s1hB1yp;1p;2p;3p;4p;6p;7p;5p;9p;8p;<p;Bp-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210g003<R0p4p710R1p8p1003Zp4p710P1p8p10045p4p710p1004Tp4p710p8g0050j15Tg005Uj1VTg0063j1STg00<^j1{Tg009Bj2FTg00:Qj1=Tg00=Uj2iTg00;Lj2:Tg00>2j2TTg00HZj1RTg00>Mj1_Tg00:oj23Tg00>oj2QTg006Vj17Tg00?Uj2ETg00@]j3KTg00e4j4GTg00eej2YTg00AXj3LTg00Fnj2mTg00GVj3kTg00H:j1jTg00I:j2hTg00JTj1gTg00K2j1fTg00R9j6eTg00K]j2dTg00R]j3cTg00ZTj7aTg00MGj1`Tg00L@j3HTg00Mij3JTg00NLj2zTg00B2j2^Tg00Nnj2yTg00OZj3xTg00P9j4wTg009lj1>Tg00QVj2]Tg00;hR1j20Tg00S@j3OTg0186j5qTg00BLR2j1\Tg00D>R3j21Tg00<Dj22Tg00D[j1pTg00E9j4oTg019:j6XTg00Pkj4CTg00T;j2WTg00T[j1[TP0j6?Tg019bl9ZTg00VYj3lTg00YEj4PTg00Z0j7NTg00[\j8rTg00WUl<sTg00X:lBtTg00X`l<uTg00Lcj7vTf0R0#5#5p=Bg00\@R4/00p=;f2R5f1R6'1/00p=8g00\^R7/]0p=AP7P6g00_:P0CPp=IP6g00][R8g00^:R9P9g00^ZR:P0g00_aR;FNp=bP7P6g00`AR<P0CPp=@f4R=P8P9P9P:f3R>P5P6P8P9P9P:P0P;FNGrp=4P5P8P9P9P:P7P6P<P0CPP;FNp=DP7P=P>P5P6P0E?p=61^70p=9g00]<R;P7P7P7P2P2f5R2P=P>P5P6P0M<sp=nP7P7P7P7P7P7P3P0P6P5P3P>P=P2f6R3f7R<f8f9MBtp=MP7P7P1P<P1P3P2P=P>P5P6P0M<up=<P5P8P9P9P:P6P0Fvp=Ug008>R2#5R3#BR1#5R<#5R?#5R@#VRA#SRBp,2spRC#{1FACRC#;RD%=3R3%=@R@'iRE,:C'T%V1#SRF#RRG#_RHg010IRIp,3memRJ%=1R1,3CRK,QARLg008c#7#7#7#7#7#7#7#7RM/E>RN3KRO%=<R<,3CRP,QARQ1EM5RR3KRSPLPMCGRT1EM=,YG9LH0X>HR=PHPIPOPLPMCGP=PIPJPLP>PKA801EX971m3@RJ1:43%;@1:4E[[R=%;3RUg00aLRVAk3@6UW;R@%;E\V^;URUp-0RVg00ahRW#jRX%RWRW1h76RY%g7RZ%f7R[P[P8P9P9P:P[P8P9P9P:P>Ee1d72R8%A3=c7AR3'I,b[FaR\%`9R9P[%A1R]9H78R^=J7]R_/@3D41z[:R:P0P5g00bTR`g00c4Ra'^1y05=L`adAx746CwRab3b6b7X07W11:0E,T6R`1361Rb?81E[^07^1VP0PDPCP>O3RDb2b4b5Rc1FALRdPJP=P@PUPXPWPYPZP[%B2#>#>#>#5#B#>#B#>#>#5#B#=Re#A%=?R?#A9H785D[RfP9P[1]74R4/@^D4P:Pab3b6b7X07130?,0eRe%;b[^07P0PCp,4HsprO2R?b2b4b5PJP=P@PUPXPWPYPZP[P\P9P[1I^3D4P:Pab3b6b7X07X1V1:bE\`^07^1VPDb2b4b55OKRbD6DqPTPIPRPOPQPLPMP;PM%\MRO,1dRT1FAQRQ'0%\0Rg,1QRh/0d'2X8;PK110ORi/0QA8QO0'2X97PP11KORj/0010iK'2X97Rk10jPRl11PORm/0KRn'211K1Ro/0PRp11P1Rq/0KRr'2PlPnPpPrP0X:7Rr1060#pXB7X:7RpPjPoPrPrPrP7P7g00`h1160Co#9X=7X87RnPKPK%9KRlPOP1PrPr%9gX:;PMP1%91EnRsM:MRtPPPP%9PRuG<PrPpPmPqPrPrPrPnPPPPPuPOP1PsM:MRuPKPKPlG<EXPJP=P@PUPXPWPYPZ%A<9H78Rv9D[_AJ7v]Rw=D[^5U[P:Pab3b6b7X071301Rx/11Ry130<Rz'0A8z1x'2^07P0PCO1Rzb2b4b5CCPQPJP=P@PUPXPWPYPZP[PfP9P[1@4vD4P:Pab3b6b7X07136<R<#;\e^07P?b2b4b5PJP=P@PUPXPWPYPZP[P\P9P[1Iv3D4P:Pab3b6b7X07X1V1:<E\`^07^1VPDb2b4b55OPRvD6PdPbD61WFRRR%[5R{E?PK10iEX97R|10jE10oEPrPpPjPoPtPEPE%9ER}G<PcCCPdPbD6RcP;PM10hEX8;PPP|10mE10qEPrPpPmPqPuPEPEP}G<PJP=P@PUPXPWPYPZP[P\P9P[1@w3D4P:Pab3b6b7X07X1VA8<1E\`^07^1VPDb2b4b5CCPQPvD6PRP{E?M9ZE?PI%>2#5#B#=R2,3CRC,QAR{1EM6RR5KSPLPMCGPIPRPSP{PLPMP;PM1FA{R{,0T11{gRg/0d'2X8;PK10i{A8{O0'2X97PCPk10jCRk11CORi/0KRT'210oCRA11C1RS/0KRv'2PkPTPAPvPrPpPjPoPtPCPC%9CRtG<PrPpPiPSPrPrPrPnPCPCPtPOP1PsM:MRsPKPKPlG<EXPJP=P@PUPXPWPYPZ%A29H78R89D[_AJ78]R]=D[^5U[P:Pab3b6b7X071302R0,0yA801x'2^07Pzb2b4b5CCP{PJP=P@PUPXPWPYPZP[PfP9P[1@48D4P:Pab3b6b7X071362R2#;\e^07P?b2b4b5PJP=P@PUPXPWPYPZP[P\P9P[1I83D4P:Pab3b6b7X07X1V1:2E\`^07^1VPDb2b4b55OCR8D6PdPbD61WFRRR%[6RFE?PcP;PM10gEX8;PCP|10iE10SEPrPpPiPSPsPEPEP}G<PJP=P@PUPXPWPYPZP[P\P9P[1@]3D4P:Pab3b6b7X07X1VA821E\`^07^1VPDb2b4b5CCP{P8D6PRPFE?M9ZE?PIAl>56PLPMCG1YGN5LHeb<XABX@BW?o"). Qed.
  Lemma rd_s0 : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 16)) 8 = Some (W8 s0).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Strnlen ()) ["FPX_1"; "SNL"] "h04__x1h14__p1h27__arithh34__ffh46__sat2h56__sat3h68__varmaph75__with81zh91nh:1xh;2Hah<1Hh=1mh>1oh?2rah@2s0hA2s1hB1yp;1p;2p;3p;4p;6p;7p;5p;9p;8p;<p;Bp-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210g003<R0p4p710R1p8p1003Zp4p710P1p8p10045p4p710p1004Tp4p710p8g0050j13Tg005Uj1UTg0063j1NTg00<^j1wTg009Bj2BTg00:Qj17Tg00=Uj2aTg00;Lj2;Tg00>2j2MTg00HZj1LTg00>Mj1WTg00:oj24Tg00>oj2JTg006Vj15Tg00?Uj2HTg00@]j3CTg00e4j4ETg00eej2PTg00AXj3DTg00D>R1j21Tg00;hR2j20Tg00Fnj2cTg00GVj3bTg00H:j1`Tg00I:j2_Tg00JTj1^Tg00K2j1]Tg00R9j6\Tg00K]j2[Tg00R]j3ZTg00ZTj7YTg00MGj1XTg00L@j3GTg00Mij3KTg00NLj2vTg00B2j2VTg00Nnj2uTg00OZj3tTg00P9j4sTg009lj18Tg00QVj2TTg00S@j3OTP0j66Tg0186j5pTg00BLR0j1STg00<Dj2?Tg00D[j1oTg00E9j4nTg019:j6jTg00Lcj7iTg00Pkj4FTg00T;j2hTg00T[j1kTg019bl9gTg00VYj3mTg00YEj4RTg00Z0j7fTg00[\j8eTg00WUl<dTg00X:lBqTg00X`l<rTf0R3#3#3p=>g00\@R4/03p==g00\^R5/T3p=:P5f1R6g00_:P3CRp=IP6g00][R7g00^:R8P8g00^ZR9P3g00_aFfp=2P5P6g00`AP3CRp=9f3R:P7P8P8P9f2R;P6P3Gep=@1V53p=<g00]<R<P5P5P5P0P0f5R0f4R=P:P;P6P3M<dp=lP5P5P5P5P5P5P1P3P6P;P1P:P=P0f6R1f7R>f8f9MBqp=QP5P5P2P>P2P1P0P=P:P;P6P3M<rp=Ag008>R=#3R0#>R1#3R2#3R>#3R?#UR@#NRAp,2spRB#w1B@BRB#=RC%70R0%7?R?'aRD,;B'M%U1#NRE#LRF#WRGg010IRHp,3mem%71R1,4B,J@g008c#5#5#5#5#5#5#5#5RI/H:RJ3CRK%72R2,4BRL,J@RM1HI;RN3CROPMPICE1PFJ9DG3X>GPHPKPMP;P5PL1131/0DX851c0?RK1;40%=?1;4D[[RJ%=0RPg00aLRQAb0?6UW;R?%=D\Q^;PRPp-0RQg00ahRR#`RS%LRRR1_56RT%^5RU%]5RVPVP7P8P8P9PVP7P8P8P9P:E\1[5=RW%:0=Z5@R0'I,2VFYRX%X8RY%:29G5WRZ%:1R[5K5R\/90,2VC@1vV9R]P3P;g00bTR^g00c4R_'V1u3;=D^_dAt546CsR_b3b6b7X05W11;3D,M6R^1462R`/11/0D[^05^1QP3PCPBP:O3RCb2b4b5Ra1B@MRbPKPJP?PPPSPRPTPUPV%>=#8#8#8#3#>#8#>#8#8#3#>#7Rc#:%7>R>#:9G5W'9,2VRdPY1T54R4/9Z,2VC@P]P_b3b6b7X05143>,0cRc%=`[^05P3PBp,4HsprO2R>b2b4b5PKPJP?PPPSPRPTPUPVPXPY1IZ0,2VC@P]P_b3b6b7X05X1Q1;`D\^^05^1QPCb2b4b55OLR`E6DpPH%8=#3#>#7R=,4BRe,J@Rf1HI6Rg5COPMPICEPHPgPOPfPMPIP<PI%SIRO,1b1B@fRf'0%S3R@,1fRh/0b'?X9<P5PL113ORi/0f11fO/03'?X85P5Pe11LORj/0310iL'?X8510jeRk11eORl/0LRm'?11L1Rn/0eRo11e1Rp/0LRq'?PkPmPoPqP3X:5Rq1063#oXB5X:5RoPjPnPqPqPqP5P5g00`h1163Cn#<X=5X95RmPLPL%<LRkPOP1PqPq%<@X:<PIP1%<1ElR@M:QRrPePe%<eRsGAPqPoPlPpPqPqPqPmPePePsPOP1P@M:QR@PLPLPkGAEjPKPJP?PPPSPRPTPUPVP7P8P8P9%:=9G5WRW,9\,2VAK5W[R[/9Z,2VFiP]P_b3b6b7X051432R2/11143=RZ'011Z1/02'?^05P3PBO1b2b4b5CFPfPKPJP?PPPSPRPTPUPVPdPY194W,2VC@P]P_b3b6b7X05146=R=#=\c^05P>b2b4b5PKPJP?PPPSPRPTPUPVPXPY1IW0,2VC@P]P_b3b6b7X05X1Q1;=D\^^05^1QPCb2b4b55OeRWE6PbP`E61hEgRg%k6REE6P5PL10iDX85Ri10jD10nDPqPoPjPnPrPDPD%<DRrGAPaCFPbP`E6P<PI10hDX9<P5PePi10lD10pDPqPoPlPpP@PDPDPrGAPKPJP?PPPSPRPTPUPVPXPY19[0,2VC@P]P_b3b6b7X05X1Q11=1/0D\^^05^1QPCb2b4b5CFPfPWE6PgPEE6M9gE6PHAm:;6PMPICE1PFN5DGeb<XAAX@AW?o"). Qed.
  Lemma rd_s1 : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 24)) 8 = Some (W8 s1).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Strnlen ()) ["FPX_1"; "SNL"] "h04__x1h14__p1h27__arithh34__ffh46__sat2h56__sat3h68__varmaph75__with82Hah91Hh:2rah;2s0h<2s1h=1zp;1p;2p;3p;6p;4p;7p;5p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210g003<R0p4p710R1p8p1003Zp4p710P1p8p10045p4p710p1004Tp4p710p8g0050j10Tg005Uj1BTg0063j1@Tg00<^j1cTg009Bj2ETg00;hj21Tg00:Qj13Tg00=Uj2OTg00;Lj27Tg00>2j2?Tg00:oj29Tg00>oj2<Tg006Vj12Tg00?Uj2=Tg00@]j3FTg009lj14Tg00D>j2DTg00Fnj2WTg00GVj3VTg00H:j1UTg00HZj1CTg00I:j2RTg00JTj1QTg00K2j1PTg00R9j6NTg00K]j2MTg00QVj25Tg00R]j3LTg00YEj4:Tg00ZTj7KTg00MGj1JTg00L@j3ATg00Mij3ITg00NLj2HTg00B2j2STg00Nnj2TTg00AXj3GTg00OZj3bTg00P9j4aTg00S@j3`TP0j6_Tg0186j5]Tg00>Mj1ZTg00VYj3[Tg00e4j4\Tg00eej2YTg00Z0j7XTg00[\j8^Tf0R0#0#0p=6f1R1g00][R2g00^:R3P3g00^ZR4P0g00_aFXp=8g00\^R5P1g00`AP0C:p=;f3R6P2P3P3P4f2R7P1P0G^p=>g008>R8#0R9#6R:#0R;#0R<#0R=#BR>#@R?p,2spR@#cg00\@RA1E>@R@'1RB%39R9%3=R='ORC,7@'?g010IRDp,3mem%3:RE,9@,<>g008c#2#2#2#2#2#2#2#2RF/=63F%3;,9@,<>1=F73F%48#0#6#3R;,9@RG,<>RHP1P5PG1D0E/1CX=51W9=RI17A911A=17AC[[RJ11A9RKg00aLRLAV9=1UW8R=11AC\L^8KRKp-0RLg00ahRM#URN%CMRM1R51RO%Q5RP%P5RQPQP2P3P3P4PQP2P3P3P4P6ENP51M58R2g00_:RR1559=L5>R9C:,8QFKRS%J3R3155;9A52RT155E5I5/;9,8QC>1HQ4R4P0P7g00bTRUg00c4RV'S1T07=GUVdAb5A1CaRVb3b6b7X05W1170C,?1RU191;R;/DE/1C[^05^1LP0PBP@P6O3RBb2b4b51E>HPIPJP=PKPNPMPOPPPQ%68#4#4#4#0#6#4#6#4#4#0#6#3R8,55%3<R<,559A52';,8QP3155A/;T,8QC>P4PVb3b6b7X05190<,1811A;[^05P0P@p,4HsprO2b2b4b5PIPJP=PKPNPMPOPPPQPSP3P5PTPRP9C:,8QC>P4PVb3b6b7X05X1L17;C\U^05^1LPBb2b4b55`GE_D]%B:#@#CR:#ZPDA[671PHPFC\1=F1,Y:3Geb9X<?X;?W:o"). Qed.

  (* [comment removed for export] *)
  Ltac okstk :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub RSEGS mem (Z_to_bv 64 (usp - 32)) _ 32 8);
      [u_norm; lia | exact Hstk | u_norm; lia | u_norm; cbn; lia].

  Ltac kept_cs := cbv [callee_saved In]; tauto.

  (* [comment removed for export] *)
  Ltac msd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia
        | gres; rwH; reflexivity
        | okstk ]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mld8 F D vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of RD with rdn _ _ ?c _ = _ =>
              replace a with c by (unfold v_addi; unorm; f_equal; lia) end end;
          exact RD
        | apply bytes_le_to_Z_8 ]
      | step_simpl]; vnorm.

  Lemma strnlen_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
    getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0xba46c : word) mem rom)
                   (mkst regs' ret (mem1 ret (getr regs 8) (getr regs 9)) rom)
      /\ keeps_cs regs regs' /\ getr regs' 10 = Z_to_bv 64 K.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Strnlen ()) ["FPX_1"; "SNL"] "p'0h01Hh11bi001bh21xi011xh34__x1h42gHh51Eh67__arithh77__sat65h87__sat66h97__sat67h:4cstrh;2Hxh<3Hx'h=2N1h>2N2h?2N8h@2N9hA4__ffhB8__varmaphC5__withD1zi021zhE2r2hF4__p1hG1ehH4__x2hI2r1hJ1rhK2H5hL1nhM5regs'hN3A10hO2H0hP2H3hQ2H4hR2H6hS2HahT2KChU4__x3hV4__x4hW2b1hX2b2hY1mhZ2H1h[3H10h\3H11h]2H2h^3HK0i033HK0h_3HKLh`3HKni043HKnha4Hbufi054Hbufhb4Hn64i064Hn64hc3Hnwi073Hnwhd4Hrethe3Hroi083Hrohf2Hshg3Hsphh4Hwini094Hwinhi2R1hj3R10hk3R11hl3R12hm2R2hn2R8ho2R9hp2RKhq3RUNhr2S2hs2S9ht2_Hhu3_H0hv1jhw5lemmahx4regshy3rethz2s0h{2s1h|1yi0:3Hnzi0;5Hzeroi0<8bv_is_wfi0=;bv_unsignedi0>1pp%0p%1p%2p%3p%4p&0p&1p;1p;2p;3p;6p;5p;4p;@p;:p;Bp;7p;=p;<p;?p;>p;Ap;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0g01:eR0p4p710p9g002PR1p4p7210g003<R2p4p710R3p8p1003Zp4p710P3p8p10045p4p710g004TR3p4p710p8g0050j1:Tg009lj1@Tg005Uk109Tg0063S00j1|TP1k21uTg01;`k11jTg00:Qj1jTg01<Yj22Tg00AXj30k11VTg00>oj2Rk11>Tg00<^k110Tg009Bj2hTg00=Uk21iTg00;Lj2`Tg00>2S01j2BTg01=Kk61[Tg00T;k21XTg00BLR1k10TTg00d1R4k51HTg01>IS02j2_Tg00HZk10iTg00>Mk10YTg00eek20CTg00D>R5j2ETg00fGk212Tg00fdk211Tg00gAk11tTg00gak40~Tg00h=k21mTg00Cej16Tg00hUk11lTg01>cj55Tg00VYj3CTg00:oj2bTg01?Uj2eTg01@Wj38Tg01AKj2=Tg00MGk10lTg00B2j2\Tg01B?k11JTg01B]m@0kTg01C^k31FTg01DBj2^Tg006Vj1~Tg012^k21?Tg00H:k10jTg01Dej4ATg01Egk208Tg00i]k11=Tg00jBk21<Tg00Fnk21;Tg00GVk31:Tg00I:k20RTg00JTk119Tg00K2k118Tg00K]k20QTg00L@k30ETg00NLk217Tg00Nnk216Tg00OZk315Tg00P9k414Tg00QVk20hTg00;hR6j2HTg00R]k313Tg00S@j3cTP2j6;Tg00D[k11rTg00E9k41qTg00Pkk40@Tg01FOm:0dTg01GPmB0cTg00?Uj2MTg00@]j3lTg015Vk30bTg01HOk70aTg01IQk30PTg01J4k30?Tg01Jak10<Tg01Kam=0OTg013>k403Tg01LXk21kTg01MJm<1hTg01NLk20yTP3j6Kl:Yj7]Tg01OHk10MTg00<DS03j2<Tg01P>k20LTg017[k40UTg01P]k40ZTg01Q7k31bTg01R3k21aTg01S1m?1`Tg01T8k30qTg01TRk30;Tg01Tlk60pTg01UHk50STg01Uek20oTg00IXk11YTg00J6k40`Tg00[8k61WTg00k3k20_Tg00o`k30nTg00k\k21TTg00lHk30ITg01VWk31STg01WMk11RTg01XKm>1QTg01YDk20^Tg01Z7m@1PTg01[7k31OTg01\4k10mTg01]8mA0\Tg01]mk31NTg01^jk31UTg01_gk11MTg01`Xk31LTg01aJk11KTg01b9k61\TP0k71]Tg01bdk21^Tg01cVk20tTg01dQm>1ITg01eRk40sTg01enk80uTg01g2k30=Tg00e4k41GTg01gnk31eTg00Mik31fTg00YEk40NTg00Z0k70XTg01hEk81ETg00[\k80{Tg00R9k61DTg00ZTk71CTg00WUm<1nTg00X:mB1oTg00X`m<1BTg01hbk71pTf1R0f0R3g01i^S0440Pp=Ff3R2f2R7/20;03p=>%j3Q0460P0p=Sg00\@R8/H3p=a1E70/H3p=u%@3#@p>00%@3#:p>0H%:3#@#:#:p>06%:3#@p=n%@3#@#:#:p>0Ff6R9f5R:f4R;AC270P3D5p=}1e70/B3p=dg010IR<P9P:P;P2P7D5<0=0/B3p=NP<P2P7P0H1G=0;3p=qg00\^R=?038p>0e%:3#:#@#@p=x%@3#:#:#jp=y%:3#@#@#@#:#@#:#:#@#:#:#@p>02%:3#:#@#:p>0x%:3#:#:#jp=zg01j::1e03p=PA0703#6p=Z1227120350;p=31227=0;0/B3p=?A09:;A0270/B3'Bp>0:A89:;?827?803p=XA8;27?803p=1B0=<03p>0]%:3#:p>0JP9P:P;P21270P3E;p=D1h271h0350=p=Q%:3#@#@#@#:#@#:#:#@#:p>011\=3p=GB0P270=0;3p=[P9A8:;2P7P0P3D5p=tP:P;P2P7P0D5>0=<3p=J%~3#~p>1A%~3#~#~#~p>051M039l27p>0G%:3#jp>1@P;P2P7P0H03>0I:3p=720h=3p>04B1f=03p=mP7g00][S05g00^:S06Q06g00^ZS07P=P0g01k@P3H0Ng00_aR>K0Xp=sA0=03p=oP=P9P:P;P2P7P0P3L1Ep={P7Q05Q06Q06Q07P=P0g00`AR?P3H0NP>K0Xp=wP=P0P?P3H0Np>07P;Q05Q06Q06Q07P2P7P0Q05Q06Q06Q07P3P>K0XL0{p=kP0Q05Q06Q06Q07P3J1Dp>0gP7Q05Q06Q06Q07P=P0g00_:R?P3H0NP>K0Xp>0BP7Q05Q06Q06Q07P0P3K1Cp>0fP=P0P?P3H0Np>0AP=P;P2P7P0P3E;p=IP9P:P;1\27P0P3E;p>1sg00]<R?P=P=P=P1P1P:P;P2P7P0P3N<1np>0}P=P=P=P=P=P=P5P3P0P7P5P2P;P:P9f7R5f8R1f9R>NB1op>0WP=P=P6P5P6P9P:P;P2P7P0P3N<1Bp>0VP5P9P:1\;21270P3E;p=OAl;27?l03p>0|1203,M7p=T1M:;9l59?l27?l03p=r1=039827p=pg00bTS08/\3p>0>P5A89:;P2P7P0D5>0=<3p=vB0I:;2P7P0P3CAp=L1227,M;9l9:?l03p>1g1h0390=7p>0zP<P:P;P2P7P0P3K1pp=VB0I703:0I;2p>0w12039027p=UA0:;2A0703g00cTR6'<'<p=gA09:;A0270/<3'<p=4A0703/<6p=WA0;271<03'<p=iA89:;?827/20=053p=f1<36p>0vA0270/<3p>1dP9P:P;P2P7P0P3H0UH0Up>0D1B03,B7p>1cP:P;P2P7P0D5:0=<9/B3p>1_P;P2P7P0P3D5:0=<:p>1Z1<36,<0p>0r1<03,<7,<2,<;p>0KP2Q05Q06Q06Q07P7P0P3L0{p>0[P;P2P7Q04P0P3EKp=9g008>R@#:S09#@RA$09RBQ09#:S0:#:RC#:S0;#:RD#:RE$09RF#|RG+1uRH&1j3PGP7%j@S0<,FBRIP0C>PGP2Q09#jRJ,FBRKp,2spRLC>%:AS0=,SBRM,2;S0>p,1sRN50GS0?%@AS0@,SBRA,2:S0Ap,1nS0B,RFRO50G&10L1hFLS0C#aS0DQ0C%jERE-1iJRP'`S0E'B&10N1hFNS0F#aS0GQ0F/`PS0H'Bp,3memRQPNp,3bufS0Ip,1KS0JQ0Bp,3HOKRRJ1[Q0JQ0<&09CRS#|S0KQ0I+1XRT$0TS0L3uPRPQPNQ0IQ0JQ0BI1HP4PQPNQ0IQ0JQ0Bp,2fxR4f<RR%:@$00$0H$0H$06#n$0H$0F,SFRUPQp,3romRVP4P3f;RWPW%jCRC,FBRX,2RQ0:#@S0M,SBRY,2RS0NPVF}123MS0OQ0J,RFRZ50GS0P9dR3FNXMH,_HP3Q0K$0iS0Q$0YS0RPQPNPTQ0QQ0I+0CDqQ0FQ0J'ES0S012CR[011CQ0FQ0L'ES0T7uCQ0T/`PQ0J#aQ0KQ0J$1tR\Q0I1RS8R]H0~,hS$0e21m3\Q0KP0Q0IP]H0~,hS$0e#6[^v?Q0JQ0B7uCQ0B/`P&1lQfLS0U/2XPGfMS0V/2YPGP<P4fNRSPUPQPVD5R]P4P3%n@$0F$0F#x$00#yS0W,FFR\ACS70R^PVD5R_XJHPGP3PI&02@$0x#zS0X,FFS0YPGP3PKQ0C%jDS0Z'bR`,RFRaPGP3PXPOPGP3PYPNPGQ0OPNPG123A1RF8RbPGP3%@@S0[#:S0\#:S0],SBRcPO%|BRd1Pd3ReAZd0IRfAZd7KRgAZd2XRhAZd;YRiPGP9P:fUS0^P:D3[[[[[]2D?K0:D?D?D?D?S0_XJHP4P3PSP^PVD5XEHfORj/e3S0`Q0P'BXEHPHP4PjPUPQPVP_Q0_FNXIHA8SKaR_PXPOPYPNPAPbFXPcPOPIQ0X,RFRkD1RlP4PlP\Q0VP0P3PVF}Rm-0]]12lIS0aQ0Y50GS0bPGPlPKPaC>S0cPGPlPXPOC>S0dPGPlPYPNC>S0e12lMS0f=0GNS0gPGPlPAPbC>S0hPGPlPcPOC>S0iPGfTS0j?8KaS0kPXPOPYPNPAPbFXPcPOPIPkD1S0lP:Q0jP:D3\i\h\g\f\e^2dS0m'BS0n'BS0o'BS0p'BS0q'BS0r'BS0s'BS0tP]P4P_Q0:#jR_,=US0uPQPVD5Pm&0YG&0lG'\S0vP4P<PSPUPQPVg01kgPKPKQ0]$09S0wQ0[#@$00$00S0x#:$0J$0J'SPag01m1Q08g01n;S0y'\RUg01n[PUPGPL&1JDRD,=3=0GaX1G1\GaS0z1=LD=0GaePSPKfJS0{FDN@0kg01oeRD%|3Rm%|0R]Q01%|7?003P2P7P2P0CQRl[P7P0P7P3CQ%|2?070[Rn%|;?027\lB1F703P3n2001000000120000000WXWWWLS0|Pn^X]^Wm^LDS0}P3PF&01@#x$0H#zRD,FFRmQ0u%GDPFPmPFQ0uCQdO4b0PGPFPDQ041^FDdQ0uD[PGPmP4fPRD?8KaR]P3PQPVP4P]PXPOPYPND1PAPbPcPOD1PIPkP\ACj27PVFtS0~EJX1GP4A8jKaRnPmPQPVD5P4Pn1=m_S10PQQ0C/bCS11,RFRlg008cS12$1AS13#~S14#~$05RoPSH0GPVD5P4PnPXPOPYPNPAPbFXPcPOPIPkD1RpP\P^PVD5Q0vP4P<PnPmPQPVg020CPKPIQ0wQ0]$1@S15'FS16PlPSg021MPUg022W21?dGRmPdPGPKPa&0jmS17E7R^PjPKPUCAPGPnPKPaC>RqePqPGPaQ0wQ16+08,=3S18=0GlX1GP`Q15,E3,RFS19=0GlXD=PG&1>FS1:Q1:Q15,E`S1;Q11PG\=Q1:'\S1<&1=TRTQ0L#aRqQ0S01<CRrQ0S#a%aC%a[[[R[21;JERs1`8J%aE1`8PS1=[[Rt%aJRug00aLS1>B1:JE0UWSREQ1>%aP[^SuRug00ahS1?$0jS1@Q1?$0iS1A20R=0S1B&19=S1C&18=Rv20Q=@S1DQ0Z$04Rw60E=RxQ15$04S1E'mS1FQ1D&04CRy60E=S1G3sQ07-17vS1HP3P7Q08g00c4Rz'\Q0821637;0zdB15=80H14S1IbAbBbCX3=Q0Z,b3RzQ15'ES1J1b3CS1K'o^3=P3Q0CO1S1Lb6b7b8b9b:F{1hFaS1MPTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CPv%:@#n$0F#n#x#zR{$04=wvxS1NQ06$0lS1OPv20h=8S1P007xDkQ1HQ1IbAbBbCX3=1H{zS1QQ0Z,b0R{#a[^3=P3Q0Cp,4HsprO2S1Rb6b7b8b9b:S1SPTPqPrP[PsPtPEPup-0R|Q1@Q1AQ1BQ1CPv20gv2Q1D&04J>13=FS1T60Bv60fvS1UQ1OPvQ1T-0AxDkQ1HQ1IbAbBbCX3=WFS1V1`3P,B0RJ1`{P[^3=^F|S1WP3Q0DQ0CPSO3S1Xb6b7b8b9b:5c`S1YDIQ15,=aS1Z=0Gle12]KS1[P3E;b4P^PjPIPUCAPGPnPIPjPID3RnePnPG12DIRnA0G3DX1GR}PGPjP}PGPjPnQ0VK1sP]PIP3FDb4P<PQPaPl&05o$05$05$05$05$05S1\PoP`Q1\$0TRn,E3S1]/HPXD=S1^1E`nR}/HPS1_Q0Z,E`S1`/HPS1aP3X2=R~1H03$1rX|=X2=S1bP}Q1`P~P~P~P=P=g00`h1E03H1q#GXY=XL=S1cP`P`%G`PnQ0ZP~P~&0T3#GX2?S1dQ1\Q0ZQ0Z#GJ0}N:0WS1ePPPP%GPL0VS1fPTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CPvQ1UQ1OPv1mxwS1gQ1T+07DkQ1HQ1IbAbBbCX3=XF|S1hQ0Z=u{P\J^3=^F|S1iP3Q0DQ0CQ0VO3R{b6b7b8b9b:H0@Q1MQ1SPTPqPrP[PsPtPEPuQ1VQ1WP{b6b7b8b9b:5c`S1jDIp,4HstkS1kP`1hFlRw,H3XD=Q111H`3XD=S1lPTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CQ1G9wvxQ1HQ1IbAbBbCX3=Q1K,Hz^3=Q1Lb6b7b8b9b:PwQ11PTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CPvQ1NQ1OPvQ1PQ1G+07DkQ1HQ1IbAbBbCX3=Q1Q1b0CR?#a[^3=Q1Rb6b7b8b9b:PTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CPvQ1UQ1OPvQ1GQ1T+0ADkQ1HQ1IbAbBbCX3=XF|1`?P\J^3=^F|P{b6b7b8b9b:3cS1mDIQ1MQ1jDIQ11&0ToR{Q1M/En5u3XD=S1nP`Q11/E{RnQ1]'HXD=1Hn}S1oQ11/ECR?Q1`'HP~Q1bPnP?P~P~P~Q1cQ11Q11Q11#GP{PCP~P~Q1dPoPC%GCJ0}S1dN:0WP}Q1`Q1eL0VPTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CQ1G/myQ1g5wvQ1HQ1IbAbBbCX3=Q1KQ0Z,EzS1p7uC^3=Q1Lb6b7b8b9b:H0@Q1oeQ1MQ1jDIPwQ1mDIN:0dNB0cQ0|Q0}P3PF&01@#x$0H#yRw,FFR?Q10%GwPFP?PFQ10CQdO4b0PGPFPwQ041^FwdQ10D[PGP?P4fQS1m?8KaRwP31MoDS1j9lQlS1oPVP4PwPXPOPYPND1PAPbPcPOD1PIPkP\ACD;2S1qPVFtS1rEJX1GP4P]P?1MojS1s9lQlS1tPVD5P4P]1=?_S1uQ1tQ0CQ0;#jS0;'bS1v,RFRnPo12DXS1wH0GPVD5Q0~Q0vP4P<P]P?Q1tPVg023aPKPXQ0wQ0;'FS0~PnQ1wg024kPUg0265P^PDPKPUCAQ1[=0GaR?eP?PGPaQ0wQ0~+08,=3S1[=0GnX1GP`Q0;,E3,RFS1x=0GnXD=PGQ1:Q1:Q0;,E`S1yQ1vQ1<PTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CQ0;$04R?,mxS1zQ1D>0E=?S1{5svQ1HQ1IbAbBbCX3=Q0;,EzS1|Q0;,b3S1}'o^3=Q1Lb6b7b8b9b:F{Q1MQ1SPTPqPrP[PsPtPEPuQ1VQ1WP3Q0DQ0CPjO3S1~b6b7b8b9b:5c`S20DIQ0;,=aS21=0Gne12wKS22P3E;b4P^PDPXPUCAPGP]PXQ1wC>R]eP]PGQ1m/2XS1wfRS23/2XS2490G3X1GPGQ1wPwPXP3GOb4P<PoPQQ1tPnQ1s@0bQlP<PQPaPnQ1\PoP`Q1^Q1_Q1aQ1fPTPqPrP[PsPtPEPuQ1hQ1iQ1Xb6b7b8b9b:H0@Q1MQ1YDIQ1kP`1hFnR],H3XD=Q1vQ1lPTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CQ1{9wvxQ1HQ1IbAbBbCX3=Q1},Hz^3=Q1Lb6b7b8b9b:P]Q1vPTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CPvQ1NQ1OPvQ1PQ1{+07DkQ1HQ1IbAbBbCX3=Q1QQ0;,b0R?#a[^3=Q1Rb6b7b8b9b:PTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CPvQ1UQ1OPvQ1{Q1T+0ADkQ1HQ1IbAbBbCX3=XF|1`?P\J^3=^F|Q1Xb6b7b8b9b:3cS1XDIQ1MQ1YDIQ1vQ1nP`Q1v/E{R?Q1]'HXD=1H?}S1sQ1v/ECS1tQ1`'HP~Q1bP?Q1tP~P~P~Q1cQ1vQ1vQ1v#GP{PCQ1dN:0WP}Q1`Q1eL0VPTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CQ1{/myQ1g5wvQ1HQ1IbAbBbCX3=Q1}Q1p7uC^3=Q1Lb6b7b8b9b:H0@Q1seQ1MQ1YDIP]Q1XDIN:0dK0aNB0cQ0|Q0}P3PF&01@#x$00#zR],FFR?Q1u%G]PFP?PFQ1uCQdO4b0PGPFP]Q041^F]dQ1uD[PGP?P4Q23?8KaR]P3PQPlQ1m,MoPnQ24,MoI0|S24PVP4P]PXPOPYPND1PAPbPcPOD1PIPkP\Q1m?C:;S1XPVFtS1YEJX1GP4PwP?Q1oQ1w,MoS1w7lnS1sPVD5P4Pw1=?_S1tQ1sQ0CQ15'bS25,RFS26PoQ1m/2YS27H0GPVD5Q1rQ0vP4P<PwP?Q1sPVg027?PKPYQ0w/FCS1rQ26Q27g028IPUg029SP^Q1mPKPUCAQ22=0GaR?eP?PGPaQ0wQ1r+08,=3S22Q2650GX1GP`1E3C,RFS28Q2650GXD=PGQ1:Q1:1E`CS29Q25Q1<PTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1C1mxyS2:Q1DQ1E60E=S1E5svQ1HQ1IbAbBbCX3=1EzCS2;Q15,b3S2<'o^3=Q1Lb6b7b8b9b:F{Q1MQ1SPTPqPrP[PsPtPEPuQ1VQ1WP3Q0DQ0CPDO3b6b7b8b9b:5c`DI1=aCS2=Q2650GeP]PKP3FDb4P^Q1mPYPUCAPGPwPYQ27C>RwePwPGQ23/2YS27fSS2>/2YRw90G3X1GPGQ27P]PYP3GOb4P<PoQ1oQ1sQ26Q1wQ1o<0bnP<PoPQQ1oQ26Q1j@0bQlP<PQPaQ26Q1\PoP`Q1^Q1_Q1aQ1fPTPqPrP[PsPtPEPuQ1hQ1iQ1~b6b7b8b9b:H0@Q1MQ20DIQ1kP`Q26,hFR?,H3XD=Q25Q1lPTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CQ1E9wvxQ1HQ1IbAbBbCX3=Q2<,Hz^3=Q1Lb6b7b8b9b:P?Q25PTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CPvQ1NQ1OPvQ1PQ1E+07DkQ1HQ1IbAbBbCX3=Q1QQ15,b0Rz#a[^3=Q1Rb6b7b8b9b:PTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CPvQ1UQ1OPvQ1EQ1T+0ADkQ1HQ1IbAbBbCX3=XF|1`zP\J^3=^F|Q1~b6b7b8b9b:3cS1~DIQ1MQ20DIQ25Q1nP`Q25/E{RJQ1]'HXD=1HJ}RzQ25/ECRxQ1`'HP~Q1bPJPxP~P~P~Q1cQ25Q25Q25#GP{PCQ1dN:0WP}Q1`Q1eL0VPTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CQ1E/myQ1g5wvQ1HQ1IbAbBbCX3=Q2<Q1p7uC^3=Q1Lb6b7b8b9b:H0@PzeQ1MQ20DIP?Q1~DIN:0dK0aK0aNB0cQ0|Q0}P3PF&01@#x$00#yR?,FFRzQ1t%G?PFPzPFQ1tCQdO4b0PGPFP?Q041^F?dQ1tD[PGPzP4Q2>?8KaR?P3PQPlPoQ23PnQ2>=ToXQ261MowGrPVP4P?PXPOPYPND1PAPbPcPOD1PIPkP\Q23?C9:PVFtEJX1GP4P]PzQ24Q26PoQ27H0GRwPVD5P4Q08PHQ04:0PB8S27:0?BXS24P]P]PX12]AQ0wQ0wQ0480P8S1~+08S20Cpn01000000200001=z_S1ePwPVD5Q1YQ0vP4P<P]PzPwPVg02:]RwPXPAQ1~g02;g&0<w$0>g02=1N=0OQ0|Q0}P3PF&01@$06$0J#zRw,FFRzQ1e%GwPFPzPFQ1eCQdO4b0PGPFPwQ041^FwdQ1eD[PGPzP4Q0kPXQ0k/2AS1YQ20CpP3PQPlPoQ2>PnQ0j=ToXQ26Q0j/2YS1d,MoGrRwPVP4Q0lP\Q2>P5P9PVF}R]EJX1GP^Q2>PAPUCAPGP?PAQ2>PAD3R?eP?PGQ0j/2AR?P4Q0^?8KaRyPXQ20,=3S0lPzPQPlPoQ0jPnQ0^=ToXQ26Q0^=ToYGrR}PVP4PyPXPOPYPNPAPbFXPcPOPIPkD1S1cP\Q0jP1P5PVF}R{GvX1GPGP?P4PyPXP3PzP}PVP{GvX1GP4Q0k?8X?R{PzPwPVD5P4Q08PHQ27:0?BYS0kP{P{PY12{MQ20Cpn01000000200001=z_S1bPwPVD5P]Q0vP4P<P{PzPwPVg02>;RwPYPMQ1~g02?E&0<w$0>g02@ON=0OQ0|Q0}P3PF&01@$06$0J#yRw,FFRzQ1b%GwPFPzPFQ1bCQdO4b0PGPFPwQ041^FwdQ1bD[PGPzP4fVS1]?8KaRwQ1]/2A78XR{PY12{MS1nQ20CpP3PQPlPoQ0^PnQ1]=ToXQ26Q1]=ToYGrR]PVP4PwPXPOPYPND1PAPbPcPOD1PIPkP\Q0^?C>1S1UPVFtRwEJX1GPmPdPGPXQ0^/2AR}H03P^Q0^PMPUELPGA8yX}PMQ0^PMD3R}eP}PGQ1]/2MR}P4fWS1R?8KaRyQ1R/2A78XR~PYQ0lPzPQPlPoQ1]PnQ1R=ToXQ26Q1R=ToYGrRxPVP4PyPXPOPYPNPAPbFXPcPOPIPkD1S1QP\Q1]f:S1NP>PVF}RyGvX1GPGP}P4P~PYP3PzPxPVPyGvX1GP4A8{Y}R{PzP]PVD5P4Q08PHQ27:0?BAP{P{PAQ27,2{Q20Cpn01000000200011=z_RJP]PVD5PwQ0vP4P<P{PzP]PVg02AYR]PAQ27Q1~g02Bc&0<]$0>g02CmN=0OQ0|Q0}P3PF&01@$06#n#zR],FFRzPJ%G]PFPzPFPJCQdO4b0PGPFP]Q041^F]dPJD[PGPzP4fXS1l?8KaR]PXQ1l/2AR{PYQ1l/2MS1kD1RwPAQ27,2wQ20CpP3PQPlPoQ1RPnQ1l=ToXQ26Q1l=ToYGrS1iPVP4P]PXPOPYPND1PAPbPcPOD1PIPkP\Q1RQ1N7CWPVFtR]EJX1GPGPbP4PwPAP3PzQ1iPVP]GvX1GP4P~PYQ1R/2MPAPbD1R~PzPxPVD5P4Q08PHQ27:0?BcP~P~Pc12~XQ20Cpn01000000200011=z_R]PxPVD5PyQ0vP4P<P~PzPxPVg02E7RxPcPXQ1~g02FA&0<x$0>g02GKN=0OQ0|Q0}P3PF&01@$06#n#yRx,FFRzP]%GxPFPzPFP]CQdO4b0PGPFPxQ041^FxdP]D[PGPzP4fYS1i?8KaRxPXQ1i/2AR~PYQ1i/2MPAPbFXRyPc12yXS1hQ20CpP3PQPlPoQ1lPnQ1i=ToXQ26Q1i=ToYGrS1fPVP4PxPXPOPYPNPAPbFXPcPOPIPkD1S1aP\Q1lPRPWPVF}S1_EJX1GPmPdPGPAPbH03S1^PmPdPGPYQ1kPmPdPGPXP{P^E7E7Q1lPXPUELPGA8wAbPXP{C>R{eP{PGP~P4fZS1k?8KaR{PXQ1k/2APYQ1k/2MPAPbFXS1\PcQ0lPzPQPlPoQ1iPnQ1k=ToXQ26Q1k=ToYGrRwPVP4P{PXPOPYPNPAPbFXPcPOPIPkD1S1jP\Q1if=R{;CRS1oPVD5RxGvX1GPGP~P4Q1\PcP3PzPwPVPxGvX1GP4A8yc~RyPzQ1fPVD5P4Q08PHQ27:0?BIS1\Py1=z_Rx98yIn0100000020001Q0=#@S1w$09RwQ0x$00#x$00$0F$0J,SwS0x+08-1kzRwQ1fPVD5Q1_Q0vP4P<PyPzQ1fPVg02HURzPIQ0xg02I_&0<z$0>g02JiN<1hQ0|Q0}P3PFP\PwQ0W#GPFP\PFPwCQdO4b0PGPFQ0WQ04Q0W,^FdPwD[PGP\P4f[S0W?8KaRzPXQ0W/2AS0xPYQ0W/2MS1fPAPbFXPcQ0xPIPxD1P3PQPlPoQ1kH0GS1_PnPoQ0WPXQ26Q0W=ToYK1gS1sPVP4PzPXPOPYPNPAPbFXPcPOPIPkD1S2?P\Q1kf>S2@P{PVF}RzEJX1GQ0|Q0}P3PFPkPxQ0X#GS0X1hFkS2A@0zFxdO4b0A0GkxPGPkP4f\S2B?8KaRyPXQ2B/2AS2CPYQ2B/2MS2DPAPbFXPcQ2CPIP3D1P\PQPlPoQ0WPnQ2B=ToXQ26Q2B=ToYGrS2CPVP4A8yXOS2EPYPNPAPbD1PcPOPIPkD1S2FP\Q0Wf?S2GQ2@PVF}RQEJX1GPGPOP4PyPXP3PYQ2DPAPbFXPcP3PIPkD1P\Q2CPVPQEJX1GPGPNP4Q2EPYP3PAPbD1PcPOPIPkD1P\Q2CPVPQEJX1GP4Q2?P\Q1_PnQ2@,MoQ261Mo{I0|PVD5RQ-0y<20]QzeP4Q2?P\Q1sPVPzEJeQ1fQ1]E;Q0xQ0^E;PxP3EKb0PwP3EKb0EV1=~8&0M~E;Q1hP3E;b4P]P3EKb0EV1=b8&0MbE;PJP3EKb0EV1=}8&0M}E;Q1nP3E;b4Q1bP3EKb0EV1=?8&0M?E;Q1YP3E;b4Q1eP3EKb0EVQ1tP3EKb0EVQ1uP3EKb0EVQ10P3EKb0EVQ0uP3EKb0EVQ0bQ0sPmPdPGPIPkPmPdPGPcPOPmQ1^PmPdPGPYPNH03PmPdPGPXPOP^E7I0wE7E7S1^PSPIPUCAQ0a=0GkR^eP^PGPkQ0Y90G3X1GQ0|Q0}P3PFPkQ0YQ0XQ2AQ0Y80zFdO4b0PpPIP3FDb4Q0cQ0rQ1^PSPKPUCAQ0ceQ0cPGPaA0G3aX1GS0cQ0zPpPKP3FDb4Q0dQ0qQ1^PSPXPUCAQ0deQ0dPGPOA0G3OX1GR^1\GOR?PpPXP3FDb4Q0eQ0pQ1^PSPYPUCAQ0eeQ0ePGPNA0G3NX1GS0e1\GNR}PpPYP3FDb4Q0gQ0oQ1^PSPMPUCAPGQ0fPSPMCURJePJPG12jMRJQ0ePGPNQ0eP}PJQ0{E;PpPMP3FDb4Q0hQ0nQ1^PSPAPUCAQ0heQ0hPGPbA0G3bX1GPGPbPpPAP3GOb4Q0iQ0mQ1^PSPcPUCAQ0ieQ0iPGPOP^P?PpPcP3FDb4Q03A0dI:A0dK:S0iPdQ0[,SBRpP:Pd1FB_R?P:PdPXP:PdPYP:PdQ0M#:,SBR^P:PdQ0M#@,SBRJP:PdQ0=#:,SBR}P:PdQ1w,SBR]P:PdQ0@#:,SBR~P:PdQ0@#@,SBRwP:PdQ15,FBRxP:PdQ0]#@,SBRzP:PdQ0\#@S0\#:,SBRQP:PdQ0\#@,SBRyP:EgF4F4F4F4F4F4S0]'<PGQ1cP9Q0^P9D3P;A0dI9PdPIAZd3IS1cAZd0KS0@AZd7XS1wAZd2YS0=PGQ2?P;Q0WP;D3]@]?]>]=X2dAZdIIA0dIKS0M#6AZdIXA0dIYS0m#6PGQ1jPIQ1kPID3P21\dIO1+0LW@W?W>W=P5P3P:P;P2P7M:YW0P3O1PdPKP9A0dp9S1jPdP?P9PdPXP9PdPYP9PdP^P9PdPJP9PdP}P9PdP]P9PdP~P9PdPwP9PdPxP9PdPzP9PdPQP9AWdy9F4F4F4F4F4F4S0hDiQ03A0dK5A0dp5S0nPdP?P5PdPXP5PdPYP5PdP^P5PdPJP5PdP}P5PdP]P5PdP~P5PdPwP5PdPxP5PdPzP5PdPQP5AWdy5F4F4F4F4F4F4S0f'<PGQ1QP1Q1RP1D3P3A0dK1PdPKQ1cQ0@Q1wQ0=PGf]S1QPKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S0oP;Q1QP;D3]@]?]>]=X2dAZdKIA0dKKS0g#6AZdKXA0dKYS0p#6PGQ2FPKQ2BPKD3P71\dKS2FO1+0LW@W?W>W=P>P3P5P9P:P;M:YW0P3O1PdPpP1A0d?1S0dPdPXP1PdPYP1PdP^P1PdPJP1PdP}P1PdP]P1PdP~P1PdPwP1PdPxP1PdPzP1PdPQP1PdPyP1EgF4F4F4F4F4S0qDiQ03A0dp>A0d?>S0zPdPXP>PdPYP>PdP^P>PdPJP>PdP}P>PdP]P>PdP~P>PdPwP>PdPxP>PdPzP>PdPQP>PdPyP>EgF4F4F4F4F4S0r'<PGQ1aQ1NQ1iQ1ND3P3Q1N90dpPdPpQ1cQ0@Q1wQ0=PGf_S1aPKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S2AP;Q1aP;D3]@]?]>]=X2dA0dpIS0X#6S0aA0dpKS0s#6S0bA0dpXS0u#6S10A0dpYS1u#6S1tQ1^f^S1ePpPUCAPGQ1ePKPaPXPOD1PYPNPAPbD1PcPOPIPkPpQ1e/2pGfS1YeQ1YPGQ1a/2pS1Yf`S1b/2pS1n90G3X1GPGQ1YQ2APpP3GOb4W@W?W>W=PWP3P>P1P5P9M:YW0P3O1PdP?Q1NQ1N90dXS1YPdPYQ1NPdP^Q1NPdPJQ1NPdP}Q1NPdP]Q1NPdP~Q1NPdPwQ1NPdPxQ1NPdPzQ1NPdPQQ1NQ1N9WdyF4F4F4F4F4S1hDiQ03A0d?WA0dXWS0xPdPYPWPdP^PWPdPJPWPdP}PWPdP]PWPdP~PWPdPwPWPdPxPWPdPzPWPdPQPWAWdyWF4F4F4F4F4S1f'<PGQ2?PRQ0WPRD3P3A0d?RPdP?Q1cQ0@Q1wQ0=PGfaS2?PKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S1sP;Q2?P;D3]@]?]>]=X2dA0d?IS1_#6S2CA0d?KS2E#6S2DA0d?XS2H#6S2IA0d?YS2J#6S2KQ1^Q1bP?PUCAPGQ1bPKPaPXPOD1PYPNPAPbD1PcPOPIPkP?Q1b/2?GfS2LeQ2LPGQ2?/2?S2LfbS2M/2?S2N90G3X1GPGQ2LQ1sP?P3GOb4W@W?W>W=P{P3PWQ1NP>P1M:YW0P3O1PdPXPRA0dYRS2LPdP^PRPdPJPRPdP}PRPdP]PRPdP~PRPdPwPRPdPxPRPdPzPRPdPQPRPdPyPREgF4F4F4F4S2ODiQ03A0dX{A0dY{S2PPdP^P{PdPJP{PdP}P{PdP]P{PdP~P{PdPwP{PdPxP{PdPzP{PdPQP{PdPyP{EgF4F4F4F4S2Q'<PGQ0oQ2@Q1QQ2@D3P3Q2@90dXPdPXQ1cQ0@Q1wQ0=PGfcS0oPKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S2RP;Q0oP;D3]@]?]>]=X2dAZdXIA0dXKS2S#6AZdXXA0dXYS2T#6PGQ2MPKPaPXPOD1PYPNPAPbD1PcPOPIPkPXQ2M/2XGfP01\dXO1+0LW@W?W>W=Q2GP3P{PRPWQ1NM:YW0P3O1PdPYQ2@Q2@90d^S2UPdPJQ2@PdP}Q2@PdP]Q2@PdP~Q2@PdPwQ2@PdPxQ2@PdPzQ2@PdPQQ2@Q2@9WdyF4F4F4F4S2VDiQ03Q2G90dYQ2G90d^S2WPdPJQ2GPdP}Q2GPdP]Q2GPdP~Q2GPdPwQ2GPdPxQ2GPdPzQ2GPdPQQ2GQ2G9WdyF4F4F4F4S2X'<PGQ2Af@S2AQ1aQ2AD3P3Q2A90dYPdPYQ1cQ0@Q1wQ0=PGfeS2YPKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S2ZP;Q2YP;D3]@]?]>]=X2dAZdYIA0dYKS2[#6AZdYXA0dYYS2\#6PGfdS2]PKPaPXPOD1PYPNPAPbD1PcPOPIPkPYQ2]/2YGfP31\dYS2^O1+0LW@W?W>W=fAS2_P3Q2GQ2@P{PRM:YW0P3O1PdP^Q2AQ2A90dJS2`PdP}Q2APdP]Q2APdP~Q2APdPwQ2APdPxQ2APdPzQ2APdPQQ2APdPyQ2AEgF4F4F4S2aDiQ03Q2_90d^Q2_90dJS2bPdP}Q2_PdP]Q2_PdP~Q2_PdPwQ2_PdPxQ2_PdPzQ2_PdPQQ2_PdPyQ2_EgF4F4F4S2c'<PGQ1sfBS1sQ2?Q1sD3P3Q1s90d^PdP^Q1cQ0@Q1wQ0=PGfgS2dPKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S2eP;Q2dP;D3]@]?]>]=X2dA0d^IS2f#6S2gA0d^KS2h#6S2iA0d^XS2j#6S2kA0d^YS2l#6S2mQ1^ffS2nP^PUCAPGQ2nPKPaPXPOD1PYPNPAPbD1PcPOPIPkP^Q2n/2^GfS2oeQ2oPGQ2d/2^S2ofhS2p/2^S2q90G3X1GPGQ2oQ2eP^P3GOb4W@W?W>W=fCS2oP3Q2_Q2AQ2GQ2@M:YW0P3O1PdPJQ1sQ1s90d}S2rPdP]Q1sPdP~Q1sPdPwQ1sPdPxQ1sPdPzQ1sPdPQQ1sQ1s9WdyF4F4F4S2sDiQ03Q2o90dJQ2o90d}S2tPdP]Q2oPdP~Q2oPdPwQ2oPdPxQ2oPdPzQ2oPdPQQ2oQ2o9WdyF4F4F4S2u'<PGQ2RfDS2RQ0oQ2RD3P3Q2R90dJPdPJQ1cQ0@Q1wQ0=PGfiS2vPKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S2wP;Q2vP;D3]@]?]>]=X2dA0dJIS2x#6S2yA0dJKS2z#6S2{A0dJXS2|#6S2}A0dJYS2~#6S30Q1^Q2pPJPUCAPGQ2pPKPaPXPOD1PYPNPAPbD1PcPOPIPkPJQ2p/2JGfS31eQ31PGQ2v/2JS31fjS32/2JS3390G3X1GPGQ31Q2wPJP3GOb4W@W?W>W=fES31P3Q2oQ1sQ2_Q2AM:YW0P3O1PdP}Q2RQ2R90d]S34PdP~Q2RPdPwQ2RPdPxQ2RPdPzQ2RPdPQQ2RPdPyQ2REgF4F4S35DiQ03Q3190d}Q3190d]S36PdP~Q31PdPwQ31PdPxQ31PdPzQ31PdPQQ31PdPyQ31EgF4F4S37'<PGQ2ZfFS2ZQ2YQ2ZD3P3Q2Z90d}PdP}Q1cQ0@Q1wQ0=PGfkS38PKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S39P;Q38P;D3]@]?]>]=X2dA0d}IS3:#6S3;A0d}KS3<#6S3=A0d}XS3>#6S3?A0d}YS3@#6S3AQ1^Q32P}PUCAPGQ32PKPaPXPOD1PYPNPAPbD1PcPOPIPkP}Q32/2}GfS3BeQ3BPGQ38/2}S3BflS3C/2}S3D90G3X1GPGQ3BQ39P}P3GOb4W@W?W>W=fGS3BP3Q31Q2RQ2oQ1sM:YW0P3O1PdP]Q2ZQ2Z90d~S3EPdPwQ2ZPdPxQ2ZPdPzQ2ZPdPQQ2ZQ2Z9WdyF4F4S3FDiQ03Q3B90d]Q3B90d~S3GPdPwQ3BPdPxQ3BPdPzQ3BPdPQQ3BQ3B9WdyF4F4S3H'<PGQ2efHS2eQ2dQ2eD3P3Q2e90d]PdP]Q1cQ0@Q1wQ0=PGfmS3IPKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S3JP;Q3IP;D3]@]?]>]=X2dA0d]IS3K#6S3LA0d]KS3M#6S3NA0d]XS3O#6S3PA0d]YS3Q#6S3RQ1^Q3CP]PUCAPGQ3CPKPaPXPOD1PYPNPAPbD1PcPOPIPkP]Q3C/2]GfS3SeQ3SPGQ3I/2]S3SfnS3T/2]S3U90G3X1GPGQ3SQ3JP]P3GOb4W@W?W>W=fIS3SP3Q3BQ2ZQ31Q2RM:YW0P3O1PdP~Q2eQ2e90dwS3VPdPxQ2ePdPzQ2ePdPQQ2ePdPyQ2eEgF4S3WDiQ03Q3S90d~Q3S90dwS3XPdPxQ3SPdPzQ3SPdPQQ3SPdPyQ3SEgF4S3Y'<PGQ2wQ0{Q2vQ0{D3P3Q0{90d~PdP~Q1cQ0@Q1wQ0=PGfoS2wPKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S3ZP;Q2wP;D3]@]?]>]=X2dA0d~IS3[#6S3\A0d~KS3]#6S3^A0d~XS3_#6S3`A0d~YS3a#6S3bQ1^Q3TP~PUCAPGQ3TPKPaPXPOD1PYPNPAPbD1PcPOPIPkP~Q3T/2~GfS3ceQ3cPGQ2w/2~S3cfpS3d/2~S3e90G3X1GPGQ3cQ3ZP~P3GOb4W@W?W>W=fKS3cP3Q3SQ2eQ3BQ2ZM:YW0P3O1PdPwQ0{Q0{90dxS3fPdPzQ0{PdPQQ0{Q0{9WdyF4S3gDiQ03Q3c90dwQ3c90dxS3hPdPzQ3cPdPQQ3cQ3c9WdyF4S3i'<PGQ39Q0UQ38Q0UD3P3Q0U90dwPdPwQ1cQ0@Q1wQ0=PGfqS39PKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S3jP;Q39P;D3]@]?]>]=X2dA0dwIS3k#6S3lA0dwKS3m#6S3nA0dwXS3o#6S3pA0dwYS3q#6S3rQ1^Q3dPwPUCAPGQ3dPKPaPXPOD1PYPNPAPbD1PcPOPIPkPwQ3d/2wGfS3seQ3sPGQ39/2wS3sfrS3t/2wS3u90G3X1GPGQ3sQ3jPwP3GOb4W@W?W>W=Q0VP3Q3cQ0{Q3SQ2eM:YW0P3O1PdPxQ0UQ0U90dzS3sPdPQQ0UPdPyQ0UEgS3vDiQ03Q0V90dxQ0V90dzS3wPdPQQ0VPdPyQ0VEgS3x'<PGQ3JPSQ3IPSD3P3A0dxSPdPxQ1cQ0@Q1wQ0=PGfsS3JPKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S3yP;Q3JP;D3]@]?]>]=X2dA0dxIS3z#6S3{A0dxKS3|#6S3}A0dxXS3~#6S40A0dxYS41#6S42Q1^Q3tPxPUCAPGQ3tPKPaPXPOD1PYPNPAPbD1PcPOPIPkPxQ3t/2xGfS43eQ43PGQ3J/2xS43ftS44/2xS4590G3X1GPGQ43Q3yPxP3GOb4W@W?W>W=PjP3Q0VQ0UQ3cQ0{M:YW0P3O1PdPzPSA0dQSS43AWdySS46DiQ03A0dzjA0dQjS47AWdyjS48'<PGQ3ZPDQ2wPDD3P3A0dzDPdPzQ1cQ0@Q1wQ0=PGfuS3ZPKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S49P;Q3ZP;D3]@]?]>]=X2dA0dzIS4:#6S4;A0dzKS4<#6S4=A0dzXS4>#6S4?A0dzYS4@#6S4AQ1^Q44PzPUCAPGQ44PKPaPXPOD1PYPNPAPbD1PcPOPIPkPzQ44/2zGfS4BeQ4BPGQ3Z/2zS4BfvS4C/2zS4D90G3X1GPGQ4BQ49PzP3GOb4W@W?W>W=Q1mP3PjPSQ0VQ0UM:YW0P3O1PdPQPDA0dyDS4B$0vH1dQ03Q1m90dQQ1m90dyS4E$0vPGQ3jQ23Q39Q23D3P3Q2390dQPdPQQ1cQ0@Q1wQ0=PGfwS3jPKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S4FP;Q3jP;D3]@]?]>]=X2dA0dQIS4G#6S4HA0dQKS4I#6S4JA0dQXS4K#6S4LA0dQYS4M#6S4NQ1^Q4CPQPUCAPGQ4CPKPaPXPOD1PYPNPAPbD1PcPOPIPkPQQ4C/2QGfS4OeQ4OPGQ3j/2QS4OfxS4P/2QS4Q90G3X1GPGQ4OQ4FPQP3GOb4W@W?W>W=Q2>P3Q1mPDPjPSM:YW0P3O1Q239WdyQ03Q2>90dyP6PGQ3yQ0jQ3JQ0jD3P3Q0j90dyPdPyQ1cQ0@Q1wQ0=PGfyS3yPKPaPXPOD1PYPNPAPbD1PcPOPIPkD1S4FP;Q3yP;D3]@]?]>]=X2dA0dyIS1c#6S0@A0dyKS1w#6S0=A0dyXS4O#6S4RA0dyYS4S#6S4TQ1^Q4PPyPUCAPGQ4PPKPaPXPOD1PYPNPAPbD1PcPOPIPkPyQ4P/2yGfRkePkPGQ3y/2yS1^fzRk/2yS4U90G3X1GPGQ1^Q4FPyP3GOb4W@W?W>W=Q0^P3Q2>Q23Q1mPDM:YW0P3O1P6PGQ49Q1]Q3ZQ1]D3P3n010000100X;6P3O1n200100001021100011000W;P3O1n200100001021100011000W;P3O1n200100001021100011000W;P3O1n200100001021100011000W;P3O1n200100001021100011000W;P3O1n200100001021100011000W;P3O1n200100001021100011000W;P3O1n200100001021100011000W;P3O1n200100001021100011000W;P3O1n201100001021100011000W;P3O1n201100001021100011000W;P3O1n201100001021100011000W;P3O1n201100001021100011000W;P3O1n201100001021100011000W;P3O1n201100001021100011000W;P3O1n201100001021100011000X@iX?hX>gX=fX;eX2dH0UK0DK0DK0DQ0teH0UH0ZQ0_Q01PGP0PIQ0YC>PGP0PKPaPGP0PXPOPGP0PYPNPG120MS0tPNPG120APbPGP0PcPOPGP5P:Q1]P:D3\i\h\g\f\e^2dD?K0:D?D?D?P4P2P\Q1XPVP4P3Q1mQ1XPVD5Q23Q0P7d3FNXEH,_HP3PGP2PIQ0YC>PGP;PKPaPGP;PXPOPGP;PYPNQ0?PGP;PAPbC>PGP;PcPOPGQ1NP:Q1iP:D3\i\h\g\f\e^2dD?41cD?D?D?Q0112:KS0?=0GaS1XPGP:PXPOPGP:PYPNPG12:MS49PNPGQ0APbPGP:PcPOPGPWP:Q1kP:D3\i\h\g\f\e^2dD?K0:D?D?P4P5P\Q1UPVP4P3Q0^Q1UPVD5Q1]Q0P7d3FNXEH,_HP3PGP5PKPaC>PGP1PXPOPG121YS1UPNPG121MS0APNPGP1PAPbPGP1PcPOPGQ2@P:Q1QP:D3\i\h\g\f\e^2dD?D?K0:D?Q01PGP>PXPOC>PG12>YS4FPNPG12>MS1^PNPGP>PAPbPGP>PcPOPGQ2GP:Q1eP:D3\i\h\g\f\e^2dD?D?K0:P4PWP\Q1oPVP4P3Q1iQ1oPVD5Q1kQ0P7d3FNXEH,_HP3PGPWPXPOC>PGQ0NPNPG12RMPNPGPRPAPbPGPRPcPOPGQ1sP:Q2?P:D3\i\h\g\f\e^2dD?D?K0:Q01PGP{PYPNC>PGP{PMPNPGP{PAPbPGP{PcPOPGQ2oP:Q2MP:D3\i\h\g\f\e^2dD?D?D?P4Q2GP\Q1QQ2_Q2A3CS0NPVP4P3Q1QQ0NPVD5Q1eQ0P7d3FNXEH,_HP3PGQ2GPYPNC>PGQ2APMPNPGQ2APAPbPGQ2APcPOPGQ2ZP:Q2YP:D3\i\h\g\f\e^2dD?D?D?Q01PGQ2_PMPNC>PGQ2_PAPbPGQ2_PcPOPGQ3BP:Q2nP:D3\i\h\g\f\e^2dD?D?P4Q2oP\Q2?Q31Q2R3CS0NPVP4P3Q2?Q0NPVD5Q2MQ0P7d3FNXEH,_HP3PGQ2oPMPNC>PGQ2RPAPbPGQ2RPcPOPGQ0{P:Q2vP:D3\i\h\g\f\e^2dD?D?Q01PGQ31PAPbC>PGQ31PcPOPGQ3cP:Q32P:D3\i\h\g\f\e^2dD?P4Q3BP\Q2YQ3SQ2e3CS0NPVP4P3Q2YQ0NPVD5Q2nQ0P7d3FNXEH,_HP3PGQ3BPAPbC>PGQ2ePcPOPGPSP:Q3IP:D3\i\h\g\f\e^2dD?Q01PGQ3SPcPOC>PGPjP:Q3TP:D3\i\h\g\f\e^2dP4Q3cP\Q2vQ0VQ0U3CRAPVP4P3Q2vPAPVD5Q32Q0P7d3FNXEH,_HP3PGQ3cPcPOC>PGQ23P:Q39P:D3\i\h\g\f\e^2dP<P4Q0VP\Q38?CjSRfPVD5P4P3Q0YQ3C?CDjRgPVD5XJHQ0OQ0S,RFRh50GRi1eS3RO'BS0OXJHP4P3Q3CPgPVD5XEHQ3IQ0P7d3XEHP4PfPNQ0IQ0JQ0BPVQ0VQ0YPGeRfQ38@1bjSQ0Y1\=8+1aQ3SP>P:P0N?1`P4PSP\PGePgPVP4P3PfPgPVD51BOiFNXMH,_HQ02PHP4PjP\Q3IQ1m;CDROPVP4P3Q0YPOPVD5Q0`/BiFNXMHP4PDP\Q3TQ23Q1m3CS0`PVP4P3Q0YQ0`PVD51eD3,BiFNXIH,_HP3P4Q1mP\Q2wQ2>Q233CROPVP4P3Q0YPOPVD5Q1m/e3S02/BiFNQ01P4Q23P\Q3dQ0jQ2>3CRgPVP4P0Q0YPgPVD5EJQ23Q0t=0GhRg7d0P4Q0jP\Q3tQ1]Q0^3CRfPVD5RcP4P3Q0YPfPVQ0j/e3,BiK1_XIH,_HP3PcP4P2Q0YPfPVJ1ZQ0^Q0>=0Gh7d;Q01Q1]/e:Q49=0GhP4Q1lP\Q4CQ1kQ1i3CS49PVP4P3Q0YQ49PVD5Q1l/e3,BiFNXIH,_HP3Q1l/e5Q0A=0GhPHP4Q0WP\Q3yQ1QQ2B3CRfPVP4P3Q0YPfPVD5Q0W/e3,BiFNXIHP>P4Q1kP\Q4PQ2BQ0W3CRiPVP4P>Q0YPiPVD5EJQ1^=0GhRcQ1k/e>RA'BP:PcPAP3P0K0DH0ZWNWTP0P3O2n2001000000121000000W0WqP0P3O2n2001000000121000000W0XJHP0P3O2n2001000000121101000bGQ0OQ01Pg1ej0P4P2Q0YPOPVP4P3Q2wPOPVD5Q3dQ0P7d3FNXEH,_HP3PGP2PMPhC>Q23/e;PGQ2>/2KQ0cQ3cQ0?P3PKQ0DQ0EQ0MQ0gQ0sQ2EQ2SQ2[Q2hQ2zQ3<Q3MQ3]Q3mQ3|Q4<Q4IQ1w+0rI0KI0KI0KS2['<RO'<RgQ0DQ0EQ0GQ0HPgQ0GQ0HQ0T/H`RAQ0CQ0F'HRcPgPVPNO1S0TQ0K$0YS0KQ0MQ0gQ2[Q2F40q80;ObRROXKAPOXKcp,5HdisjS0MJ0pWQWPQ3CI0SWOW0Q38I0S1PdKS2[eO2E;Q1XPGQ1dQ0eQ2R129YS0eP0PYQ0DQ0EQ0mQ0pQ1uQ2JQ2TQ2\Q2lQ2~Q3@Q3QQ3aQ3qQ41Q4@Q4MQ4S+0rI0KI0KS1d'<S1X'<S2F'<S0g'<S2S'<RO'<RgQ0DQ0EQ0GQ0HPgQ0GQ0HPAPcPgQ0TQ0KQ0mQ0pQ2SQ1uQ0gQ2JQ2FQ2TQ1XQ2\Q1dQ2^40q40;40;40;40;80;ObRROXKAPOXKcQ0MJ0pWQWPQ3II0SWOW0Q3CI0S1PdYS0EeO2E;Q0e=0GNPHP4P1Q0YQ44Q1lQ1R3CRcPVP4P3Q44PcPVD5Q3ZQ0P7d3FNXEHP5PXPZPMPZD1PIQ3JPXQ1RD1PYQ1]PKPLD1ROP4P5Q0YQ3JQ1RQ1]3CRAPVD5RgP4POQ3JPAPVD5S0e+0]Q44/eOS0GPGPOPMPZC>S0H'BPgP4P5Q0Y/=_S0MPAPVD5Q0eQ0vP4P<P5Q0YPAPVg02L3PMQ27Q0\$09/FCg02M=PUg02NGPGPbQ08Q0A00o3Q0y30X1GPGPhQ0820o3bQ0y30X1GQ0S1hFbS0y,o3#6XD=P=P8Q0S/o3#6XD=PTPqPrP[PsPtPEPuQ1@Q1AP=20R=7P0&1Y=RAH0`S0\Q1CPvQ1PQ1DQ09-0Q=Rg'mRO60BvS09Q1OPvQ05Q06Q06Q07Q1P9svOJ1WH0[Q1HQ1IbAbBbCX3=XH=1E30S07,`8S061E07S05$0eP6[[^3=^H=P3Q0JQ0Fp,3HsKO3S0eb6b7b8b9b:Q0yPTPqPrP[PsPtPEPuQ1@Q1APAQ1CQ1PQ1P5wvQ1HQ1IbAbBbC1H88P3b6b7b8b9b:PTPqPrP[PsPtPEPuQ1@Q1APAQ1CQ1PQ1T60BvQ1HQ1IbAbBbCQ1=P3b6b7b8b9b:5c8E;1hFhS1=Q0SPTPqPrP[PsPtPEPuQ1@Q1AQ0\Q1CPvQ09Q1OPvQ1P007ODkQ1HQ1IbAbBbCX3=XH=Q06Q05#a[^3=^H=Q0eb6b7b8b9b:S0ePTPqPrP[PsPtPEPuQ1?Q14-0_=Q13-0_=Q12-0_=60n=60n=g0122+1TQ1@40IQ1AP=P=20R=;P7PAH0`P020R=2H0`Q1CPvQ1DQ0:-0Q=RA'mQ1T60BvQ1OPvQ0<$04,mg=wvAQ1OPv20gv9Q0[-0Q=Q1T60Bv60fvQ1OPvQ1T-0AODkH0[H0[Q1HQ1IbAbBbCX3=XH=XU=XV=XF|S1T1E32/`PQ0<=u7;1`;P,B91E2;/`P[[[^3=^H=^U=^V=^F|S0<P3Q0DQ0LQ0CQ0JQ0FQ0oQ3dQ3tO8b6b7b8b9b:3cDI:1ShbP5PMP2FDP5Q27&1R5FDN>1QQ0|Q0}P3PF&02@$0x#yRb,FFRPQ0M%GbPFPPPFQ0MCQdO4b0PGPFPbQ041^FbdQ0MD[PGPPP4P>P3Q3ZQ1iQ1l3CRbPVP4A8>XZRAPMPZPIQ3ZD1PXQ1iPYQ1lD1PKPLQ3ZPbPVFtS1OEJX1GP4P1PPPcPVD5P4A81XZS0[1=P_S0:PcPVD5P4Q0[PMPZPIQ44PXQ1lFXPYQ1RPKPLD1S0[Q44PcPVD5Q0vP4P<P1PPPcPVg02OQPXPMPYPZg02P[PUg02QePUPGPhQ4F-0^3=0GZX1GPGPN20^h3=0GZX1GQ0SQ0F,b3,RF=0GZXD=PGQ1:Q1:Q0SQ0F'bQ0JQ1<PTPqPrP[PsPtPEPuQ1@Q1AQ0\Q1CQ1D:0E=O=svgQ1HQ1IbAbBbCX3=XH=Q07/b3/o0^3=^H=P3Q0JQ0FO2b6b7b8b9b:F{Q1=Q0SQ0ePTPqPrP[PsPtPEPuQ1TQ0<P3Q0DQ0LQ0CQ0JQ0FQ2]Q39Q3JO8b6b7b8b9b:3cDI20^hN=0GZeQ1UP0E;Q0AP;E;N@1PQ0|Q0}P3PF&02@#x#zRh,FFRNQ0:%GhPFPNPFQ0:CQdO4b0PGPFPhQ041^FhdQ0:D[PGPNP4Q1N?8XZRhP3Q49PVP4PhPMPZPIQ4CD1PXQ1kPYQ1iD1PKPLQ4CQ49PVFtEJX1GP4PAPNPbPVD5P4Q08PHQ27:0?BMPAPAPM12AXQ20Cpn01000000200001=N_RgPbPVD5Q1OQ0vP4P<PAPNPbPVg02RoRbPMPXQ1~g02T9&0<b$0>g02UCN=0OQ0|Q0}P3PF&02@#x#yRb,FFRNPg%GbPFPNPFPgCQdO4b0PGPFPbQ041^FbdPgD[PGPNP4A8WXZRbPM12bXS1OQ20CpP3Q3jQ0WQ1k3CRAPVP4A8bMZRbQ3j78IROPXQ0WPYQ1kPKPLFXS27Q3jPAPVD5RcEJX1GPmPdPGPXPZQ17E7S17Q1NPXPUCAPGPhPXPZC>RhePhPGPZP4A8RXZRhPMQ0lPNPiPVP4A8hMZS0lQ4P78IRPQ2B78XS49Q0W78YPKPLQ4PPiPVFtS0AGvX1GPGPZP4PhPMP3PNPiPVQ0AGvX1GP4PbPNPAPVD5P4Q08PHQ1\PbPOn01000000200001=N_ROPAPVD5PcQ0vP4P<PbPNPAPVg02VMPIPKQ16Q3j,MoQ3jg02WWPUg02XaPmPdPGPMPZQ17E7RAPWPKPUCAPGPbPKPWPKD3RbePbPG12RKS17Q0RPfQ18PoQ0QQ3y,Mo+0CRbDqX1GPGPaQ0RPfQ15,=3PoPbDqX1GP`Q1990GlXD=PGQ1:Q1:Q11Q1;Q1<PTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CQ1GQ1F5svQ1HQ1IbAbBbCX3=Q1KQ1J'o^3=Q1Lb6b7b8b9b:F{Q1MQ1SPTPqPrP[PsPtPEPuQ1VQ1WP3Q0DQ0CQ3jO3b6b7b8b9b:5c`DIQ1Z90GlRbePbPGPlQ0RQ1eQ1Q5CkRlP3PoQ0Q1Mok+0CDqX1GQ3yQ1QQ2B41OQ1ZP3EKb0Q17P9E;Q0lPKP3FDb4Q3j$0mNA0\Q0|Q0}P3PF&02@$06#zRb,FFRNPO%GbPFPNPFPOCQdO4b0PGPFPbQ041^FbdPOD[PGPNP4P{PXPZPMPZPIQ3yFXRbP3PfPVP4Q1Q98bXRcQ2B78YS0l?8KLS1ZQ3yPfPVD5S1KEJX1GP4PPPNPiPVD5P4Q08PHQ24PPQ49n01000000200001=N_RhPiPVD5Q0AQ0vP4P<PPPNPiPVg02YkPXPKQ0~Q2B,MoS0~Q2Bg02[5PUg02\?PmPdPGPIQ4PH03PAPRPKPUELPGPPPKQ17C>RPePPPG12{KS17Q0RPlQ1[PoQ0QQ1e,Mo+0CS1[DqX1GPGPaQ0RPlQ0;,=3PoQ1[DqX1GP`Q1x90GnXD=PGQ1:Q1:Q1vQ1yQ1<PTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CQ1{Q1z5svQ1HQ1IbAbBbCX3=Q1}Q1|'o^3=Q1Lb6b7b8b9b:F{Q1MQ1SPTPqPrP[PsPtPEPuQ1VQ1WP3Q0DQ0CQ4PO3b6b7b8b9b:5c`DIQ2190GnRPePPPGPnQ0Rf{RnQ1aQ1e3CRPP3PoQ0QQ1a,Mo+0CS0QDqX1GQ1eQ1Q61NkQ21P3EKb0Q17P5E;PbPKP3FDb4Q2B$0mS21NA0\Q0|Q0}P3PF&02@$06#yRb,FFRiPh%GbPFPiPFPhCQdO4b0PGPFPbQ041^FbdPhD[PGPiP4Q2@PXPZPMPZD1PIPkPXQ1eD1RbP3PlPVP4Q1Q98bYS1}?8KLS1|PkPlPVD5S1{EJX1GP4PcPiPfPVD5P4Q08PHQ0kPcQ0ln01000000200001=i_RNPfPVD5Q1KQ0vP4P<PcPiPfPVg02]IPYPKQ1rQ0~Q2Bg02^SPUg02_]PmPdPGPXQ1QPmPdPGPIQ3yPAE7E7S0~P{PKPUCAPGPcPKQ17C>RcePcPGQ2@/2KRcQ0RPPQ22PoQ1[DqX1GPGPaQ0RPP1=3CPoQ1[DqX1GP`Q26Q2850GXD=PGQ1:Q1:Q25Q29Q1<PTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CQ1EQ2:5svQ1HQ1IbAbBbCX3=Q2<Q2;'o^3=Q1Lb6b7b8b9b:F{Q1MQ1SPTPqPrP[PsPtPEPuQ1VQ1WP3Q0DQ0CQ3yO3b6b7b8b9b:5c`DIQ26Q2=50GRCePCPGQ26Q0Rf|RCQ1bQ1a3CS0RP3PoQ0QDqX1GQ1aQ1e61UnQ2=P3EKb0PcP1E;PbPKP3FDb4Q21NA0\Q0|Q0}P3PF&02@#n#n#zRb,FFRoPN%GbPFPoPFPNCQdO4b0PGPFPbQ041^FbdPND[PGPoP4Q2GPXPZPMPZPIPnFXPXQ1aPYQ1eD1RbP3PPPVP4A8bKLRfPnPPPVD5RiEJX1GP4Q1}PoPlPVD5P4Q1|1=o_R_PlPVD5Q1{Q0vP4P<Q1}PoPlPVg02`gPKPKQ0wQ0Z'FRlPLg02b1PUg02c;PUPmPdPGPYQ1QH03PmPdPGPXQ1ePmPdPGPIPkPAE7E7Q2@PKPUELPGQ1}PKPcC>RcePcPGQ2G/2KRcQ0w008l,=3=0GLX1GPGPaQ0Z,=3=0GLX1GP`Q0Z,E3,RF=0GLXD=Q0C,RFRl=0GLPG&1VGRo&1MG:1LGoQ1`,RFPLPlPGPo&1KGPlPLP3J1\K1]Ww21^FLPGQ1:Q1:Q1`Q0CQ1<PTPqPrP[PsPtPEPuQ1@Q1AQ1BQ1CQ1gQ1D5svQ1HQ1IbAbBbCX3=Q1p/o3^3=Q1Lb6b7b8b9b:F{O2Q1MQ1SPTPqPrP[PsPtPEPuQ1VQ1WP3Q0DQ0CPkO3b6b7b8b9b:5c`DIQ0Z,=a=0GLePcP>E;PbPKP3FDb4N@0kQ0|Q0}P3PF&02@#n#n#yR@,FFRbP_%G@PFPbPFP_CQdO4b0PGPFP@Q041^F@dP_D[PGPbP4Q2APXPZPMPZD1PIPCPXQ1bD1PYQ1aPKPLD1R@P3Q0RPVP4P@PCQ0RPVD5EJX1GRFP4PfPbPPPVD5P4PfQ20-0tnPPPVD5PiQ0vP4P<PfPbPPPVg02dEPIQ1~Png02eOPUg02fYPmPdPGPKPLH03RPPmPdPGPYQ1eH03PmPdPGPXQ1aPmPdPGPIPnPAE7E7I0wRbQ2GPIPUCAPGPfPIPnC>RcePcPGPCf}Rc90G3X1GPGPCP@PIP3GOb4N>1IPGPnPF20y<i20tn8PkE;EVP_P3EKb0EVPNP3EKb0EVPhP3EKb0EVPOP3EKb0EV1=Z8&0MZE;Q1OP3E;b4PgP3EKb0EVQ0:P3EKb0EVQ0MP3EKb0EVQ0GQ0HP31Pd0Q03A0dI7PdPKP7PdPpP7PdP?P7PdPXP7PdPYP7PdP^P7PdPJP7PdP}P7PdP]P7PdP~P7PdPwP7PdPxP7PdPzP7PdPQP7AWdy7F4F4F4F4F4F4F4PGQ27P2Q4PP2D3P0A0dI2PdPIPGQ1|P0PnP0D3^<eX2d1PdIPmPPPmPdPGPYQ2BQ0~E7P{PIPUELPGQ1ZPIQ3yC>RgePgPGPkPGP3PCPICUX1GPG12nIPkQ4PH0sQ1|PIP3FDb4W<P;P3P7F]W0P3O1PdPKP2PdPpP2PdP?P2PdPXP2PdPYP2PdP^P2PdPJP2PdP}P2PdP]P2PdP~P2PdPwP2PdPxP2PdPzP2PdPQP2AWdy2F4F4F4F4F4F4F4Q03A0dK;PdPpP;PdP?P;PdPXP;PdPYP;PdP^P;PdPJP;PdP}P;PdP]P;PdP~P;PdPwP;PdPxP;PdPzP;PdPQP;PdPyP;EgF4F4F4F4F4F4PGQ1ZP:PkP:D3P3Q0iPdPKPGP@P0PcP0D3^<eX2dQ2[PbQ2GPKPUCAPGPfPKPLC>RbePbPGPLPGP3f~RbPKCUX1GPG12cKPLQ3yH0sP@PKP3FDb4W<P9P3P;F]W0P3O1Q0]Q03Q1jQ0hPGPfP5PCP5D3P3Q0nPdPpPGQ1sPXPZPMPZD1PIPbPXQ2MD1PYQ2?PKPLD1RfP0p+01@R@P0D3^<eX2d1PdpPmPPPmPdPGPYQ1bPmPdPGPXQ2?PmPdPGPIPcPAE7E7E7Q2_PpPUELPGQ2_PXPZPMPZD1PIPcPXQ2?D1PYQ1bPKPLD1RcPpQ2_PpD3RgePgPGQ1s/2pRgPGP3p+01AR8PpCUX1GROPGQ1nPOQ2oPpP0Q0XPdPpQ00PBP|P3P=P|P0P6g02gcROP|P3Q1>P6P6n0110>0003100001000000RhP6n011020003001010>1010>n10110000012010=10<XGdRNPIP3D9P620L63R_b0W5Q0aeQ0sPdPpPNPKP3D9P6P_b0W5Q0beQ0uPdPpPNPXP3D9P6P_b0W5Q10eQ1uPdPpQ00PBP|P3P=P|P0P6POP|P3POP|P3P6P6Q1>n0110>0003100001000000RiP6P6n0110>00031010>1010>00P6n011020003001010>1010>n10110000012010=10<XGdPYP3D9P6P_b0W5Q1teO6PgP{PpP0O2E;PfPpP3FDb4W<P1P3P9F]W0P3O1Q0fQ03Q0dQ0qPGPcP>PbP>D3P3Q0zPdP?PGQ2RPXPZPMPZD1PIP8PXQ2]D1PYQ0oPKPLD1R>P0p+01BRbP0D3^<eX2d1Pd?PmPPPmPdPGPYQ2MPmPdPGPXQ0oPmPdPGPIP@PAE7E7E7Q2oP?PUELPGQ2oPXPZPMPZD1PIP@PXQ0oD1PYQ2MPKPLD1R@P?Q2oP?D3RcePcPGQ2R/2?RcPGP3p+01CRpP?CUX1GRfPGQ2NPfQ31P?P0Q1_PdP?Q00PBP|P3P=P|P0P6POP|P3P6Q1>P6n0110>0003100001000000RfP6n011020003001010>1010>n10110000012010=10<XGdRgPIP3D9P6P_b0W5Q2CeQ2EPdP?Q00PBP|P3P=P|P0P6POP|P3P6PfP6n0110>00031010>1010>00P6n011020003001010>1010>n10110000012010=10<XGdRfPKP3D9P6P_b0W5Q2DeQ2HPdP?Q00PBP|P3P=P|P0P6POP|P3P6POP|P3P6PiP6n0110>00031010>1010>00P6n0110>00031010>1010>00P6n011020003001010>1010>n10110000012010=10<XGdPXP3D9P6P_b0W5Q2IeQ2JPdP?PgPYP3D9P6P_b0W5Q2KeO6PcQ2GP?P0O2E;P>P?P3FDb4W<Q1NP3P1F]W0P3O1Q0rQ03Q1YQ1hPGP@PWP8PWD3P3Q0xPdPXPGQ2ZPXPZPMPZD1PIPpPXQ2nD1PYQ2YPKPLD1RWP0p+01DR8P0D3^<eX2d1PdXPmPPPmPdPGPYQ2]PmPdPGPXQ2YPmPdPGPIPbPAE7E7E7Q31PXPUELPGQ31PXPZPMPZD1PIPbPXQ2YD1PYQ2]PKPLD1RbPXQ2YC>R@eP@PGQ2nPGP3p+01ER@PXCUX1GPG128XPWPXP3GOb4W<PRP3Q1NF]W0P3O1Q1fQ03Q2LQ2OPGPbP{PpP{D3P3Q2PPdPYPGQ2ePXPZPMPZD1PIP@PXQ2pD1PYQ2dPKPLD1R{P0p+01FRpP0D3^<eX2dQ0EPmPPPmPdPGPYQ2nPmPdPGPXQ2dPmPdPGPIP8PAE7E7E7Q3BPYPUELPGQ3BPXPZPMPZD1PIP8PXQ2dD1PYQ2nPKPLD1R8PYQ2nC>RbePbPGQ2dPGP3p+01GRbPYCUX1GPG12pYP{PYP3GOb4W<Q2@P3PRF]W0P3O1Q2QQ03Q2UQ2VPGP8Q2GP@Q2GD3P3Q2WPdP^PGQ0{PXPZPMPZD1PIPbPXQ32D1PYQ2vPKPLD1R@P0p+01HR8P0D3^<eX2d1Pd^PmPPPmPdPGPYQ2pPmPdPGPXQ2vPmPdPGPIPpPAE7E7E7Q3SP^PUELPGQ3SPXPZPMPZD1PIPpPXQ2vD1PYQ2pPKPLD1RpP^Q3SP^D3RRePRPGQ0{/2^RRPGP3p+01IR{P^CUX1GRWPGQ2qPWQ3cP^P0Q2fPdP^PgPIP3D9P6P_b0W5Q2geQ2hPdP^Q00PBP|P3P=P|P0P6POP|P3P6PhP6n0110>00031010>1010>00RWP6n011020003001010>1010>n10110000012010=10<XGdR?PKP3D9P6P_b0W5Q2ieQ2jPdP^P?PXP3D9P6P_b0W5Q2keQ2lPdP^PgPYP3D9P6P_b0W5Q2meO6PRQ31P^P0O2E;P@P^P3FDb4W<Q2AP3Q2@F]W0P3O1Q2XQ03Q2`Q2aPGPpQ2_PbQ2_D3P3Q2bPdPJPGQ0UPXPZPMPZD1PIP{PXQ3CD1PYQ38PKPLD1RbP0p+01JRpP0D3^<eX2d1PdJPmPPPmPdPGPYQ32PmPdPGPXQ38PmPdPGPIP8PAE7E7E7Q3cPJPUELPGQ3cPXPZPMPZD1PIP8PXQ38D1PYQ32PKPLD1R8PJQ3cPJD3R^eP^PGQ0U/2JR^PGP3p+01KR@PJCUX1GRRPGQ33PRQ0VPJP0Q2xPdPJPNPIP3D9P6P_b0W5Q2yeQ2zPdPJPNPKP3D9P6P_b0W5Q2{eQ2|PdPJPNPXP3D9P6P_b0W5Q2}eQ2~PdPJQ00PBP|P3P=P|P0P6POP|P3PhP6P6n0110>00031010>1010>00P6n011020003001010>1010>n10110000012010=10<XGdRhPYP3D9P6P_b0W5Q30eO6P^Q3BPJP0O2E;PbPJP3FDb4W<Q1sP3Q2AF]W0P3O1Q2cQ03Q2rQ2sPGP8Q2oP{Q2oD3P3Q2tPdP}PGPSPXPZPMPZD1PIP@PXQ3TD1PYQ3IPKPLD1R{P0p+01LR8P0D3^<eX2d1Pd}PmPPPmPdPGPYQ3CPmPdPGPXQ3IPmPdPGPIPpPAE7E7E7Q0VP}PUELPGQ0VPXPZPMPZD1PIPpPXQ3ID1PYQ3CPKPLD1RpP}Q0VP}D3RJePJPG12S}RJPGP3p+01MRbP}CUX1GR^PGQ3DP^PjP}P0Q3:PdP}PgPIP3D9P6P_b0W5Q3;eQ3<PdP}PfPKP3D9P6P_b0W5Q3=eQ3>PdP}Q00PBP|P3P=P|P0P6POP|P3P6PWP6n0110>00031010>1010>00R^P6n011020003001010>1010>n10110000012010=10<XGdPXP3D9P6P_b0W5Q3?eQ3@PdP}PgPYP3D9P6P_b0W5Q3AeO6PJQ3SP}P0O2E;P{P}P3FDb4W<Q2RP3Q1sF]W0P3O1Q2uQ03Q34Q35PGPpQ31P@Q31D3P3Q36PdP]PGPDPXPZPMPZD1PIPbPXQ3dD1PYQ2wPKPLD1R@P0p+01NRpP0D3^<eX2d1Pd]PmPPPmPdPGPYQ3TPmPdPGPXQ2wPmPdPGPIP8PAE7E7E7PjP]PUELPGPjPXPZPMPZD1PIP8PXQ2wD1PYQ3TPKPLD1R8P]PjP]D3R}eP}PG12D]R}PGP3p+01OR{P]CUX1GRJPGQ3UPJQ1mP]P0Q3KPdP]PNPIP3D9P6P_b0W5Q3LeQ3MPdP]PNPKP3D9P6P_b0W5Q3NeQ3OPdP]PNPXP3D9P6P_b0W5Q3PeQ3QPdP]Q00PBP|P3P=P|P0P6POP|P3PWP6P6n0110>00031010>1010>00P6n011020003001010>1010>n10110000012010=10<XGdPYP3D9P6P_b0W5Q3ReO6P}Q3cP]P0O2E;P@P]P3FDb4W<Q2ZP3Q2RF]W0P3O1Q37Q03Q3EQ3FPGP8Q3BPbQ3BD3P3Q3GPdP~PGQ23PXPZPMPZD1PIP{PXQ3tD1PYQ39PKPLD1RbP0p+01PR8P0D3^<eX2d1Pd~PmPPPmPdPGPYQ3dPmPdPGPXQ39PmPdPGPIPpPAE7E7E7Q1mP~PUELPGQ1mPXPZPMPZD1PIPpPXQ39D1PYQ3dPKPLD1RpP~Q1mP~D3R]eP]PGQ23/2~R]PGP3p+01QR@P~CUX1GR}PGQ3eP}Q2>P~P0Q3[PdP~PgPIP3D9P6P_b0W5Q3\eQ3]PdP~P?PKP3D9P6P_b0W5Q3^eQ3_PdP~P?PXP3D9P6P_b0W5Q3`eQ3aPdP~PgPYP3D9P6P_b0W5Q3beO6P]Q0VP~P0O2E;PbP~P3FDb4W<Q2eP3Q2ZF]W0P3O1Q3HQ03Q3VQ3WPGPpQ3SP{Q3SD3P3Q3XPdPwPGQ0jPXPZPMPZD1PIP@PXQ44D1PYQ3JPKPLD1R{P0p+01RRpP0D3^<eX2d1PdwPmPPPmPdPGPYQ3tPmPdPGPXQ3JPmPdPGPIP8PAE7E7E7Q2>PwPUELPGQ2>PXPZPMPZD1PIP8PXQ3JD1PYQ3tPKPLD1R8PwQ2>PwD3R~eP~PGQ0j/2wR~PGP3p+01SRbPwCUX1GR]PGQ3uP]Q0^PwP0Q3kPdPwPNPIP3D9P6P_b0W5Q3leQ3mPdPwPNPKP3D9P6P_b0W5Q3neQ3oPdPwPNPXP3D9P6P_b0W5Q3peQ3qPdPwPhPYP3D9P6P_b0W5Q3reO6P~PjPwP0O2E;P{PwP3FDb4W<Q0{P3Q2eF]W0P3O1Q3YQ03Q3fQ3gPGP8Q3cP@Q3cD3P3Q3hPdPxPGQ1]PXPZPMPZD1PIPbPXQ4CD1PYQ3ZPKPLD1R@P0p+01TR8P0D3^<eX2d1PdxPmPPPmPdPGPYQ44PmPdPGPXQ3ZPmPdPGPIPpPAE7E7E7Q0^PxPUELPGQ0^PXPZPMPZD1PIPpPXQ3ZD1PYQ44PKPLD1RpPxQ0^PxD3RwePwPGQ1]/2xRwPGP3p+01UR{PxCUX1GR~PGQ45P~Q1RPxP0Q3zPdPxPgPIP3D9P6P_b0W5Q3{eQ3|PdPxPfPKP3D9P6P_b0W5Q3}eQ3~PdPxQ00PBP|P3P=P|P0P6POP|P3P6P^P6n0110>00031010>1010>00P6n011020003001010>1010>n10110000012010=10<XGdPXP3D9P6P_b0W5Q40eQ41PdPxPgPYP3D9P6P_b0W5Q42eO6PwQ1mPxP0O2E;P@PxP3FDb4W<Q0UP3Q0{F]W0P3O1Q3iQ03Q3sQ3vPGPpQ0VPbQ0VD3P3Q3wPdPzPGQ1lPXPZPMPZD1PIP{PXQ4PD1PYQ3jPKPLD1RbP0p+01VRpP0D3^<eX2d1PdzPmPPPmPdPGPYQ4CPmPdPGPXQ3jPmPdPGPIP8PAE7E7E7Q1RPzPUELPGQ1RPXPZPMPZD1PIP8PXQ3jD1PYQ4CPKPLD1R8PzQ1RPzD3RxePxPGQ1l/2zRxPGP3p+01WR@PzCUX1GRwPGQ4DPwQ1iPzP0Q4:PdPzPNPIP3D9P6P_b0W5Q4;eQ4<PdPzPNPKP3D9P6P_b0W5Q4=eQ4>PdPzPNPXP3D9P6P_b0W5Q4?eQ4@PdPzQ00PBP|P3P=P|P0P6POP|P3P^P6P6n0110>00031010>1010>00P6n011020003001010>1010>n10110000012010=10<XGdPYP3D9P6P_b0W5Q4AeO6PxQ2>PzP0O2E;PbPzP3FDb4W<PSP3Q0UF]W0P3O1Q3xQ03Q43Q46PGP8PjP{PjD3P3Q47PdPQPGQ1kPXPZPMPZD1PIP@PXPkD1PYQ3yPKPLD1RjP0p+01XR{P0D3^<eX2d1PdQPmPPPmPdPGPYQ4PPmPdPGPXQ3yPmPdPGPIPpPAE7E7E7Q1iPQPUELPGQ1iPXPZPMPZD1PIPpPXQ3yD1PYQ4PPKPLD1RpPQQ1iPQD3R8eP8PGQ1k/2QR8PGP3p+01YRzPQCUX1GRbPGQ4QPbQ0WPQP0Q4GPdPQPgPIP3D9P6P_b0W5Q4HeQ4IPdPQP?PKP3D9P6P_b0W5Q4JeQ4KPdPQP?PXP3D9P6P_b0W5Q4LeQ4MPdPQPgPYP3D9P6P_b0W5Q4NeO6P8Q0^PQP0O2E;PjPQP3FDb4W<PDP3PSF]W0P3O1Q48Q03Q4BP6PGPpQ1mP@Q1mD3P3Q4EPdPyPGQ2BPXPZPMPZD1PIPzPXPCD1PYPnPKPLD1RCP0p+01ZP0D3^<eX2d1PdyPmPPPmPdPGPYPkPmPdPGPXPnPmPdPGPIP{PAE7E7E7Q0WPyPUELPGQ0WPXPZPMPZD1PIP{PXPnD1PYPkPKPLD1RLPyQ0WPyD3RkePkPGQ2B/2yRkPGP3p+01[PyCUX1GRnPGQ4UPnQ1QPyP0Q1cPdPyPNPIP3D9P6P_b0W5Q0@eQ1wPdPyPNPKP3D9P6P_b0W5Q0=eQ4OPdPyPNPXP3D9P6P_b0W5Q4ReQ4SPdPyPhPYP3D9P6P_b0W5Q4TeO6PkQ1RPyP0O2E;PCPyP3FDb4W<Q23P3PDF]W0P3O1P6PGPLQ2>PzQ2>D3P3n010000000X;6P3O1n200100000021100010000W;P3O1n200100000021100011000W;P3O1n200100000021100011000W;P3O1n200100000021100011000W;P3O1n200100000021100011000W;P3O1n200100000021100011000W;P3O1n200100000021100011000W;P3O1n200100000021100011000W;P3O1n200100000021100011000W;P3O1n201100000021100011000W;P3O1n201100000021100011000W;P3O1n201100000021100011000W;P3O1n201100000021100011000W;P3O1n201100000021100011000W;P3O1n201100000021100011000W;P3O1n201100000021100011000b<X;eX2dQ0GePmPPPmPdPGPYQ1]PmPdPGPXQ1RPmPdPGPIQ3JPAE7E7E7P5PMPUELQ0HeQ0HPGPZA0G3ZX1GPGPZQ0[PMP3GOb4K0DH0ZbsbrWTWNP0P3O2n2001000000121000000W0XEHQ0OP4P7Q0YQ0`PVP4P3Q3TQ0`PVD5Q2wQ0P7d3FNXEH,_H[^IHeL0uWpWlP0P3O2n2001000000121000000W0WkP0P3O2n2001000000121000000W0WjP0P3O2n2001000000121000000W0WoP0P3O2n2011000000121000000W0WnP0P3O2n2011000000121000000W0WmP0P3O2n2011000000121000000W0WiP0P3O2n2011000000121000000W0XIHQ0_P4P7P\Q1qPVP4P3PDQ1qPVD5Q02Q0P'BFNXEH,_H[^IHeL0ub{bzWeWbW`WuWtW^WcWhWaP1P5P9P:P;P2P7P0P3O9n500000100000019110510910710310;10:104106108bYb_bfbgW\W[W]WZWdXyGWxo"). Qed.
End SNL.

Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  (0 < bv_unsigned s + K)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
  (0x13898 <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0xba46c : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0Strnlen ()) ["FPX_1"] "p'0h05regs'h14mem'h21Hh33A10h42H1h53H10h63H11h72H2h83HOKh95Hdisjh:4Hreth;3HsKh<4Hsprh=4Hstkh>1Kh?2KCh@3RUNhA3bufhB1ehC3memhD1nhE1rhF4regshG3rethH3romhI1shJ2spi001xp;1p;2p;5p;4p;3p;Cp;6p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9g002PR0p4p7210p1003<p4p710R1p8p1003Zp4p710P1p8p10045p4p710p1004Tp4p710p8g0050j16Tg005Uj1ITg0063j1MTg00>Mj1`Tg00HZj1\Tg009lj19TP0j2YTg00d1j5UTg009Bj24Tg00D>j2NTg00;Lj2STg00:Qj17Tg00:oj28Tg00>oj22Tg02hHj4[Tg00AXj33Tg00;hj2JTg00T;j2ZTg00BLj1XTg00<Dj2WTg01;`j1VTg01<Yj20Tg02iHlCTTg01>cj51Tg00VYj5CTg01>IR0j2>Tg012^j2RTg00H:j1QTg00lHj3@Tg02jKj3ATg00>2R1j2:Tg01?Uj2GTg02kGj6_Tg017[j4KTg01P]j4PTg006Vj1HTg01IQj3^Tg01g2j3OTg013>j4]Tf0R2#6#6p=E%H2#H#H#Hp=<%62#9p=D%92#6p=Ff1R3g01i^7^2p=?f3R4f2R5123233p=;1G53/:2p=5g010IR6f6R7f5R8f4R9P4P5P3D13O/:2p==P5g00\^R:P3P2C]p=BP8P9P4P5P3D1=O62p=Lg008>R;#6R<#6R=#6R>#ER?#6#IR@#MRA%I>#MRB#`[RC%\B%9<RD#IRE/YARFf8RGf7RHP8P9P4DUg00\@14@GRI/N8'Sg00bTP6f:R6%7?R?,8I,2@g008c#<#<#<#<#<#<#<#<C[g00c433%6;#D#9#F#E#F#D#F#E#7f9RI,4@/8?'Jf;RJ,4@RK1ZBI#X'N14@6RB/8?'J1JBK'W%V8%7;,?E,0H=3A7%7<,?E,0Gf=R<53A%6D#7,?ERB,0IRKf?RL53APA%9D#7,?E,06P@f<RDC;fBRMfARNf@ROPLf>RPP<PDPIPGPHP7P8PJP6P9P4P5P3P2MCTp,2fxR5PD%D;#9#F#F#D#E#D#9#D#9#E#7,?@R;PAefCR7P<D1P5P2PJP7PNPJ%7>,?ER>,0D%9=#7,?ERE,0DDCP<PA102BR=P@PLC;95D2F=X0F,>FP0PFP5P<P;fDR0PPD1P5P2PDP0PMPD10<>10<EDCPPPAP=P@POC;95<2F=X0FP5PLP;fFR<POD1RDP5P3PPP2PO103BRJ12@MRQ53A1RA:RR14@0/8?,2@=BA?%QRRS3@9A<2':95L3F=X1C,>CX0F,>FP2PDP5P2PPP<P0PP10L>10LEDCPOA3A=Q95L2F=P1P5POP;fGRQPNP5P3PLPQfEPL10O>10OEDCPND1ELPAPJP@P7C;95O3P5P7P;fJROP0D1P5P3PMP2P012@<RL93AJfHR=,4@/8?,2@=BA?=@RS9AO2':9573F=X1C,>CX0F,>FP2P5PMP;fIRPP7P5P4PNPPPQPN10M>10MEDCP7D1EL109B=3AL9579P11G08PA108BP@PQC;P5PQP;fNR0P=D1P5P3P<P2P=12@OR193AJfLR9,4@/8?,2@=BA?=@RS9A02':95Q3F=X1C,>CX0F,>FP21G<H10GB=3A1PFP5POP;fQR1fKRGD1P5P3PPP2PGPAPJP@fMRJC;fOR<,4@/8?,2@=BA?=@RS9A12':95O3F=X1C,>CX0FPIPCP5PPP;fPR1POD1P5P6P=P2POPA106BP@P9C;14@0/8?,2@=BA?=@RS9A12':95P6F=X1CP<PJPQ10=>R>10=EREDCR6P5P=P;P<PPP5PIPQP6PPD1EL1G=IR=PAPKP@PGC;RG14@J/8?,2@=BA?=@RS9A<6R6':RS':P8P=PSP3PGP6P2P<PJP7PQP>PEE_CKCKCKCPCPW3W?P3P2O2n2001000010121000000W2W@P3P2O2n2001000010121000000W2XEFP3P2O2n2001000010121100000bBW6W5W7W4W:W9W<W=W;W8XGAWFXHCXD:X>:WAXJAXIAWCo"). Qed.

End FPX_1.

End Ns0Strnlen.
Module Ns0LibMainRet.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0020.Ns0_code_r20000_21000.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Theorem main_ret_0 : forall regs mem rom,
  getr regs 10 = Z_to_bv 64 0 ->
  exists regs',
    msteps RSEGS (mkst regs (0x38da0 : word) mem rom) (mkst regs' (0x38e20 : word) mem rom)
    /\ getr regs' 8 = Z_to_bv 64 0
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ (forall r : reg, r <> 1 -> r <> 8 -> r <> 10 -> r <> 11 -> getr regs' r = getr regs r).
Proof.
  intros regs mem rom Ha0.
  destruct (c_lts (getr regs 21) (getr regs 0)) eqn:Hc.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_tk F_38d58 D_38d58 ltac:(exact Hc).
      stepn F_38d64 D_38d64.
      stepn F_38eac D_38eac.
      stepret F_38eb0 D_38eb0 (Z_to_bv 64 0x38db0) ltac:(reflexivity).
      stepn F_38d68 D_38d68.
      stepn F_38d6c D_38d6c.
      stepb_tk F_38d70 D_38d70 ltac:(cond_compute).
      apply mst_refl.
    + repeat split; gres; try reflexivity.
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
  - (* [comment removed for export] *)
    eexists. split.
    + stepb_ft F_38d58 D_38d58 ltac:(exact Hc).
      stepn F_38d5c D_38d5c.
      stepn F_38d60 D_38d60.
      apply mst_refl.
    + repeat split; gres; try reflexivity; try (rewrite Ha0; reflexivity).
      intros r H1 H8 H10 H11. rewrite !getr_other by assumption. reflexivity.
Qed.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0LibMainRet.
Module Ns0PrintfBufBase.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Frame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0055.SymAux OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefPrintfLib.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Ns0PrintfBufBase () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9Morphisms:forall_defC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilC47Corelib4Init5Logic6eq_indK47Corelib4Init9Datatypes3nat02C47Corelib4Init5Peano2ltK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K45stdpp9bitvector;definitions2bv01C56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08c59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase9allregs32C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC69OSSVerify5KrLib7Mh_00638SymExec23SX24ridxC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula0:C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib=SymExec2Sound4SX2S:ridx_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26edenotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase=nth_allregs32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S>ridx_roundtripC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega5Tauto4kind02K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool02C47Corelib7Classes9Morphisms@reflexive_properC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib5Lists4List=app_nth2_plusI47Corelib4Init5Peano2le00C47Corelib4Init3Nat3subC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3addC47Corelib7Classes?RelationClasses=eq_TransitiveC59OSSVerify5KrLib7Mh_01058SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes?RelationClasses<eq_ReflexiveC47Corelib7Classes9MorphismsJreflexive_eq_dom_reflexiveC47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes?RelationClasses<eq_SymmetricC47Corelib7Classes?RelationClasses8symmetryC47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01058SymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive8blobs_evC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX22evC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z6inj_leC59OSSVerify5KrLib7Mh_00387SeqExec9getr_zeroC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase>regs_ok_by_idxC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase7ev_junkC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase5pf_srC1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint04K47Corelib4Init7Decimal4uint0;K47Corelib4Init7Decimal4uint03K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintC59OSSVerify5KrLib7Mh_00389StreamSim7wseg_okC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsWSrc_jsoncons_fuzz_msgpack_encoder_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint01I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib7Mh_00438AgentLib7u64_litC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?store_ok_windowC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00c59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase9wseg_dataC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase3pfH00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib7Mh_01056SymRun6stk_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib7Mh_01056SymRun<kalign_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun<krange_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun=kwr_of_stk_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun:kimg_introC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC59OSSVerify5KrLib7Mh_01056SymRun;kword_introC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase=data_store_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib7Mh_00638SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK47Corelib4Init9Datatypes6option01C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK47Corelib5Lists7ListDef6Forall02I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase5pf_knC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase5PF_FRC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase3ev0C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_Zc59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase3ev1C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0058@Ns0PrintfBufBase3ev2C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Definition PF_FR : Z := 1056.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record pfH (mem : word -> option byte) (sp : word) (w can : Z) : Prop := PFH {
  Psp16  : bv_unsigned sp mod 16 = 0;
  PspLo  : 0xfa420 <= bv_unsigned sp;
  PspHi  : bv_unsigned sp <= 0x7fffffffffff;
  Pstk   : stk_ok RSEGS mem sp PF_FR;
  Pimg   : forall i, 0x10000 <= i < 0xc6000 -> mem (Z_to_bv 64 i) = None;
  Pflags : rdn RSEGS mem (Z_to_bv 64 0xc6cc0) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  Pwend  : rdn RSEGS mem (Z_to_bv 64 0xc6ce0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf9440));
  Pwpos  : rdn RSEGS mem (Z_to_bv 64 0xc6ce8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 w));
  Pw     : 0xf9040 <= w <= 0xf943e;
  Pbsz   : rdn RSEGS mem (Z_to_bv 64 0xc6d20) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
  Plock  : rdn RSEGS mem (Z_to_bv 64 0xc6d4c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  Plbf   : rdn RSEGS mem (Z_to_bv 64 0xc6d50) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  Pcan   : rdn RSEGS mem (Z_to_bv 64 0xf8ac0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
  Pcan64 : 0 <= can < 2 ^ 64 }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pf_vals (regs : bvmap 5 word) (sp : word) (w can : Z) : list word :=
  [sp; Z_to_bv 64 w; Z_to_bv 64 can] ++ junk_vals regs.

Definition pfE (regs : bvmap 5 word) (sp : word) (w can : Z) : env :=
  Env (vals_ev (pf_vals regs sp w can)) (blobs_ev []).

Definition pf_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0 | 1 => ELit 0x38fd8 | 2 => EVar 0 | 11 => ELit 0
                          | _ => EVar (3 + i) end)%nat (seq 0 32)).

Definition pf_kn : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0xfa420 0x7fffffffffff;
   KWr (SA (EVar 0) (-1056)) 1056;
   KImg 0x10000 0xc6000;
   KWord (SA (ELit 0) 0xc6cc0) 4 (ELit 5);
   KWord (SA (ELit 0) 0xc6ce0) 8 (ELit 0xf9440);
   KWord (SA (ELit 0) 0xc6ce8) 8 (EVar 1);
   KRange (EVar 1) 0xf9040 0xf943e;
   KWord (SA (ELit 0) 0xc6d20) 8 (ELit 1024);
   KWord (SA (ELit 0) 0xc6d4c) 4 (ELit 4294967295);
   KWord (SA (ELit 0) 0xc6d50) 4 (ELit 4294967295);
   KWord (SA (ELit 0) 0xf8ac0) 8 (EVar 2);
   KWr (SA (ELit 0) 0xc6000) 0x34000;
   KWr (SA (EVar 1) 0) 2].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition allregs32 : list reg :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_allregs32 : forall n, (n < 32)%nat -> nth n allregs32 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0PrintfBufBase ()) ["FPX_1"] "p'0h02Hnh11Hh22n0h31ni001nh44__p1h54__x1h62b1h72b2h83Hn0h97__arithh:4__ffh;8__varmaph<5__with=4cstrh>1xp%0p;1p;2p;3p;4p;6p;<p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210p1003<p4p710R0p8p1003Zp4p710P0p8p10045p4p710p1004Tp4p710p8g0050R0j10Tg005OR1j21Tg005gj1>Tg006Lj1QTg0071j1cTg007Oj1;Tg0082j3[Tg008UR2j1=Tg0095j2CTg009[j39Tg00:5j2<Tg00:_j3MTg00;Cj4@Tg00;_j1JTg00<=R3j2ITg00<Yj2?Tg00=6j4YTg00=]j1XTg00>Bj2FTg00>^j1VTg00?>j1UTg00?^j2TTg00@<j1PTg00@Zj1OTg00AEj2BTg00Ahj2NTg00BKj4GTg00C6j1RTg00CXj6STg00D<j2bTg00D^j2DTg00E8j2aTg00Edj3`Tg00FCj4_Tg00G5l<KTg00GZl<^Tg00H?j7]Tg00Hcj3ATg00IFj8\Tf4R4f3R5f2R6g00IjR7f1R8C@f0R939p=W%=9,C8p=4g00K1R:1<89'Dp=2f5R;P4P5P7P6C@%=9,C839p=3P6P8P7P9C@p=51?45/?6/?8/?9p=71D:9p=Hg00KOR<P<P:P:P0P2P2f6g00KnR=P;P4P<P<P:P:P0P2P2P5P=P6P8P9M<KM<Kp=6P<P:P1P2P3g00LRP;P4P5P6P8P9M<^p=ZP8g00M4R;g00MSR3P3g00N3R2P9g00NSF]p=EAA:45=A:6=A:8=A:9p=8P5P;P3P3P2P6P8P9G\p=L%09#0#0#0p=:g00O3R1#0R=#0R0#0R>#0R?#0R@#0RA#0RB#0RC#0RD#0RE#0RF#0RG#0RH#0RI#0RJ#0RK#0RL#0RM#0RN#0RO#0RP#0RQ#0RR#0RS#0RT#0RU#0RV#0RW#0RX#0RY#0RZ#0R[,19R\P<g00ORR]#>R^#Q#cR_#;R`P`P8g00P7Rag00PU5[_Rb%=8Rc,C_DW^0\P8111[g00Q1R\%;9Rd%;8Reg00QO%;6?9891<561<5859:Rf[1<681<6959:%;5?968[Rg%;4?956\fAM689P9n2001000000120000000W7W6W3RfPg^7e^6d^3\R\P9P_P`P1P7PbC@14_1R112_1O4b1W0P<%09R1/1[P`P`%08R7PbP_P7E3]0P911=[PfP\P9P_A5`=b14_=R=12_=O4b1W0P<%01R1/1[P`P`%07R=PbP_P=E3]0P9110[PfP\P9P_A5`0b14_0R012_0O4b1W0P<%01R1/1[P`P`%0=R0PbP_P0E3]0P911>[PfP\P9P_A5`>b14_>R>12_>O4b1W0P<%01R1/1[P`P`%00R>PbP_P>E3]0P911?[PfP\P9P_A5`?b14_?R?12_?O4b1W0P<%01R1/1[P`P`%0>R?PbP_P?E3]0P911@[PfP\P9P_A5`@b14_@R@12_@O4b1W0P<%01R1/1[P`P`%0?R@PbP_P@E3]0P911A[PfP\P9P_A5`Ab14_ARA12_AO4b1W0P<%01R1/1[P`P`%0@RAPbP_PAE3]0P911B[PfP\P9P_A5`Bb14_BRB12_BO4b1W0P<%01R1/1[P`P`%0ARBPbP_PBE3]0P911C[PfP\P9P_A5`Cb14_CRC12_CO4b1W0P<%01R1/1[P`P`%0BRCPbP_PCE3]0P911D[PfP\P9P_A5`Db14_DRD12_DO4b1W0P<%01R1/1[P`P`%0CRDPbP_PDE3]0P911E[PfP\P9P_A5`Eb14_ERE12_EO4b1W0P<%01R1/1[P`P`%0DREPbP_PEE3]0P911F[PfP\P9P_A5`Fb14_FRF12_FO4b1W0P<%01R1/1[P`P`%0ERFPbP_PFE3]0P911G[PfP\P9P_A5`Gb14_GRG12_GO4b1W0P<%01R1/1[P`P`%0FRGPbP_PGE3]0P911H[PfP\P9P_A5`Hb14_HRH12_HO4b1W0P<%01R1/1[P`P`%0GRHPbP_PHE3]0P911I[PfP\P9P_A5`Ib14_IRI12_IO4b1W0P<%01R1/1[P`P`%0HRIPbP_PIE3]0P911J[PfP\P9P_A5`Jb14_JRJ12_JO4b1W0P<%01R1/1[P`P`%0IRJPbP_PJE3]0P911K[PfP\P9P_A5`Kb14_KRK12_KO4b1W0P<%01R1/1[P`P`%0JRKPbP_PKE3]0P911L[PfP\P9P_A5`Lb14_LRL12_LO4b1W0P<%01R1/1[P`P`%0KRLPbP_PLE3]0P911M[PfP\P9P_A5`Mb14_MRM12_MO4b1W0P<%01R1/1[P`P`%0LRMPbP_PME3]0P911N[PfP\P9P_A5`Nb14_NRN12_NO4b1W0P<%01R1/1[P`P`%0MRNPbP_PNE3]0P911O[PfP\P9P_A5`Ob14_ORO12_OO4b1W0P<%01R1/1[P`P`%0NROPbP_POE3]0P911P[PfP\P9P_A5`Pb14_PRP12_PO4b1W0P<%01R1/1[P`P`%0ORPPbP_PPE3]0P911Q[PfP\P9P_A5`Qb14_QRQ12_QO4b1W0P<%01R1/1[P`P`%0PRQPbP_PQE3]0P911R[PfP\P9P_A5`Rb14_RRR12_RO4b1W0P<%01R1/1[P`P`%0QRRPbP_PRE3]0P911S[PfP\P9P_A5`Sb14_SRS12_SO4b1W0P<%01R1/1[P`P`%0RRSPbP_PSE3]0P911T[PfP\P9P_A5`Tb14_TRT12_TO4b1W0P<%01R1/1[P`P`%0SRTPbP_PTE3]0P911U[PfP\P9P_A5`Ub14_URU12_UO4b1W0P<%01R1/1[P`P`%0TRUPbP_PUE3]0P911V[PfP\P9P_A5`Vb14_VRV12_VO4b1W0P<%01R1/1[P`P`%0URVPbP_PVE3]0P911W[PfP\P9P_A5`Wb14_WRW12_WO4b1W0P<%01R1/1[P`P`%0VRWPbP_PWE3]0P911X[PfP\P9P_A5`Xb14_XRX12_XO4b1W0P<%01R1/1[P`P`%0WRXPbP_PXE3]0P911Y[PfP\P9P_A5`Yb14_YRY12_YO4b1W0P<%01R1/1[P`P`%0XRYPbP_PYE3]0P911Z[PfP\P9P_A5`Zb14_ZRZ12_ZO4b1W0%01/1[%0YR1/1[Pc%J]RZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7%>^#>#>#>#JR^'IS00P11?9ZX>:R1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1P1PcO1S01O1S02O1S03O1R\O1RfO1RdO1ReO1RgO1RhO1RiO1RjO1RkO1RlO1RmO1RnO1RoO1RpO1RqO1RrO1RsO1RtO1RuO1RvO1RwO1RxO1RyO1RzO1R{O1R|O1R}O1R~O1P1PYP~P1PXP}P1PWP|P1PVP{P1PUPzP1PTPyP1PSPxP1PRPwP1PQPvP1PPPuP1POPtP1PNPsP1PMPrP1PLPqP1PKPpP1PJPoP1PIPnP1PHPmP1PGPlP1PFPkP1PEPjP1PDPiP1PCPhP1PBPgP1PAPeP1P@PdP1P?PfP1P>P\P1P0Q03P1P=Q02P1P7Q01P1P8Pc%HcF6F6F6F6F6F6F6F6F6F6F6F6F6F6F6F6P[P^%H^EZP9CYQ00%X6%=6,Fap-0R[g00QjRc#V%Uc1T:8%P:%O:RcP:1B:ag00RV1N:]R]CG,Ec%R3R1PcP:P]1B:ZR]P]P]P]D8P]P]P]P]D8P]P]P]P]D8P]P]P]P]D8P]P]P]P]D8P]P]P]P]D8P]P]P]P]D8P]P]P]P]D8g00S=1B:^CG,EcP1PcP;P3P3P2P5ESCLCL1bc2P9P6g00SdRcg00TDR2'D1a96=9c2dA`:a8C_b:b;b<X5:W41Fa9P8PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7PZPZPZPZD7/I^P5[[^5:^4[P9P`P`%:4#:#:#:#:#:#:#:R`PbP_P`E3%=4P8P6O4b9b=b8W0X3<P9O1n0110001020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020111100X2<P9O1n0110000020011100X2<P9O1n0110000020011100X2<P9O1n0110000020011100X2<P9O1n0110000020011100X2<P9O1n0110000020011100X2<P9O1n0110000020011100X2<P9O1n0110000020011100X2<P9O1n0110000020011100P9O1W0X3<o"). Qed.

Lemma regs_ok_by_idx : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i allregs32 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0PrintfBufBase ()) ["FPX_1"] "p'0h03Hr0h12Hxh21bi001bh32H0h44__x1h54__x2h62b1h72b2h81nh91rh:1Eh;1Hh<1Rh=7__arithh>4__ffh?8__varmaph@5__withA1ihB2srp;1p;2p;3p;4p;7p;5p;6p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9g002PR0p4p7210g003<R1p4p710R2p8p1003Zp4p710P2p8p10045p4p710g004TR2p4p710p8g00?>j1GTg005gj16Tg006Lj1[Tg0071j1CTg007Oj14TP0j2`Tg0050j12Tg005Oj2QTg0082j3KTg00;Cj41Tg00Tdj1HTg00Udj38Tg00D^j2;Tg009[j30Tg00VQj1:Tg00:5j27Tg00:_j3]Tg00WOj1\Tg00Wmj2YTg00XNj2?Tg00Y7j3XTg00Y`j3WTg00ZIj2VTg00>^j1UTg00[5j3PTg00?^j2OTg00[Uj1NTg00\3j4JTg00@<j1LTg00@Zj1MTg00Ahj2=Tg00BKj4ITg00H?j7>Tg00\Qj5RTg00]5j6STg00C6j1TTg00IFj8iTg00D<j2hTg00E8j2gTg00Edj3fTg00FCj4eTg00]Yj2dTg0095j2<TP1j7aTg00^6j1DTg00_8j2BTg008Uj1FTg00`8j2_TP2j6@Tg00aCj1bTg00bIj2^Tg00cIj3cTg00dHj2ETf0R2#2#2p=Z%22#2#2#2p=5f4R1f3R0f2R3'Ef1R4/B230p=3g00SdR5g00TDR6702p=91E34=002p=Ag00e:g00f9R7#Gg00ORR8#6R9#[#CR:%69#6#6#6#6#CR;#4R<'`g00KOg00O3R=#2R>#2#Z#5#5#5#5#5#5#5,Q2P<P3%4:R?P4g00IjR@g00P7RAg00PU5K:RBC1P1P7P4P0%HARCC1D3[]AA8:2BRDP51;52A8:4B=052P5A8:0B=052P<f6REP1f8RFP5P7P4PCP7%:1RGf7RHPCC1RIn0100000020000D3]0P4A8:3BRJ#9g00Q1RK%42RL%44RMg00QO%43?042g00K1RN1703170430RO[1734173250N%40?034[RP%41?003\OA]342P2n2001000000120000000W7W6W8PP^7M^6L^8KP2P:P1PBg00QjRK%\8,YN1?N>5XN1?N=5WNg00g9'V%UK3P%GKPN1ON3P4%NNCJ%LN%MNRKg00M4R=g00MSR>P>g00N3RLPKP=P>P>PKP=P>P>g00geRMPN1=N8g00hE1=N9CIR9g00NSR8F>PKP=P>P>PMDRES%T>PKP=P>P>PLP9P8F>Gi1hKLP2P31;561g23#9dAfNA4Ceb>b?b@X4NX5N1d24#9A0N43[^4N^5NP217:Bf5RN,7:P3O3b=O4b3A0?0BP?PB%9DP<PFP4f:RDPCD3]0X9?A8:BB#91<;A,;<P<PHPBf9RAPCD3eW0P1P2P4Fab3W0g00hl905JP1%:0RJ%D0O2P<PNP?PJP@PBC1PHP7PJPEPCC1D3P?P?PGP@PBC1P<PHP2P7%:NRBPFPCC1,BAR@CAX2?P2%FG,<:RJ%D1,_GE@P<PEPJPFPID3P?%FB,<:P<PFP2PDP7%:EPAPCC1D3X2?P2PN%bNE@P<PHPNP@CAP2b1b1b1W0n0110000020101P2O1b0b2P<P3P2P11^02D3eX9?Ac034eW;W<WBW:o"). Qed.

Section Entry.
  Variables (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (w can : Z).
  Hypothesis PH : pfH mem sp w can.
  Hypothesis R1 : getr regs 1 = Z_to_bv 64 0x38fd8.
  Hypothesis R2 : getr regs 2 = sp.
  Hypothesis R11 : getr regs 11 = Z_to_bv 64 0.

  Let E := pfE regs sp w can.

  Lemma ev_junk : forall i, (3 <= i < 35)%nat -> ev E i = getr regs (Z_to_bv 5 (Z.of_nat (i - 3))).
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0PrintfBufBase ()) ["FPX_1"; "Entry"] "h04__p1h14__p2h24__x1h34__x2h43H12h53Hi0h67__arithh74__ffh84__p3h98__varmaph:5__with;4cstrh<1ih=1nh>1xh?3z12h@1HhA2HihB1bhC7defaulthD1lhE5lemmahF1mhG1yp&0p;1p;2p;3p;<p;6p;4p;=p;9p;5p;Bp;7p;8p-1R0g00iLR1p4p710p9P0p1000SR2p4p710p9P0P2p4p7210p9P0P2p4p73110p9P0p10011p4p710p9P0g00j9R0p4p710p9p1002Pp4p7210g003<R2p4p710R3p8g00k3R4p4p710P3p8p10045p4p710p1004Tp4p710p8g0050R3j11Tg00kUR5j2\Tg005OR6j2LTg00QOj20Tg00koj2STg009[j32j1ITg008UR7j13Tg006Lj1GTg00;_j1DTg00lFj26Tg00<Yj28Tg00lck20=Tg00mFk30;Tg00D^j2:Tg00GZl<PTg00>BR8j25Tg005gj1?Tg00<=R9j24Tg00mcj6^Tg00=6j4_Tg00=]j1gTg00nLj2eTg00nnj2ETg00XNj2JTg00Y`j3FTg00ZIj2NTg00WOj1lTg00Wmj2kTg00Y7j3jTg00>^j1TTg00[5j3<Tg00?>j1]Tg00?^k20FTg00[Uk10ETg00\3k40DTg00@<k10CTg00@Zk10ATg00Ahj2iTg00AEj2ATg00oHk30<Tg00BKj4CTg00C6k10:Tg00Hcj3XTg00D<k206Tg00E8k205Tg00Edk304Tg00FCk403Tg00okj4bTg0071j1OTg007Oj1aTg0095j27Tg010Vk201Tg0116j2WTg011Mk100Tg012=j1~Tg013<j3}Tg00;Cj4@j1xTg013Yj4UTg014@j1{Tg014oj4RTg015fj3yTg016\j1zTg017Kj6wTg0186j2VTP1l=|Tg00dHj2KTP0l9vTg018bk202Tg019>j4uTg019Zj6tTP2j6cTP4j5sTg01:[k207k108Tg01;Vj1rTg01<Tk209Tg01=Sj2hTg01>Oj2pTg01>llBoTg00G5m<0>Tg00CXj6nTg00H?k70?Tg01?Rk70@Tg01@6j7mTg00IFk80BTf0R4#1#1#1#1p=;%14#1p=qg00P7R2/p4p==g00K1R0f1R1;24p=>g00KOR:P:P:P0P0P0g01@ZP7P7P7f6R;g01A:f5R<f4R=f3R>f2R?P1P4MBop=dP:P:P0P0P3P7P7P>g00KnP?P1P4N<0>p=MP:P0P5P7P8g01AaP<P=P>P?P1P4M<Pp=`P:P0P6P7P9g00LRP<P=P>P?P1P4M<Pp=QA2042p=YP1g00M4R9g00MSR6P6g00N3R8P4Enp=[P0P1g00hEP4CCp=ZP1P9P6P6P8P4g00NSK0?p=9P?P9P6P6P8P1P4K0@p=BP?P9P6P6P8P1P4Fmp=fP>P9P6P6P8P?P1P4L0Bp=Hg00O3R9#1R5#1R3#1R@/\4%1@#;#;#;#;#;#;#;RA#1#qRB,L4'01S1@RC#1RD#1RE#1RF=2:1%31RGg00ORRH#G#DRI'6#=RJ%DHRK'8RL/8KRM/8KRN/>GP:P0%I:ROP7%I0%34R7,>GA2:1420=1440;XG:X>:PFPN184KX>0RNPEPMPNPDPLPNPCPJ1614#=XF0X=0RJP1PG1:0GRNP@PI1:0IRLFdCMCMCMP1PGPNM<P1\@1RD1L1BRM'015IGRE%?HRF#?#?RP#G#G#DRQ,4GRR'0RSPDPMPEPRP@PIPLP1PGPNE`P1PGPNPBPQ1:0QRNEQE^P4C_PS%g?%3?RS,52%3>RG/6IRR,e2142R%=RRE/>R'015R2%YE'0'E%3=/6IRE#=RRP0p-0RMg00QjRD1J03R31J051J09R55F05F0g00g9RT'NRU1J0@%lH,k0=j03=F05R55F0/NT1N5T%TDR55<D5<D3<%]DRTP020F0?P1&0E0H0DR3&0C0RV&0A0RW1[W=1i0HRH1i0FRX1A0IRY60<0RZ'Z,9W5BWR[P0PZg00RVRZ1A02R\CC,9W1ZH\,9WR\5BW5fW&0:6R6PWP0PYPZPXCC,9W1[W<RZ5BWP61A0KRY9X0H=X0Y=X0Y/ZX,9WCHCH206W8R8P4P?g00SdRYg00TDR]':2054?=2Y]dB04021H03R]b7b9b:X20X30X0MW1161IRY,>4,0?R^15Y2%Y4RY'0'E15I?/0=18?K/8K/8K/>>[[^20^30^0M^1MP4%3;RK/4Q16KI,42PKP1P?P=O6b6b?b4b;b5Cb%?P#?RK#?#OR_#aR`p,2spp,1w,7_p,3can,7_%T`5<`5<`5<`Ra+01Rb/WC=2:1RcePc1S?@Rc,WbRd=2:?P`%I`Re&00`P`P>p,4regsRf#~Rg9}`aRh17_2R_C@P`1S>@Ri,WbRbPhP_C@%]`RjP`^C`Rk]DRl^=:RmP:PlPOPjPk%IjP`P`PePeCURnCURoCURpP:PlPoPjPkPnP`P`Pe%{`CRCRCR9ymp%x`P>PbP:PO%z:PbP>P4EwPhPh1VjhP_P_1V`_M=|%GF#ORF%3i'7,KfRiPi1V`iM9vWEP4P`P`PcPgP_C@RjA2`4iXB`RiP`%3c,7F,KfRbPi1:`bP`PcP:P`17F7,KfX<:R72029ACuP_C@P`P7PcPAP_1LcA16SI#=R7%DKRK'4PcP7PJP?PS1:0SRJP@PIPLFdPAPK1:0KEQ1\@?RA1L?BR7'015ISR914SQRi'0ROPAP7P9PiP@PIPLP?PSPJE`P?PSPJPBPQPNEQE^P1C_PO%g>152G1e2E142E1>RE'015E2%YR'0'E%3</6I#=P0A<DU5PTP3PVPWABWZ\9fW[P6PW1[W;P0PXg00S=RX1A0QCC,9W5BWP6P0PHPX1A0KCC,9WCHCHP8P]b7b9b:X20X30X0MX1MX8M10>Y,E^14?Q,0<14?K[[^20^30^0M^1M^8MP4f7#3R4,5I164IRI/52142IP4P1P?P=O7b6b?b4b;b5CbEtEcA2`jbeP`PdPhP_C@P`PaPgP_PcDsEcO2b@207h1%3C,7F,KfRf52`e&08h%OP#a#]#T#r+09/h1=2`fep,1E/h1=2`feWAX<:o"). Qed.

  Lemma ev0 : ev E 0 = sp.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0PrintfBufBase ()) ["FPX_1"; "Entry"] "p;1p;2p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210p1003<p4p710R0p8p1003Zp4p710P0p8p10045p4p710p1004Tp4p710p8g005gj10Tg0071j13Tg007Oj12Tg00D^j21Tg00OR#0#0#0#0#0#0#3#2p,2sp'1o"). Qed.
  Lemma ev1 : ev E 1 = Z_to_bv 64 w.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0PrintfBufBase ()) ["FPX_1"; "Entry"] "p;1p;2p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210p1003<p4p710R0p8p1003Zp4p710P0p8p10045p4p710p1004Tp4p710p8g005gj10Tg0071j14Tg007Oj12Tg0095j21Tg00D^j23Tg00OR#0#0#0#0#0#0#4R0#2p,1w,10'3o"). Qed.
  Lemma ev2 : ev E 2 = Z_to_bv 64 can.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0PrintfBufBase ()) ["FPX_1"; "Entry"] "p;1p;2p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210p1003<p4p710R0p8p1003Zp4p710P0p8p10045p4p710p1004Tp4p710p8g005gj10Tg0071j14Tg007Oj12Tg0095j21Tg00D^j23Tg00OR#0#0#0#0#0#0#4R0#2p,3can,10'3o"). Qed.

  Lemma pf_regs_ok : regs_ok E pf_sr regs.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0PrintfBufBase ()) ["FPX_1"; "Entry"] "p'0h02Hih11ni001nh23Hi0h37__arithh44__ffh58__varmaph65__with71bh84__p1h94__x1h:1ih;4cstrh<1xp%0p;1p;2p;3p;4p;6p;<p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210g003<R0p4p710R1p8p1003Zp4p710P1p8p10045p4p710p1004Tp4p710p8g0050R1j10Tg005OR2j21Tg005gj1ETg0071j1UTg007Oj1[Tg006Lj1FTg0082j3WTg00Tdj1jTg01BCj1dTg00;Cj4MTg00_8j2TTg00;_j1BTg00kUR3j2ATg00>BR4j27Tg00<=R5j23Tg00QOj28Tg00mcj6<Tg00=6j49Tg00>^j1fTg00?>j1eTg00[Uj1cTg00@<j1bTg00@Zj1aTg00D<j2`Tg00D^j2STg00E8j2_Tg009[j3LTg00Edj3]Tg00FCj4\Tg008UR6j1RTg00<Yj2KTg00=]j1wTg00?^j2vTg00AEj2ZTg00Ahj2uTg00C6j1sTg00CXj6qTg01CAj4pTg00dHj2OTg00koj2mTg0095j2lTg00GZl<VTg00BKj4NTg00H?j7QTg01?Rj7kTg00okj4nTg01DMj2oTg01=Sj2iTP0j6hTg00G5l<YTg00Hcj3PTg00IFj8gTf7R0f6R7f5R8f4R9g00IjR:f3R;CM'Of2R<g00f9R=f1R>g01ERR?f0R@CM'T3Lp=21O<>=L;@p=^1m>@#R,l<,O;p=>g00PURA9W<>,O;=L9@p=@%F@#Bp=Gg00K1RB/S@p=5g00KORCPBP3P6P4g01AaP8P9P;P<P>P@M<Vp=?PCPBP2P6P5g00LRP8P9P;P<P>P@M<Vp=41ZB@p=6P7g00M4R5g00MSR2P2g00N3R4P8P5P2P2P4PBP9g00RVR3P;CNg00NSRDFQP<P5P2P2P4PBP>g00S=REP@CNPDFQFkp=:189;P<P>P@Cn,o8p=;P0P7P81S9;1i<>P@Ehp==%E@#Bp=J1K9;/K</K>/K@p=DPCPCPBPBP1P6P6P7g00KnR7P8P9PCPCPBPBP1P6P6P;P7P<P>P@M<YM<Yp=CP<P5P2P2P4PBP>P3P@CNPDFQp=tAPB9;=PB<=PB>=PB@p=IP<P5P2P2P4PBP>PEP@CNPDFQp=rP;P5P2P2P4P<P>P@Ggp=X%0@#0#0#0p=Hp,1ERDP?p,4regsREg00O3R3#0R7#0R6#0R1#0R8#0R0#0RF#0RG#0RH#0RI#0RJ#0RK#0RL#0RM#0RN#0RO#0RP#0RQ#0RR#0RS#0RT#0RU#0RV#0RW#0RX#0RY#0RZ#0R[#0R\#0R]#0R^#0R_#0R`,1@RaPCg00ORRb#ERc#ERd#ERe#ES00#ERf#E#U#[RgPE%FcRc#URh#[RiP>g00P7Rj=WhARAPDP>%jjRkG2^0aP>113`%dEPgPEPiP3P:PACMP=P3P?PkCM,TDC^eW0PC%0@R?/1`PgPEPi%0>S01PAPDQ01PkG2]0P@117`p,2R1PgPEPiP7PAPDP7PkG2eW0PC%0?R?/1`PgPEPiQ01#0S02PAPDQ02PkG2]0P@116`p,2R2PgPEPiP6PAPDP6PkG2eW0PC%0?R?/1`PgPEPiQ02#0S03PAPDQ03PkG2]0P@111`R6PgPEPhPFP1C>R7PgPEPh%FbR3#BR=P@D@X7gPgP7PDPFPF1A1FR7%0`R:#0Ra#0Rl,1FRm%E3Rn#BRo,7=Rp%FeRq#GRr,3oRs'8RtP7PmPpPsP1P=%5=RsPFPo%5oRpE?PFPoPpPlPr%5rRmE4E<P6%BfRf,3=R6P1P=PsP`Pf%5fR7E4P@C9P6g00QjR6#fRu%e6R6%cBRv%bBRw%aBRxPx%6=Ry%6oRzPxPz%6rRzF:1`x4R{P@P<g00SdR|g00TDR}'S1_@<=L|}dA]Bj>C\R}b4b5b6PtP@b3b2E;G=PgPEPiP1PAPDP1PkG2eW0PC%0?R?/1`PgPEPiQ03#0S04PAPDQ04PkG2]0P@118`S05PgPEPhPGP1C>RtPgPEPh%BdR|P@D@X7gPgPtPDPGPG1A1GS0611GlS07%F3R3#BRt,7=S0813trR~'8S09Q06Q07Q08P~P1P=PsPGPt%5tS08E?PGPtQ08PlPrPmE4E<Q0513|fR~P8P|%5|P`PfP7E4P@C9P~PuP6PvPwPxPxPy%6tR~PxP~PzF:P{P}b4b5b6Q09P@b3b2E;G=PgPEPiP8PAPDP8PkG2eW0PC%0?R?/1`PgPEPiQ04#0R8PAPDP8PkG2]0P@110`S09PgPEPhPHP1C>R~PgPEPh%BcR|P@D@X7gPgP~PDPHPH1A1HS0511HlS07%BeRe,7=S0613erR~'8S0:Q05Q07Q06P~P1P=PsPHPe%5eS06E?PHPeQ06PlPrPmE4E<Q0913|fR~P0P|%5|P`PfP7E4P@C9P~PuP6PvPwPxPxPy%6eR~PxP~PzF:P{P}b4b5b6Q0:P@b3b2E;G=PgPEPiP0PAPDP0PkG2eW0PC%0?R?/1`PgPEPi%08R0PAPDP0PkG2]0P@11F`S0:PgPEPhPIP1C>R~PgPEPhPoP@D@X7gPgP~PDPIPI1A1IS0911IlS07%FdRd#BR~,7=S0513~rR|'8S0;Q09Q07Q05P|P1P=PsPIP~%5~S05E?PIP~Q05PlPrPmE4E<Q0:13ofR|PFPoPpP`PfP7E4P@C9P|PuP6PvPwPxPxPy%6~R|PxP|PzF:P{P}b4b5b6Q0;P@b3b2E;G=PgPEPiPFPAPDPFPkG2eW0PC%0?R?/1`PgPEPi%00RFPAPDPFPkG2]0P@11G`S0;PgPEPhPJP1C>R|PgPEPhPtP@D@X7gPgP|PDPJPJ1A1JS0:11JlS07%EcR|#BRp,7=S0913prRo'8S0<Q0:Q07Q09PoP1P=PsPJPp%5pRoE?PJPpPoPlPrPmE4E<Q0;13tfS0;PGPtQ08P`PfP7E4P@C9Q0;PuP6PvPwPxPxPy%6pRtPxPtPzF:P{P}b4b5b6Q0<P@b3b2E;G=PgPEPiPGPAPDPGPkG2eW0PC%0?R?/1`PgPEPi%0FRGPAPDPGPkG2]0P@11H`S0<PgPEPhPKP1C>RtPgPEPhPeP@D@X7gPgPtPDPKPK1A1KS0;11KlS08%FcRc#BRt,7=S0913trS07'8S0:Q0;Q08Q09Q07P1P=PsPKPt%5tS07E?PKPtQ07PlPrPmE4E<Q0<13efS0<PHPeQ06P`PfP7E4P@C9Q0<PuP6PvPwPxPxPy%6tRtPxPtPzF:P{P}b4b5b6Q0:P@b3b2E;G=PgPEPiPHPAPDPHPkG2eW0PC%0?R?/1`PgPEPi%0GRHPAPDPHPkG2]0P@11I`S0:PgPEPhPLP1C>RtPgPEPhP~P@D@X7gPgPtPDPLPL1A1LS0<11LlS06%EnRt#BRe,7=S0713erS09'8S08Q0<Q06Q07Q09P1P=PsPLPe%5eS09E?PLPeQ09PlPrPmE4E<Q0:13~fS0:PIP~Q05P`PfP7E4P@C9Q0:PuP6PvPwPxPxPy%6eR~PxP~PzF:P{P}b4b5b6Q08P@b3b2E;G=PgPEPiPIPAPDPIPkG2eW0PC%0?R?/1`PgPEPi%0HRIPAPDPIPkG2]0P@11J`S08PgPEPhPMP1C>R~PgPEPhPpP@D@X7gPgP~PDPMPM1A1MS0:11MlS05%FnRn#BR~,7=S0713~rS06'8S0<Q0:Q05Q07Q06P1P=PsPMP~%5~S06E?PMP~Q06PlPrPmE4E<Q0813pfS08PJPpPoP`PfP7E4P@C9Q08PuP6PvPwPxPxPy%6~RoPxPoPzF:P{P}b4b5b6Q0<P@b3b2E;G=PgPEPiPJPAPDPJPkG2eW0PC%0?R?/1`PgPEPi%0IRJPAPDPJPkG2]0P@11K`p,3R11PgPEPiPKPAPDPKPkG2eW0PC%0?R?/1`PgPEPi%0JRKPAPDPKPkG2]0P@11L`S0<PgPEPhPOP1C>RoPgPEPhPeP@D@X7gPgPoPDPOPO1A1OS0811OlS07%F3Ro#BRp,7=S0513prS0:'8S0;Q08Q07Q05Q0:P1P=PsPOPp%5pS0:E?POPpQ0:PlPrPmE4E<Q0<13efS0<PLPeQ09P`PfP7E4P@C9Q0<PuP6PvPwPxPxPy%6pRePxPePzF:P{P}b4b5b6Q0;P@b3b2E;G=PgPEPiPLPAPDPLPkG2eW0PC%0?R?/1`PgPEPi%0KRLPAPDPLPkG2]0P@11M`S0;PgPEPhPPP1C>RePgPEPhP~P@D@X7gPgPePDPPPP1A1PS0<11PlS09Q00#BRe,7=S0513erS07'8S08Q0<Q09Q05Q07P1P=PsPPPe%5eS07E?PPPeQ07PlPrPmE4E<Q0;13~fS0;PMP~Q06P`PfP7E4P@C9Q0;PuP6PvPwPxPxPy%6eR~PxP~PzF:P{P}b4b5b6Q08P@b3b2E;G=PgPEPiPMPAPDPMPkG2eW0PC%0?S08/1`PgPEPi%0LR?PAPDP?PkG2]0P@11N`S0;PgPEPhPQP1C>RMPgPEPh%E3R3#BR~P@D@X7gPgPMPDPQPQ1A1QS0611QlS05%BqRM,7=S0913MrS0<'8S0=Q06Q05Q09Q0<P1P=PsPQPM%5MS0<E?PQPMQ0<PlPrPmE4E<Q0;13~fS0;PNP~%5~P`PfP7E4P@C9Q0;PuP6PvPwPxPxPy%6MR~PxP~PzF:P{P}b4b5b6Q0=P@b3b2E;G=PgPEPiPNPAPDPNPkG2eW0PCQ08#0S08/1`PgPEPi%0?RNPAPDPNPkG2]0P@11O`S0=PgPEPhPRP1C>R~PgPEPhPpP@D@X7gPgP~PDPRPR1A1RS0;11RlS09%JdR~,7=S0513~rS06'8S0>Q0;Q09Q05Q06P1P=PsPRP~%5~S06E?PRP~Q06PlPrPmE4E<Q0=13pfS0=POPpQ0:P`PfP7E4P@C9Q0=PuP6PvPwPxPxPy%6~RpPxPpPzF:P{P}b4b5b6Q0>P@b3b2E;G=PgPEPiPOPAPDPOPkG2eW0PCQ08#0RO/1`PgPEPi%0NRpPAPDPpPkG2]0P@11P`S08PgPEPhPSP1C>S0>PgPEPhPeP@D@X7gPgQ0>PDPSPS1A1SS0>11SlS0=%GdRd,7=S0:13drS05'8S09Q0>Q0=Q0:Q05P1P=PsPSPd%5dS05E?PSPdQ05PlPrPmE4E<Q0813efS08PPPeQ07P`PfP7E4P@C9Q08PuP6PvPwPxPxPy%6dRePxPePzF:P{P}b4b5b6Q09P@b3b2E;G=PgPEPiPPPAPDPPPkG2eW0PC%0ORO/1`PgPEPi%0pRPPAPDPPPkG2]0P@11Q`S09PgPEPhPTP1C>RePgPEPhPMP@D@X7gPgPePDPTPT1A1TS0811TlS07%J|Re,7=S0:13erS0='8S0>Q08Q07Q0:Q0=P1P=PsPTPe%5eS0=E?PTPeQ0=PlPrPmE4E<Q0913MfS09PQPMQ0<P`PfP7E4P@C9Q09PuP6PvPwPxPxPy%6eRMPxPMPzF:P{P}b4b5b6Q0>P@b3b2E;G=PgPEPiPQPAPDPQPkG2eW0PC%0ORO/1`PgPEPi%0PRQPAPDPQPkG2]0P@11R`S0>PgPEPhPUP1C>RMPgPEPhP~P@D@X7gPgPMPDPUPU1A1US0911UlS0<%G|R|,7=S0:13|rRM'8S07Q09Q0<Q0:PMP1P=PsPUP|%5|RME?PUP|PMPlPrPmE4E<Q0>13~fS0>PRP~Q06P`PfP7E4P@C9Q0>PuP6PvPwPxPxPy%6|R~PxP~PzF:P{P}b4b5b6Q07P@b3b2E;G=PgPEPiPRPAPDPRPkG2eW0PC%0ORO/1`PgPEPi%0QRRPAPDPRPkG2]0P@11S`S07PgPEPhPVP1C>R~PgPEPhPdP@D@X7gPgP~PDPVPV1A1VS0>11VlS06%JcR~,7=S0:13~rS0<'8S09Q0>Q06Q0:Q0<P1P=PsPVP~%5~S0<E?PVP~Q0<PlPrPmE4E<Q0713dfS07PSPdQ05P`PfP7E4P@C9Q07PuP6PvPwPxPxPy%6~RdPxPdPzF:P{P}b4b5b6Q09P@b3b2E;G=PgPEPiPSPAPDPSPkG2eW0PC%0ORO/1`PgPEPi%0RRSPAPDPSPkG2]0P@11T`S09PgPEPhPWP1C>RdPgPEPhPeP@D@X7gPgPdPDPWPW1A1WS0711WlS05%GcRc,7=S0:13crRd'8S06Q07Q05Q0:PdP1P=PsPWPc%5cRdE?PWPcPdPlPrPmE4E<Q0913efS09PTPeQ0=P`PfP7E4P@C9Q09PuP6PvPwPxPxPy%6cRePxPePzF:P{P}b4b5b6Q06P@b3b2E;G=PgPEPiPTPAPDPTPkG2eW0PC%0ORO/1`PgPEPi%0SRTPAPDPTPkG2]0P@11U`S06PgPEPhPXP1C>RePgPEPhP|P@D@X7gPgPePDPXPX1A1XS0911XlS0=%JtRe,7=S0:13erS05'8S07Q09Q0=Q0:Q05P1P=PsPXPe%5eS05E?PXPeQ05PlPrPmE4E<Q0613|fS06PUP|PMP`PfP7E4P@C9Q06PuP6PvPwPxPxPy%6eRMPxPMPzF:P{P}b4b5b6Q07P@b3b2E;G=PgPEPiPUPAPDPUPkG2eW0PC%0ORO/1`PgPEPi%0TRUPAPDPUPkG2]0P@11V`S07PgPEPhPYP1C>RMPgPEPhP~P@D@X7gPgPMPDPYPY1A1YS0611YlS0:%GtRt,7=RM13trR|'8S0=Q06Q0:PMP|P1P=PsPYPt%5tR|E?PYPtP|PlPrPmE4E<Q0713~fRMPVP~Q0<P`PfP7E4P@C9PMPuP6PvPwPxPxPy%6tRMPxPMPzF:P{P}b4b5b6Q0=P@b3b2E;G=PgPEPiPVPAPDPVPkG2eW0PC%0ORO/1`PgPEPi%0URVPAPDPVPkG2]0P@11W`S0=PgPEPhPZP1C>RMPgPEPhPcP@D@X7gPgPMPDPZPZ1A1ZS0<11ZlS07%JnRM,7=S0:13MrR~'8S06Q0<Q07Q0:P~P1P=PsPZPM%5MR~E?PZPMP~PlPrPmE4E<Q0=13cfS0=PWPcPdP`PfP7E4P@C9Q0=PuP6PvPwPxPxPy%6MRdPxPdPzF:P{P}b4b5b6Q06P@b3b2E;G=PgPEPiPWPAPDPWPkG2eW0PC%0ORO/1`PgPEPi%0VRWPAPDPWPkG2]0P@11X`S06PgPEPhP[P1C>RdPgPEPhPeP@D@X7gPgPdPDP[P[1A1[S0=11[lS0:%GnRn,7=Rd13nrRc'8S07Q0=Q0:PdPcP1P=PsP[Pn%5nRcE?P[PnPcPlPrPmE4E<Q0613efRdPXPeQ05P`PfP7E4P@C9PdPuP6PvPwPxPxPy%6nRdPxPdPzF:P{P}b4b5b6Q07P@b3b2E;G=PgPEPiPXPAPDPXPkG2eW0PC%0ORO/1`PgPEPi%0WRXPAPDPXPkG2]0P@11Y`S07PgPEPhP\P1C>RdPgPEPhPtP@D@X7gPgPdPDP\P\1A1\S0511\lS06%J3Rd,7=S0:13drRe'8S0=Q05Q06Q0:PeP1P=PsP\Pd%5dReE?P\PdPePlPrPmE4E<Q0713tfS07PYPtP|P`PfP7E4P@C9Q07PuP6PvPwPxPxPy%6dR|PxP|PzF:P{P}b4b5b6Q0=P@b3b2E;G=PgPEPiPYPAPDPYPkG2eW0PC%0ORO/1`PgPEPi%0XRYPAPDPYPkG2]0P@11Z`S0=PgPEPhP]P1C>R|PgPEPhPMP@D@X7gPgP|PDP]P]1A1]S0711]lS0:%G3R3,7=R|133rRt'8S06Q07Q0:P|PtP1P=PsP]P3%53RtE?P]P3PtPlPrPmE4E<Q0=13MfR|PZPMP~P`PfP7E4P@C9P|PuP6PvPwPxPxPy%63R|PxP|PzF:P{P}b4b5b6Q06P@b3b2E;G=PgPEPiPZPAPDPZPkG2eW0PC%0ORO/1`PgPEPi%0YRZPAPDPZPkG2]0P@11[`S06PgPEPhP^P1C>R|PgPEPhPnP@D@X7gPgP|PDP^P^1A1^S0=11^lS0:%JoR|,7=R~13|rRM'8S07Q0=Q0:P~PMP1P=PsP^P|%5|RME?P^P|PMPlPrPmE4E<Q0613nfR~P[PnPcP`PfP7E4P@C9P~PuP6PvPwPxPxPy%6|R~PxP~PzF:P{P}b4b5b6Q07P@b3b2E;G=PgPEPiP[PAPDP[PkG2eW0PC%0ORO/1`PgPEPi%0ZR[PAPDP[PkG2]0P@11\`S07PgPEPhP_P1C>R~PgPEPhPdP@D@X7gPgP~PDP_P_1A1_S0611_lR~%GoRo,7=Rc13orRn'8S0:Q06P~PcPnP1P=PsP_Po%5oRnE?P_PoPnPlPrPmE4E<Q0713dfRcP\PdPeP`PfP7E4P@C9PcPuP6PvPwPxPxPy%6oRcPxPcPzF:P{P}b4b5b6Q0:P@b3b2E;G=PgPEPiP\PAPDP\PkG2eW0PC%0ORO/1`PgPEPi%0[R\PAPDP\PkG2]0P@11]`S0:PgPEPhP`P1C>RcPgPEPhP3P@D@X7gPgPcPDP`P`1A1`Rc11`lRe17=fRd13frR~'8S07PcPePdP~P1P=PsP`PfP7E?P`PfP7PlPrPmE4E<Q0:133fR~P]P3PtP`PfP7E4P@C9P~PuP6PvPwPxPxPy%6fR~PxP~PzF:P{P}b4b5b6Q07P@b3b2E;G=PgPEPiP]PAPDP]PkG2eW0PC%0ORO/1`PgPEPi%0\R]PAPDP]PkG2]0P@11^`S07PgPEPhP:P1C>RtPgPEPhP|P@D@X7gPgPtPDP:P:1A1:Rt11:lR3Q00#GRd,7=Re13drRc'8S00PtP3PePcP1P=PsP:Pd%5dRcE?P:PdPcPlPrPmE4E<Q0713|fRcP^P|PMP`PfP7E4P@C9PcPuP6PvPwPxPxPy%6dRdPxPdPzF:P{P}b4b5b6Q00P@b3b2E;G=PgPEPiP^PAPDP^PkG2eW0PC%0ORO/1`PgPEPi%0]R^PAPDP^PkG2]0P@11_`RdPgPEPhPaP1C>RcPgPEPhPoP@D@X7gPgPcPDPaPa1A1aRc11alRh%JqRq,7=RM13qrR|'8R:PcPhPMP|P1P=PsPaPq%5qRsE?PaPqPsPlPrPmE4E<Pd13ofRdP_PoPnP`PfP7E4P@C9PdPuP6PvPwPxPxPy%6qRqPxPqPzF:P{P}b4b5b6P:P@b3b2E;G=PgPEPiP_PAPDP_PkG2eW0%0O/1`%0^RO/1`%R>R_%BbR:P:P:P:DDP:P:P:P:DDP:P:P:P:DDP:P:P:P:DDP:P:P:P:DDP:P:P:P:DDP:P:P:P:DDP:P:P:P:DD/3fS00PO1K@:X<BROPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOPOP_O1S07O1S0:O1S06O1S0=O1S05O1S0<O1S09O1S0>O1S08O1S0;O1RzO1RqO1RyO1RvO1RdO1RnO1RoO1RmO1RrO1RlO1RsO1RaO1R=O1R1O1R|O1RMO1RhO1RcO1ReO1R3O1RtO1POP^PtPOP]P3POP\PePOP[PcPOPZPhPOPYPMPOPXP|POPWP1POPVP=POPUPaPOPTPsPOPSPlPOPRPrPOPQPmPOPPPoPOPpPnPOPNPdPOP?PvPOPLPyPOPKPqPOPJPzPOPIQ0;POPHQ08POPGQ0>POPFQ09POP0Q0<POP8Q05POQ04Q0=POQ03Q06POQ02Q0:POQ01Q07POP>P_%5_FCFCFCFCFCFCFCFCFCFCFCFCFCFCFCFCP`PfP7E4P@C9Q00%w<%R<,7jp-0R7PuP61vB>PwPx1ZBj1uBbRb5tx%s2RwPxPb%6:RbPbPbPbDIPbPbPbPbDIPbPbPbPbDIPbPbPbPbDIPbPbPbPbDIPbPbPbPbDIPbPbPbPbDIPbPbPbPbDI=rx~PwPxP5P2P2P4P;EqCXCXP{P}b4b5b6X9BW817j@P>P:P:P:P:DDP:P:P:P:DDP:P:P:P:DDP:P:P:P:DDP:P:P:P:DDP:P:P:P:DDP:P:P:P:DDP:P:P:P:DD/3fP;[[^9B^87P@PgPEPi%H9#H#H#H#H#H#H#HRiPAPDPiPkG2%R9P>P<O4b3b;b2W0X:CP@O1n0110001020111100X1CP@O1n0110001020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020011100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020111100X1CP@O1n0110000020011100X1CP@O1n0110000020011100X1CP@O1n0110000020011100P@O1W0X:CCpo"). Qed.

  Lemma wseg_data : wseg_ok RSEGS (Z_to_bv 64 0xc6000) 212992 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0PrintfBufBase ()) ["FPX_1"; "Entry"] "p;2p;1p;3p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210p1003<p4p710R0p8p1003Zp4p710P0p8p10045p4p710p1004Tp4p710p8g00D^j2=Tg0071j16Tg006Lj12Tg005gj11Tg00;_j1;Tg0095j2:Tg01FUj13Tg01G3j14Tg01GQj17Tg01Goj15Tg01HLj18Tg01Hkj39Tg009[j3<Tf0#1#1p=0g00SdR0g00TDR1'=g01Iig00ORR2#0#0#0#6%22#1#0#2#2#1#0#0#0#0#0#0#;':g01KR#3#4#4#3#7#3#5#839=<01do"). Qed.

  Lemma data_store_ok : forall m a n,
    0xc6000 <= a -> a + Z.of_nat n <= 0xfa000 -> store_ok RSEGS m (Z_to_bv 64 a) n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0PrintfBufBase ()) ["FPX_1"; "Entry"] "h04__x1h17__arithh24__ffh38__varmaph45__with54cstrh64__x2h72Hah87__sat12h97__sat13h:1zh;2Hnh<1ah=1mh>1np;1p;2p;3p;4p;6p;>p;7p;8p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210g003<R0p4p710R1p8p1003Zp4p710P1p8p10045p4p710p1004Tp4p710p8g005gj10Tg0071j1HTg007Oj1CTg01L0j1jTg006Lj12Tg00;_j1<Tg00>Bj21Tg008Uj18Tg00<Yj2:Tg0095j2FTg01FUj1?Tg01G3j1MTg01GQj1iTg01Goj1gTg01HLj1cTg00=]j1^Tg01LRj2\Tg00<=j29Tg01M:j2ZTg01MWj3YTg00>^j1XTg00?>j1WTg00[Uj1VTg00@<j1UTg00@Zj1TTg00AEj2;Tg01N;j3PTg00BKj4=Tg00D<j2OTg00D^j2DTg00E8j2QTg009[j3NTg00Edj3RTg00FCj4STg00QOj2LTg01N^j2GTg00?^j2ETg00Ahj2JTg00C6j1hTg00:5j2fTg0050j1ATg00XNj2@Tg00Y`j3ITg00ZIj2bTg00[5j3aTg00\3j4_Tg00Hcj3`TP0j6KTg01O[l>]Tg00H?j7dTg01?Rj7eTg00IFj8[Tf0R0#0#0p=>%00#0#0#0p=5g00P7R1/10p=4g00K1R2f1R3g00RVP0C=p=6P3g00M4R4g00MSR5P5g00N3R6P0g00NSFdp=3f2R7P4P5P5P6P3P0Fep=Bf3R8P4P5P5P6P7P3P0G[p=7g00ORR4#0R9#>R:#0#>R;#HR<#C%H:#C#j[g00KO%24#0#>#2#2#0#5#5#5#<R:/13R=%83,:7%24#2#2#2#0#2#0#5#5#5#<R>'1g01Iif4R?1F<:1F<8R@g01KR#?#M#M#?#i#?#g#cP7P:P>%^7RA%87#4RB%<9RC%<;R;'\RD191C%4;1ZC;RE,91[[RF%4CRGg01P_RHAYC;3UW7R;%4E\H^7GRGg00QjRH#XRI%WHRJ%V2RK%U2RL%T2RM1;21RN1;2:RO'6,3MP2POg00S=RP1;2C=P2<RCC=,3M3B1OM6R6P0P7g00SdRQg00TDRR'D1Q07=NQRdAR213CSR1b2b3b4%4:19:E'LP0b1b8b9b5,G:1D2>PAPBPDPFP;PGPIPJPKPL1;2>RR/6C,3MP6P1b2b3b411>ERQP0b1b8b9b5PQeg01Q;P2P811:0RQX:2PAPBPIPJ1E23PLPM1J24R4,6O,3MRO%h5R5POC7P6P1b2b3b4X02P=\Q^02P0f5RQP8O2b1b51f<@R@PAPBPDPFP;PGg00O3RG#A#AR;#A,@21@2;1@2G5I25I2g00g9'b=aHIPJP21E27P3PKC_RKPLPM1J29R9,6N,3MP5PMA`249/6R,3MRRP5PMPOP516N4,3MP2P4PPPCC=,3M5BMC7C7C7P6P1b2b3b4X02X62%431:37/1>RC11:7%48198E'L[[[^02^62P0f6#8f7P8P?PQO5b1b8b9b5,G8REEKP2P8%88,:0/1>X:2PAPBPIPJPKPLPMPRP5PRC7P6P1b2b3b4X02X621:03/1>PC[^02^62P0%8?PQP7O3b1b5P@PEEKM>]W;W7W>X<2W=o"). Qed.

  Lemma pf_know_ok : know_ok RSEGS E mem pf_kn.
Proof.
ltac2:(KReplay.run1 (kr_t_Ns0PrintfBufBase ()) ["FPX_1"; "Entry"] "p'0h07__arithh14__ffh27__sat66h37__sat67h47__sat68h58__varmaph65__with71zh84__x1h91mh:1dh;4__x2h<4__p1h=4__x3h>1bh?4cstrh@1xhA2HahB2HdhC2HmhD4__x4hE3HsphF5Pbsz0hG5Pcan0hH6Pcan65hI7Pflags0hJ5Pimg0hK5Plbf0hL6Plock0hM5Psp17hN6PspHi0hO6PspLo0hP5Pstk0hQ3Pw0hR6Pwend0hS6Pwpos0hT2Z0hU1ihV1nhW1phX1yi004Pbszi014Pcani026Pcan64i036Pflagsi044Pimgi054Plbfi065Plocki075Psp16i085PspHii095PspLoi0:4Pstki0;2Pwi0<5Pwendi0=5Pwposp%0p&0p;4p;1p;2p;3p;6p;7p;9p;8p;@p;5p;<p;Bp-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9P0p1001Xp4p710p9p1002Pp4p7210g003<R0p4p710R1p8p1003Zp4p710P1p8p10045p4p710p1004Tp4p710p8g01RBR1k40gTg01SEk40fTg005gj14Tg0071k10@Tg00:5j2KTg00;_j1?Tg01TDj2pTg00>BR2j20Tg006Lj12Tg01Tdk40VTg00<=j2TTg007Ok103Tg01L0j1~Tg0095j2ITg00C6j1}Tg009[j3_Tg00?>j1zTg0050j1PTg00QOj28Tg01M:k20DTg01U^k10BTg00D^j2UTg01VUk30aj4uTg01WVj1tTg01XVk20]Tg01YXk30?Tg00WOk10ZTg01ZZj2FTg01[[j2sTg01\]k20YTg00Tdj1gTg01]_j3[Tg00>^k10:Tg01^ak20XTg01LRk20WTg01MWk30UTg00[Uk10TTg00@<k10STg00@Zk10QTg00AEk206Tg00D<k20PTg00E8k20OTg00Edk30MTg00FCk40LTg01=Sk202TP0j6\Tg00_8j2OTg01_Rk70KTg00?^j2iTg00Ahj2dTg01`Rj7|Tg01aRm90JTg01N;k30ITg01bSk80HTg00kUR0j2mTg00okj4CTg00<YR3j21Tg008UR4j1]Tg01cQk10GTg01cok40FTg01dRl@VTg01N^j2vTg00=]k10ETg00\3j4`Tg01eQj5wTg01f\k400Tg01g7k101Tg01h7k10=Tg01i6k305Tg01j2k204Tg00XNj2qTg00Y`k309Tg00ZIk20RTg00[5k307Tg01k0k20ATg01kQk20eTg01lYk20dTg01m;k40cTg00BKj4oTg00H?j7nTg01?Rk70>Tg00IFk80^Tg00GZm<0<Tg00Hck30;Tg00G5m<0\Tg01>lmB0_Tg01mlk40`Tg00CXk60[Tg01nlk60bTf0R5#4#4p==g00K1R6g00P7R77_5p=j%25#2p=G%25#2#4#2p=b%25#4#4#4p=;%45#2p=L%45#4#4#?p=B%25#2#2#2p=Z%25#2#2#2#2#2#2#2p=l%45#4#4#4p=Jf2R8f1R9'0/85p=S%45#2#2#4p=c20e95-0d8p=Hf5R:g01IiR;f4R<f3R=/I8P9H0c;_5p=<%25#4p=a%45#?p=x%25#4#2#4p=k1079/85p>0C1075p=3g01oMS00@0795p=@20665p=7P6P9g00S=P5Cop=fP9g00M4R>g00MSR?P?g00N3R@P5g00NSRAFnp=rg00SdRBg00TDRC7_5p>0NP8P>P?P?P@P6P9g00RVRDP5CoPAFnp=5P8P>P?P?P@P9P5K0>p=eP=P>P?P?P@P8P9P5L0^p=:P6P9PDP5Cop=^P=P>P?P?P@P8P>P?P?P@P9PAFnP5K0>p=Q1095,88p={1U65p=Ag00KOREP6P0P4P2g01AaP:P<P=P8P9P5N<0<p=hB0;695p=D1175p=RP6P7P=P8P9P5E\p=61189/05p=EPEP6P6P6P4P4P:P<P=P8P9P5N<0\p=yP6P6P6P6P6P6P3P5P9P8P3P=P<P:f6R3f7S01f8R4f9S02NB0_p=XP6P6P2Q01P2P3P:P<P=P8P9P5N<0<p=WP=P>P?P?P@P6B0;689PDP5CoPAFnp=>10731T:<1189/05,8='8'8p=NP;P=1I89P5H0`=_BCp=M1157p=YP9P>P?P?P@P5J0[p>08Q00P<P=P8P9P5J0bp=9p,2PHp,3memR>p,2spRAp,1wRDp,3canR2H0gP1P>PAPDP2P;p,1ER1P>g020OH0fS03P5g00ORR0#4RF#4S04#4RG#4RH#=RI$0@RJ/KARK%?HRL'pRM#j%G0#b#=#;#L#=#BRN/0K%20S05#G#Z#l#l#lRO#2#G#Z#l#?RP,0KP;P>PAg021RH0V%JIRQ#4#=#BRRQ05#4#=#G#=#J#J#BRS,T57S5&0@G$03RT#~P>1IJ9O1%}T3_[^U6%zTRT#~RUP>PJ%;0#G#c#L#;#BRVg00O3RW#PRX#PS06#PS07#PRY%2FS08#?RZ,IJ9HTYE<PUP>PJ%;0#G#c#L#G#=#BR[%PY#P#P#PR\%Z0#=#a#;#;#BR],IJ9HT\E<PUP>PJ%;0#G#c#L#b#BR^P\1IJDS099HT\S0:E<%Z0#=#a#J#;#BR_/0DS0;%Z0#=#a#;#L#Z#xR`,0DS0<'8PUP>PJ%;0#b#k#L#=#BRaP\%?QRQ,IJ9HT\E<PUP>PJ%;0#G#c#k#c#xRbPY%?ORO,IJ9HTYRcE<PUP>PJ%;0#b#k#k#BRdPYPcE<PUP>PJ%Z0#=#L#L#L#;#BRcP\1IJ2S0=9HT\S0>E<%?FRe%?IRI+0DRf,T2-0C2&0BA%3KR21TKf'81U671IJ7Rg,KJRh#jB0a;1>Ri%tWRj00]LB0?jNPRk%aH#JRH$0Z,Fj%?HRH'sS0?20YRSS0@%g7Rl/FV%gZRZ7[YS0A1Fl[%g]S0B7[\S0C1Fl^%tXR]7[\S0DB0?]_`S0E1Fla%gQS0F7[\S0G1Flb%gORO7[YS0H1Fld?[YOS0I1FlcQ06#tS0J7[\S0K1FlSRQ%a0#;#J#J#BRm'sS0L1F]7Rn/seS0MQ00$0:S0N'@S0O'@S0P'@S0Q'@S0R'@S0S'@S0T'@S0U'@S0V'@S0W'@S0X'@S0Y'@Ro'@P;P1P>PjPL20XKLRp%3L%3M[\2R220WeIRM1T7e%3I1T7fS0Z[[Rq%3eRrg01P_RsB0UeI9UWARI%3f\s^ArRsg00QjS0[$0:RtQ0[#zRu&0T6Rv&0S6Rw&0Q6Rx20667Ry%7L'f'r20Px@R@P5P81UBC20O58$0NdB0M679H0LRCb1b5b61T7LP5b0b2b3b4&03JRBPA1KJ5Rz/pL#jX>Bf?2021WR{g022UR|E\1O1j,KJR}/pL#jeK0KPiPkPoP;P1P>PjPNPPPBPA10zP9SNzX>BPpP2PMPqPIPsPtPu1i69RoPwPx1d60Rk%7P55xRL%}?R?Px%7NS0\=5xkR~P?Aex~LC:C:P@PCb1b5b6X86105P10N9108P9SN8[[^86P5PKfAfBRLO3b0b2b3b4P{P|E\10}P9SN}eF|PiQ0?Q0YP;P1P>PjPAPHP|f<S0YPpP2PMPqPIPsPtPuPoPwPxP~P?PxPx%7HR~,^yA5x~kCQC:P@PCb1b5b6X8610N5%3HR~?{H9[^86P5PKPLO2b0b2b3b4A{~HKeN90JPiQ0@Q0XP;P1P>PRPSPpP2PMPqPIPsPtPuPvPw%7R95xyP@PCb1b5b6%3RP5b0b2b3b4PpP2PMPqPIPsPtPuPvPw%7SRR%7eS0X>0I6JR~55xP@PCb1b5b610SfP5b0b2b3b4f;S0@L0HPiQ0AQ0WP;P1P>PlPgPVPYPZ1O1ZS0W1UBgRZQ0W,UB1mXY%?0RHQ04#?RL'0R|PXPH%AHS0APYPL%ALS0?EhPpP2PMPqPIPsPtPuPvPw%7HS0]%7LRA55xP@PCb1b5b6P|P5b0b2b3b4CCS0^1mY\%?GRG,0LR|PYPLQ0?P\PG%AGS0_EhPpP2PMPqPIPsPtPuPvPw%7GRj95xAP@PCb1b5b6P|P5b0b2b3b4CCS0`115VS0a#3X76PpP2PMPqPIPsPtPuPvPw%7V,DyS0b95xyP@PCb1b5b6%RVRV#3P5b0b2b3b4PhP5C6Q0a%]YR|;EfX7611V|S0c/0fS0d11VLR}/0fS0eP5X@6RP1095$0GXX6X@6R{Q0cP}PPPPPPP6P6g023V1195H0F#AX96XV6R}PVPV%AVP|PLPPPP%]5#AX@ES0cPYPLQ0?EyS0?M:XPfPf%AfRVGWPpP2PMPqPIPsPtPuPvPwPxQ0bPAP~C>P@PCb1b5b6Q0eP5b0b2b3b4CCQ0dePhP5C6PUP>PJQ0aPYQ0W9HTYE<X76f:S0WPhP5C6M@VPiQ0CQ0VP;P1P>PlPgP[P\Q0BQ0B,O1S0BPZQ0B,UB1mX\10HGS0VPXPHQ0AP\PGQ0_EhPpP2PMPqPIPsPtPuPvPwQ0]=5xjP@PCb1b5b6Q0VP5b0b2b3b4CCS0V1m\\10GGRHP\PGQ0_P\PGQ0_EhPpP2PMPqPIPsPtPuPvPwA5xjjP@PCb1b5b6PHP5b0b2b3b4CCS0]115[S0A#3X76PpP2PMPqPIPsPtPuPvPw%7[,DyS0C95xyP@PCb1b5b6%R[R[#3P5b0b2b3b4PhP5C6Q0A%]\RH;EfX7611[HS0a/0fS0d11[GS0e/0fS0bPPP{Q0aQ0ePPPPPPP}P[P[%A[PHPGPPPPQ0cP\PGQ0_EyS0_M:XPfPfPVGWPpP2PMPqPIPsPtPuPvPwPxQ0CPjP~C>P@PCb1b5b6Q0bP5b0b2b3b4CCQ0dePhP5C6PUP>PJQ0AP\Q0B9HT\E<X76Q02PhP5C6M@VPiQ0DQ0UP;P1P>PlPgP^P\P]Q09PZg024:S0UQ0VQ0]115^R[#3X76PpP2PMPqPIPsPtPuPvPw%7^,DyS0D95xyP@PCb1b5b6%R^R^#3P5b0b2b3b4PhP5C6AE[HfX7611^HS0B/0fS0A11^GS0d/0fS0bPPP{Q0BQ0dPPPPPPP}P^P^%A^PHPGQ0_M:XPfPfPVGWPpP2PMPqPIPsPtPuPvPwPxQ0DPjP~C>P@PCb1b5b6Q0bP5b0b2b3b4CCQ0AePhP5C6PUP>PJP[P\Q0:E<X76P4PhP5C6M@VPiQ0EQ0TP;P1P>P]P_P`PBQ0910z`9S_zX>BP6PD105`9S_5R[X76PpP2PMPqPIPsPtPuPoPwPx%7_=5xkS0T%7`95xkS0E5exS0:P?Q0:C:P@PCb1b5b6X8610_9S0A109`S0b'8\[^86P5PDQ0@O2S0Db0b2b3b4Q09,KJS0dPpP2PMPqPIPsPtPuPoPwPxQ0:P?A5xykS0B1fk~,rx5exC:P@PCb1b5b6X86%39R^1T9f'8\[^86Q0Db0b2b3b4,vDS0CE\2021XS0cQ0UE\1O1],KJR]10]`5S_eF|PiQ0GQ0SP;P1P>PlPgPaP\Q0FQ0F,O1R_PZ1UB_Q0VQ0]115aR]#3X76PpP2PMPqPIPsPtPuPvPw%7a,DyS0F95xyP@PCb1b5b6%RaRa#3P5b0b2b3b4PhP5C6AE]HfX7611aHR`/0fS0S11aGRX/0fS0GPPP{P`PXPPPPPPP}PaPa%AaPHPGQ0_M:XPfPfPVGWPpP2PMPqPIPsPtPuPvPwPxQ0FPjP~C>P@PCb1b5b6Q0GP5b0b2b3b4CCQ0SePhP5C6PUP>PJP]P\AHT\_E<X76P3PhP5C6M@VPiQ0HQ0RP;P1P>PlPgPbPYPO1O1OR_PZ1UB_S0RQ0^Q0`115bR]#3X76PpP2PMPqPIPsPtPuPvPw%7b,DyS0H95xyP@PCb1b5b6%RbRb#3P5b0b2b3b4PhP5C6AE]|fX7611b|Ra/0fS0S11bLRX/0fR`PPP{PaPXPPPPPPP}PbPb%AbP|PLQ0?M:XPfPfPVGWPpP2PMPqPIPsPtPuPvPwPxQ0HPAP~C>P@PCb1b5b6P`P5b0b2b3b4CCQ0SePhP5C6PUP>PJP]PYAHTY_RTE<X76P:PhP5C6M@VPiQ0IQ0QP;P1P>PlPgPdPYPOP_PZQ0RQ0^Q0`115dR_#3X76PpP2PMPqPIPsPtPuPvPw%7d,DyRO95xyP@PCb1b5b6%RdRd#3P5b0b2b3b4PhP5C6AE_|fX7611d|R]/0fR`11dLRb/0fRXPPP{P]PbPPPPPPP}PdPd%AdP|PLQ0?M:XPfPfPVGWPpP2PMPqPIPsPtPuPvPwPxPOPAP~C>P@PCb1b5b6PXP5b0b2b3b4CCP`ePhP5C6PUP>PJP_PYPTE<X76P<PhP5C6M@VPiQ0KQ0PP;P1P>PlPgPcP\Q0JQ0=PZg025;Q0VQ0]115cRZ#3X76PpP2PMPqPIPsPtPuPvPw%7c,DyRg95xyP@PCb1b5b6%RcRc#3P5b0b2b3b4PhP5C6AEZHfX7611cHRl/0fRT11cGRY/0fR_PPP{PlPYPPPPPPP}PcPc%AcPHPGQ0_M:XPfPfPVGWPpP2PMPqPIPsPtPuPvPwPxPgPjP~C>P@PCb1b5b6P_P5b0b2b3b4CCPTePhP5C6PUP>PJPZP\Q0>E<X76P=PhP5C6M@VPiQ0LQ0O115SR\P\Pf%3mRZP\PmPfFN%]9,18R\/0mRUP>PJ11<S/1=P8CM[\^^9E^:6'8X76%RSRTPTPfPZPTPmPfFNR_P>PJ11T=RjP8CM\U\^^9E^:6PpP2PMPqPIPsPtPuPvPwPxPx1DyRRg,^yPxPx1fg~PxPx%7mRV,^yPxPgPVP~C>CQCQCQP@PCb1b5b6P_P5b0b2b3b4P>PjP8&0E8Rj%]8#3R_PpP2PMPqPIPsPtPuPoPwPxQ0BP?1DgkRg95xRC:P@PCb1b5b6X86%3511T9RT,0S[^86P5P4P3O2b0b2b3b4b?PjP_PpP2PMPqPIPsPtPuP61i68RGP9PvC`PwPxPxPk1d6FRFPVC>P?PxPgPF%G0#b#=#J#J#BR0#7RgC>C:P@PCb1b5b6X86X;6AE59mAET80[^86^;6P5Q01#]RTP4P:O3b0b2b3b4b?DwXCUXB^X9EX:6H00PhPpP2PMPqPIPsPtPuPvPwPxPx1^yy1fy~,rxCQP@PCb1b5b6Q0Z9S77P5b0b2b3b4,v7C6&01Q,O1,KJ&0=Q'1R7P7PfPZP7PmPfFNP>PJ117=P8CM\U\^^9E^:6'8eB051QmP>PJ2041Q/1=P8CM\U\^^9E^:6'8eP;P1P>Q0LCuePiQ0MQ0NPBQ09%YzRzPzPfPrPzPePfFN10\eR\P>PJ1KJ<#Y/1=P8CM[\^^9E^:6'8X>BP6PD%Y5RBPBPfPrPBPePfFNP>PJ%Y</1=P8CM\\\^^9E^:6'8X76%YDRBPBPfPrPBPePfFNP>PJ11B=RBP8CM\\\^^9E^:6PpP2PMPqPIPsPtPuPoPwPxQ0:P?PxPx1DkyRk,^yPxPx1fk~PxPxQ0X,^yPxPkQ0XP~C>CQCQCQC:P@PCb1b5b6X86%Y9R~P~PfPrP~PePfFN\[^86Q0Db0b2b3b4P>PBP8PjP_PpP2PMPqPIPsp-0RBQ0[Q07,q6Q06,q61q6W60966096g00g9+0R<07tRtPuP6P61i6=P8PvC`P9PvC`PwPxA5xyFP?PxQ0T208x:5exP?PxQ0\Q04,d655xP?1DkFRk95xRC:C:C:P@PCb1b5b6X86X;6X=6W<Q0A/8<10N<%Y=/1<RR,0S[[\^^86^;6^=6^<BP5Q0<PKP4PDP3f@RSfGRyO7b0b2b3b4b?PjP_PpP2PMPqPIPsPtPuP6PGP9P61i6<P=PvC`C`PwPxPxPFQ05,d6RFQ0XC>P?Px208x3Q0E5exP?PxQ0\Q08,d655xP?PxPkPFPgC>C:C:C:P@PCb1b5b6X86X;6X=6XD6X<BAE98eQ0b,8:10N:AER:0[[[^86^;6^=6^D6^<BP5Q0;PKPTP4PDP:PSPyO8b0b2b3b4b?DwXC\XB^X9EX:6H00Q0dQ0CE\Q0cQ0UE\&01n,O1,KJ&0=n'1RyPyPfPrPyPePfFNP>PJ11y=P8CM\\\^^9E^:6'8eB051neP>PJ2041n/1=P8CM\\\^^9E^:6'8eP;P1P>Q0MCueQ0000AiD9D9D9D9D9D9D9D9D9D9D9D9D9D9Q03ebTbEWHWGWKWLWFWQWSWRWIWJWPWNWOWMf=Q0YQ0@Q0WQ02P4Q01P3P:P<P=P8P9P5O>n4000010000001>110710910810:10410310<10=10;100106105101102bWo"). Qed.
End Entry.

End FPX_1.

End Ns0PrintfBufBase.
Module Ns0MainEntryN.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require RunEnv PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.RunEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.FileSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.ArgvEnv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MuslStrlen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SymExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemSplit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.RefLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.StartupTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0StartupDefs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0Startup OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0StartupFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0058.Ns0MainEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Section MainEntryN.
  Context {RE : RunEnv}.
  Variable sp0 : word.
  Variables av envv : list (list byte).
  Variable uid : word.
  Variable hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 av envv uid hw rdraw tid regs mem.

  Definition p0N : word := cat_argv_ptr sp0 av envv 0.
  Definition auxvpN : word := auxv_w sp0 av envv.
  Definition rndN : word := at_random_ptr sp0 av envv.

  Definition valsN : list word := [sp0; p0N; p0N; auxvpN; rndN; tid] ++ junk_vals regs.
  (* [comment removed for export] *)
  Definition blobsN : list (list byte) := [[]; []; word_to_le_bytes 8 (canary_w (ed_random rdraw)); word_to_le_bytes 8 hw].
  Definition EN : env := Env (vals_ev valsN) (blobs_ev blobsN).

  Definition sr_mainN : list expr :=
    [ELit 0; ELit 0xa8c84; spx (-48); ELit 0x10800; ELit 0xd8850; EVar 11; EVar 12; EVar 13;
     spx 8; EVar 15; EVar 16; spx 8; EVar 18; EVar 19; EVar 20; EVar 21;
     EVar 22; EVar 23; ELit 0x38c2c; EVar 25; ELit 0; ELit 0; ELit 0; ELit 0;
     ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

  Definition kn_stackN : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (-8388608)) 8388608;
     KWord (SA (EVar 0) 8) 8 (EVar 1);
     KRange (EVar 1) 0x7fff80000000 0x800000400000].

  Definition kn_mainN : list kentry := kn_stackN ++ kn_image.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  Lemma len_avN : (1 <= length av <= 1024)%nat.
Proof using sp0 av Hva. destruct Hva as [[H1 H2] _]. lia. Qed.

  Lemma evN_junk : forall i, (i < 32)%nat -> ev EN (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
Proof using sp0 av envv hw rdraw tid regs.
intros i Hi. unfold EN. cbn [ev]. unfold valsN.
change (6 + i)%nat with (length [sp0; p0N; p0N; auxvpN; rndN; tid] + i)%nat.
unfold vals_ev. rewrite app_nth2_plus. unfold junk_vals.
rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
Qed.

  Lemma spxN_val : forall k, edenot EN (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
Proof using sp0 av envv hw rdraw tid regs. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev EN 0) with sp0.
apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac reg_caseN :=
    cbn [nth sr_mainN all_regs];
    first [ rewrite spxN_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot EN (EVar n)) with (ev EN n);
              first [ rewrite (evN_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact (me_ra _ _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ _ ME)
          | exact (me_s2 _ _ _ _ _ _ _ _ _ ME)
          | rewrite (me_sp _ _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
          | rewrite (me_s0 _ _ _ _ _ _ _ _ _ ME); reflexivity
          | rewrite (me_a1 _ _ _ _ _ _ _ _ _ ME); reflexivity
          | apply (me_szero _ _ _ _ _ _ _ _ _ ME); cbn; tauto
          | idtac ].

  Theorem main_regs_okN : regs_ok EN sr_mainN regs.
Proof using sp0 av envv uid hw rdraw tid regs mem Hvsp Htid ME.
pose proof Hlo. pose proof Hhi.
apply regs_ok_by_index.
intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseN.
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma main_strN : forall k, (k < length av)%nat ->
    rdn RSEGS mem (cat_argv_ptr sp0 av envv k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr sp0 av envv k))%Z
    /\ (bv_unsigned (cat_argv_ptr sp0 av envv k) <= bv_unsigned sp0 + 2107576)%Z
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z
    /\ (exists t8, rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr sp0 av envv k) + Z.of_nat (length (nth k av []))))
                         8 = Some t8).
Proof using sp0 av envv uid hw rdraw tid regs mem Hva Hve Hvsp ME.
intros k.
intros Hk'.
pose proof Hlo. pose proof Hhi.
pose proof (lay_bsb_nw RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
destruct (argv_ptr_bounds_at sp0 av envv Hva Hve ltac:(unfold sp_window_hi; lia) k Hk') as [B1 B2].
pose proof (u_cat_argv_ptr RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
pose proof (struct_av_bound RPH sp0 rdraw av envv uid hw Hva Hve) as Hsb.
pose proof (total_arg_bytes_firstn_le k av) as Hf.
pose proof (argv_str_len av Hva k Hk') as Hlen.
pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv uid hw rdraw) as Hw. unfold wmem in Hw.
repeat split.
- rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by lia.
rewrite Hw by lia. apply read_argv_cstr_k; [exact Hk' | exact Hnw].
- exact B1.
- lia.
- exact Hlen.
- destruct (read_word_stack RPH RSEGS sp0 av envv k (length (nth k av [])) uid hw rdraw Hk' ltac:(lia) Hnw) as (t8 & Hl8 & Hr8).
exists t8. rewrite w_add_nat in Hr8.
rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
Qed.

  (* [comment removed for export] *)
  Lemma main_strN_fits : entry_stack_fits sp0 av envv -> forall k, (k < length av)%nat ->
    (bv_unsigned (cat_argv_ptr sp0 av envv k) + Z.of_nat (length (nth k av [])) + 17 <= 0x800000000000)%Z.
Proof using sp0 av envv uid hw rdraw Hva Hve Hvsp.
intros Hfit k Hk'. pose proof Hlo. pose proof Hhi.
pose proof (u_cat_argv_ptr RPH sp0 rdraw av envv uid hw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
pose proof (bsb_len_lower RPH sp0 av envv uid hw rdraw) as Hlow.
pose proof (total_arg_bytes_firstn_le (S k) av) as Hmono.
pose proof (total_arg_bytes_firstn_S av k Hk') as Hstep.
pose proof (build_stack_bytes_within_span RPH sp0 av envv uid hw rdraw) as Hspan.
unfold entry_stack_fits, sp_window_hi in Hfit. lia.
Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma keN0 : ev EN 0 = sp0.
Proof using sp0 av envv hw rdraw tid regs. reflexivity. Qed.
  Lemma keN1 : ev EN 1 = p0N.
Proof using sp0 av envv hw rdraw tid regs. reflexivity. Qed.
  Lemma keN3 : ev EN 3 = auxvpN.
Proof using sp0 av envv hw rdraw tid regs. reflexivity. Qed.
  Lemma keN5 : ev EN 5 = tid.
Proof using sp0 av envv hw rdraw tid regs. reflexivity. Qed.

  Lemma know_stackN : know_ok RSEGS EN mem kn_stackN.
Proof using sp0 av envv uid hw rdraw tid regs mem Hva Hve Hvsp ME.
pose proof Hlo. pose proof Hhi. pose proof Hal. pose proof len_avN as Hlen.
destruct (main_strN 0%nat ltac:(lia)) as (_ & B1 & B2 & _ & _).
unfold kn_stackN, know_ok.
repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?keN0, ?keN1;
unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?keN0.
- split; [lia | exact Hal].
- lia.
- split; [lia|]. intros d m Hd Hm.
apply (main_entry_store_ok_win sp0 av envv uid hw rdraw tid regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite keN0. unfold v_addi.
rewrite (main_entry_rdn_above sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv uid hw rdraw Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(lia)) as Hr.
unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
- unfold p0N. lia.
Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvpN : forall segs,
    rdn segs (D_main sp0 av envv hw (ed_random rdraw) tid) (Z_to_bv 64 0xf8ae8) 8
    = Some (word_to_le_bytes 8 auxvpN).
Proof using sp0 av envv hw rdraw tid Hvsp.
intros segs.
pose proof (u64_range tid). pose proof (u64_range hw). pose proof Hlo. pose proof Hhi.
unfold auxvpN, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.

  Lemma wseg_dataN : wseg_ok RSEGS (Z_to_bv 64 0xc6000) 0x34000 = true.
Proof using. vm_compute. reflexivity. Qed.

  Lemma range_disjoint_subN : forall lo n c i, range_disjoint_b lo n c = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> range_disjoint_b i 1 c = true.
Proof using sp0 Hvsp.
intros lo n [c w] i H Hlo' Hhi'. unfold range_disjoint_b in *. cbn [fst snd] in *.
apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
Qed.

  Lemma missb_subN : forall lo n i, D_main_missb lo n = true ->
    (lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> D_main_missb i 1 = true.
Proof using sp0 Hvsp.
intros lo n i H Hlo' Hhi'. unfold D_main_missb in *.
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply Z.leb_le in H2. apply Z.leb_le in H3.
apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
apply forallb_forall. intros c Hc. apply (range_disjoint_subN lo n); [|lia|lia].
apply (proj1 (forallb_forall _ _) H1). exact Hc.
Qed.

  Lemma kimg_okN : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0xfa000)%Z ->
    kentry_ok RSEGS EN mem (KImg lo hi).
Proof using sp0 av envv uid hw rdraw tid regs mem Hva Hvsp ME.
intros lo hi Hb Hle Hhi'. pose proof Hlo as HLO. pose proof Hhi as HHI.
assert (Hlo0 : (0 <= lo)%Z).
{ unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
apply Z.leb_le in Hb. exact Hb. }
cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
rewrite (main_entry_mem_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
apply (D_main_none sp0 av envv hw (ed_random rdraw) tid i Hva); [lia | lia |].
apply (missb_subN lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
Qed.

  Ltac kimgN := apply kimg_okN; [vm_compute; reflexivity | lia | lia].

  Ltac kw_preN :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_dataN L :=
    kw_preN;
    rewrite (main_entry_rdn_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_memN L := kw_preN; rewrite (L RSEGS); try reflexivity.
  Ltac kblob8N L :=
    unorm; rewrite ?Z.add_0_l; repeat split; try lia;
    try (unfold EN; cbn [eb blobs_ev blobsN nth]; rewrite length_N_to_le_bytes; reflexivity);
    intros i Hi; unfold EN; cbn [eb blobs_ev blobsN nth];
    rewrite (main_entry_mem_data sp0 av envv uid hw rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    apply L; lia.

  Lemma know_imageN : know_ok RSEGS EN mem kn_image.
Proof using sp0 av envv uid hw rdraw tid regs mem Hva Hvsp Htid ME.
pose proof Hlo as HLO. pose proof Hhi as HHI. pose proof (u64_range tid) as Ht.
unfold kn_image, know_ok.
repeat apply Forall_cons; try apply Forall_nil;
try kimgN;
cbn [kentry_ok a_base a_off edenot]; rewrite ?keN3, ?keN5; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
rewrite ?(u_small 0) by lia; cbn [Z.add].
- split; [lia|]. intros d m Hd Hm.
eapply (store_ok_window RSEGS mem (Z_to_bv 64 0xc6000) (Z_to_bv 64 (0xc6000 + d)) 0x34000 m 0xc6000 0xfa000);
[reflexivity | reflexivity | cbn; lia | apply wseg_dataN | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
- kw_dataN (D_main_self sp0 av envv hw rdraw tid).
- kw_memN (main_entry_tid sp0 av envv uid hw rdraw tid HLO regs mem ME).
- kw_dataN (D_main_locale sp0 av envv hw rdraw tid).
- kblob8N (D_canary_pt sp0 av envv hw rdraw tid Hva).
- kblob8N (D_guard_pt sp0 av envv hw rdraw tid Hva).
- kw_dataN D_main_auxvpN.
- kw_dataN (D_main_pagesize sp0 av envv hw rdraw tid Hva).
- kblob8N (D_hwcap_pt sp0 av envv hw rdraw tid Hva).
- lia.
Qed.

  Theorem main_know_okN : know_ok RSEGS EN mem kn_mainN.
Proof using sp0 av envv uid hw rdraw tid regs mem Hva Hve Hvsp Htid ME.
unfold kn_mainN, know_ok. apply Forall_app; split; [apply know_stackN | apply know_imageN].
Qed.

  Lemma valsN_length : length valsN = 38%nat.
Proof using sp0 av envv tid regs. unfold valsN. rewrite length_app, junk_vals_length. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma evN_argc : ev EN 16 = argcN av.
Proof using sp0 av envv uid hw rdraw tid regs mem ME. change 16%nat with (6 + 10)%nat. rewrite (evN_junk 10) by lia. exact (me_a0 _ _ _ _ _ _ _ _ _ ME). Qed.
End MainEntryN.
End FPX_1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End Ns0MainEntryN.
