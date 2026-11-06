(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcR.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PStmt. Import PStmt.StrNota.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BigLinkZA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ju0PlanKit AsanPlanCore
BigLinkBase BigLinkGlueUb0 L5Defs L5KnU L5KnAU.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_upkA1 LibSegJu_upkA0 LibSegJu_upkB0 LibSegJu_upkB1 LibSegJu_upkT LibSegJu_uigA1a LibSegJu_uigA1b LibSegJu_uigA0 LibSegJu_uigB0 LibSegJu_uigB1a LibSegJu_uigB1b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMUPKP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_upkA1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_upkA1.regs0 LibSegJu_upkA1.regs_out0).
Lemma KS_upkA1_ok : BG.kept_ok 48 LibSegJu_upkA1.regs0 LibSegJu_upkA1.regs_out0 KS_upkA1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition upkA1_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#7???7?800010v24#7????????>=8Hv24#8P_v2#10#10v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8I+v24#100#28B#1v21#4000B#1000v23#7???????<000Jav23#1P_v2#10#10v23#1Pv24#128v23#1,1_v2#10#10,1,7X#37050#3708<Y,T,2_v2#10T,8v24T,:v23Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma upkA1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_upkA1] fx R M V upkA1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_upkA1] LibSegJu_upkA1.regs0 LibSegJu_upkA1.kn0 LibSegJu_upkA1.BR LibSegJu_upkA1.PSS LibSegJu_upkA1.NX0 LibSegJu_upkA1.F0 225360 LibSegJu_upkA1.seg_sound_ax fx R M V upkA1_conc_s. Qed.
Definition KS_upkA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_upkA0.regs0 LibSegJu_upkA0.regs_out0).
Lemma KS_upkA0_ok : BG.kept_ok 48 LibSegJu_upkA0.regs0 LibSegJu_upkA0.regs_out0 KS_upkA0 = true. Proof. vm_compute. reflexivity. Qed.
Definition upkA0_conc_s := ",12A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#7???7?800010v24#7????????>=8Hv24#8P_v2#10#10v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28,2_v2#10#10+v24#100#28,1,>X#37050#37720Y,T,1#3707<T,2_v2#10T,8v24T,;v22T,<#4000Lb+v24#118v22Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000Lb+v24#120#Jb+v24#100#8"%pstring.
Lemma upkA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_upkA0] fx R M V upkA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_upkA0] LibSegJu_upkA0.regs0 LibSegJu_upkA0.kn0 LibSegJu_upkA0.BR LibSegJu_upkA0.PSS LibSegJu_upkA0.NX0 LibSegJu_upkA0.F0 225360 LibSegJu_upkA0.seg_sound_ax fx R M V upkA0_conc_s. Qed.
Definition KS_upkB0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_upkB0.regs0 LibSegJu_upkB0.regs_out0).
Lemma KS_upkB0_ok : BG.kept_ok 48 LibSegJu_upkB0.regs0 LibSegJu_upkB0.regs_out0 KS_upkB0 = true. Proof. vm_compute. reflexivity. Qed.
Definition upkB0_conc_s := ",16A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#10S,8v24S,:#B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#7???7?800010v24#7????????>=8Hv24#8P_v2#10#10v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29,2_v2#10#10+v24#100#28,1,=X#3707<#3709<Y,T,1v28T,2v2T,8v29T,:#100Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29"%pstring.
Lemma upkB0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_upkB0] fx R M V upkB0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_upkB0] LibSegJu_upkB0.regs0 LibSegJu_upkB0.kn0 LibSegJu_upkB0.BR LibSegJu_upkB0.PSS LibSegJu_upkB0.NX0 LibSegJu_upkB0.F0 225404 LibSegJu_upkB0.seg_sound_ax fx R M V upkB0_conc_s. Qed.
Definition KS_upkB1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_upkB1.regs0 LibSegJu_upkB1.regs_out0).
Lemma KS_upkB1_ok : BG.kept_ok 48 LibSegJu_upkB1.regs0 LibSegJu_upkB1.regs_out0 KS_upkB1 = true. Proof. vm_compute. reflexivity. Qed.
Definition upkB1_conc_s := ",1<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#10S,8v24S,:v21B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#7???7?800010v24#7????????>=8Hv24#8P_v2#10#10v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28B#1v21#4000B#1000v22#7???????<000Jav22#1P_v2#10#10v22#1Pv24#128v22#1La_v2#8v28La_v2#10v29,2_v2#10#10+v24#100#28,1,:X#3707<#3708<Y,T,:v22Lb+v24#120v21Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29"%pstring.
Lemma upkB1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_upkB1] fx R M V upkB1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_upkB1] LibSegJu_upkB1.regs0 LibSegJu_upkB1.kn0 LibSegJu_upkB1.BR LibSegJu_upkB1.PSS LibSegJu_upkB1.NX0 LibSegJu_upkB1.F0 225404 LibSegJu_upkB1.seg_sound_ax fx R M V upkB1_conc_s. Qed.
Definition KS_upkT : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_upkT.regs0 LibSegJu_upkT.regs_out0).
Lemma KS_upkT_ok : BG.kept_ok 48 LibSegJu_upkT.regs0 LibSegJu_upkT.regs_out0 KS_upkT = true. Proof. vm_compute. reflexivity. Qed.
Definition upkT_conc_s := ",9A#v2p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#10B#7???7?800010v2#800000000000Hv2#10I_v2#10#10La_v2#8v28La_v2#10v29,,1,5X#37090#3709<Y,T,1v28T,2v2T,8v29"%pstring.
Lemma upkT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_upkT] fx R M V upkT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_upkT] LibSegJu_upkT.regs0 LibSegJu_upkT.kn0 LibSegJu_upkT.BR LibSegJu_upkT.PSS LibSegJu_upkT.NX0 LibSegJu_upkT.F0 225424 LibSegJu_upkT.seg_sound_ax fx R M V upkT_conc_s. Qed.
Definition KS_uigA1a : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uigA1a.regs0 LibSegJu_uigA1a.regs_out0).
Lemma KS_uigA1a_ok : BG.kept_ok 48 LibSegJu_uigA1a.regs0 LibSegJu_uigA1a.regs_out0 KS_uigA1a = true. Proof. vm_compute. reflexivity. Qed.
Definition uigA1a_conc_s := ",14A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24S,;#1B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#1Ja+v24#100#8I+v24#100#28B#1000v23#7???????<000,2_v2#20#20+v24#100#28,1,>X#37144#37230Y,T,:#T,;+v23#1T,<#1T,=#Lb+v24#120#Lb+v24#118+v23#1Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000"%pstring.
Lemma uigA1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uigA1a] fx R M V uigA1a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uigA1a] LibSegJu_uigA1a.regs0 LibSegJu_uigA1a.kn0 LibSegJu_uigA1a.BR LibSegJu_uigA1a.PSS LibSegJu_uigA1a.NX0 LibSegJu_uigA1a.F0 225604 LibSegJu_uigA1a.seg_sound_ax fx R M V uigA1a_conc_s. Qed.
Definition KS_uigA1b : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uigA1b.regs0 LibSegJu_uigA1b.regs_out0).
Lemma KS_uigA1b_ok : BG.kept_ok 48 LibSegJu_uigA1b.regs0 LibSegJu_uigA1b.regs_out0 KS_uigA1b = true. Proof. vm_compute. reflexivity. Qed.
Definition uigA1b_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24S,;#1B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8I+v24#100#28B#2v21#4000B#1000v23#7???????<000,2_v2#20#20+v24#100#28,1,>X#37144#37230Y,T,:_v21#1T,;+v23#1T,<#1T,=#Lb+v24#120_v21#1Lb+v24#118+v23#1Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000"%pstring.
Lemma uigA1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uigA1b] fx R M V uigA1b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uigA1b] LibSegJu_uigA1b.regs0 LibSegJu_uigA1b.kn0 LibSegJu_uigA1b.BR LibSegJu_uigA1b.PSS LibSegJu_uigA1b.NX0 LibSegJu_uigA1b.F0 225604 LibSegJu_uigA1b.seg_sound_ax fx R M V uigA1b_conc_s. Qed.
Definition KS_uigA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uigA0.regs0 LibSegJu_uigA0.regs_out0).
Lemma KS_uigA0_ok : BG.kept_ok 48 LibSegJu_uigA0.regs0 LibSegJu_uigA0.regs_out0 KS_uigA0 = true. Proof. vm_compute. reflexivity. Qed.
Definition uigA0_conc_s := ",13A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24S,;#1B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28,2_v2#20#20+v24#100#28,1,12X#37144#37720Y,T,1#371<<T,2_v2#20T,8v24T,9#1T,;v22T,<#4000T,12#Lb+v24#118v22Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000Lb+v24#120#Jb+v24#100#8"%pstring.
Lemma uigA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uigA0] fx R M V uigA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uigA0] LibSegJu_uigA0.regs0 LibSegJu_uigA0.kn0 LibSegJu_uigA0.BR LibSegJu_uigA0.PSS LibSegJu_uigA0.NX0 LibSegJu_uigA0.F0 225604 LibSegJu_uigA0.seg_sound_ax fx R M V uigA0_conc_s. Qed.
Definition KS_uigB0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uigB0.regs0 LibSegJu_uigB0.regs_out0).
Lemma KS_uigB0_ok : BG.kept_ok 48 LibSegJu_uigB0.regs0 LibSegJu_uigB0.regs_out0 KS_uigB0 = true. Proof. vm_compute. reflexivity. Qed.
Definition uigB0_conc_s := ",1<A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v24S,9#1S,:#S,12#B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;,2_v2#20#20+v24#100#28,1,10X#371<<#37230Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;"%pstring.
Lemma uigB0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uigB0] fx R M V uigB0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uigB0] LibSegJu_uigB0.regs0 LibSegJu_uigB0.kn0 LibSegJu_uigB0.BR LibSegJu_uigB0.PSS LibSegJu_uigB0.NX0 LibSegJu_uigB0.F0 225740 LibSegJu_uigB0.seg_sound_ax fx R M V uigB0_conc_s. Qed.
Definition KS_uigB1a : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uigB1a.regs0 LibSegJu_uigB1a.regs_out0).
Lemma KS_uigB1a_ok : BG.kept_ok 48 LibSegJu_uigB1a.regs0 LibSegJu_uigB1a.regs_out0 KS_uigB1a = true. Proof. vm_compute. reflexivity. Qed.
Definition uigB1a_conc_s := ",1=A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v24S,9#1S,:#1S,12#B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28B#1000v22#7???????<000La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;,2_v2#20#20+v24#100#28,1,14X#371<<#37230Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#1T,<+v22#1T,=#1T,>#T,12v2;Lb+v24#120#Lb+v24#118+v22#1Lb+v24#108v22Lb+v24#110#4000Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;"%pstring.
Lemma uigB1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uigB1a] fx R M V uigB1a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uigB1a] LibSegJu_uigB1a.regs0 LibSegJu_uigB1a.kn0 LibSegJu_uigB1a.BR LibSegJu_uigB1a.PSS LibSegJu_uigB1a.NX0 LibSegJu_uigB1a.F0 225740 LibSegJu_uigB1a.seg_sound_ax fx R M V uigB1a_conc_s. Qed.
Definition KS_uigB1b : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_uigB1b.regs0 LibSegJu_uigB1b.regs_out0).
Lemma KS_uigB1b_ok : BG.kept_ok 48 LibSegJu_uigB1b.regs0 LibSegJu_uigB1b.regs_out0 KS_uigB1b = true. Proof. vm_compute. reflexivity. Qed.
Definition uigB1b_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v24S,9#1S,:v21S,12#B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28B#2v21#4000B#1000v22#7???????<000La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;,2_v2#20#20+v24#100#28,1,14X#371<<#37230Y,T,1v28T,2v2T,8v29T,9v2:T,:_v21#1T,;#1T,<+v22#1T,=#1T,>#T,12v2;Lb+v24#120_v21#1Lb+v24#118+v22#1Lb+v24#108v22Lb+v24#110#4000Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;"%pstring.
Lemma uigB1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uigB1b] fx R M V uigB1b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uigB1b] LibSegJu_uigB1b.regs0 LibSegJu_uigB1b.kn0 LibSegJu_uigB1b.BR LibSegJu_uigB1b.PSS LibSegJu_uigB1b.NX0 LibSegJu_uigB1b.F0 225740 LibSegJu_uigB1b.seg_sound_ax fx R M V uigB1b_conc_s. Qed.
End PMUPKP.
