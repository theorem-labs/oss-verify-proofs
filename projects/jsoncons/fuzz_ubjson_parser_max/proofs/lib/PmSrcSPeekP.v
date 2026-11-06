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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Js0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_pkA1 LibSegJs_pkA0 LibSegJs_pkB0 LibSegJs_pkB1 LibSegJs_pkT LibSegJs_igA1a LibSegJs_igA1b LibSegJs_igA0 LibSegJs_igB0 LibSegJs_igB1a LibSegJs_igB1b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSPKP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_pkA1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_pkA1.regs0 LibSegJs_pkA1.regs_out0).
Lemma KS_pkA1_ok : BG.kept_ok 48 LibSegJs_pkA1.regs0 LibSegJs_pkA1.regs_out0 KS_pkA1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition pkA1_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#7???7?800010v24#7????????>=8Hv24#8P_v2#10#10v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8I+v24#100#28B#1v21#4000B#1000v23#7???????<000Jav23#1P_v2#10#10v23#1Pv24#128v23#1,1_v2#10#10,1,7X#3643<#36474Y,T,2_v2#10T,8v24T,:v23Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma pkA1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_pkA1] fx R M V pkA1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_pkA1] LibSegJs_pkA1.regs0 LibSegJs_pkA1.kn0 LibSegJs_pkA1.BR LibSegJs_pkA1.PSS LibSegJs_pkA1.NX0 LibSegJs_pkA1.F0 222268 LibSegJs_pkA1.seg_sound_ax fx R M V pkA1_conc_s. Qed.
Definition KS_pkA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_pkA0.regs0 LibSegJs_pkA0.regs_out0).
Lemma KS_pkA0_ok : BG.kept_ok 48 LibSegJs_pkA0.regs0 LibSegJs_pkA0.regs_out0 KS_pkA0 = true. Proof. vm_compute. reflexivity. Qed.
Definition pkA0_conc_s := ",12A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#7???7?800010v24#7????????>=8Hv24#8P_v2#10#10v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28,2_v2#10#10+v24#100#28,1,>X#3643<#36:08Y,T,1#36468T,2_v2#10T,8v24T,;v22T,<#4000Lb+v24#118v22Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000Lb+v24#120#Jb+v24#100#8"%pstring.
Lemma pkA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_pkA0] fx R M V pkA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_pkA0] LibSegJs_pkA0.regs0 LibSegJs_pkA0.kn0 LibSegJs_pkA0.BR LibSegJs_pkA0.PSS LibSegJs_pkA0.NX0 LibSegJs_pkA0.F0 222268 LibSegJs_pkA0.seg_sound_ax fx R M V pkA0_conc_s. Qed.
Definition KS_pkB0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_pkB0.regs0 LibSegJs_pkB0.regs_out0).
Lemma KS_pkB0_ok : BG.kept_ok 48 LibSegJs_pkB0.regs0 LibSegJs_pkB0.regs_out0 KS_pkB0 = true. Proof. vm_compute. reflexivity. Qed.
Definition pkB0_conc_s := ",16A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#10S,8v24S,:#B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#7???7?800010v24#7????????>=8Hv24#8P_v2#10#10v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29,2_v2#10#10+v24#100#28,1,=X#36468#36484Y,T,1v28T,2v2T,8v29T,:#100Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29"%pstring.
Lemma pkB0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_pkB0] fx R M V pkB0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_pkB0] LibSegJs_pkB0.regs0 LibSegJs_pkB0.kn0 LibSegJs_pkB0.BR LibSegJs_pkB0.PSS LibSegJs_pkB0.NX0 LibSegJs_pkB0.F0 222312 LibSegJs_pkB0.seg_sound_ax fx R M V pkB0_conc_s. Qed.
Definition KS_pkB1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_pkB1.regs0 LibSegJs_pkB1.regs_out0).
Lemma KS_pkB1_ok : BG.kept_ok 48 LibSegJs_pkB1.regs0 LibSegJs_pkB1.regs_out0 KS_pkB1 = true. Proof. vm_compute. reflexivity. Qed.
Definition pkB1_conc_s := ",1<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#10S,8v24S,:v21B#7???7?800010v2#800000000000Hv2#10I_v2#10#10B#7???7?800010v24#7????????>=8Hv24#8P_v2#10#10v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28B#1v21#4000B#1000v22#7???????<000Jav22#1P_v2#10#10v22#1Pv24#128v22#1La_v2#8v28La_v2#10v29,2_v2#10#10+v24#100#28,1,:X#36468#36474Y,T,:v22Lb+v24#120v21Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29"%pstring.
Lemma pkB1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_pkB1] fx R M V pkB1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_pkB1] LibSegJs_pkB1.regs0 LibSegJs_pkB1.kn0 LibSegJs_pkB1.BR LibSegJs_pkB1.PSS LibSegJs_pkB1.NX0 LibSegJs_pkB1.F0 222312 LibSegJs_pkB1.seg_sound_ax fx R M V pkB1_conc_s. Qed.
Definition KS_pkT : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_pkT.regs0 LibSegJs_pkT.regs_out0).
Lemma KS_pkT_ok : BG.kept_ok 48 LibSegJs_pkT.regs0 LibSegJs_pkT.regs_out0 KS_pkT = true. Proof. vm_compute. reflexivity. Qed.
Definition pkT_conc_s := ",9A#v2p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#10B#7???7?800010v2#800000000000Hv2#10I_v2#10#10La_v2#8v28La_v2#10v29,,1,5X#36478#36484Y,T,1v28T,2v2T,8v29"%pstring.
Lemma pkT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_pkT] fx R M V pkT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_pkT] LibSegJs_pkT.regs0 LibSegJs_pkT.kn0 LibSegJs_pkT.BR LibSegJs_pkT.PSS LibSegJs_pkT.NX0 LibSegJs_pkT.F0 222328 LibSegJs_pkT.seg_sound_ax fx R M V pkT_conc_s. Qed.
Definition KS_igA1a : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_igA1a.regs0 LibSegJs_igA1a.regs_out0).
Lemma KS_igA1a_ok : BG.kept_ok 48 LibSegJs_igA1a.regs0 LibSegJs_igA1a.regs_out0 KS_igA1a = true. Proof. vm_compute. reflexivity. Qed.
Definition igA1a_conc_s := ",14A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24S,;#1B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#1Ja+v24#100#8I+v24#100#28B#1000v23#7???????<000,2_v2#20#20+v24#100#28,1,<X#36528#365><Y,T,:#T,<+v23#1Lb+v24#120#Lb+v24#118+v23#1Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000"%pstring.
Lemma igA1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_igA1a] fx R M V igA1a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_igA1a] LibSegJs_igA1a.regs0 LibSegJs_igA1a.kn0 LibSegJs_igA1a.BR LibSegJs_igA1a.PSS LibSegJs_igA1a.NX0 LibSegJs_igA1a.F0 222504 LibSegJs_igA1a.seg_sound_ax fx R M V igA1a_conc_s. Qed.
Definition KS_igA1b : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_igA1b.regs0 LibSegJs_igA1b.regs_out0).
Lemma KS_igA1b_ok : BG.kept_ok 48 LibSegJs_igA1b.regs0 LibSegJs_igA1b.regs_out0 KS_igA1b = true. Proof. vm_compute. reflexivity. Qed.
Definition igA1b_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24S,;#1B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8I+v24#100#28B#2v21#4000B#1000v23#7???????<000,2_v2#20#20+v24#100#28,1,<X#36528#365><Y,T,:_v21#1T,<+v23#1Lb+v24#120_v21#1Lb+v24#118+v23#1Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000"%pstring.
Lemma igA1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_igA1b] fx R M V igA1b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_igA1b] LibSegJs_igA1b.regs0 LibSegJs_igA1b.kn0 LibSegJs_igA1b.BR LibSegJs_igA1b.PSS LibSegJs_igA1b.NX0 LibSegJs_igA1b.F0 222504 LibSegJs_igA1b.seg_sound_ax fx R M V igA1b_conc_s. Qed.
Definition KS_igA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_igA0.regs0 LibSegJs_igA0.regs_out0).
Lemma KS_igA0_ok : BG.kept_ok 48 LibSegJs_igA0.regs0 LibSegJs_igA0.regs_out0 KS_igA0 = true. Proof. vm_compute. reflexivity. Qed.
Definition igA0_conc_s := ",13A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24S,;#1B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8I+v24#100#28,2_v2#20#20+v24#100#28,1,12X#36528#36:08Y,T,1#3659<T,2_v2#20T,8v24T,9#1T,;v22T,<#4000T,12#Lb+v24#118v22Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000Lb+v24#120#Jb+v24#100#8"%pstring.
Lemma igA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_igA0] fx R M V igA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_igA0] LibSegJs_igA0.regs0 LibSegJs_igA0.kn0 LibSegJs_igA0.BR LibSegJs_igA0.PSS LibSegJs_igA0.NX0 LibSegJs_igA0.F0 222504 LibSegJs_igA0.seg_sound_ax fx R M V igA0_conc_s. Qed.
Definition KS_igB0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_igB0.regs0 LibSegJs_igB0.regs_out0).
Lemma KS_igB0_ok : BG.kept_ok 48 LibSegJs_igB0.regs0 LibSegJs_igB0.regs_out0 KS_igB0 = true. Proof. vm_compute. reflexivity. Qed.
Definition igB0_conc_s := ",1<A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v24S,9#1S,:#S,12#B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;,2_v2#20#20+v24#100#28,1,10X#3659<#365><Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;"%pstring.
Lemma igB0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_igB0] fx R M V igB0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_igB0] LibSegJs_igB0.regs0 LibSegJs_igB0.kn0 LibSegJs_igB0.BR LibSegJs_igB0.PSS LibSegJs_igB0.NX0 LibSegJs_igB0.F0 222620 LibSegJs_igB0.seg_sound_ax fx R M V igB0_conc_s. Qed.
Definition KS_igB1a : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_igB1a.regs0 LibSegJs_igB1a.regs_out0).
Lemma KS_igB1a_ok : BG.kept_ok 48 LibSegJs_igB1a.regs0 LibSegJs_igB1a.regs_out0 KS_igB1a = true. Proof. vm_compute. reflexivity. Qed.
Definition igB1a_conc_s := ",1=A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v24S,9#1S,:#1S,12#B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28B#1000v22#7???????<000La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;,2_v2#20#20+v24#100#28,1,12X#3659<#365><Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;+v22#1T,=v22T,12v2;Lb+v24#120#Lb+v24#118+v22#1Lb+v24#108v22Lb+v24#110#4000Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;"%pstring.
Lemma igB1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_igB1a] fx R M V igB1a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_igB1a] LibSegJs_igB1a.regs0 LibSegJs_igB1a.kn0 LibSegJs_igB1a.BR LibSegJs_igB1a.PSS LibSegJs_igB1a.NX0 LibSegJs_igB1a.F0 222620 LibSegJs_igB1a.seg_sound_ax fx R M V igB1a_conc_s. Qed.
Definition KS_igB1b : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_igB1b.regs0 LibSegJs_igB1b.regs_out0).
Lemma KS_igB1b_ok : BG.kept_ok 48 LibSegJs_igB1b.regs0 LibSegJs_igB1b.regs_out0 KS_igB1b = true. Proof. vm_compute. reflexivity. Qed.
Definition igB1b_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v24S,9#1S,:v21S,12#B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8I+v24#100#28B#2v21#4000B#1000v22#7???????<000La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;,2_v2#20#20+v24#100#28,1,12X#3659<#365><Y,T,1v28T,2v2T,8v29T,9v2:T,:_v21#1T,;+v22#1T,=v22T,12v2;Lb+v24#120_v21#1Lb+v24#118+v22#1Lb+v24#108v22Lb+v24#110#4000Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;"%pstring.
Lemma igB1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_igB1b] fx R M V igB1b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_igB1b] LibSegJs_igB1b.regs0 LibSegJs_igB1b.kn0 LibSegJs_igB1b.BR LibSegJs_igB1b.PSS LibSegJs_igB1b.NX0 LibSegJs_igB1b.F0 222620 LibSegJs_igB1b.seg_sound_ax fx R M V igB1b_conc_s. Qed.
End PMSPKP.
