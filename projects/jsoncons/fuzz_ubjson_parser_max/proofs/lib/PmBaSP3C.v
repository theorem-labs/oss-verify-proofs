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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_baCs0 LibSegJs_baCs1 LibSegJs_baCs2 LibSegJs_baCs3 LibSegJs_baCs4 LibSegJs_baCs5 LibSegJs_baCs6 LibSegJs_baCs7 LibSegJs_baCs8 LibSegJs_baCs9 LibSegJs_baCs10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBAP3C.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_baCs0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCs0.regs0 LibSegJs_baCs0.regs_out0).
Lemma KS_baCs0_ok : BG.kept_ok 64 LibSegJs_baCs0.regs0 LibSegJs_baCs0.regs_out0 KS_baCs0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition baCs0_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#20La+v24#178+v22#20B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#371:4#:>098Y,T,1#3596<T,2_v2#80T,8#2T,:#40T,;#2T,<#20T,=^#7#?????????????>0T,>v22T,13v30T,14#20Lb_v2#80v24Lb_v2#78#3734<Lb_v2#48+v24#168"%pstring.
Lemma baCs0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCs0] fx R M V baCs0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCs0] LibSegJs_baCs0.regs0 LibSegJs_baCs0.kn0 LibSegJs_baCs0.BR LibSegJs_baCs0.PSS LibSegJs_baCs0.NX0 LibSegJs_baCs0.F0 225700 LibSegJs_baCs0.seg_sound_ax fx R M V baCs0_conc_s. Qed.
Definition KS_baCs1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCs1.regs0 LibSegJs_baCs1.regs_out0).
Lemma KS_baCs1_ok : BG.kept_ok 64 LibSegJs_baCs1.regs0 LibSegJs_baCs1.regs_out0 KS_baCs1 = true. Proof. vm_compute. reflexivity. Qed.
Definition baCs1_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#40La+v24#178+v22#40B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#371:4#:>098Y,T,1#3596<T,2_v2#80T,8#4T,:#80T,;#4T,<#40T,=^#7#?????????????>0T,>v22T,13v30T,14#40Lb_v2#80v24Lb_v2#78#3734<Lb_v2#48+v24#168"%pstring.
Lemma baCs1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCs1] fx R M V baCs1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCs1] LibSegJs_baCs1.regs0 LibSegJs_baCs1.kn0 LibSegJs_baCs1.BR LibSegJs_baCs1.PSS LibSegJs_baCs1.NX0 LibSegJs_baCs1.F0 225700 LibSegJs_baCs1.seg_sound_ax fx R M V baCs1_conc_s. Qed.
Definition KS_baCs2 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCs2.regs0 LibSegJs_baCs2.regs_out0).
Lemma KS_baCs2_ok : BG.kept_ok 64 LibSegJs_baCs2.regs0 LibSegJs_baCs2.regs_out0 KS_baCs2 = true. Proof. vm_compute. reflexivity. Qed.
Definition baCs2_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#80La+v24#178+v22#80B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#371:4#:>098Y,T,1#3596<T,2_v2#80T,8#8T,:#100T,;#8T,<#80T,=^#7#?????????????>0T,>v22T,13v30T,14#80Lb_v2#80v24Lb_v2#78#3734<Lb_v2#48+v24#168"%pstring.
Lemma baCs2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCs2] fx R M V baCs2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCs2] LibSegJs_baCs2.regs0 LibSegJs_baCs2.kn0 LibSegJs_baCs2.BR LibSegJs_baCs2.PSS LibSegJs_baCs2.NX0 LibSegJs_baCs2.F0 225700 LibSegJs_baCs2.seg_sound_ax fx R M V baCs2_conc_s. Qed.
Definition KS_baCs3 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCs3.regs0 LibSegJs_baCs3.regs_out0).
Lemma KS_baCs3_ok : BG.kept_ok 64 LibSegJs_baCs3.regs0 LibSegJs_baCs3.regs_out0 KS_baCs3 = true. Proof. vm_compute. reflexivity. Qed.
Definition baCs3_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#100La+v24#178+v22#100B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#371:4#:>098Y,T,1#3596<T,2_v2#80T,8#10T,:#200T,;#10T,<#100T,=^#7#?????????????>0T,>v22T,13v30T,14#100Lb_v2#80v24Lb_v2#78#3734<Lb_v2#48+v24#168"%pstring.
Lemma baCs3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCs3] fx R M V baCs3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCs3] LibSegJs_baCs3.regs0 LibSegJs_baCs3.kn0 LibSegJs_baCs3.BR LibSegJs_baCs3.PSS LibSegJs_baCs3.NX0 LibSegJs_baCs3.F0 225700 LibSegJs_baCs3.seg_sound_ax fx R M V baCs3_conc_s. Qed.
Definition KS_baCs4 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCs4.regs0 LibSegJs_baCs4.regs_out0).
Lemma KS_baCs4_ok : BG.kept_ok 64 LibSegJs_baCs4.regs0 LibSegJs_baCs4.regs_out0 KS_baCs4 = true. Proof. vm_compute. reflexivity. Qed.
Definition baCs4_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#200La+v24#178+v22#200B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#371:4#:>098Y,T,1#3596<T,2_v2#80T,8#20T,:#400T,;#20T,<#200T,=^#7#?????????????>0T,>v22T,13v30T,14#200Lb_v2#80v24Lb_v2#78#3734<Lb_v2#48+v24#168"%pstring.
Lemma baCs4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCs4] fx R M V baCs4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCs4] LibSegJs_baCs4.regs0 LibSegJs_baCs4.kn0 LibSegJs_baCs4.BR LibSegJs_baCs4.PSS LibSegJs_baCs4.NX0 LibSegJs_baCs4.F0 225700 LibSegJs_baCs4.seg_sound_ax fx R M V baCs4_conc_s. Qed.
Definition KS_baCs5 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCs5.regs0 LibSegJs_baCs5.regs_out0).
Lemma KS_baCs5_ok : BG.kept_ok 64 LibSegJs_baCs5.regs0 LibSegJs_baCs5.regs_out0 KS_baCs5 = true. Proof. vm_compute. reflexivity. Qed.
Definition baCs5_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#400La+v24#178+v22#400B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#371:4#:>098Y,T,1#3596<T,2_v2#80T,8#40T,:#800T,;#40T,<#400T,=^#7#?????????????>0T,>v22T,13v30T,14#400Lb_v2#80v24Lb_v2#78#3734<Lb_v2#48+v24#168"%pstring.
Lemma baCs5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCs5] fx R M V baCs5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCs5] LibSegJs_baCs5.regs0 LibSegJs_baCs5.kn0 LibSegJs_baCs5.BR LibSegJs_baCs5.PSS LibSegJs_baCs5.NX0 LibSegJs_baCs5.F0 225700 LibSegJs_baCs5.seg_sound_ax fx R M V baCs5_conc_s. Qed.
Definition KS_baCs6 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCs6.regs0 LibSegJs_baCs6.regs_out0).
Lemma KS_baCs6_ok : BG.kept_ok 64 LibSegJs_baCs6.regs0 LibSegJs_baCs6.regs_out0 KS_baCs6 = true. Proof. vm_compute. reflexivity. Qed.
Definition baCs6_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#800La+v24#178+v22#800B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#371:4#:>098Y,T,1#3596<T,2_v2#80T,8#80T,:#1000T,;#80T,<#800T,=^#7#?????????????>0T,>v22T,13v30T,14#800Lb_v2#80v24Lb_v2#78#3734<Lb_v2#48+v24#168"%pstring.
Lemma baCs6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCs6] fx R M V baCs6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCs6] LibSegJs_baCs6.regs0 LibSegJs_baCs6.kn0 LibSegJs_baCs6.BR LibSegJs_baCs6.PSS LibSegJs_baCs6.NX0 LibSegJs_baCs6.F0 225700 LibSegJs_baCs6.seg_sound_ax fx R M V baCs6_conc_s. Qed.
Definition KS_baCs7 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCs7.regs0 LibSegJs_baCs7.regs_out0).
Lemma KS_baCs7_ok : BG.kept_ok 64 LibSegJs_baCs7.regs0 LibSegJs_baCs7.regs_out0 KS_baCs7 = true. Proof. vm_compute. reflexivity. Qed.
Definition baCs7_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#1000La+v24#178+v22#1000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#371:4#:>098Y,T,1#3596<T,2_v2#80T,8#100T,:#2000T,;#100T,<#1000T,=^#7#?????????????>0T,>v22T,13v30T,14#1000Lb_v2#80v24Lb_v2#78#3734<Lb_v2#48+v24#168"%pstring.
Lemma baCs7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCs7] fx R M V baCs7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCs7] LibSegJs_baCs7.regs0 LibSegJs_baCs7.kn0 LibSegJs_baCs7.BR LibSegJs_baCs7.PSS LibSegJs_baCs7.NX0 LibSegJs_baCs7.F0 225700 LibSegJs_baCs7.seg_sound_ax fx R M V baCs7_conc_s. Qed.
Definition KS_baCs8 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCs8.regs0 LibSegJs_baCs8.regs_out0).
Lemma KS_baCs8_ok : BG.kept_ok 64 LibSegJs_baCs8.regs0 LibSegJs_baCs8.regs_out0 KS_baCs8 = true. Proof. vm_compute. reflexivity. Qed.
Definition baCs8_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#2000La+v24#178+v22#2000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#371:4#:>098Y,T,1#3596<T,2_v2#80T,8#200T,:#4000T,;#200T,<#2000T,=^#7#?????????????>0T,>v22T,13v30T,14#2000Lb_v2#80v24Lb_v2#78#3734<Lb_v2#48+v24#168"%pstring.
Lemma baCs8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCs8] fx R M V baCs8_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCs8] LibSegJs_baCs8.regs0 LibSegJs_baCs8.kn0 LibSegJs_baCs8.BR LibSegJs_baCs8.PSS LibSegJs_baCs8.NX0 LibSegJs_baCs8.F0 225700 LibSegJs_baCs8.seg_sound_ax fx R M V baCs8_conc_s. Qed.
Definition KS_baCs9 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCs9.regs0 LibSegJs_baCs9.regs_out0).
Lemma KS_baCs9_ok : BG.kept_ok 64 LibSegJs_baCs9.regs0 LibSegJs_baCs9.regs_out0 KS_baCs9 = true. Proof. vm_compute. reflexivity. Qed.
Definition baCs9_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#4000La+v24#178+v22#4000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#371:4#:>098Y,T,1#3596<T,2_v2#80T,8#400T,:#8000T,;#400T,<#4000T,=^#7#?????????????>0T,>v22T,13v30T,14#4000Lb_v2#80v24Lb_v2#78#3734<Lb_v2#48+v24#168"%pstring.
Lemma baCs9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCs9] fx R M V baCs9_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCs9] LibSegJs_baCs9.regs0 LibSegJs_baCs9.kn0 LibSegJs_baCs9.BR LibSegJs_baCs9.PSS LibSegJs_baCs9.NX0 LibSegJs_baCs9.F0 225700 LibSegJs_baCs9.seg_sound_ax fx R M V baCs9_conc_s. Qed.
Definition KS_baCs10 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJs_baCs10.regs0 LibSegJs_baCs10.regs_out0).
Lemma KS_baCs10_ok : BG.kept_ok 64 LibSegJs_baCs10.regs0 LibSegJs_baCs10.regs_out0 KS_baCs10 = true. Proof. vm_compute. reflexivity. Qed.
Definition baCs10_conc_s := ",26A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v30p#2#40S,2_v2#70S,8v24S,9v26S,:v30S,12v25S,13+v24#18B#7???7?800080v2#800000000000Hv2#10I_v2#80#80B#7???7?800080v24#7????????>80Hv24#8P_v2#80#80v24#180B#7???7?800080v26#7??????????0Hv26#8P_v2#80#80v26#10B#7???7?800080v25#7??????????8Hv25#8P_v2#80#80v25#8O#10000#;60=0Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10I+v24#8#8I+v24#168#18La+v24#168v22La+v24#170+v22#8000La+v24#178+v22#8000B#1000v22#7??????00000Hv22#10Mav26#La+v24#148#1000000B#v30#1000000,2_v2#80#10_v2#48#8,1,?X#371:4#:>098Y,T,1#3596<T,2_v2#80T,8#800T,:#10000T,;#800T,<#8000T,=^#7#?????????????>0T,>v22T,13v30T,14#8000Lb_v2#80v24Lb_v2#78#3734<Lb_v2#48+v24#168"%pstring.
Lemma baCs10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_baCs10] fx R M V baCs10_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_baCs10] LibSegJs_baCs10.regs0 LibSegJs_baCs10.kn0 LibSegJs_baCs10.BR LibSegJs_baCs10.PSS LibSegJs_baCs10.NX0 LibSegJs_baCs10.F0 225700 LibSegJs_baCs10.seg_sound_ax fx R M V baCs10_conc_s. Qed.
End PMBAP3C.
