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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_fbE LibSegJs_fbA LibSegJs_fbB1 LibSegJs_fbB2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSFBP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_fbE : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_fbE.regs0 LibSegJs_fbE.regs_out0).
Lemma KS_fbE_ok : BG.kept_ok 48 LibSegJs_fbE.regs0 LibSegJs_fbE.regs_out0 KS_fbE = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition fbE_conc_s := ",17A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128B#7???7?800020v25#7????????>?0Hv25#8P_v2#20#20v25#110O#10000#;60=0Pv24#128v25#110La+v24#?0v25La+v24#?8+v25#10Lav25#;2:98La+v25#10#;29:8Ma+v25#98#2Ma+v25#9<#La+v25#:0+v25#10,1_v2#20#20,1,8X#36:08#36:=4Y,T,:#T,<#78Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma fbE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_fbE] fx R M V fbE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_fbE] LibSegJs_fbE.regs0 LibSegJs_fbE.kn0 LibSegJs_fbE.BR LibSegJs_fbE.PSS LibSegJs_fbE.NX0 LibSegJs_fbE.F0 223752 LibSegJs_fbE.seg_sound_ax fx R M V fbE_conc_s. Qed.
Definition KS_fbA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_fbA.regs0 LibSegJs_fbA.regs_out0).
Lemma KS_fbA_ok : BG.kept_ok 48 LibSegJs_fbA.regs0 LibSegJs_fbA.regs_out0 KS_fbA = true. Proof. vm_compute. reflexivity. Qed.
Definition fbA_conc_s := ",17A#v2p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128B#7???7?800020v25#7????????>?0Hv25#8P_v2#20#20v25#110O#10000#;60=0Pv24#128v25#110La+v24#?0v25La+v24#?8+v25#10Lav25#;2:98La+v25#10#;29:8Ma+v25#98#Ma+v25#9<#La+v25#:0+v25#10,1_v2#20#20,1,<X#36:08#5;254Y,T,1#36:54T,2_v2#20T,8v24T,:+v25#10T,=#5;254U,12,<Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma fbA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_fbA] fx R M V fbA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_fbA] LibSegJs_fbA.regs0 LibSegJs_fbA.kn0 LibSegJs_fbA.BR LibSegJs_fbA.PSS LibSegJs_fbA.NX0 LibSegJs_fbA.F0 223752 LibSegJs_fbA.seg_sound_ax fx R M V fbA_conc_s. Qed.
Definition KS_fbB1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_fbB1.regs0 LibSegJs_fbB1.regs_out0).
Lemma KS_fbB1_ok : BG.kept_ok 48 LibSegJs_fbB1.regs0 LibSegJs_fbB1.regs_out0 KS_fbB1 = true. Proof. vm_compute. reflexivity. Qed.
Definition fbB1_conc_s := ",21A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v24S,:#4000S,12#4000B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128B#7???7?800020v25#7????????>?0Hv25#8P_v2#20#20v25#110O#10000#;60=0Pv24#128v25#110La+v24#?0v25La+v24#?8+v25#10Lav25#;2:98La+v25#10#;29:8Ma+v25#98#Ma+v25#9<#La+v25#:0+v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;,1_v2#20#20,1,;X#36:54#36:=4Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;"%pstring.
Lemma fbB1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_fbB1] fx R M V fbB1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_fbB1] LibSegJs_fbB1.regs0 LibSegJs_fbB1.kn0 LibSegJs_fbB1.BR LibSegJs_fbB1.PSS LibSegJs_fbB1.NX0 LibSegJs_fbB1.F0 223828 LibSegJs_fbB1.seg_sound_ax fx R M V fbB1_conc_s. Qed.
Definition KS_fbB2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_fbB2.regs0 LibSegJs_fbB2.regs_out0).
Lemma KS_fbB2_ok : BG.kept_ok 48 LibSegJs_fbB2.regs0 LibSegJs_fbB2.regs_out0 KS_fbB2 = true. Proof. vm_compute. reflexivity. Qed.
Definition fbB2_conc_s := ",24A#v2p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v24S,:v23S,12#4000B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800020v24#7????????>=8Hv24#8P_v2#20#20v24#128B#7???7?800020v25#7????????>?0Hv25#8P_v2#20#20v25#110O#10000#;60=0Pv24#128v25#110La+v24#?0v25La+v24#?8+v25#10Lav25#;2:98La+v25#10#;29:8Ma+v25#98#Ma+v25#9<#La+v25#:0+v25#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;B#v23#3???I+v25#98#4,2_v2#20#20+v25#98#4,1,?X#36:54#36:=4Y,T,1v28T,2v2T,8v29T,9v2:T,;#2T,<#T,=#T,12v2;Mb+v25#98#2Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;"%pstring.
Lemma fbB2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_fbB2] fx R M V fbB2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_fbB2] LibSegJs_fbB2.regs0 LibSegJs_fbB2.kn0 LibSegJs_fbB2.BR LibSegJs_fbB2.PSS LibSegJs_fbB2.NX0 LibSegJs_fbB2.F0 223828 LibSegJs_fbB2.seg_sound_ax fx R M V fbB2_conc_s. Qed.
End PMSFBP.
