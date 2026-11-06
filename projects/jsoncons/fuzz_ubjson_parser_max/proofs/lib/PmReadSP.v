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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_rcA LibSegJs_rcB LibSegJs_rcC LibSegJs_rcD LibSegJs_rcE.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMRDP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_rcA : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_rcA.regs0 LibSegJs_rcA.regs_out0).
Lemma KS_rcA_ok : BG.kept_ok 52 LibSegJs_rcA.regs0 LibSegJs_rcA.regs_out0 KS_rcA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition rcA_conc_s := ",?A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21S,;+v21#190S,<v22B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v21#7????????=60Hv21#8P_v2#:0#:0v21#2:0Iv21#180O#10000#;60=0,4_v2#:0#:0+v21##18+v21#20#10+v21#70#88,1,24X#355?8#7?8;<Y,T,1#35834T,2_v2#90T,8+v21#20T,9+v21#70T,:+v21#:0T,12+v21#190Kb+v21#:8#50Mb+v21#90#Lb+v21#88#Lb+v21#80#6Mb+v21#78#1002Lb+v21#98+v21#30Mb+v21#94#Lb+v21#28#Lb+v21#20#:?4:8Lb+v21#:0#Lb+v21#70#:?4=0Lb_v2#88+v21#18Lb_v2#80+v21#20Lb_v2#78#35784Lb_v2#70v22Lb_v2#68+v21#18Lb_v2#60v21Lb_v2#58#35648Nb+v21#10#Mb+v21#<#QNb+v21#8#1Nb++v21#8#1#Lbv21#:?3<0Mb+v21#14#Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rcA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_rcA] fx R M V rcA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_rcA] LibSegJs_rcA.regs0 LibSegJs_rcA.kn0 LibSegJs_rcA.BR LibSegJs_rcA.PSS LibSegJs_rcA.NX0 LibSegJs_rcA.F0 218616 LibSegJs_rcA.seg_sound_ax fx R M V rcA_conc_s. Qed.
Definition KS_rcB : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_rcB.regs0 LibSegJs_rcB.regs_out0).
Lemma KS_rcB_ok : BG.kept_ok 52 LibSegJs_rcB.regs0 LibSegJs_rcB.regs_out0 KS_rcB = true. Proof. vm_compute. reflexivity. Qed.
Definition rcB_conc_s := ",=A#v2p#2#40A#v21p#2#40S,2_v2#90S,8+v21#20S,9+v21#70B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v21#7????????=60Hv21#8P_v2#:0#:0v21#2:0Iv21#180O#10000#;60=0,4+v21#20#8+v21#30#8+v21#70#8+v21#?8#<,1,;X#35834#7?8;<Y,T,1#35870T,:+v21#38T,;#;2928T,<#:?460Lb+v21#30#;2928Lb+v21#20#:?438Lb+v21#70#:?460Mb+v21#100^#?#???????????????Lb+v21#?8#"%pstring.
Lemma rcB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rcB] fx R M V rcB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rcB] LibSegJs_rcB.regs0 LibSegJs_rcB.kn0 LibSegJs_rcB.BR LibSegJs_rcB.PSS LibSegJs_rcB.NX0 LibSegJs_rcB.F0 219188 LibSegJs_rcB.seg_sound_ax fx R M V rcB_conc_s. Qed.
Definition KS_rcC : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_rcC.regs0 LibSegJs_rcC.regs_out0).
Lemma KS_rcC_ok : BG.kept_ok 52 LibSegJs_rcC.regs0 LibSegJs_rcC.regs_out0 KS_rcC = true. Proof. vm_compute. reflexivity. Qed.
Definition rcC_conc_s := ",13A#v2p#2#40A#v21p#2#40S,2_v2#90S,8+v21#20S,9+v21#70S,12+v21#190B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v21#7????????=60Hv21#8P_v2#:0#:0v21#2:0Iv21#180O#10000#;60=0La_v2#78#35784La_v2#80+v21#20La_v2#88+v21#18La+v21#190#;2:98La+v21#230+v21#1:0,3+v21#30#8+v21#40#30+v21#108#38,1,10X#35870#:>098Y,T,1#357;<T,2_v2#70T,9+v21#18T,:#4000T,;#4000Lb+v21#138#Lb+v21#130#Lb+v21#128#4000Lb+v21#120#Lb+v21#118#Lb+v21#110+v21#1:0Lb+v21#108+v21#190Lb+v21#30#:?508Kb+v21#40#30"%pstring.
Lemma rcC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_rcC] fx R M V rcC_conc_s).
Proof. r1pf L5KA.zeros_at [KS_rcC] LibSegJs_rcC.regs0 LibSegJs_rcC.kn0 LibSegJs_rcC.BR LibSegJs_rcC.PSS LibSegJs_rcC.NX0 LibSegJs_rcC.F0 219248 LibSegJs_rcC.seg_sound_ax fx R M V rcC_conc_s. Qed.
Definition KS_rcD : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_rcD.regs0 LibSegJs_rcD.regs_out0).
Lemma KS_rcD_ok : BG.kept_ok 52 LibSegJs_rcD.regs0 LibSegJs_rcD.regs_out0 KS_rcD = true. Proof. vm_compute. reflexivity. Qed.
Definition rcD_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40S,2_v2#70S,8+v21#20S,9+v21#18S,:v23S,12+v21#190B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v21#7????????=60Hv21#8P_v2#:0#:0v21#2:0Iv21#180B#7???7?8000:0v22#7?????????>0P_v2#:0#:0v22#20Pv22#20v21#2:0O#10000#;60=0La_v2#58#35648La_v2#60v21La_v2#68+v21#18La_v2#70v22Lav22#:?340La+v22#8#1000000Ma+v22#18#400,5_v2#60#10_v2#30#8+v21#120#8+v21#130#8+v21#140#40,1,11X#357;<#:>098Y,T,1#3596<T,2_v2#60T,8#1T,:#20T,;#1T,12+v21#150T,13+v21#168Lb_v2#60v21Lb_v2#58#3568<Lb_v2#30+v21#168Kb+v21#150#30Lb+v21#148#1000000Mb+v21#140#400Lb+v21#130v23Lb+v21#120v23"%pstring.
Lemma rcD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_rcD] fx R M V rcD_conc_s).
Proof. r1pf L5KA.zeros_at [KS_rcD] LibSegJs_rcD.regs0 LibSegJs_rcD.kn0 LibSegJs_rcD.BR LibSegJs_rcD.PSS LibSegJs_rcD.NX0 LibSegJs_rcD.F0 219068 LibSegJs_rcD.seg_sound_ax fx R M V rcD_conc_s. Qed.
Definition KS_rcE : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_rcE.regs0 LibSegJs_rcE.regs_out0).
Lemma KS_rcE_ok : BG.kept_ok 52 LibSegJs_rcE.regs0 LibSegJs_rcE.regs_out0 KS_rcE = true. Proof. vm_compute. reflexivity. Qed.
Definition rcE_conc_s := ",25A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40S,2_v2#60S,8#1S,9+v21#18S,:v24S,12+v21#150S,13+v21#168B#7???7?8000:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?8000:0v21#7????????=60Hv21#8P_v2#:0#:0v21#2:0Iv21#180O#10000#;60=0La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#28v2?La_v2#58#3568<La_v2#60v21La+v21#168#La+v21#170#La+v21#178#B#1000v24#7?????????>0Hv24#10Iv24#20P_v2#:0#:0v24#20Pv24#20v21#2:0,3_v2#50#20+v21#168#18+v24##20,1,15X#3596<#3570<Y,T,1v2;T,2v2T,8v2<T,9v2=T,:_v2#50T,;#T,<#T,=v24T,>#T,?#T,12v2>T,13v2?Lb+v21#170+v24#20Lb+v21#178+v24#20Lb+v21#168v24Lb+v24#18#Nb+v24#10#Lb+v24#8#Mbv24#"%pstring.
Lemma rcE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rcE] fx R M V rcE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rcE] LibSegJs_rcE.regs0 LibSegJs_rcE.kn0 LibSegJs_rcE.BR LibSegJs_rcE.PSS LibSegJs_rcE.NX0 LibSegJs_rcE.F0 219500 LibSegJs_rcE.seg_sound_ax fx R M V rcE_conc_s. Qed.
End PMRDP.
