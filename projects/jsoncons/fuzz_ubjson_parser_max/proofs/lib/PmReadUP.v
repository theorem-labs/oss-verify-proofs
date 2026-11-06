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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_urcA LibSegJu_urcB LibSegJu_urcC LibSegJu_urcD LibSegJu_urcE.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMRDUP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_urcA : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_urcA.regs0 LibSegJu_urcA.regs_out0).
Lemma KS_urcA_ok : BG.kept_ok 52 LibSegJu_urcA.regs0 LibSegJu_urcA.regs_out0 KS_urcA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition urcA_conc_s := ",?A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21S,;+v21#190S,<v22B#7???7?8000;0v2#800000000000Hv2#10I_v2#;0#;0B#7???7?8000;0v21#7????????=60Hv21#8P_v2#;0#;0v21#2:0Iv21#180O#10000#;7120,4_v2#;0#;0+v21##18+v21#20#10+v21#70#88,1,24X#35>;<#80910Y,T,1#36114T,2_v2#:0T,8+v21#20T,9+v21#70T,:+v21#:0T,12+v21#190Kb+v21#:8#50Mb+v21#90#Lb+v21#88#Lb+v21#80#6Mb+v21#78#1002Lb+v21#98+v21#30Mb+v21#94#Lb+v21#28#Lb+v21#20#;04?8Lb+v21#:0#Lb+v21#70#;0520Lb_v2#98+v21#18Lb_v2#90+v21#20Lb_v2#88#36058Lb_v2#80v22Lb_v2#78+v21#18Lb_v2#70v21Lb_v2#68#35?0<Nb+v21#10#Mb+v21#<#QNb+v21#8#1Nb++v21#8#1#Lbv21#;0410Mb+v21#14#Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma urcA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_urcA] fx R M V urcA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_urcA] LibSegJu_urcA.regs0 LibSegJu_urcA.kn0 LibSegJu_urcA.BR LibSegJu_urcA.PSS LibSegJu_urcA.NX0 LibSegJu_urcA.F0 220860 LibSegJu_urcA.seg_sound_ax fx R M V urcA_conc_s. Qed.
Definition KS_urcB : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_urcB.regs0 LibSegJu_urcB.regs_out0).
Lemma KS_urcB_ok : BG.kept_ok 52 LibSegJu_urcB.regs0 LibSegJu_urcB.regs_out0 KS_urcB = true. Proof. vm_compute. reflexivity. Qed.
Definition urcB_conc_s := ",=A#v2p#2#40A#v21p#2#40S,2_v2#:0S,8+v21#20S,9+v21#70B#7???7?8000;0v2#800000000000Hv2#10I_v2#;0#;0B#7???7?8000;0v21#7????????=60Hv21#8P_v2#;0#;0v21#2:0Iv21#180O#10000#;7120,4+v21#20#8+v21#30#8+v21#70#8+v21#?8#<,1,;X#36114#80910Y,T,1#36150T,:+v21#38T,;#;3978T,<#;04;0Lb+v21#30#;3978Lb+v21#20#;0488Lb+v21#70#;04;0Mb+v21#100^#?#???????????????Lb+v21#?8#"%pstring.
Lemma urcB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urcB] fx R M V urcB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urcB] LibSegJu_urcB.regs0 LibSegJu_urcB.kn0 LibSegJu_urcB.BR LibSegJu_urcB.PSS LibSegJu_urcB.NX0 LibSegJu_urcB.F0 221460 LibSegJu_urcB.seg_sound_ax fx R M V urcB_conc_s. Qed.
Definition KS_urcC : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_urcC.regs0 LibSegJu_urcC.regs_out0).
Lemma KS_urcC_ok : BG.kept_ok 52 LibSegJu_urcC.regs0 LibSegJu_urcC.regs_out0 KS_urcC = true. Proof. vm_compute. reflexivity. Qed.
Definition urcC_conc_s := ",13A#v2p#2#40A#v21p#2#40S,2_v2#:0S,8+v21#20S,9+v21#70S,12+v21#190B#7???7?8000;0v2#800000000000Hv2#10I_v2#;0#;0B#7???7?8000;0v21#7????????=60Hv21#8P_v2#;0#;0v21#2:0Iv21#180O#10000#;7120La_v2#88#36058La_v2#90+v21#20La_v2#98+v21#18La+v21#190#;3:>8La+v21#230+v21#1:0,3+v21#30#8+v21#40#30+v21#108#38,1,11X#36150#:?0><Y,T,1#36098T,2_v2#80T,9+v21#18T,:#4000T,;#4000T,12+v21#208Lb+v21#138#Lb+v21#130#Lb+v21#128#4000Lb+v21#120#Lb+v21#118#Lb+v21#110+v21#1:0Lb+v21#108+v21#190Lb+v21#30#;0558Kb+v21#40#30"%pstring.
Lemma urcC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_urcC] fx R M V urcC_conc_s).
Proof. r1pf L5KA.zeros_at [KS_urcC] LibSegJu_urcC.regs0 LibSegJu_urcC.kn0 LibSegJu_urcC.BR LibSegJu_urcC.PSS LibSegJu_urcC.NX0 LibSegJu_urcC.F0 221520 LibSegJu_urcC.seg_sound_ax fx R M V urcC_conc_s. Qed.
Definition KS_urcD : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_urcD.regs0 LibSegJu_urcD.regs_out0).
Lemma KS_urcD_ok : BG.kept_ok 52 LibSegJu_urcD.regs0 LibSegJu_urcD.regs_out0 KS_urcD = true. Proof. vm_compute. reflexivity. Qed.
Definition urcD_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40S,2_v2#80S,8+v21#20S,9+v21#18S,:v23B#7???7?8000;0v2#800000000000Hv2#10I_v2#;0#;0B#7???7?8000;0v21#7????????=60Hv21#8P_v2#;0#;0v21#2:0Iv21#180B#7???7?8000;0v22#7?????????>0Hv22#8P_v2#;0#;0v22#20Pv22#20v21#2:0O#10000#;7120La_v2#68#35?0<La_v2#70v21La_v2#78+v21#18La_v2#80v22Lav22#;0390La+v22#8#1000000Ma+v22#18#400,5_v2#90#30_v2#38#10+v21#120#8+v21#130#8+v21#140#40,1,1=X#36098#:?0><Y,T,1#363><T,2_v2#90T,8#1T,9#T,:#20T,;#1T,<#T,=+v21#168T,12+v21#168Lb_v2#90_v2#50Lb_v2#88#36208Lb_v2#30+v21#168Lb_v2#38#Lb_v2#78+v21#18Lb_v2#70v21Lb_v2#68#35?60Lb+v21#178#Lb+v21#170#Lb+v21#168#Lb+v21#160#Lb+v21#158#Lb+v21#150#Lb+v21#148#1000000Mb+v21#140#400Lb+v21#130v23Lb+v21#120v23Lb_v2#80v22"%pstring.
Lemma urcD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urcD] fx R M V urcD_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urcD] LibSegJu_urcD.regs0 LibSegJu_urcD.kn0 LibSegJu_urcD.BR LibSegJu_urcD.PSS LibSegJu_urcD.NX0 LibSegJu_urcD.F0 221336 LibSegJu_urcD.seg_sound_ax fx R M V urcD_conc_s. Qed.
Definition KS_urcE : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_urcE.regs0 LibSegJu_urcE.regs_out0).
Lemma KS_urcE_ok : BG.kept_ok 52 LibSegJu_urcE.regs0 LibSegJu_urcE.regs_out0 KS_urcE = true. Proof. vm_compute. reflexivity. Qed.
Definition urcE_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40S,2_v2#90S,8#1S,9#S,:v24S,12+v21#168B#7???7?8000;0v2#800000000000Hv2#10I_v2#;0#;0B#7???7?8000;0v21#7????????=60Hv21#8P_v2#;0#;0v21#2:0Iv21#180O#10000#;7120La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#28v2?La_v2#68#35?60La_v2#70v21La_v2#78+v21#18La_v2#88#36208La_v2#90_v2#50La_v2#38#La_v2#30+v21#168La+v21#168#La+v21#170#La+v21#178#B#1000v24#7?????????>0Hv24#10Iv24#20P_v2#;0#;0v24#20Pv24#20v21#2:0,4_v2#80#20_v2#50#20+v21#168#18+v24##20,1,16X#363><#35?=<Y,T,1v2;T,2v2T,8v2<T,9v2=T,:#20T,;+v21#168T,<#T,=#T,>#T,?#T,10#T,12v2>T,13v2?Lb+v21#170+v24#20Lb+v21#178+v24#20Lb+v21#168v24Lb+v24#18#Nb+v24#10#Lb+v24#8#Mbv24#"%pstring.
Lemma urcE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urcE] fx R M V urcE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urcE] LibSegJu_urcE.regs0 LibSegJu_urcE.kn0 LibSegJu_urcE.BR LibSegJu_urcE.PSS LibSegJu_urcE.NX0 LibSegJu_urcE.F0 222188 LibSegJu_urcE.seg_sound_ax fx R M V urcE_conc_s. Qed.
End PMRDUP.
