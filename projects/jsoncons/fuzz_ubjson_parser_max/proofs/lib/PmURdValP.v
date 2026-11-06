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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_ruTC LibSegJu_ruTD LibSegJu_ruTF LibSegJu_ruTH LibSegJu_ruTI LibSegJu_ruTL LibSegJu_ruTN LibSegJu_ruTS LibSegJu_ruTT LibSegJu_ruTU LibSegJu_ruTZ LibSegJu_ruTA LibSegJu_ruTd_c1 LibSegJu_ruTi_c1 LibSegJu_ruTl_c1 LibSegJu_ruTO LibSegJu_ruX69 LibSegJu_ruX71 LibSegJu_ruX74 LibSegJu_ruX75 LibSegJu_ruX77 LibSegJu_ruX79 LibSegJu_ruX80 LibSegJu_ruX81 LibSegJu_ruX82 LibSegJu_ruX86 LibSegJu_ruX87 LibSegJu_ruX88 LibSegJu_ruX89 LibSegJu_ruY0 LibSegJu_ruY92 LibSegJu_ruY101 LibSegJu_ruY106 LibSegJu_ruY109 LibSegJu_ruY124 LibSegJu_ruCN LibSegJu_ruCV LibSegJu_ruDN LibSegJu_ruDV LibSegJu_ruIN LibSegJu_ruIV LibSegJu_ruLN LibSegJu_ruLV LibSegJu_ruUN LibSegJu_ruUV LibSegJu_rudN_c1 LibSegJu_rudV_c1 LibSegJu_ruiN_c1 LibSegJu_ruiV_c1 LibSegJu_rulN_c1 LibSegJu_rulV_c1 LibSegJu_rudV2_c1 LibSegJu_ruDV2 LibSegJu_ruCW LibSegJu_ruCK LibSegJu_ruSG0 LibSegJu_ruSGe LibSegJu_ruSF LibSegJu_ruHG0 LibSegJu_ruHGe LibSegJu_ruHF LibSegJu_ruSW LibSegJu_ruSK LibSegJu_ruHB LibSegJu_ruHK3 LibSegJu_ruHK2 LibSegJu_ruA0 LibSegJu_ruAe LibSegJu_ruO0 LibSegJu_ruOe LibSegJu_ruDfT LibSegJu_ruET.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMURVP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_ruTC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTC.regs0 LibSegJu_ruTC.regs_out0).
Lemma KS_ruTC_ok : BG.kept_ok 48 LibSegJu_ruTC.regs0 LibSegJu_ruTC.regs_out0 KS_ruTC = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition ruTC_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#43S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,12X#36:?<#374;8Y,T,1#36;6<T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#31T,<#1T,12v25T,13#1Nb_v2#31#Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTC] fx R M V ruTC_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTC] LibSegJu_ruTC.regs0 LibSegJu_ruTC.kn0 LibSegJu_ruTC.BR LibSegJu_ruTC.PSS LibSegJu_ruTC.NX0 LibSegJu_ruTC.F0 223996 LibSegJu_ruTC.seg_sound_ax fx R M V ruTC_conc_s. Qed.
Definition KS_ruTD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTD.regs0 LibSegJu_ruTD.regs_out0).
Lemma KS_ruTD_ok : BG.kept_ok 48 LibSegJu_ruTD.regs0 LibSegJu_ruTD.regs_out0 KS_ruTD = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTD_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#44S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#36:?<#374;8Y,T,1#36=>0T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#8T,12v25T,13#8Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTD] fx R M V ruTD_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTD] LibSegJu_ruTD.regs0 LibSegJu_ruTD.kn0 LibSegJu_ruTD.BR LibSegJu_ruTD.PSS LibSegJu_ruTD.NX0 LibSegJu_ruTD.F0 223996 LibSegJu_ruTD.seg_sound_ax fx R M V ruTD_conc_s. Qed.
Definition KS_ruTF : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTF.regs0 LibSegJu_ruTF.regs_out0).
Lemma KS_ruTF_ok : BG.kept_ok 48 LibSegJu_ruTF.regs0 LibSegJu_ruTF.regs_out0 KS_ruTF = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTF_conc_s := ",29A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<#46S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#50#50+v24#8#1,1,?X#36:?<#3704<Y,T,:#T,;#1T,<#T,=v24T,>v26T,?#34864Nb+v24#8#1Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTF] fx R M V ruTF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTF] LibSegJu_ruTF.regs0 LibSegJu_ruTF.kn0 LibSegJu_ruTF.BR LibSegJu_ruTF.PSS LibSegJu_ruTF.NX0 LibSegJu_ruTF.F0 223996 LibSegJu_ruTF.seg_sound_ax fx R M V ruTF_conc_s. Qed.
Definition KS_ruTH : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTH.regs0 LibSegJu_ruTH.regs_out0).
Lemma KS_ruTH_ok : BG.kept_ok 48 LibSegJu_ruTH.regs0 LibSegJu_ruTH.regs_out0 KS_ruTH = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTH_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#48S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,>X#36:?<#37::4Y,T,1#36<54T,2_v2#50T,8v24T,9v26T,;v26T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTH] fx R M V ruTH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTH] LibSegJu_ruTH.regs0 LibSegJu_ruTH.kn0 LibSegJu_ruTH.BR LibSegJu_ruTH.PSS LibSegJu_ruTH.NX0 LibSegJu_ruTH.F0 223996 LibSegJu_ruTH.seg_sound_ax fx R M V ruTH_conc_s. Qed.
Definition KS_ruTI : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTI.regs0 LibSegJu_ruTI.regs_out0).
Lemma KS_ruTI_ok : BG.kept_ok 48 LibSegJu_ruTI.regs0 LibSegJu_ruTI.regs_out0 KS_ruTI = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTI_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#49S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#36:?<#374;8Y,T,1#36=08T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#2T,12v25T,13#2Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTI] fx R M V ruTI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTI] LibSegJu_ruTI.regs0 LibSegJu_ruTI.kn0 LibSegJu_ruTI.BR LibSegJu_ruTI.PSS LibSegJu_ruTI.NX0 LibSegJu_ruTI.F0 223996 LibSegJu_ruTI.seg_sound_ax fx R M V ruTI_conc_s. Qed.
Definition KS_ruTL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTL.regs0 LibSegJu_ruTL.regs_out0).
Lemma KS_ruTL_ok : BG.kept_ok 48 LibSegJu_ruTL.regs0 LibSegJu_ruTL.regs_out0 KS_ruTL = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTL_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#4<S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#36:?<#374;8Y,T,1#36=40T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#8T,12v25T,13#8Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTL] fx R M V ruTL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTL] LibSegJu_ruTL.regs0 LibSegJu_ruTL.kn0 LibSegJu_ruTL.BR LibSegJu_ruTL.PSS LibSegJu_ruTL.NX0 LibSegJu_ruTL.F0 223996 LibSegJu_ruTL.seg_sound_ax fx R M V ruTL_conc_s. Qed.
Definition KS_ruTN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTN.regs0 LibSegJu_ruTN.regs_out0).
Lemma KS_ruTN_ok : BG.kept_ok 48 LibSegJu_ruTN.regs0 LibSegJu_ruTN.regs_out0 KS_ruTN = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTN_conc_s := ",29A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<#4>S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,1_v2#50#50,1,:X#36:?<#3704<Y,T,:#T,;#13680Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTN] fx R M V ruTN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTN] LibSegJu_ruTN.regs0 LibSegJu_ruTN.kn0 LibSegJu_ruTN.BR LibSegJu_ruTN.PSS LibSegJu_ruTN.NX0 LibSegJu_ruTN.F0 223996 LibSegJu_ruTN.seg_sound_ax fx R M V ruTN_conc_s. Qed.
Definition KS_ruTS : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTS.regs0 LibSegJu_ruTS.regs_out0).
Lemma KS_ruTS_ok : BG.kept_ok 48 LibSegJu_ruTS.regs0 LibSegJu_ruTS.regs_out0 KS_ruTS = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTS_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#53S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,>X#36:?<#37::4Y,T,1#36<0<T,2_v2#50T,8v24T,9v26T,;v26T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTS] fx R M V ruTS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTS] LibSegJu_ruTS.regs0 LibSegJu_ruTS.kn0 LibSegJu_ruTS.BR LibSegJu_ruTS.PSS LibSegJu_ruTS.NX0 LibSegJu_ruTS.F0 223996 LibSegJu_ruTS.seg_sound_ax fx R M V ruTS_conc_s. Qed.
Definition KS_ruTT : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTT.regs0 LibSegJu_ruTT.regs_out0).
Lemma KS_ruTT_ok : BG.kept_ok 48 LibSegJu_ruTT.regs0 LibSegJu_ruTT.regs_out0 KS_ruTT = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTT_conc_s := ",29A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<#54S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#50#50+v24#8#1,1,?X#36:?<#3704<Y,T,:#T,;#1T,<#T,=v24T,>v26T,?#34864Nb+v24#8#1Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTT] fx R M V ruTT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTT] LibSegJu_ruTT.regs0 LibSegJu_ruTT.kn0 LibSegJu_ruTT.BR LibSegJu_ruTT.PSS LibSegJu_ruTT.NX0 LibSegJu_ruTT.F0 223996 LibSegJu_ruTT.seg_sound_ax fx R M V ruTT_conc_s. Qed.
Definition KS_ruTU : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTU.regs0 LibSegJu_ruTU.regs_out0).
Lemma KS_ruTU_ok : BG.kept_ok 48 LibSegJu_ruTU.regs0 LibSegJu_ruTU.regs_out0 KS_ruTU = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTU_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#55S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#36:?<#374;8Y,T,1#36>84T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#1T,12v25T,13#1Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTU_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTU] fx R M V ruTU_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTU] LibSegJu_ruTU.regs0 LibSegJu_ruTU.kn0 LibSegJu_ruTU.BR LibSegJu_ruTU.PSS LibSegJu_ruTU.NX0 LibSegJu_ruTU.F0 223996 LibSegJu_ruTU.seg_sound_ax fx R M V ruTU_conc_s. Qed.
Definition KS_ruTZ : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTZ.regs0 LibSegJu_ruTZ.regs_out0).
Lemma KS_ruTZ_ok : BG.kept_ok 48 LibSegJu_ruTZ.regs0 LibSegJu_ruTZ.regs_out0 KS_ruTZ = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTZ_conc_s := ",29A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<#5:S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#50#50+v24#8#1,1,=X#36:?<#3704<Y,T,:#T,;#2T,<v24T,>#3485<Nb+v24#8#1Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTZ] fx R M V ruTZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTZ] LibSegJu_ruTZ.regs0 LibSegJu_ruTZ.kn0 LibSegJu_ruTZ.BR LibSegJu_ruTZ.PSS LibSegJu_ruTZ.NX0 LibSegJu_ruTZ.F0 223996 LibSegJu_ruTZ.seg_sound_ax fx R M V ruTZ_conc_s. Qed.
Definition KS_ruTA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTA.regs0 LibSegJu_ruTA.regs_out0).
Lemma KS_ruTA_ok : BG.kept_ok 48 LibSegJu_ruTA.regs0 LibSegJu_ruTA.regs_out0 KS_ruTA = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTA_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#5;S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,>X#36:?<#37>78Y,T,1#36=<8T,2_v2#50T,8v24T,9v26T,<v26T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTA] fx R M V ruTA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTA] LibSegJu_ruTA.regs0 LibSegJu_ruTA.kn0 LibSegJu_ruTA.BR LibSegJu_ruTA.PSS LibSegJu_ruTA.NX0 LibSegJu_ruTA.F0 223996 LibSegJu_ruTA.seg_sound_ax fx R M V ruTA_conc_s. Qed.
Definition KS_ruTd : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTd_c1.regs0 LibSegJu_ruTd_c1.regs_out0).
Lemma KS_ruTd_ok : BG.kept_ok 48 LibSegJu_ruTd_c1.regs0 LibSegJu_ruTd_c1.regs_out0 KS_ruTd = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTd_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#64S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#36:?<#374;8Y,T,1#36><8T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#4T,12v25T,13#4Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTd_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTd] fx R M V ruTd_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTd] LibSegJu_ruTd_c1.regs0 LibSegJu_ruTd_c1.kn0 LibSegJu_ruTd_c1.BR LibSegJu_ruTd_c1.PSS LibSegJu_ruTd_c1.NX0 LibSegJu_ruTd_c1.F0 223996 LibSegJu_ruTd_c1.seg_sound_ax fx R M V ruTd_conc_s. Qed.
Definition KS_ruTi : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTi_c1.regs0 LibSegJu_ruTi_c1.regs_out0).
Lemma KS_ruTi_ok : BG.kept_ok 48 LibSegJu_ruTi_c1.regs0 LibSegJu_ruTi_c1.regs_out0 KS_ruTi = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTi_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#69S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#36:?<#374;8Y,T,1#36;<8T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#1T,12v25T,13#1Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTi] fx R M V ruTi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTi] LibSegJu_ruTi_c1.regs0 LibSegJu_ruTi_c1.kn0 LibSegJu_ruTi_c1.BR LibSegJu_ruTi_c1.PSS LibSegJu_ruTi_c1.NX0 LibSegJu_ruTi_c1.F0 223996 LibSegJu_ruTi_c1.seg_sound_ax fx R M V ruTi_conc_s. Qed.
Definition KS_ruTl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTl_c1.regs0 LibSegJu_ruTl_c1.regs_out0).
Lemma KS_ruTl_ok : BG.kept_ok 48 LibSegJu_ruTl_c1.regs0 LibSegJu_ruTl_c1.regs_out0 KS_ruTl = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTl_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#6<S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#36:?<#374;8Y,T,1#36?38T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#4T,12v25T,13#4Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTl] fx R M V ruTl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTl] LibSegJu_ruTl_c1.regs0 LibSegJu_ruTl_c1.kn0 LibSegJu_ruTl_c1.BR LibSegJu_ruTl_c1.PSS LibSegJu_ruTl_c1.NX0 LibSegJu_ruTl_c1.F0 223996 LibSegJu_ruTl_c1.seg_sound_ax fx R M V ruTl_conc_s. Qed.
Definition KS_ruTO : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruTO.regs0 LibSegJu_ruTO.regs_out0).
Lemma KS_ruTO_ok : BG.kept_ok 48 LibSegJu_ruTO.regs0 LibSegJu_ruTO.regs_out0 KS_ruTO = true. Proof. vm_compute. reflexivity. Qed.
Definition ruTO_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#7;S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,>X#36:?<#38324Y,T,1#36;?<T,2_v2#50T,8v24T,9v26T,<v26T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruTO_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruTO] fx R M V ruTO_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruTO] LibSegJu_ruTO.regs0 LibSegJu_ruTO.kn0 LibSegJu_ruTO.BR LibSegJu_ruTO.PSS LibSegJu_ruTO.NX0 LibSegJu_ruTO.F0 223996 LibSegJu_ruTO.seg_sound_ax fx R M V ruTO_conc_s. Qed.
Definition KS_ruX69 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX69.regs0 LibSegJu_ruX69.regs_out0).
Lemma KS_ruX69_ok : BG.kept_ok 48 LibSegJu_ruX69.regs0 LibSegJu_ruX69.regs_out0 KS_ruX69 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX69_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#45S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX69_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX69] fx R M V ruX69_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX69] LibSegJu_ruX69.regs0 LibSegJu_ruX69.kn0 LibSegJu_ruX69.BR LibSegJu_ruX69.PSS LibSegJu_ruX69.NX0 LibSegJu_ruX69.F0 223996 LibSegJu_ruX69.seg_sound_ax fx R M V ruX69_conc_s. Qed.
Definition KS_ruX71 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX71.regs0 LibSegJu_ruX71.regs_out0).
Lemma KS_ruX71_ok : BG.kept_ok 48 LibSegJu_ruX71.regs0 LibSegJu_ruX71.regs_out0 KS_ruX71 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX71_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#47S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX71_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX71] fx R M V ruX71_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX71] LibSegJu_ruX71.regs0 LibSegJu_ruX71.kn0 LibSegJu_ruX71.BR LibSegJu_ruX71.PSS LibSegJu_ruX71.NX0 LibSegJu_ruX71.F0 223996 LibSegJu_ruX71.seg_sound_ax fx R M V ruX71_conc_s. Qed.
Definition KS_ruX74 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX74.regs0 LibSegJu_ruX74.regs_out0).
Lemma KS_ruX74_ok : BG.kept_ok 48 LibSegJu_ruX74.regs0 LibSegJu_ruX74.regs_out0 KS_ruX74 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX74_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#4:S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX74_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX74] fx R M V ruX74_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX74] LibSegJu_ruX74.regs0 LibSegJu_ruX74.kn0 LibSegJu_ruX74.BR LibSegJu_ruX74.PSS LibSegJu_ruX74.NX0 LibSegJu_ruX74.F0 223996 LibSegJu_ruX74.seg_sound_ax fx R M V ruX74_conc_s. Qed.
Definition KS_ruX75 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX75.regs0 LibSegJu_ruX75.regs_out0).
Lemma KS_ruX75_ok : BG.kept_ok 48 LibSegJu_ruX75.regs0 LibSegJu_ruX75.regs_out0 KS_ruX75 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX75_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#4;S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX75_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX75] fx R M V ruX75_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX75] LibSegJu_ruX75.regs0 LibSegJu_ruX75.kn0 LibSegJu_ruX75.BR LibSegJu_ruX75.PSS LibSegJu_ruX75.NX0 LibSegJu_ruX75.F0 223996 LibSegJu_ruX75.seg_sound_ax fx R M V ruX75_conc_s. Qed.
Definition KS_ruX77 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX77.regs0 LibSegJu_ruX77.regs_out0).
Lemma KS_ruX77_ok : BG.kept_ok 48 LibSegJu_ruX77.regs0 LibSegJu_ruX77.regs_out0 KS_ruX77 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX77_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#4=S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX77_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX77] fx R M V ruX77_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX77] LibSegJu_ruX77.regs0 LibSegJu_ruX77.kn0 LibSegJu_ruX77.BR LibSegJu_ruX77.PSS LibSegJu_ruX77.NX0 LibSegJu_ruX77.F0 223996 LibSegJu_ruX77.seg_sound_ax fx R M V ruX77_conc_s. Qed.
Definition KS_ruX79 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX79.regs0 LibSegJu_ruX79.regs_out0).
Lemma KS_ruX79_ok : BG.kept_ok 48 LibSegJu_ruX79.regs0 LibSegJu_ruX79.regs_out0 KS_ruX79 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX79_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#4?S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX79_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX79] fx R M V ruX79_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX79] LibSegJu_ruX79.regs0 LibSegJu_ruX79.kn0 LibSegJu_ruX79.BR LibSegJu_ruX79.PSS LibSegJu_ruX79.NX0 LibSegJu_ruX79.F0 223996 LibSegJu_ruX79.seg_sound_ax fx R M V ruX79_conc_s. Qed.
Definition KS_ruX80 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX80.regs0 LibSegJu_ruX80.regs_out0).
Lemma KS_ruX80_ok : BG.kept_ok 48 LibSegJu_ruX80.regs0 LibSegJu_ruX80.regs_out0 KS_ruX80 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX80_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#50S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX80_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX80] fx R M V ruX80_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX80] LibSegJu_ruX80.regs0 LibSegJu_ruX80.kn0 LibSegJu_ruX80.BR LibSegJu_ruX80.PSS LibSegJu_ruX80.NX0 LibSegJu_ruX80.F0 223996 LibSegJu_ruX80.seg_sound_ax fx R M V ruX80_conc_s. Qed.
Definition KS_ruX81 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX81.regs0 LibSegJu_ruX81.regs_out0).
Lemma KS_ruX81_ok : BG.kept_ok 48 LibSegJu_ruX81.regs0 LibSegJu_ruX81.regs_out0 KS_ruX81 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX81_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#51S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX81_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX81] fx R M V ruX81_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX81] LibSegJu_ruX81.regs0 LibSegJu_ruX81.kn0 LibSegJu_ruX81.BR LibSegJu_ruX81.PSS LibSegJu_ruX81.NX0 LibSegJu_ruX81.F0 223996 LibSegJu_ruX81.seg_sound_ax fx R M V ruX81_conc_s. Qed.
Definition KS_ruX82 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX82.regs0 LibSegJu_ruX82.regs_out0).
Lemma KS_ruX82_ok : BG.kept_ok 48 LibSegJu_ruX82.regs0 LibSegJu_ruX82.regs_out0 KS_ruX82 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX82_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#52S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX82_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX82] fx R M V ruX82_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX82] LibSegJu_ruX82.regs0 LibSegJu_ruX82.kn0 LibSegJu_ruX82.BR LibSegJu_ruX82.PSS LibSegJu_ruX82.NX0 LibSegJu_ruX82.F0 223996 LibSegJu_ruX82.seg_sound_ax fx R M V ruX82_conc_s. Qed.
Definition KS_ruX86 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX86.regs0 LibSegJu_ruX86.regs_out0).
Lemma KS_ruX86_ok : BG.kept_ok 48 LibSegJu_ruX86.regs0 LibSegJu_ruX86.regs_out0 KS_ruX86 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX86_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#56S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX86_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX86] fx R M V ruX86_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX86] LibSegJu_ruX86.regs0 LibSegJu_ruX86.kn0 LibSegJu_ruX86.BR LibSegJu_ruX86.PSS LibSegJu_ruX86.NX0 LibSegJu_ruX86.F0 223996 LibSegJu_ruX86.seg_sound_ax fx R M V ruX86_conc_s. Qed.
Definition KS_ruX87 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX87.regs0 LibSegJu_ruX87.regs_out0).
Lemma KS_ruX87_ok : BG.kept_ok 48 LibSegJu_ruX87.regs0 LibSegJu_ruX87.regs_out0 KS_ruX87 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX87_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#57S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX87_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX87] fx R M V ruX87_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX87] LibSegJu_ruX87.regs0 LibSegJu_ruX87.kn0 LibSegJu_ruX87.BR LibSegJu_ruX87.PSS LibSegJu_ruX87.NX0 LibSegJu_ruX87.F0 223996 LibSegJu_ruX87.seg_sound_ax fx R M V ruX87_conc_s. Qed.
Definition KS_ruX88 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX88.regs0 LibSegJu_ruX88.regs_out0).
Lemma KS_ruX88_ok : BG.kept_ok 48 LibSegJu_ruX88.regs0 LibSegJu_ruX88.regs_out0 KS_ruX88 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX88_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#58S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX88_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX88] fx R M V ruX88_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX88] LibSegJu_ruX88.regs0 LibSegJu_ruX88.kn0 LibSegJu_ruX88.BR LibSegJu_ruX88.PSS LibSegJu_ruX88.NX0 LibSegJu_ruX88.F0 223996 LibSegJu_ruX88.seg_sound_ax fx R M V ruX88_conc_s. Qed.
Definition KS_ruX89 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruX89.regs0 LibSegJu_ruX89.regs_out0).
Lemma KS_ruX89_ok : BG.kept_ok 48 LibSegJu_ruX89.regs0 LibSegJu_ruX89.regs_out0 KS_ruX89 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruX89_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#59S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruX89_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruX89] fx R M V ruX89_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruX89] LibSegJu_ruX89.regs0 LibSegJu_ruX89.kn0 LibSegJu_ruX89.BR LibSegJu_ruX89.PSS LibSegJu_ruX89.NX0 LibSegJu_ruX89.F0 223996 LibSegJu_ruX89.seg_sound_ax fx R M V ruX89_conc_s. Qed.
Definition KS_ruY0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruY0.regs0 LibSegJu_ruY0.regs_out0).
Lemma KS_ruY0_ok : BG.kept_ok 48 LibSegJu_ruY0.regs0 LibSegJu_ruY0.regs_out0 KS_ruY0 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruY0_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v21S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#B#v21#42,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruY0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruY0] fx R M V ruY0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruY0] LibSegJu_ruY0.regs0 LibSegJu_ruY0.kn0 LibSegJu_ruY0.BR LibSegJu_ruY0.PSS LibSegJu_ruY0.NX0 LibSegJu_ruY0.F0 223996 LibSegJu_ruY0.seg_sound_ax fx R M V ruY0_conc_s. Qed.
Definition KS_ruY92 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruY92.regs0 LibSegJu_ruY92.regs_out0).
Lemma KS_ruY92_ok : BG.kept_ok 48 LibSegJu_ruY92.regs0 LibSegJu_ruY92.regs_out0 KS_ruY92 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruY92_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v21S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#B#5<v21#63,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruY92_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruY92] fx R M V ruY92_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruY92] LibSegJu_ruY92.regs0 LibSegJu_ruY92.kn0 LibSegJu_ruY92.BR LibSegJu_ruY92.PSS LibSegJu_ruY92.NX0 LibSegJu_ruY92.F0 223996 LibSegJu_ruY92.seg_sound_ax fx R M V ruY92_conc_s. Qed.
Definition KS_ruY101 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruY101.regs0 LibSegJu_ruY101.regs_out0).
Lemma KS_ruY101_ok : BG.kept_ok 48 LibSegJu_ruY101.regs0 LibSegJu_ruY101.regs_out0 KS_ruY101 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruY101_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v21S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#B#65v21#68,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruY101_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruY101] fx R M V ruY101_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruY101] LibSegJu_ruY101.regs0 LibSegJu_ruY101.kn0 LibSegJu_ruY101.BR LibSegJu_ruY101.PSS LibSegJu_ruY101.NX0 LibSegJu_ruY101.F0 223996 LibSegJu_ruY101.seg_sound_ax fx R M V ruY101_conc_s. Qed.
Definition KS_ruY106 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruY106.regs0 LibSegJu_ruY106.regs_out0).
Lemma KS_ruY106_ok : BG.kept_ok 48 LibSegJu_ruY106.regs0 LibSegJu_ruY106.regs_out0 KS_ruY106 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruY106_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v21S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#B#6:v21#6;,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruY106_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruY106] fx R M V ruY106_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruY106] LibSegJu_ruY106.regs0 LibSegJu_ruY106.kn0 LibSegJu_ruY106.BR LibSegJu_ruY106.PSS LibSegJu_ruY106.NX0 LibSegJu_ruY106.F0 223996 LibSegJu_ruY106.seg_sound_ax fx R M V ruY106_conc_s. Qed.
Definition KS_ruY109 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruY109.regs0 LibSegJu_ruY109.regs_out0).
Lemma KS_ruY109_ok : BG.kept_ok 48 LibSegJu_ruY109.regs0 LibSegJu_ruY109.regs_out0 KS_ruY109 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruY109_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v21S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#B#6=v21#7:,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruY109_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruY109] fx R M V ruY109_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruY109] LibSegJu_ruY109.regs0 LibSegJu_ruY109.kn0 LibSegJu_ruY109.BR LibSegJu_ruY109.PSS LibSegJu_ruY109.NX0 LibSegJu_ruY109.F0 223996 LibSegJu_ruY109.seg_sound_ax fx R M V ruY109_conc_s. Qed.
Definition KS_ruY124 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruY124.regs0 LibSegJu_ruY124.regs_out0).
Lemma KS_ruY124_ok : BG.kept_ok 48 LibSegJu_ruY124.regs0 LibSegJu_ruY124.regs_out0 KS_ruY124 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruY124_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v21S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#B#7<v21#??,1_v2#50#50,1,?X#36:?<#370:<Y,T,1#36?98T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ruY124_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruY124] fx R M V ruY124_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruY124] LibSegJu_ruY124.regs0 LibSegJu_ruY124.kn0 LibSegJu_ruY124.BR LibSegJu_ruY124.PSS LibSegJu_ruY124.NX0 LibSegJu_ruY124.F0 223996 LibSegJu_ruY124.seg_sound_ax fx R M V ruY124_conc_s. Qed.
Definition KS_ruCN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruCN.regs0 LibSegJu_ruCN.regs_out0).
Lemma KS_ruCN_ok : BG.kept_ok 48 LibSegJu_ruCN.regs0 LibSegJu_ruCN.regs_out0 KS_ruCN = true. Proof. vm_compute. reflexivity. Qed.
Definition ruCN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:#S,12v25S,13#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,1,5X#36;6<#370:<Y,T,1#36?84T,:v26T,;#1"%pstring.
Lemma ruCN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruCN] fx R M V ruCN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruCN] LibSegJu_ruCN.regs0 LibSegJu_ruCN.kn0 LibSegJu_ruCN.BR LibSegJu_ruCN.PSS LibSegJu_ruCN.NX0 LibSegJu_ruCN.F0 224108 LibSegJu_ruCN.seg_sound_ax fx R M V ruCN_conc_s. Qed.
Definition KS_ruCV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruCV.regs0 LibSegJu_ruCV.regs_out0).
Lemma KS_ruCV_ok : BG.kept_ok 48 LibSegJu_ruCV.regs0 LibSegJu_ruCV.regs_out0 KS_ruCV = true. Proof. vm_compute. reflexivity. Qed.
Definition ruCV_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:#1S,12v25S,13#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Ja_v2#31#1,,1,7X#36;6<#37844Y,T,1#36;84T,:_v2#31T,;#1T,13_v2#31T,14#1"%pstring.
Lemma ruCV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruCV] fx R M V ruCV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruCV] LibSegJu_ruCV.regs0 LibSegJu_ruCV.kn0 LibSegJu_ruCV.BR LibSegJu_ruCV.PSS LibSegJu_ruCV.NX0 LibSegJu_ruCV.F0 224108 LibSegJu_ruCV.seg_sound_ax fx R M V ruCV_conc_s. Qed.
Definition KS_ruDN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruDN.regs0 LibSegJu_ruDN.regs_out0).
Lemma KS_ruDN_ok : BG.kept_ok 48 LibSegJu_ruDN.regs0 LibSegJu_ruDN.regs_out0 KS_ruDN = true. Proof. vm_compute. reflexivity. Qed.
Definition ruDN_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25S,13#8B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#v21#7,,1,5X#36=>0#370:<Y,T,1#36?84T,:v26T,;#1"%pstring.
Lemma ruDN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruDN] fx R M V ruDN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruDN] LibSegJu_ruDN.regs0 LibSegJu_ruDN.kn0 LibSegJu_ruDN.BR LibSegJu_ruDN.PSS LibSegJu_ruDN.NX0 LibSegJu_ruDN.F0 224736 LibSegJu_ruDN.seg_sound_ax fx R M V ruDN_conc_s. Qed.
Definition KS_ruDV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruDV.regs0 LibSegJu_ruDV.regs_out0).
Lemma KS_ruDV_ok : BG.kept_ok 48 LibSegJu_ruDV.regs0 LibSegJu_ruDV.regs_out0 KS_ruDV = true. Proof. vm_compute. reflexivity. Qed.
Definition ruDV_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:#8S,12v25S,13#8B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Ja_v2#48#8,,1,4X#36=>0#36>54Y,T,=#;0238T,?#34800"%pstring.
Lemma ruDV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruDV] fx R M V ruDV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruDV] LibSegJu_ruDV.regs0 LibSegJu_ruDV.kn0 LibSegJu_ruDV.BR LibSegJu_ruDV.PSS LibSegJu_ruDV.NX0 LibSegJu_ruDV.F0 224736 LibSegJu_ruDV.seg_sound_ax fx R M V ruDV_conc_s. Qed.
Definition KS_ruIN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruIN.regs0 LibSegJu_ruIN.regs_out0).
Lemma KS_ruIN_ok : BG.kept_ok 48 LibSegJu_ruIN.regs0 LibSegJu_ruIN.regs_out0 KS_ruIN = true. Proof. vm_compute. reflexivity. Qed.
Definition ruIN_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25S,13#2B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#v21#1,,1,5X#36=08#370:<Y,T,1#36?84T,:v26T,;#1"%pstring.
Lemma ruIN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruIN] fx R M V ruIN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruIN] LibSegJu_ruIN.regs0 LibSegJu_ruIN.kn0 LibSegJu_ruIN.BR LibSegJu_ruIN.PSS LibSegJu_ruIN.NX0 LibSegJu_ruIN.F0 224520 LibSegJu_ruIN.seg_sound_ax fx R M V ruIN_conc_s. Qed.
Definition KS_ruIV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruIV.regs0 LibSegJu_ruIV.regs_out0).
Lemma KS_ruIV_ok : BG.kept_ok 48 LibSegJu_ruIV.regs0 LibSegJu_ruIV.regs_out0 KS_ruIV = true. Proof. vm_compute. reflexivity. Qed.
Definition ruIV_conc_s := ",2;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:#2S,12v25S,13#2B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#Ja_v2#48#2,1+v24#8#1,1,10X#36=08#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#1T,<#T,=v24T,>v26T,?#347?8T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma ruIV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruIV] fx R M V ruIV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruIV] LibSegJu_ruIV.regs0 LibSegJu_ruIV.kn0 LibSegJu_ruIV.BR LibSegJu_ruIV.PSS LibSegJu_ruIV.NX0 LibSegJu_ruIV.F0 224520 LibSegJu_ruIV.seg_sound_ax fx R M V ruIV_conc_s. Qed.
Definition KS_ruLN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruLN.regs0 LibSegJu_ruLN.regs_out0).
Lemma KS_ruLN_ok : BG.kept_ok 48 LibSegJu_ruLN.regs0 LibSegJu_ruLN.regs_out0 KS_ruLN = true. Proof. vm_compute. reflexivity. Qed.
Definition ruLN_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25S,13#8B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#v21#7,,1,5X#36=40#370:<Y,T,1#36?84T,:v26T,;#1"%pstring.
Lemma ruLN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruLN] fx R M V ruLN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruLN] LibSegJu_ruLN.regs0 LibSegJu_ruLN.kn0 LibSegJu_ruLN.BR LibSegJu_ruLN.PSS LibSegJu_ruLN.NX0 LibSegJu_ruLN.F0 224576 LibSegJu_ruLN.seg_sound_ax fx R M V ruLN_conc_s. Qed.
Definition KS_ruLV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruLV.regs0 LibSegJu_ruLV.regs_out0).
Lemma KS_ruLV_ok : BG.kept_ok 48 LibSegJu_ruLV.regs0 LibSegJu_ruLV.regs_out0 KS_ruLV = true. Proof. vm_compute. reflexivity. Qed.
Definition ruLV_conc_s := ",2;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:#8S,12v25S,13#8B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#Ja_v2#48#8,1+v24#8#1,1,10X#36=40#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#1T,<#T,=v24T,>v26T,?#347?8T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma ruLV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruLV] fx R M V ruLV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruLV] LibSegJu_ruLV.regs0 LibSegJu_ruLV.kn0 LibSegJu_ruLV.BR LibSegJu_ruLV.PSS LibSegJu_ruLV.NX0 LibSegJu_ruLV.F0 224576 LibSegJu_ruLV.seg_sound_ax fx R M V ruLV_conc_s. Qed.
Definition KS_ruUN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruUN.regs0 LibSegJu_ruUN.regs_out0).
Lemma KS_ruUN_ok : BG.kept_ok 48 LibSegJu_ruUN.regs0 LibSegJu_ruUN.regs_out0 KS_ruUN = true. Proof. vm_compute. reflexivity. Qed.
Definition ruUN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:#S,12v25S,13#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,1,5X#36>84#370:<Y,T,1#36?84T,:v26T,;#1"%pstring.
Lemma ruUN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruUN] fx R M V ruUN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruUN] LibSegJu_ruUN.regs0 LibSegJu_ruUN.kn0 LibSegJu_ruUN.BR LibSegJu_ruUN.PSS LibSegJu_ruUN.NX0 LibSegJu_ruUN.F0 224900 LibSegJu_ruUN.seg_sound_ax fx R M V ruUN_conc_s. Qed.
Definition KS_ruUV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruUV.regs0 LibSegJu_ruUV.regs_out0).
Lemma KS_ruUV_ok : BG.kept_ok 48 LibSegJu_ruUV.regs0 LibSegJu_ruUV.regs_out0 KS_ruUV = true. Proof. vm_compute. reflexivity. Qed.
Definition ruUV_conc_s := ",2;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:#1S,12v25S,13#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#Ja_v2#48#1,1+v24#8#1,1,?X#36>84#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,<#T,=v24T,>v26T,?#347?0T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma ruUV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruUV] fx R M V ruUV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruUV] LibSegJu_ruUV.regs0 LibSegJu_ruUV.kn0 LibSegJu_ruUV.BR LibSegJu_ruUV.PSS LibSegJu_ruUV.NX0 LibSegJu_ruUV.F0 224900 LibSegJu_ruUV.seg_sound_ax fx R M V ruUV_conc_s. Qed.
Definition KS_rudN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_rudN_c1.regs0 LibSegJu_rudN_c1.regs_out0).
Lemma KS_rudN_ok : BG.kept_ok 48 LibSegJu_rudN_c1.regs0 LibSegJu_rudN_c1.regs_out0 KS_rudN = true. Proof. vm_compute. reflexivity. Qed.
Definition rudN_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25S,13#4B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#v21#3,,1,5X#36><8#370:<Y,T,1#36?84T,:v26T,;#1"%pstring.
Lemma rudN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rudN] fx R M V rudN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rudN] LibSegJu_rudN_c1.regs0 LibSegJu_rudN_c1.kn0 LibSegJu_rudN_c1.BR LibSegJu_rudN_c1.PSS LibSegJu_rudN_c1.NX0 LibSegJu_rudN_c1.F0 224968 LibSegJu_rudN_c1.seg_sound_ax fx R M V rudN_conc_s. Qed.
Definition KS_rudV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_rudV_c1.regs0 LibSegJu_rudV_c1.regs_out0).
Lemma KS_rudV_ok : BG.kept_ok 48 LibSegJu_rudV_c1.regs0 LibSegJu_rudV_c1.regs_out0 KS_rudV = true. Proof. vm_compute. reflexivity. Qed.
Definition rudV_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:#4S,12v25S,13#4B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Ja_v2#48#4,,1,4X#36><8#36?04Y,T,=#;0238T,>#34800"%pstring.
Lemma rudV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rudV] fx R M V rudV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rudV] LibSegJu_rudV_c1.regs0 LibSegJu_rudV_c1.kn0 LibSegJu_rudV_c1.BR LibSegJu_rudV_c1.PSS LibSegJu_rudV_c1.NX0 LibSegJu_rudV_c1.F0 224968 LibSegJu_rudV_c1.seg_sound_ax fx R M V rudV_conc_s. Qed.
Definition KS_ruiN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruiN_c1.regs0 LibSegJu_ruiN_c1.regs_out0).
Lemma KS_ruiN_ok : BG.kept_ok 48 LibSegJu_ruiN_c1.regs0 LibSegJu_ruiN_c1.regs_out0 KS_ruiN = true. Proof. vm_compute. reflexivity. Qed.
Definition ruiN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:#S,12v25S,13#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,1,5X#36;<8#370:<Y,T,1#36?84T,:v26T,;#1"%pstring.
Lemma ruiN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruiN] fx R M V ruiN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruiN] LibSegJu_ruiN_c1.regs0 LibSegJu_ruiN_c1.kn0 LibSegJu_ruiN_c1.BR LibSegJu_ruiN_c1.PSS LibSegJu_ruiN_c1.NX0 LibSegJu_ruiN_c1.F0 224200 LibSegJu_ruiN_c1.seg_sound_ax fx R M V ruiN_conc_s. Qed.
Definition KS_ruiV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruiV_c1.regs0 LibSegJu_ruiV_c1.regs_out0).
Lemma KS_ruiV_ok : BG.kept_ok 48 LibSegJu_ruiV_c1.regs0 LibSegJu_ruiV_c1.regs_out0 KS_ruiV = true. Proof. vm_compute. reflexivity. Qed.
Definition ruiV_conc_s := ",2;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:#1S,12v25S,13#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#Ja_v2#48#1,1+v24#8#1,1,?X#36;<8#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,<#T,=v24T,>v26T,?#347?8T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma ruiV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruiV] fx R M V ruiV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruiV] LibSegJu_ruiV_c1.regs0 LibSegJu_ruiV_c1.kn0 LibSegJu_ruiV_c1.BR LibSegJu_ruiV_c1.PSS LibSegJu_ruiV_c1.NX0 LibSegJu_ruiV_c1.F0 224200 LibSegJu_ruiV_c1.seg_sound_ax fx R M V ruiV_conc_s. Qed.
Definition KS_rulN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_rulN_c1.regs0 LibSegJu_rulN_c1.regs_out0).
Lemma KS_rulN_ok : BG.kept_ok 48 LibSegJu_rulN_c1.regs0 LibSegJu_rulN_c1.regs_out0 KS_rulN = true. Proof. vm_compute. reflexivity. Qed.
Definition rulN_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25S,13#4B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#v21#3,,1,5X#36?38#370:<Y,T,1#36?84T,:v26T,;#1"%pstring.
Lemma rulN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rulN] fx R M V rulN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rulN] LibSegJu_rulN_c1.regs0 LibSegJu_rulN_c1.kn0 LibSegJu_rulN_c1.BR LibSegJu_rulN_c1.PSS LibSegJu_rulN_c1.NX0 LibSegJu_rulN_c1.F0 225080 LibSegJu_rulN_c1.seg_sound_ax fx R M V rulN_conc_s. Qed.
Definition KS_rulV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_rulV_c1.regs0 LibSegJu_rulV_c1.regs_out0).
Lemma KS_rulV_ok : BG.kept_ok 48 LibSegJu_rulV_c1.regs0 LibSegJu_rulV_c1.regs_out0 KS_rulV = true. Proof. vm_compute. reflexivity. Qed.
Definition rulV_conc_s := ",2;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:#4S,12v25S,13#4B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#Ja_v2#48#4,1+v24#8#1,1,10X#36?38#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#1T,<#T,=v24T,>v26T,?#347?8T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma rulV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rulV] fx R M V rulV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rulV] LibSegJu_rulV_c1.regs0 LibSegJu_rulV_c1.kn0 LibSegJu_rulV_c1.BR LibSegJu_rulV_c1.PSS LibSegJu_rulV_c1.NX0 LibSegJu_rulV_c1.F0 225080 LibSegJu_rulV_c1.seg_sound_ax fx R M V rulV_conc_s. Qed.
Definition KS_rudV2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_rudV2_c1.regs0 LibSegJu_rudV2_c1.regs_out0).
Lemma KS_rudV2_ok : BG.kept_ok 48 LibSegJu_rudV2_c1.regs0 LibSegJu_rudV2_c1.regs_out0 KS_rudV2 = true. Proof. vm_compute. reflexivity. Qed.
Definition rudV2_conc_s := ",2:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,>#34800S,12v25S,13#4B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,1+v24#8#1,1,>X#36?0<#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#1T,<v24T,=v26T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma rudV2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rudV2] fx R M V rudV2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rudV2] LibSegJu_rudV2_c1.regs0 LibSegJu_rudV2_c1.kn0 LibSegJu_rudV2_c1.BR LibSegJu_rudV2_c1.PSS LibSegJu_rudV2_c1.NX0 LibSegJu_rudV2_c1.F0 225036 LibSegJu_rudV2_c1.seg_sound_ax fx R M V rudV2_conc_s. Qed.
Definition KS_ruDV2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruDV2.regs0 LibSegJu_ruDV2.regs_out0).
Lemma KS_ruDV2_ok : BG.kept_ok 48 LibSegJu_ruDV2.regs0 LibSegJu_ruDV2.regs_out0 KS_ruDV2 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruDV2_conc_s := ",2:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,?#34800S,12v25S,13#8B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,1+v24#8#1,1,>X#36>58#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#1T,<v24T,=v26T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma ruDV2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruDV2] fx R M V ruDV2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruDV2] LibSegJu_ruDV2.regs0 LibSegJu_ruDV2.kn0 LibSegJu_ruDV2.BR LibSegJu_ruDV2.PSS LibSegJu_ruDV2.NX0 LibSegJu_ruDV2.F0 224856 LibSegJu_ruDV2.seg_sound_ax fx R M V ruDV2_conc_s. Qed.
Definition KS_ruCW_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruCW.regs0 LibSegJu_ruCW.regs_out0).
Lemma KS_ruCW_0_ok : BG.kept_ok 48 LibSegJu_ruCW.regs0 LibSegJu_ruCW.regs_out0 KS_ruCW_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ruCW_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruCW.regs0 LibSegJu_ruCW.regs_out1).
Lemma KS_ruCW_1_ok : BG.kept_ok 48 LibSegJu_ruCW.regs0 LibSegJu_ruCW.regs_out1 KS_ruCW_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruCW_conc_s := ",17A#v2p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#50S,8v24S,9v26S,;v23S,12v25S,13v27S,14#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#v27#800000000000,,2,2X#36;84#36?;<Y,,6X#36;84#370:<Y,1T,1#36?84T,:v26T,;#7T,13#7"%pstring.
Lemma ruCW_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruCW_0; KS_ruCW_1] fx R M V ruCW_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruCW_0; KS_ruCW_1] LibSegJu_ruCW.regs0 LibSegJu_ruCW.kn0 LibSegJu_ruCW.BR LibSegJu_ruCW.PSS LibSegJu_ruCW.NX0 LibSegJu_ruCW.F0 224132 LibSegJu_ruCW.seg_sound_ax fx R M V ruCW_conc_s. Qed.
Definition KS_ruCK : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruCK.regs0 LibSegJu_ruCK.regs_out0).
Lemma KS_ruCK_ok : BG.kept_ok 48 LibSegJu_ruCK.regs0 LibSegJu_ruCK.regs_out0 KS_ruCK = true. Proof. vm_compute. reflexivity. Qed.
Definition ruCK_conc_s := ",2;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25S,13v27S,14#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#48#10+v24#8#1,1,12X#36?;<#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#2T,<#T,=v24T,>v26T,?#3486<T,12v2;T,13v2<T,14v2=Nb+v24#8#1Lb_v2#40#1Lb_v2#48v27"%pstring.
Lemma ruCK_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruCK] fx R M V ruCK_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruCK] LibSegJu_ruCK.regs0 LibSegJu_ruCK.kn0 LibSegJu_ruCK.BR LibSegJu_ruCK.PSS LibSegJu_ruCK.NX0 LibSegJu_ruCK.F0 225212 LibSegJu_ruCK.seg_sound_ax fx R M V ruCK_conc_s. Qed.
Definition KS_ruSG0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruSG0.regs0 LibSegJu_ruSG0.regs_out0).
Lemma KS_ruSG0_ok : BG.kept_ok 48 LibSegJu_ruSG0.regs0 LibSegJu_ruSG0.regs_out0 KS_ruSG0 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruSG0_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10Mav26#,,1,7X#36<0<#37<;0Y,T,1#36<28T,:+v24#18T,;v21T,<+v24#150T,13v21"%pstring.
Lemma ruSG0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruSG0] fx R M V ruSG0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruSG0] LibSegJu_ruSG0.regs0 LibSegJu_ruSG0.kn0 LibSegJu_ruSG0.BR LibSegJu_ruSG0.PSS LibSegJu_ruSG0.NX0 LibSegJu_ruSG0.F0 224268 LibSegJu_ruSG0.seg_sound_ax fx R M V ruSG0_conc_s. Qed.
Definition KS_ruSGe : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruSGe.regs0 LibSegJu_ruSGe.regs_out0).
Lemma KS_ruSGe_ok : BG.kept_ok 48 LibSegJu_ruSGe.regs0 LibSegJu_ruSGe.regs_out0 KS_ruSGe = true. Proof. vm_compute. reflexivity. Qed.
Definition ruSGe_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26v27B#1v27#40,,1,:X#36<0<#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,;v27T,12v2;T,13v2<T,14v2="%pstring.
Lemma ruSGe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruSGe] fx R M V ruSGe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruSGe] LibSegJu_ruSGe.regs0 LibSegJu_ruSGe.kn0 LibSegJu_ruSGe.BR LibSegJu_ruSGe.PSS LibSegJu_ruSGe.NX0 LibSegJu_ruSGe.F0 224268 LibSegJu_ruSGe.seg_sound_ax fx R M V ruSGe_conc_s. Qed.
Definition KS_ruSF_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruSF.regs0 LibSegJu_ruSF.regs_out0).
Lemma KS_ruSF_0_ok : BG.kept_ok 48 LibSegJu_ruSF.regs0 LibSegJu_ruSF.regs_out0 KS_ruSF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ruSF_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruSF.regs0 LibSegJu_ruSF.regs_out1).
Lemma KS_ruSF_1_ok : BG.kept_ok 48 LibSegJu_ruSF.regs0 LibSegJu_ruSF.regs_out1 KS_ruSF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruSF_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v22S,;v23S,12v25S,13v21B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,2,6X#36<28#37844Y,T,1#36<38T,;v21T,14v22C%_v23v21p#2#40#1,6X#36<28#370:<Y,1T,1#36?84T,:v26T,;#1D#1%_v23v21p#2#40"%pstring.
Lemma ruSF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruSF_0; KS_ruSF_1] fx R M V ruSF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruSF_0; KS_ruSF_1] LibSegJu_ruSF.regs0 LibSegJu_ruSF.kn0 LibSegJu_ruSF.BR LibSegJu_ruSF.PSS LibSegJu_ruSF.NX0 LibSegJu_ruSF.F0 224296 LibSegJu_ruSF.seg_sound_ax fx R M V ruSF_conc_s. Qed.
Definition KS_ruHG0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruHG0.regs0 LibSegJu_ruHG0.regs_out0).
Lemma KS_ruHG0_ok : BG.kept_ok 48 LibSegJu_ruHG0.regs0 LibSegJu_ruHG0.regs_out0 KS_ruHG0 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruHG0_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10Mav26#,,1,7X#36<54#37<;0Y,T,1#36<70T,:+v24#18T,;v21T,<+v24#150T,13v21"%pstring.
Lemma ruHG0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruHG0] fx R M V ruHG0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruHG0] LibSegJu_ruHG0.regs0 LibSegJu_ruHG0.kn0 LibSegJu_ruHG0.BR LibSegJu_ruHG0.PSS LibSegJu_ruHG0.NX0 LibSegJu_ruHG0.F0 224340 LibSegJu_ruHG0.seg_sound_ax fx R M V ruHG0_conc_s. Qed.
Definition KS_ruHGe : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruHGe.regs0 LibSegJu_ruHGe.regs_out0).
Lemma KS_ruHGe_ok : BG.kept_ok 48 LibSegJu_ruHGe.regs0 LibSegJu_ruHGe.regs_out0 KS_ruHGe = true. Proof. vm_compute. reflexivity. Qed.
Definition ruHGe_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26v27B#1v27#40,,1,:X#36<54#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,;v27T,12v2;T,13v2<T,14v2="%pstring.
Lemma ruHGe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruHGe] fx R M V ruHGe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruHGe] LibSegJu_ruHGe.regs0 LibSegJu_ruHGe.kn0 LibSegJu_ruHGe.BR LibSegJu_ruHGe.PSS LibSegJu_ruHGe.NX0 LibSegJu_ruHGe.F0 224340 LibSegJu_ruHGe.seg_sound_ax fx R M V ruHGe_conc_s. Qed.
Definition KS_ruHF_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruHF.regs0 LibSegJu_ruHF.regs_out0).
Lemma KS_ruHF_0_ok : BG.kept_ok 48 LibSegJu_ruHF.regs0 LibSegJu_ruHF.regs_out0 KS_ruHF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ruHF_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruHF.regs0 LibSegJu_ruHF.regs_out1).
Lemma KS_ruHF_1_ok : BG.kept_ok 48 LibSegJu_ruHF.regs0 LibSegJu_ruHF.regs_out1 KS_ruHF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruHF_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v22S,;v23S,12v25S,13v21B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,2,6X#36<70#37=;8Y,T,1#36<80T,;v21T,14v22C%_v23v21p#2#40#1,6X#36<70#370:<Y,1T,1#36?84T,:v26T,;#1D#1%_v23v21p#2#40"%pstring.
Lemma ruHF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruHF_0; KS_ruHF_1] fx R M V ruHF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruHF_0; KS_ruHF_1] LibSegJu_ruHF.regs0 LibSegJu_ruHF.kn0 LibSegJu_ruHF.BR LibSegJu_ruHF.PSS LibSegJu_ruHF.NX0 LibSegJu_ruHF.F0 224368 LibSegJu_ruHF.seg_sound_ax fx R M V ruHF_conc_s. Qed.
Definition KS_ruSW_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruSW.regs0 LibSegJu_ruSW.regs_out0).
Lemma KS_ruSW_0_ok : BG.kept_ok 48 LibSegJu_ruSW.regs0 LibSegJu_ruSW.regs_out0 KS_ruSW_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ruSW_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruSW.regs0 LibSegJu_ruSW.regs_out1).
Lemma KS_ruSW_1_ok : BG.kept_ok 48 LibSegJu_ruSW.regs0 LibSegJu_ruSW.regs_out1 KS_ruSW_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruSW_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,;v23S,12v25S,13v21S,14v22B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,2,2X#36<38#36?>8Y,,5X#36<38#370:<Y,1T,1#36?84T,:v26T,;#7"%pstring.
Lemma ruSW_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruSW_0; KS_ruSW_1] fx R M V ruSW_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruSW_0; KS_ruSW_1] LibSegJu_ruSW.regs0 LibSegJu_ruSW.kn0 LibSegJu_ruSW.BR LibSegJu_ruSW.PSS LibSegJu_ruSW.NX0 LibSegJu_ruSW.F0 224312 LibSegJu_ruSW.seg_sound_ax fx R M V ruSW_conc_s. Qed.
Definition KS_ruSK : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruSK.regs0 LibSegJu_ruSK.regs_out0).
Lemma KS_ruSK_ok : BG.kept_ok 48 LibSegJu_ruSK.regs0 LibSegJu_ruSK.regs_out0 KS_ruSK = true. Proof. vm_compute. reflexivity. Qed.
Definition ruSK_conc_s := ",2<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25S,13v21S,14v22B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#48#10+v24#8#1,1,12X#36?>8#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#1T,<#T,=v24T,>v26T,?#3486<T,12v2;T,13v2<T,14v2=Nb+v24#8#1Lb_v2#40v21Lb_v2#48v22"%pstring.
Lemma ruSK_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruSK] fx R M V ruSK_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruSK] LibSegJu_ruSK.regs0 LibSegJu_ruSK.kn0 LibSegJu_ruSK.BR LibSegJu_ruSK.PSS LibSegJu_ruSK.NX0 LibSegJu_ruSK.F0 225256 LibSegJu_ruSK.seg_sound_ax fx R M V ruSK_conc_s. Qed.
Definition KS_ruHB_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruHB.regs0 LibSegJu_ruHB.regs_out0).
Lemma KS_ruHB_0_ok : BG.kept_ok 48 LibSegJu_ruHB.regs0 LibSegJu_ruHB.regs_out0 KS_ruHB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ruHB_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruHB.regs0 LibSegJu_ruHB.regs_out1).
Lemma KS_ruHB_1_ok : BG.kept_ok 48 LibSegJu_ruHB.regs0 LibSegJu_ruHB.regs_out1 KS_ruHB_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruHB_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v23S,12v25S,13v21S,14v22B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,2,3X#36<80#36?9<Y,C%_v23#p#2#40#1,3X#36<80#36<84Y,1D#1%_v23#p#2#40"%pstring.
Lemma ruHB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruHB_0; KS_ruHB_1] fx R M V ruHB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruHB_0; KS_ruHB_1] LibSegJu_ruHB.regs0 LibSegJu_ruHB.kn0 LibSegJu_ruHB.BR LibSegJu_ruHB.PSS LibSegJu_ruHB.NX0 LibSegJu_ruHB.F0 224384 LibSegJu_ruHB.seg_sound_ax fx R M V ruHB_conc_s. Qed.
Definition KS_ruHK3 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruHK3.regs0 LibSegJu_ruHK3.regs_out0).
Lemma KS_ruHK3_ok : BG.kept_ok 48 LibSegJu_ruHK3.regs0 LibSegJu_ruHK3.regs_out0 KS_ruHK3 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruHK3_conc_s := ",2<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25S,13v21S,14v22B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#48#10+v24#8#1,1,12X#36?9<#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#1T,<#3T,=v24T,>v26T,?#3486<T,12v2;T,13v2<T,14v2=Nb+v24#8#1Lb_v2#40v21Lb_v2#48v22"%pstring.
Lemma ruHK3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruHK3] fx R M V ruHK3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruHK3] LibSegJu_ruHK3.regs0 LibSegJu_ruHK3.kn0 LibSegJu_ruHK3.BR LibSegJu_ruHK3.PSS LibSegJu_ruHK3.NX0 LibSegJu_ruHK3.F0 225180 LibSegJu_ruHK3.seg_sound_ax fx R M V ruHK3_conc_s. Qed.
Definition KS_ruHK2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruHK2.regs0 LibSegJu_ruHK2.regs_out0).
Lemma KS_ruHK2_ok : BG.kept_ok 48 LibSegJu_ruHK2.regs0 LibSegJu_ruHK2.regs_out0 KS_ruHK2 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruHK2_conc_s := ",2<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25S,13v21S,14v22B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;7120Lav25#;0238Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#48#10+v24#8#1,1,12X#36<84#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#1T,<#2T,=v24T,>v26T,?#3486<T,12v2;T,13v2<T,14v2=Nb+v24#8#1Lb_v2#40v21Lb_v2#48v22"%pstring.
Lemma ruHK2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruHK2] fx R M V ruHK2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruHK2] LibSegJu_ruHK2.regs0 LibSegJu_ruHK2.kn0 LibSegJu_ruHK2.BR LibSegJu_ruHK2.PSS LibSegJu_ruHK2.NX0 LibSegJu_ruHK2.F0 224388 LibSegJu_ruHK2.seg_sound_ax fx R M V ruHK2_conc_s. Qed.
Definition KS_ruA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruA0.regs0 LibSegJu_ruA0.regs_out0).
Lemma KS_ruA0_ok : BG.kept_ok 48 LibSegJu_ruA0.regs0 LibSegJu_ruA0.regs_out0 KS_ruA0 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruA0_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,,1,:X#36=<8#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,12v2;T,13v2<T,14v2="%pstring.
Lemma ruA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruA0] fx R M V ruA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruA0] LibSegJu_ruA0.regs0 LibSegJu_ruA0.kn0 LibSegJu_ruA0.BR LibSegJu_ruA0.PSS LibSegJu_ruA0.NX0 LibSegJu_ruA0.F0 224712 LibSegJu_ruA0.seg_sound_ax fx R M V ruA0_conc_s. Qed.
Definition KS_ruAe : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruAe.regs0 LibSegJu_ruAe.regs_out0).
Lemma KS_ruAe_ok : BG.kept_ok 48 LibSegJu_ruAe.regs0 LibSegJu_ruAe.regs_out0 KS_ruAe = true. Proof. vm_compute. reflexivity. Qed.
Definition ruAe_conc_s := ",21A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26v27B#1v27#40I+v24#8#1,1+v24#8#1,1,;X#36=<8#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:v27T,12v2;T,13v2<T,14v2=Nb+v24#8#"%pstring.
Lemma ruAe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruAe] fx R M V ruAe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruAe] LibSegJu_ruAe.regs0 LibSegJu_ruAe.kn0 LibSegJu_ruAe.BR LibSegJu_ruAe.PSS LibSegJu_ruAe.NX0 LibSegJu_ruAe.F0 224712 LibSegJu_ruAe.seg_sound_ax fx R M V ruAe_conc_s. Qed.
Definition KS_ruO0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruO0.regs0 LibSegJu_ruO0.regs_out0).
Lemma KS_ruO0_ok : BG.kept_ok 48 LibSegJu_ruO0.regs0 LibSegJu_ruO0.regs_out0 KS_ruO0 = true. Proof. vm_compute. reflexivity. Qed.
Definition ruO0_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,,1,:X#36;?<#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,12v2;T,13v2<T,14v2="%pstring.
Lemma ruO0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruO0] fx R M V ruO0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruO0] LibSegJu_ruO0.regs0 LibSegJu_ruO0.kn0 LibSegJu_ruO0.BR LibSegJu_ruO0.PSS LibSegJu_ruO0.NX0 LibSegJu_ruO0.F0 224252 LibSegJu_ruO0.seg_sound_ax fx R M V ruO0_conc_s. Qed.
Definition KS_ruOe : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruOe.regs0 LibSegJu_ruOe.regs_out0).
Lemma KS_ruOe_ok : BG.kept_ok 48 LibSegJu_ruOe.regs0 LibSegJu_ruOe.regs_out0 KS_ruOe = true. Proof. vm_compute. reflexivity. Qed.
Definition ruOe_conc_s := ",21A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26v27B#1v27#40I+v24#8#1,1+v24#8#1,1,;X#36;?<#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:v27T,12v2;T,13v2<T,14v2=Nb+v24#8#"%pstring.
Lemma ruOe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruOe] fx R M V ruOe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruOe] LibSegJu_ruOe.regs0 LibSegJu_ruOe.kn0 LibSegJu_ruOe.BR LibSegJu_ruOe.PSS LibSegJu_ruOe.NX0 LibSegJu_ruOe.F0 224252 LibSegJu_ruOe.seg_sound_ax fx R M V ruOe_conc_s. Qed.
Definition KS_ruDfT : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruDfT.regs0 LibSegJu_ruDfT.regs_out0).
Lemma KS_ruDfT_ok : BG.kept_ok 48 LibSegJu_ruDfT.regs0 LibSegJu_ruDfT.regs_out0 KS_ruDfT = true. Proof. vm_compute. reflexivity. Qed.
Definition ruDfT_conc_s := ",21A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26v27B#1v27#40I+v24#8#1,1+v24#8#1,1,;X#36?98#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,:v27T,12v2;T,13v2<T,14v2=Nb+v24#8#"%pstring.
Lemma ruDfT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruDfT] fx R M V ruDfT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruDfT] LibSegJu_ruDfT.regs0 LibSegJu_ruDfT.kn0 LibSegJu_ruDfT.BR LibSegJu_ruDfT.PSS LibSegJu_ruDfT.NX0 LibSegJu_ruDfT.F0 225176 LibSegJu_ruDfT.seg_sound_ax fx R M V ruDfT_conc_s. Qed.
Definition KS_ruET : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_ruET.regs0 LibSegJu_ruET.regs_out0).
Lemma KS_ruET_ok : BG.kept_ok 48 LibSegJu_ruET.regs0 LibSegJu_ruET.regs_out0 KS_ruET = true. Proof. vm_compute. reflexivity. Qed.
Definition ruET_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=I+v24#8#1,1+v24#8#1,1,:X#36?84#3704<Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<T,14v2=Nb+v24#8#"%pstring.
Lemma ruET_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ruET] fx R M V ruET_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ruET] LibSegJu_ruET.regs0 LibSegJu_ruET.kn0 LibSegJu_ruET.BR LibSegJu_ruET.PSS LibSegJu_ruET.NX0 LibSegJu_ruET.F0 225156 LibSegJu_ruET.seg_sound_ax fx R M V ruET_conc_s. Qed.
End PMURVP.
