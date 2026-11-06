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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_rvTC LibSegJs_rvTD LibSegJs_rvTF LibSegJs_rvTH LibSegJs_rvTI LibSegJs_rvTL LibSegJs_rvTN LibSegJs_rvTS LibSegJs_rvTT LibSegJs_rvTU LibSegJs_rvTZ LibSegJs_rvTA LibSegJs_rvTd_c1 LibSegJs_rvTi_c1 LibSegJs_rvTl_c1 LibSegJs_rvTO LibSegJs_rvX69 LibSegJs_rvX71 LibSegJs_rvX74 LibSegJs_rvX75 LibSegJs_rvX77 LibSegJs_rvX79 LibSegJs_rvX80 LibSegJs_rvX81 LibSegJs_rvX82 LibSegJs_rvX86 LibSegJs_rvX87 LibSegJs_rvX88 LibSegJs_rvX89 LibSegJs_rvY0 LibSegJs_rvY92 LibSegJs_rvY101 LibSegJs_rvY106 LibSegJs_rvY109 LibSegJs_rvY124 LibSegJs_rvCN LibSegJs_rvCV LibSegJs_rvDN LibSegJs_rvDV LibSegJs_rvIN LibSegJs_rvIV LibSegJs_rvLN LibSegJs_rvLV LibSegJs_rvUN LibSegJs_rvUV LibSegJs_rvdN_c1 LibSegJs_rvdV_c1 LibSegJs_rviN_c1 LibSegJs_rviV_c1 LibSegJs_rvlN_c1 LibSegJs_rvlV_c1 LibSegJs_rvdV2_c1 LibSegJs_rvDV2 LibSegJs_rvCW LibSegJs_rvCK LibSegJs_rvSG0 LibSegJs_rvSGe LibSegJs_rvSF LibSegJs_rvHG0 LibSegJs_rvHGe LibSegJs_rvHF LibSegJs_rvSW LibSegJs_rvSK LibSegJs_rvHB LibSegJs_rvHK3 LibSegJs_rvHK2 LibSegJs_rvA0 LibSegJs_rvAe LibSegJs_rvO0 LibSegJs_rvOe LibSegJs_rvDfT LibSegJs_rvET.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSRVP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_rvTC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTC.regs0 LibSegJs_rvTC.regs_out0).
Lemma KS_rvTC_ok : BG.kept_ok 48 LibSegJs_rvTC.regs0 LibSegJs_rvTC.regs_out0 KS_rvTC = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition rvTC_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#43S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,12X#35?3<#36830Y,T,1#35?:<T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#31T,<#1T,12v25T,13#1Nb_v2#31#Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTC] fx R M V rvTC_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTC] LibSegJs_rvTC.regs0 LibSegJs_rvTC.kn0 LibSegJs_rvTC.BR LibSegJs_rvTC.PSS LibSegJs_rvTC.NX0 LibSegJs_rvTC.F0 220988 LibSegJs_rvTC.seg_sound_ax fx R M V rvTC_conc_s. Qed.
Definition KS_rvTD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTD.regs0 LibSegJs_rvTD.regs_out0).
Lemma KS_rvTD_ok : BG.kept_ok 48 LibSegJs_rvTD.regs0 LibSegJs_rvTD.regs_out0 KS_rvTD = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTD_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#44S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#35?3<#36830Y,T,1#36210T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#8T,12v25T,13#8Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTD] fx R M V rvTD_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTD] LibSegJs_rvTD.regs0 LibSegJs_rvTD.kn0 LibSegJs_rvTD.BR LibSegJs_rvTD.PSS LibSegJs_rvTD.NX0 LibSegJs_rvTD.F0 220988 LibSegJs_rvTD.seg_sound_ax fx R M V rvTD_conc_s. Qed.
Definition KS_rvTF : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTF.regs0 LibSegJs_rvTF.regs_out0).
Lemma KS_rvTF_ok : BG.kept_ok 48 LibSegJs_rvTF.regs0 LibSegJs_rvTF.regs_out0 KS_rvTF = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTF_conc_s := ",29A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<#46S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#50#50+v24#8#1,1,?X#35?3<#36438Y,T,:#T,;#T,<#T,=v24T,>v26T,?#345;0Nb+v24#8#1Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTF] fx R M V rvTF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTF] LibSegJs_rvTF.regs0 LibSegJs_rvTF.kn0 LibSegJs_rvTF.BR LibSegJs_rvTF.PSS LibSegJs_rvTF.NX0 LibSegJs_rvTF.F0 220988 LibSegJs_rvTF.seg_sound_ax fx R M V rvTF_conc_s. Qed.
Definition KS_rvTH : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTH.regs0 LibSegJs_rvTH.regs_out0).
Lemma KS_rvTH_ok : BG.kept_ok 48 LibSegJs_rvTH.regs0 LibSegJs_rvTH.regs_out0 KS_rvTH = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTH_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#48S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,>X#35?3<#36<?8Y,T,1#36094T,2_v2#50T,8v24T,9v26T,;v26T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTH] fx R M V rvTH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTH] LibSegJs_rvTH.regs0 LibSegJs_rvTH.kn0 LibSegJs_rvTH.BR LibSegJs_rvTH.PSS LibSegJs_rvTH.NX0 LibSegJs_rvTH.F0 220988 LibSegJs_rvTH.seg_sound_ax fx R M V rvTH_conc_s. Qed.
Definition KS_rvTI : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTI.regs0 LibSegJs_rvTI.regs_out0).
Lemma KS_rvTI_ok : BG.kept_ok 48 LibSegJs_rvTI.regs0 LibSegJs_rvTI.regs_out0 KS_rvTI = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTI_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#49S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#35?3<#36830Y,T,1#36138T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#2T,12v25T,13#2Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTI] fx R M V rvTI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTI] LibSegJs_rvTI.regs0 LibSegJs_rvTI.kn0 LibSegJs_rvTI.BR LibSegJs_rvTI.PSS LibSegJs_rvTI.NX0 LibSegJs_rvTI.F0 220988 LibSegJs_rvTI.seg_sound_ax fx R M V rvTI_conc_s. Qed.
Definition KS_rvTL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTL.regs0 LibSegJs_rvTL.regs_out0).
Lemma KS_rvTL_ok : BG.kept_ok 48 LibSegJs_rvTL.regs0 LibSegJs_rvTL.regs_out0 KS_rvTL = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTL_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#4<S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#35?3<#36830Y,T,1#36170T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#8T,12v25T,13#8Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTL] fx R M V rvTL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTL] LibSegJs_rvTL.regs0 LibSegJs_rvTL.kn0 LibSegJs_rvTL.BR LibSegJs_rvTL.PSS LibSegJs_rvTL.NX0 LibSegJs_rvTL.F0 220988 LibSegJs_rvTL.seg_sound_ax fx R M V rvTL_conc_s. Qed.
Definition KS_rvTN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTN.regs0 LibSegJs_rvTN.regs_out0).
Lemma KS_rvTN_ok : BG.kept_ok 48 LibSegJs_rvTN.regs0 LibSegJs_rvTN.regs_out0 KS_rvTN = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTN_conc_s := ",29A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<#4>S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,1_v2#50#50,1,:X#35?3<#36438Y,T,:#T,;#13680Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTN] fx R M V rvTN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTN] LibSegJs_rvTN.regs0 LibSegJs_rvTN.kn0 LibSegJs_rvTN.BR LibSegJs_rvTN.PSS LibSegJs_rvTN.NX0 LibSegJs_rvTN.F0 220988 LibSegJs_rvTN.seg_sound_ax fx R M V rvTN_conc_s. Qed.
Definition KS_rvTS : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTS.regs0 LibSegJs_rvTS.regs_out0).
Lemma KS_rvTS_ok : BG.kept_ok 48 LibSegJs_rvTS.regs0 LibSegJs_rvTS.regs_out0 KS_rvTS = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTS_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#53S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,>X#35?3<#36<?8Y,T,1#3604<T,2_v2#50T,8v24T,9v26T,;v26T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTS] fx R M V rvTS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTS] LibSegJs_rvTS.regs0 LibSegJs_rvTS.kn0 LibSegJs_rvTS.BR LibSegJs_rvTS.PSS LibSegJs_rvTS.NX0 LibSegJs_rvTS.F0 220988 LibSegJs_rvTS.seg_sound_ax fx R M V rvTS_conc_s. Qed.
Definition KS_rvTT : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTT.regs0 LibSegJs_rvTT.regs_out0).
Lemma KS_rvTT_ok : BG.kept_ok 48 LibSegJs_rvTT.regs0 LibSegJs_rvTT.regs_out0 KS_rvTT = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTT_conc_s := ",29A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<#54S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#50#50+v24#8#1,1,?X#35?3<#36438Y,T,:#T,;#1T,<#T,=v24T,>v26T,?#345;0Nb+v24#8#1Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTT] fx R M V rvTT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTT] LibSegJs_rvTT.regs0 LibSegJs_rvTT.kn0 LibSegJs_rvTT.BR LibSegJs_rvTT.PSS LibSegJs_rvTT.NX0 LibSegJs_rvTT.F0 220988 LibSegJs_rvTT.seg_sound_ax fx R M V rvTT_conc_s. Qed.
Definition KS_rvTU : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTU.regs0 LibSegJs_rvTU.regs_out0).
Lemma KS_rvTU_ok : BG.kept_ok 48 LibSegJs_rvTU.regs0 LibSegJs_rvTU.regs_out0 KS_rvTU = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTU_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#55S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,10X#35?3<#36830Y,T,1#362;0T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#1T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTU_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTU] fx R M V rvTU_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTU] LibSegJs_rvTU.regs0 LibSegJs_rvTU.kn0 LibSegJs_rvTU.BR LibSegJs_rvTU.PSS LibSegJs_rvTU.NX0 LibSegJs_rvTU.F0 220988 LibSegJs_rvTU.seg_sound_ax fx R M V rvTU_conc_s. Qed.
Definition KS_rvTZ : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTZ.regs0 LibSegJs_rvTZ.regs_out0).
Lemma KS_rvTZ_ok : BG.kept_ok 48 LibSegJs_rvTZ.regs0 LibSegJs_rvTZ.regs_out0 KS_rvTZ = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTZ_conc_s := ",29A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2v2S,:v24S,;v25S,<#5:S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#50#50+v24#8#1,1,=X#35?3<#36438Y,T,:#T,;#T,<v24T,>#345:8Nb+v24#8#1Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTZ] fx R M V rvTZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTZ] LibSegJs_rvTZ.regs0 LibSegJs_rvTZ.kn0 LibSegJs_rvTZ.BR LibSegJs_rvTZ.PSS LibSegJs_rvTZ.NX0 LibSegJs_rvTZ.F0 220988 LibSegJs_rvTZ.seg_sound_ax fx R M V rvTZ_conc_s. Qed.
Definition KS_rvTA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTA.regs0 LibSegJs_rvTA.regs_out0).
Lemma KS_rvTA_ok : BG.kept_ok 48 LibSegJs_rvTA.regs0 LibSegJs_rvTA.regs_out0 KS_rvTA = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTA_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#5;S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,>X#35?3<#37090Y,T,1#361?8T,2_v2#50T,8v24T,9v26T,<v26T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTA] fx R M V rvTA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTA] LibSegJs_rvTA.regs0 LibSegJs_rvTA.kn0 LibSegJs_rvTA.BR LibSegJs_rvTA.PSS LibSegJs_rvTA.NX0 LibSegJs_rvTA.F0 220988 LibSegJs_rvTA.seg_sound_ax fx R M V rvTA_conc_s. Qed.
Definition KS_rvTd : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTd_c1.regs0 LibSegJs_rvTd_c1.regs_out0).
Lemma KS_rvTd_ok : BG.kept_ok 48 LibSegJs_rvTd_c1.regs0 LibSegJs_rvTd_c1.regs_out0 KS_rvTd = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTd_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#64S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#35?3<#36830Y,T,1#362=8T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#4T,12v25T,13#4Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTd_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTd] fx R M V rvTd_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTd] LibSegJs_rvTd_c1.regs0 LibSegJs_rvTd_c1.kn0 LibSegJs_rvTd_c1.BR LibSegJs_rvTd_c1.PSS LibSegJs_rvTd_c1.NX0 LibSegJs_rvTd_c1.F0 220988 LibSegJs_rvTd_c1.seg_sound_ax fx R M V rvTd_conc_s. Qed.
Definition KS_rvTi : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTi_c1.regs0 LibSegJs_rvTi_c1.regs_out0).
Lemma KS_rvTi_ok : BG.kept_ok 48 LibSegJs_rvTi_c1.regs0 LibSegJs_rvTi_c1.regs_out0 KS_rvTi = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTi_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#69S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#35?3<#36830Y,T,1#36008T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#1T,12v25T,13#1Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTi] fx R M V rvTi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTi] LibSegJs_rvTi_c1.regs0 LibSegJs_rvTi_c1.kn0 LibSegJs_rvTi_c1.BR LibSegJs_rvTi_c1.PSS LibSegJs_rvTi_c1.NX0 LibSegJs_rvTi_c1.F0 220988 LibSegJs_rvTi_c1.seg_sound_ax fx R M V rvTi_conc_s. Qed.
Definition KS_rvTl : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTl_c1.regs0 LibSegJs_rvTl_c1.regs_out0).
Lemma KS_rvTl_ok : BG.kept_ok 48 LibSegJs_rvTl_c1.regs0 LibSegJs_rvTl_c1.regs_out0 KS_rvTl = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTl_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#6<S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,11X#35?3<#36830Y,T,1#36348T,2_v2#50T,8v24T,9v26T,:+v24#18T,;_v2#48T,<#4T,12v25T,13#4Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTl] fx R M V rvTl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTl] LibSegJs_rvTl_c1.regs0 LibSegJs_rvTl_c1.kn0 LibSegJs_rvTl_c1.BR LibSegJs_rvTl_c1.PSS LibSegJs_rvTl_c1.NX0 LibSegJs_rvTl_c1.F0 220988 LibSegJs_rvTl_c1.seg_sound_ax fx R M V rvTl_conc_s. Qed.
Definition KS_rvTO : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvTO.regs0 LibSegJs_rvTO.regs_out0).
Lemma KS_rvTO_ok : BG.kept_ok 48 LibSegJs_rvTO.regs0 LibSegJs_rvTO.regs_out0 KS_rvTO = true. Proof. vm_compute. reflexivity. Qed.
Definition rvTO_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#7;S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,>X#35?3<#374:0Y,T,1#3603<T,2_v2#50T,8v24T,9v26T,<v26T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvTO_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvTO] fx R M V rvTO_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvTO] LibSegJs_rvTO.regs0 LibSegJs_rvTO.kn0 LibSegJs_rvTO.BR LibSegJs_rvTO.PSS LibSegJs_rvTO.NX0 LibSegJs_rvTO.F0 220988 LibSegJs_rvTO.seg_sound_ax fx R M V rvTO_conc_s. Qed.
Definition KS_rvX69 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX69.regs0 LibSegJs_rvX69.regs_out0).
Lemma KS_rvX69_ok : BG.kept_ok 48 LibSegJs_rvX69.regs0 LibSegJs_rvX69.regs_out0 KS_rvX69 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX69_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#45S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX69_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX69] fx R M V rvX69_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX69] LibSegJs_rvX69.regs0 LibSegJs_rvX69.kn0 LibSegJs_rvX69.BR LibSegJs_rvX69.PSS LibSegJs_rvX69.NX0 LibSegJs_rvX69.F0 220988 LibSegJs_rvX69.seg_sound_ax fx R M V rvX69_conc_s. Qed.
Definition KS_rvX71 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX71.regs0 LibSegJs_rvX71.regs_out0).
Lemma KS_rvX71_ok : BG.kept_ok 48 LibSegJs_rvX71.regs0 LibSegJs_rvX71.regs_out0 KS_rvX71 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX71_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#47S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX71_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX71] fx R M V rvX71_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX71] LibSegJs_rvX71.regs0 LibSegJs_rvX71.kn0 LibSegJs_rvX71.BR LibSegJs_rvX71.PSS LibSegJs_rvX71.NX0 LibSegJs_rvX71.F0 220988 LibSegJs_rvX71.seg_sound_ax fx R M V rvX71_conc_s. Qed.
Definition KS_rvX74 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX74.regs0 LibSegJs_rvX74.regs_out0).
Lemma KS_rvX74_ok : BG.kept_ok 48 LibSegJs_rvX74.regs0 LibSegJs_rvX74.regs_out0 KS_rvX74 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX74_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#4:S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX74_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX74] fx R M V rvX74_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX74] LibSegJs_rvX74.regs0 LibSegJs_rvX74.kn0 LibSegJs_rvX74.BR LibSegJs_rvX74.PSS LibSegJs_rvX74.NX0 LibSegJs_rvX74.F0 220988 LibSegJs_rvX74.seg_sound_ax fx R M V rvX74_conc_s. Qed.
Definition KS_rvX75 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX75.regs0 LibSegJs_rvX75.regs_out0).
Lemma KS_rvX75_ok : BG.kept_ok 48 LibSegJs_rvX75.regs0 LibSegJs_rvX75.regs_out0 KS_rvX75 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX75_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#4;S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX75_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX75] fx R M V rvX75_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX75] LibSegJs_rvX75.regs0 LibSegJs_rvX75.kn0 LibSegJs_rvX75.BR LibSegJs_rvX75.PSS LibSegJs_rvX75.NX0 LibSegJs_rvX75.F0 220988 LibSegJs_rvX75.seg_sound_ax fx R M V rvX75_conc_s. Qed.
Definition KS_rvX77 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX77.regs0 LibSegJs_rvX77.regs_out0).
Lemma KS_rvX77_ok : BG.kept_ok 48 LibSegJs_rvX77.regs0 LibSegJs_rvX77.regs_out0 KS_rvX77 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX77_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#4=S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX77_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX77] fx R M V rvX77_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX77] LibSegJs_rvX77.regs0 LibSegJs_rvX77.kn0 LibSegJs_rvX77.BR LibSegJs_rvX77.PSS LibSegJs_rvX77.NX0 LibSegJs_rvX77.F0 220988 LibSegJs_rvX77.seg_sound_ax fx R M V rvX77_conc_s. Qed.
Definition KS_rvX79 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX79.regs0 LibSegJs_rvX79.regs_out0).
Lemma KS_rvX79_ok : BG.kept_ok 48 LibSegJs_rvX79.regs0 LibSegJs_rvX79.regs_out0 KS_rvX79 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX79_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#4?S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX79_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX79] fx R M V rvX79_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX79] LibSegJs_rvX79.regs0 LibSegJs_rvX79.kn0 LibSegJs_rvX79.BR LibSegJs_rvX79.PSS LibSegJs_rvX79.NX0 LibSegJs_rvX79.F0 220988 LibSegJs_rvX79.seg_sound_ax fx R M V rvX79_conc_s. Qed.
Definition KS_rvX80 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX80.regs0 LibSegJs_rvX80.regs_out0).
Lemma KS_rvX80_ok : BG.kept_ok 48 LibSegJs_rvX80.regs0 LibSegJs_rvX80.regs_out0 KS_rvX80 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX80_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#50S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX80_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX80] fx R M V rvX80_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX80] LibSegJs_rvX80.regs0 LibSegJs_rvX80.kn0 LibSegJs_rvX80.BR LibSegJs_rvX80.PSS LibSegJs_rvX80.NX0 LibSegJs_rvX80.F0 220988 LibSegJs_rvX80.seg_sound_ax fx R M V rvX80_conc_s. Qed.
Definition KS_rvX81 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX81.regs0 LibSegJs_rvX81.regs_out0).
Lemma KS_rvX81_ok : BG.kept_ok 48 LibSegJs_rvX81.regs0 LibSegJs_rvX81.regs_out0 KS_rvX81 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX81_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#51S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX81_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX81] fx R M V rvX81_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX81] LibSegJs_rvX81.regs0 LibSegJs_rvX81.kn0 LibSegJs_rvX81.BR LibSegJs_rvX81.PSS LibSegJs_rvX81.NX0 LibSegJs_rvX81.F0 220988 LibSegJs_rvX81.seg_sound_ax fx R M V rvX81_conc_s. Qed.
Definition KS_rvX82 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX82.regs0 LibSegJs_rvX82.regs_out0).
Lemma KS_rvX82_ok : BG.kept_ok 48 LibSegJs_rvX82.regs0 LibSegJs_rvX82.regs_out0 KS_rvX82 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX82_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#52S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX82_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX82] fx R M V rvX82_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX82] LibSegJs_rvX82.regs0 LibSegJs_rvX82.kn0 LibSegJs_rvX82.BR LibSegJs_rvX82.PSS LibSegJs_rvX82.NX0 LibSegJs_rvX82.F0 220988 LibSegJs_rvX82.seg_sound_ax fx R M V rvX82_conc_s. Qed.
Definition KS_rvX86 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX86.regs0 LibSegJs_rvX86.regs_out0).
Lemma KS_rvX86_ok : BG.kept_ok 48 LibSegJs_rvX86.regs0 LibSegJs_rvX86.regs_out0 KS_rvX86 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX86_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#56S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX86_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX86] fx R M V rvX86_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX86] LibSegJs_rvX86.regs0 LibSegJs_rvX86.kn0 LibSegJs_rvX86.BR LibSegJs_rvX86.PSS LibSegJs_rvX86.NX0 LibSegJs_rvX86.F0 220988 LibSegJs_rvX86.seg_sound_ax fx R M V rvX86_conc_s. Qed.
Definition KS_rvX87 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX87.regs0 LibSegJs_rvX87.regs_out0).
Lemma KS_rvX87_ok : BG.kept_ok 48 LibSegJs_rvX87.regs0 LibSegJs_rvX87.regs_out0 KS_rvX87 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX87_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#57S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX87_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX87] fx R M V rvX87_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX87] LibSegJs_rvX87.regs0 LibSegJs_rvX87.kn0 LibSegJs_rvX87.BR LibSegJs_rvX87.PSS LibSegJs_rvX87.NX0 LibSegJs_rvX87.F0 220988 LibSegJs_rvX87.seg_sound_ax fx R M V rvX87_conc_s. Qed.
Definition KS_rvX88 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX88.regs0 LibSegJs_rvX88.regs_out0).
Lemma KS_rvX88_ok : BG.kept_ok 48 LibSegJs_rvX88.regs0 LibSegJs_rvX88.regs_out0 KS_rvX88 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX88_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#58S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX88_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX88] fx R M V rvX88_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX88] LibSegJs_rvX88.regs0 LibSegJs_rvX88.kn0 LibSegJs_rvX88.BR LibSegJs_rvX88.PSS LibSegJs_rvX88.NX0 LibSegJs_rvX88.F0 220988 LibSegJs_rvX88.seg_sound_ax fx R M V rvX88_conc_s. Qed.
Definition KS_rvX89 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvX89.regs0 LibSegJs_rvX89.regs_out0).
Lemma KS_rvX89_ok : BG.kept_ok 48 LibSegJs_rvX89.regs0 LibSegJs_rvX89.regs_out0 KS_rvX89 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvX89_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<#59S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvX89_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvX89] fx R M V rvX89_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvX89] LibSegJs_rvX89.regs0 LibSegJs_rvX89.kn0 LibSegJs_rvX89.BR LibSegJs_rvX89.PSS LibSegJs_rvX89.NX0 LibSegJs_rvX89.F0 220988 LibSegJs_rvX89.seg_sound_ax fx R M V rvX89_conc_s. Qed.
Definition KS_rvY0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvY0.regs0 LibSegJs_rvY0.regs_out0).
Lemma KS_rvY0_ok : BG.kept_ok 48 LibSegJs_rvY0.regs0 LibSegJs_rvY0.regs_out0 KS_rvY0 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvY0_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v21S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#B#v21#42,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvY0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvY0] fx R M V rvY0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvY0] LibSegJs_rvY0.regs0 LibSegJs_rvY0.kn0 LibSegJs_rvY0.BR LibSegJs_rvY0.PSS LibSegJs_rvY0.NX0 LibSegJs_rvY0.F0 220988 LibSegJs_rvY0.seg_sound_ax fx R M V rvY0_conc_s. Qed.
Definition KS_rvY92 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvY92.regs0 LibSegJs_rvY92.regs_out0).
Lemma KS_rvY92_ok : BG.kept_ok 48 LibSegJs_rvY92.regs0 LibSegJs_rvY92.regs_out0 KS_rvY92 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvY92_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v21S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#B#5<v21#63,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvY92_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvY92] fx R M V rvY92_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvY92] LibSegJs_rvY92.regs0 LibSegJs_rvY92.kn0 LibSegJs_rvY92.BR LibSegJs_rvY92.PSS LibSegJs_rvY92.NX0 LibSegJs_rvY92.F0 220988 LibSegJs_rvY92.seg_sound_ax fx R M V rvY92_conc_s. Qed.
Definition KS_rvY101 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvY101.regs0 LibSegJs_rvY101.regs_out0).
Lemma KS_rvY101_ok : BG.kept_ok 48 LibSegJs_rvY101.regs0 LibSegJs_rvY101.regs_out0 KS_rvY101 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvY101_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v21S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#B#65v21#68,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvY101_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvY101] fx R M V rvY101_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvY101] LibSegJs_rvY101.regs0 LibSegJs_rvY101.kn0 LibSegJs_rvY101.BR LibSegJs_rvY101.PSS LibSegJs_rvY101.NX0 LibSegJs_rvY101.F0 220988 LibSegJs_rvY101.seg_sound_ax fx R M V rvY101_conc_s. Qed.
Definition KS_rvY106 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvY106.regs0 LibSegJs_rvY106.regs_out0).
Lemma KS_rvY106_ok : BG.kept_ok 48 LibSegJs_rvY106.regs0 LibSegJs_rvY106.regs_out0 KS_rvY106 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvY106_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v21S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#B#6:v21#6;,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvY106_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvY106] fx R M V rvY106_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvY106] LibSegJs_rvY106.regs0 LibSegJs_rvY106.kn0 LibSegJs_rvY106.BR LibSegJs_rvY106.PSS LibSegJs_rvY106.NX0 LibSegJs_rvY106.F0 220988 LibSegJs_rvY106.seg_sound_ax fx R M V rvY106_conc_s. Qed.
Definition KS_rvY109 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvY109.regs0 LibSegJs_rvY109.regs_out0).
Lemma KS_rvY109_ok : BG.kept_ok 48 LibSegJs_rvY109.regs0 LibSegJs_rvY109.regs_out0 KS_rvY109 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvY109_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v21S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#B#6=v21#7:,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvY109_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvY109] fx R M V rvY109_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvY109] LibSegJs_rvY109.regs0 LibSegJs_rvY109.kn0 LibSegJs_rvY109.BR LibSegJs_rvY109.PSS LibSegJs_rvY109.NX0 LibSegJs_rvY109.F0 220988 LibSegJs_rvY109.seg_sound_ax fx R M V rvY109_conc_s. Qed.
Definition KS_rvY124 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvY124.regs0 LibSegJs_rvY124.regs_out0).
Lemma KS_rvY124_ok : BG.kept_ok 48 LibSegJs_rvY124.regs0 LibSegJs_rvY124.regs_out0 KS_rvY124 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvY124_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v21S,=v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Mav26#B#7<v21#??,1_v2#50#50,1,?X#35?3<#36490Y,T,1#363:8T,2_v2#50T,8v24T,9v26T,:v26T,;#6T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rvY124_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvY124] fx R M V rvY124_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvY124] LibSegJs_rvY124.regs0 LibSegJs_rvY124.kn0 LibSegJs_rvY124.BR LibSegJs_rvY124.PSS LibSegJs_rvY124.NX0 LibSegJs_rvY124.F0 220988 LibSegJs_rvY124.seg_sound_ax fx R M V rvY124_conc_s. Qed.
Definition KS_rvCN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvCN.regs0 LibSegJs_rvCN.regs_out0).
Lemma KS_rvCN_ok : BG.kept_ok 48 LibSegJs_rvCN.regs0 LibSegJs_rvCN.regs_out0 KS_rvCN = true. Proof. vm_compute. reflexivity. Qed.
Definition rvCN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:#S,12v25S,13#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,1,5X#35?:<#36490Y,T,1#36394T,:v26T,;#1"%pstring.
Lemma rvCN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvCN] fx R M V rvCN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvCN] LibSegJs_rvCN.regs0 LibSegJs_rvCN.kn0 LibSegJs_rvCN.BR LibSegJs_rvCN.PSS LibSegJs_rvCN.NX0 LibSegJs_rvCN.F0 221100 LibSegJs_rvCN.seg_sound_ax fx R M V rvCN_conc_s. Qed.
Definition KS_rvCV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvCV.regs0 LibSegJs_rvCV.regs_out0).
Lemma KS_rvCV_ok : BG.kept_ok 48 LibSegJs_rvCV.regs0 LibSegJs_rvCV.regs_out0 KS_rvCV = true. Proof. vm_compute. reflexivity. Qed.
Definition rvCV_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:#1S,12v25S,13#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Ja_v2#31#1,,1,7X#35?:<#36:><Y,T,1#35?<4T,:_v2#31T,;#1T,13_v2#31T,14#1"%pstring.
Lemma rvCV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvCV] fx R M V rvCV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvCV] LibSegJs_rvCV.regs0 LibSegJs_rvCV.kn0 LibSegJs_rvCV.BR LibSegJs_rvCV.PSS LibSegJs_rvCV.NX0 LibSegJs_rvCV.F0 221100 LibSegJs_rvCV.seg_sound_ax fx R M V rvCV_conc_s. Qed.
Definition KS_rvDN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvDN.regs0 LibSegJs_rvDN.regs_out0).
Lemma KS_rvDN_ok : BG.kept_ok 48 LibSegJs_rvDN.regs0 LibSegJs_rvDN.regs_out0 KS_rvDN = true. Proof. vm_compute. reflexivity. Qed.
Definition rvDN_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25S,13#8B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#v21#7,,1,5X#36210#36490Y,T,1#36394T,:v26T,;#1"%pstring.
Lemma rvDN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvDN] fx R M V rvDN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvDN] LibSegJs_rvDN.regs0 LibSegJs_rvDN.kn0 LibSegJs_rvDN.BR LibSegJs_rvDN.PSS LibSegJs_rvDN.NX0 LibSegJs_rvDN.F0 221712 LibSegJs_rvDN.seg_sound_ax fx R M V rvDN_conc_s. Qed.
Definition KS_rvDV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvDV.regs0 LibSegJs_rvDV.regs_out0).
Lemma KS_rvDV_ok : BG.kept_ok 48 LibSegJs_rvDV.regs0 LibSegJs_rvDV.regs_out0 KS_rvDV = true. Proof. vm_compute. reflexivity. Qed.
Definition rvDV_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:#8S,12v25S,13#8B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Ja_v2#48#8,,1,4X#36210#36284Y,T,=#:?1>8T,?#3454<"%pstring.
Lemma rvDV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvDV] fx R M V rvDV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvDV] LibSegJs_rvDV.regs0 LibSegJs_rvDV.kn0 LibSegJs_rvDV.BR LibSegJs_rvDV.PSS LibSegJs_rvDV.NX0 LibSegJs_rvDV.F0 221712 LibSegJs_rvDV.seg_sound_ax fx R M V rvDV_conc_s. Qed.
Definition KS_rvIN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvIN.regs0 LibSegJs_rvIN.regs_out0).
Lemma KS_rvIN_ok : BG.kept_ok 48 LibSegJs_rvIN.regs0 LibSegJs_rvIN.regs_out0 KS_rvIN = true. Proof. vm_compute. reflexivity. Qed.
Definition rvIN_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25S,13#2B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#v21#1,,1,5X#36138#36490Y,T,1#36394T,:v26T,;#1"%pstring.
Lemma rvIN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvIN] fx R M V rvIN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvIN] LibSegJs_rvIN.regs0 LibSegJs_rvIN.kn0 LibSegJs_rvIN.BR LibSegJs_rvIN.PSS LibSegJs_rvIN.NX0 LibSegJs_rvIN.F0 221496 LibSegJs_rvIN.seg_sound_ax fx R M V rvIN_conc_s. Qed.
Definition KS_rvIV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvIV.regs0 LibSegJs_rvIV.regs_out0).
Lemma KS_rvIV_ok : BG.kept_ok 48 LibSegJs_rvIV.regs0 LibSegJs_rvIV.regs_out0 KS_rvIV = true. Proof. vm_compute. reflexivity. Qed.
Definition rvIV_conc_s := ",2;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:#2S,12v25S,13#2B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#Ja_v2#48#2,1+v24#8#1,1,?X#36138#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,<#T,=v24T,>v26T,?#34544T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma rvIV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvIV] fx R M V rvIV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvIV] LibSegJs_rvIV.regs0 LibSegJs_rvIV.kn0 LibSegJs_rvIV.BR LibSegJs_rvIV.PSS LibSegJs_rvIV.NX0 LibSegJs_rvIV.F0 221496 LibSegJs_rvIV.seg_sound_ax fx R M V rvIV_conc_s. Qed.
Definition KS_rvLN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvLN.regs0 LibSegJs_rvLN.regs_out0).
Lemma KS_rvLN_ok : BG.kept_ok 48 LibSegJs_rvLN.regs0 LibSegJs_rvLN.regs_out0 KS_rvLN = true. Proof. vm_compute. reflexivity. Qed.
Definition rvLN_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25S,13#8B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#v21#7,,1,5X#36170#36490Y,T,1#36394T,:v26T,;#1"%pstring.
Lemma rvLN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvLN] fx R M V rvLN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvLN] LibSegJs_rvLN.regs0 LibSegJs_rvLN.kn0 LibSegJs_rvLN.BR LibSegJs_rvLN.PSS LibSegJs_rvLN.NX0 LibSegJs_rvLN.F0 221552 LibSegJs_rvLN.seg_sound_ax fx R M V rvLN_conc_s. Qed.
Definition KS_rvLV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvLV.regs0 LibSegJs_rvLV.regs_out0).
Lemma KS_rvLV_ok : BG.kept_ok 48 LibSegJs_rvLV.regs0 LibSegJs_rvLV.regs_out0 KS_rvLV = true. Proof. vm_compute. reflexivity. Qed.
Definition rvLV_conc_s := ",2;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:#8S,12v25S,13#8B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#Ja_v2#48#8,1+v24#8#1,1,?X#36170#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,<#T,=v24T,>v26T,?#34544T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma rvLV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvLV] fx R M V rvLV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvLV] LibSegJs_rvLV.regs0 LibSegJs_rvLV.kn0 LibSegJs_rvLV.BR LibSegJs_rvLV.PSS LibSegJs_rvLV.NX0 LibSegJs_rvLV.F0 221552 LibSegJs_rvLV.seg_sound_ax fx R M V rvLV_conc_s. Qed.
Definition KS_rvUN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvUN.regs0 LibSegJs_rvUN.regs_out0).
Lemma KS_rvUN_ok : BG.kept_ok 48 LibSegJs_rvUN.regs0 LibSegJs_rvUN.regs_out0 KS_rvUN = true. Proof. vm_compute. reflexivity. Qed.
Definition rvUN_conc_s := ",12A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:#S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,1,5X#362;0#36490Y,T,1#36394T,:v26T,;#1"%pstring.
Lemma rvUN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvUN] fx R M V rvUN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvUN] LibSegJs_rvUN.regs0 LibSegJs_rvUN.kn0 LibSegJs_rvUN.BR LibSegJs_rvUN.PSS LibSegJs_rvUN.NX0 LibSegJs_rvUN.F0 221872 LibSegJs_rvUN.seg_sound_ax fx R M V rvUN_conc_s. Qed.
Definition KS_rvUV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvUV.regs0 LibSegJs_rvUV.regs_out0).
Lemma KS_rvUV_ok : BG.kept_ok 48 LibSegJs_rvUV.regs0 LibSegJs_rvUV.regs_out0 KS_rvUV = true. Proof. vm_compute. reflexivity. Qed.
Definition rvUV_conc_s := ",2:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:#1S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#Ja_v2#48#1,1+v24#8#1,1,?X#362;0#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,<#T,=v24T,>v26T,?#3453<T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma rvUV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvUV] fx R M V rvUV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvUV] LibSegJs_rvUV.regs0 LibSegJs_rvUV.kn0 LibSegJs_rvUV.BR LibSegJs_rvUV.PSS LibSegJs_rvUV.NX0 LibSegJs_rvUV.F0 221872 LibSegJs_rvUV.seg_sound_ax fx R M V rvUV_conc_s. Qed.
Definition KS_rvdN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvdN_c1.regs0 LibSegJs_rvdN_c1.regs_out0).
Lemma KS_rvdN_ok : BG.kept_ok 48 LibSegJs_rvdN_c1.regs0 LibSegJs_rvdN_c1.regs_out0 KS_rvdN = true. Proof. vm_compute. reflexivity. Qed.
Definition rvdN_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25S,13#4B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#v21#3,,1,5X#362=8#36490Y,T,1#36394T,:v26T,;#1"%pstring.
Lemma rvdN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvdN] fx R M V rvdN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvdN] LibSegJs_rvdN_c1.regs0 LibSegJs_rvdN_c1.kn0 LibSegJs_rvdN_c1.BR LibSegJs_rvdN_c1.PSS LibSegJs_rvdN_c1.NX0 LibSegJs_rvdN_c1.F0 221912 LibSegJs_rvdN_c1.seg_sound_ax fx R M V rvdN_conc_s. Qed.
Definition KS_rvdV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvdV_c1.regs0 LibSegJs_rvdV_c1.regs_out0).
Lemma KS_rvdV_ok : BG.kept_ok 48 LibSegJs_rvdV_c1.regs0 LibSegJs_rvdV_c1.regs_out0 KS_rvdV = true. Proof. vm_compute. reflexivity. Qed.
Definition rvdV_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:#4S,12v25S,13#4B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10Ja_v2#48#4,,1,4X#362=8#36314Y,T,=#:?1>8T,>#3454<"%pstring.
Lemma rvdV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvdV] fx R M V rvdV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvdV] LibSegJs_rvdV_c1.regs0 LibSegJs_rvdV_c1.kn0 LibSegJs_rvdV_c1.BR LibSegJs_rvdV_c1.PSS LibSegJs_rvdV_c1.NX0 LibSegJs_rvdV_c1.F0 221912 LibSegJs_rvdV_c1.seg_sound_ax fx R M V rvdV_conc_s. Qed.
Definition KS_rviN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rviN_c1.regs0 LibSegJs_rviN_c1.regs_out0).
Lemma KS_rviN_ok : BG.kept_ok 48 LibSegJs_rviN_c1.regs0 LibSegJs_rviN_c1.regs_out0 KS_rviN = true. Proof. vm_compute. reflexivity. Qed.
Definition rviN_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:#S,12v25S,13#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,1,5X#36008#36490Y,T,1#36394T,:v26T,;#1"%pstring.
Lemma rviN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rviN] fx R M V rviN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rviN] LibSegJs_rviN_c1.regs0 LibSegJs_rviN_c1.kn0 LibSegJs_rviN_c1.BR LibSegJs_rviN_c1.PSS LibSegJs_rviN_c1.NX0 LibSegJs_rviN_c1.F0 221192 LibSegJs_rviN_c1.seg_sound_ax fx R M V rviN_conc_s. Qed.
Definition KS_rviV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rviV_c1.regs0 LibSegJs_rviV_c1.regs_out0).
Lemma KS_rviV_ok : BG.kept_ok 48 LibSegJs_rviV_c1.regs0 LibSegJs_rviV_c1.regs_out0 KS_rviV = true. Proof. vm_compute. reflexivity. Qed.
Definition rviV_conc_s := ",2;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:#1S,12v25S,13#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#Ja_v2#48#1,1+v24#8#1,1,?X#36008#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,<#T,=v24T,>v26T,?#34544T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma rviV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rviV] fx R M V rviV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rviV] LibSegJs_rviV_c1.regs0 LibSegJs_rviV_c1.kn0 LibSegJs_rviV_c1.BR LibSegJs_rviV_c1.PSS LibSegJs_rviV_c1.NX0 LibSegJs_rviV_c1.F0 221192 LibSegJs_rviV_c1.seg_sound_ax fx R M V rviV_conc_s. Qed.
Definition KS_rvlN : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvlN_c1.regs0 LibSegJs_rvlN_c1.regs_out0).
Lemma KS_rvlN_ok : BG.kept_ok 48 LibSegJs_rvlN_c1.regs0 LibSegJs_rvlN_c1.regs_out0 KS_rvlN = true. Proof. vm_compute. reflexivity. Qed.
Definition rvlN_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25S,13#4B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#v21#3,,1,5X#36348#36490Y,T,1#36394T,:v26T,;#1"%pstring.
Lemma rvlN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvlN] fx R M V rvlN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvlN] LibSegJs_rvlN_c1.regs0 LibSegJs_rvlN_c1.kn0 LibSegJs_rvlN_c1.BR LibSegJs_rvlN_c1.PSS LibSegJs_rvlN_c1.NX0 LibSegJs_rvlN_c1.F0 222024 LibSegJs_rvlN_c1.seg_sound_ax fx R M V rvlN_conc_s. Qed.
Definition KS_rvlV : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvlV_c1.regs0 LibSegJs_rvlV_c1.regs_out0).
Lemma KS_rvlV_ok : BG.kept_ok 48 LibSegJs_rvlV_c1.regs0 LibSegJs_rvlV_c1.regs_out0 KS_rvlV = true. Proof. vm_compute. reflexivity. Qed.
Definition rvlV_conc_s := ",2;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:#4S,12v25S,13#4B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#Ja_v2#48#4,1+v24#8#1,1,?X#36348#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,<#T,=v24T,>v26T,?#34544T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma rvlV_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvlV] fx R M V rvlV_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvlV] LibSegJs_rvlV_c1.regs0 LibSegJs_rvlV_c1.kn0 LibSegJs_rvlV_c1.BR LibSegJs_rvlV_c1.PSS LibSegJs_rvlV_c1.NX0 LibSegJs_rvlV_c1.F0 222024 LibSegJs_rvlV_c1.seg_sound_ax fx R M V rvlV_conc_s. Qed.
Definition KS_rvdV2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvdV2_c1.regs0 LibSegJs_rvdV2_c1.regs_out0).
Lemma KS_rvdV2_ok : BG.kept_ok 48 LibSegJs_rvdV2_c1.regs0 LibSegJs_rvdV2_c1.regs_out0 KS_rvdV2 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvdV2_conc_s := ",2:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,>#3454<S,12v25S,13#4B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,1+v24#8#1,1,>X#3631<#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#T,<v24T,=v26T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma rvdV2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvdV2] fx R M V rvdV2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvdV2] LibSegJs_rvdV2_c1.regs0 LibSegJs_rvdV2_c1.kn0 LibSegJs_rvdV2_c1.BR LibSegJs_rvdV2_c1.PSS LibSegJs_rvdV2_c1.NX0 LibSegJs_rvdV2_c1.F0 221980 LibSegJs_rvdV2_c1.seg_sound_ax fx R M V rvdV2_conc_s. Qed.
Definition KS_rvDV2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvDV2.regs0 LibSegJs_rvDV2.regs_out0).
Lemma KS_rvDV2_ok : BG.kept_ok 48 LibSegJs_rvDV2.regs0 LibSegJs_rvDV2.regs_out0 KS_rvDV2 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvDV2_conc_s := ",2:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,?#3454<S,12v25S,13#8B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,1+v24#8#1,1,>X#36288#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#T,<v24T,=v26T,12v2;T,13v2<T,14v2=Nb+v24#8#1"%pstring.
Lemma rvDV2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvDV2] fx R M V rvDV2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvDV2] LibSegJs_rvDV2.regs0 LibSegJs_rvDV2.kn0 LibSegJs_rvDV2.BR LibSegJs_rvDV2.PSS LibSegJs_rvDV2.NX0 LibSegJs_rvDV2.F0 221832 LibSegJs_rvDV2.seg_sound_ax fx R M V rvDV2_conc_s. Qed.
Definition KS_rvCW_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvCW.regs0 LibSegJs_rvCW.regs_out0).
Lemma KS_rvCW_0_ok : BG.kept_ok 48 LibSegJs_rvCW.regs0 LibSegJs_rvCW.regs_out0 KS_rvCW_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rvCW_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvCW.regs0 LibSegJs_rvCW.regs_out1).
Lemma KS_rvCW_1_ok : BG.kept_ok 48 LibSegJs_rvCW.regs0 LibSegJs_rvCW.regs_out1 KS_rvCW_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvCW_conc_s := ",17A#v2p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#50S,8v24S,9v26S,;v23S,12v25S,13v27S,14#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#v27#800000000000,,2,2X#35?<4#363<<Y,,6X#35?<4#36490Y,1T,1#36394T,:v26T,;#7T,13#7"%pstring.
Lemma rvCW_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvCW_0; KS_rvCW_1] fx R M V rvCW_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvCW_0; KS_rvCW_1] LibSegJs_rvCW.regs0 LibSegJs_rvCW.kn0 LibSegJs_rvCW.BR LibSegJs_rvCW.PSS LibSegJs_rvCW.NX0 LibSegJs_rvCW.F0 221124 LibSegJs_rvCW.seg_sound_ax fx R M V rvCW_conc_s. Qed.
Definition KS_rvCK : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvCK.regs0 LibSegJs_rvCK.regs_out0).
Lemma KS_rvCK_ok : BG.kept_ok 48 LibSegJs_rvCK.regs0 LibSegJs_rvCK.regs_out0 KS_rvCK = true. Proof. vm_compute. reflexivity. Qed.
Definition rvCK_conc_s := ",2;A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25S,13v27S,14#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#48#10+v24#8#1,1,12X#363<<#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;_v2#48T,<#T,=v24T,>v26T,?#345;8T,12v2;T,13v2<T,14v2=Nb+v24#8#1Lb_v2#40#1Lb_v2#48v27"%pstring.
Lemma rvCK_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvCK] fx R M V rvCK_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvCK] LibSegJs_rvCK.regs0 LibSegJs_rvCK.kn0 LibSegJs_rvCK.BR LibSegJs_rvCK.PSS LibSegJs_rvCK.NX0 LibSegJs_rvCK.F0 222156 LibSegJs_rvCK.seg_sound_ax fx R M V rvCK_conc_s. Qed.
Definition KS_rvSG0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvSG0.regs0 LibSegJs_rvSG0.regs_out0).
Lemma KS_rvSG0_ok : BG.kept_ok 48 LibSegJs_rvSG0.regs0 LibSegJs_rvSG0.regs_out0 KS_rvSG0 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvSG0_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10Mav26#,,1,7X#3604<#36?04Y,T,1#36068T,:+v24#18T,;v21T,<+v24#150T,13v21"%pstring.
Lemma rvSG0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvSG0] fx R M V rvSG0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvSG0] LibSegJs_rvSG0.regs0 LibSegJs_rvSG0.kn0 LibSegJs_rvSG0.BR LibSegJs_rvSG0.PSS LibSegJs_rvSG0.NX0 LibSegJs_rvSG0.F0 221260 LibSegJs_rvSG0.seg_sound_ax fx R M V rvSG0_conc_s. Qed.
Definition KS_rvSGe : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvSGe.regs0 LibSegJs_rvSGe.regs_out0).
Lemma KS_rvSGe_ok : BG.kept_ok 48 LibSegJs_rvSGe.regs0 LibSegJs_rvSGe.regs_out0 KS_rvSGe = true. Proof. vm_compute. reflexivity. Qed.
Definition rvSGe_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26v27B#1v27#40,,1,:X#3604<#36438Y,T,1v28T,2v2T,8v29T,9v2:T,;v27T,12v2;T,13v2<T,14v2="%pstring.
Lemma rvSGe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvSGe] fx R M V rvSGe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvSGe] LibSegJs_rvSGe.regs0 LibSegJs_rvSGe.kn0 LibSegJs_rvSGe.BR LibSegJs_rvSGe.PSS LibSegJs_rvSGe.NX0 LibSegJs_rvSGe.F0 221260 LibSegJs_rvSGe.seg_sound_ax fx R M V rvSGe_conc_s. Qed.
Definition KS_rvSF_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvSF.regs0 LibSegJs_rvSF.regs_out0).
Lemma KS_rvSF_0_ok : BG.kept_ok 48 LibSegJs_rvSF.regs0 LibSegJs_rvSF.regs_out0 KS_rvSF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rvSF_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvSF.regs0 LibSegJs_rvSF.regs_out1).
Lemma KS_rvSF_1_ok : BG.kept_ok 48 LibSegJs_rvSF.regs0 LibSegJs_rvSF.regs_out1 KS_rvSF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvSF_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v22S,;v23S,12v25S,13v21B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,2,6X#36068#36:><Y,T,1#36078T,;v21T,14v22C%_v23v21p#2#40#1,6X#36068#36490Y,1T,1#36394T,:v26T,;#1D#1%_v23v21p#2#40"%pstring.
Lemma rvSF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvSF_0; KS_rvSF_1] fx R M V rvSF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvSF_0; KS_rvSF_1] LibSegJs_rvSF.regs0 LibSegJs_rvSF.kn0 LibSegJs_rvSF.BR LibSegJs_rvSF.PSS LibSegJs_rvSF.NX0 LibSegJs_rvSF.F0 221288 LibSegJs_rvSF.seg_sound_ax fx R M V rvSF_conc_s. Qed.
Definition KS_rvHG0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvHG0.regs0 LibSegJs_rvHG0.regs_out0).
Lemma KS_rvHG0_ok : BG.kept_ok 48 LibSegJs_rvHG0.regs0 LibSegJs_rvHG0.regs_out0 KS_rvHG0 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvHG0_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10Mav26#,,1,7X#36094#36?04Y,T,1#360;0T,:+v24#18T,;v21T,<+v24#150T,13v21"%pstring.
Lemma rvHG0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvHG0] fx R M V rvHG0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvHG0] LibSegJs_rvHG0.regs0 LibSegJs_rvHG0.kn0 LibSegJs_rvHG0.BR LibSegJs_rvHG0.PSS LibSegJs_rvHG0.NX0 LibSegJs_rvHG0.F0 221332 LibSegJs_rvHG0.seg_sound_ax fx R M V rvHG0_conc_s. Qed.
Definition KS_rvHGe : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvHGe.regs0 LibSegJs_rvHGe.regs_out0).
Lemma KS_rvHGe_ok : BG.kept_ok 48 LibSegJs_rvHGe.regs0 LibSegJs_rvHGe.regs_out0 KS_rvHGe = true. Proof. vm_compute. reflexivity. Qed.
Definition rvHGe_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,:v21S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26v27B#1v27#40,,1,:X#36094#36438Y,T,1v28T,2v2T,8v29T,9v2:T,;v27T,12v2;T,13v2<T,14v2="%pstring.
Lemma rvHGe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvHGe] fx R M V rvHGe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvHGe] LibSegJs_rvHGe.regs0 LibSegJs_rvHGe.kn0 LibSegJs_rvHGe.BR LibSegJs_rvHGe.PSS LibSegJs_rvHGe.NX0 LibSegJs_rvHGe.F0 221332 LibSegJs_rvHGe.seg_sound_ax fx R M V rvHGe_conc_s. Qed.
Definition KS_rvHF_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvHF.regs0 LibSegJs_rvHF.regs_out0).
Lemma KS_rvHF_0_ok : BG.kept_ok 48 LibSegJs_rvHF.regs0 LibSegJs_rvHF.regs_out0 KS_rvHF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rvHF_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvHF.regs0 LibSegJs_rvHF.regs_out1).
Lemma KS_rvHF_1_ok : BG.kept_ok 48 LibSegJs_rvHF.regs0 LibSegJs_rvHF.regs_out1 KS_rvHF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvHF_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v22S,;v23S,12v25S,13v21B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,2,6X#360;0#37000Y,T,1#360<0T,;v21T,14v22C%_v23v21p#2#40#1,6X#360;0#36490Y,1T,1#36394T,:v26T,;#1D#1%_v23v21p#2#40"%pstring.
Lemma rvHF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvHF_0; KS_rvHF_1] fx R M V rvHF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvHF_0; KS_rvHF_1] LibSegJs_rvHF.regs0 LibSegJs_rvHF.kn0 LibSegJs_rvHF.BR LibSegJs_rvHF.PSS LibSegJs_rvHF.NX0 LibSegJs_rvHF.F0 221360 LibSegJs_rvHF.seg_sound_ax fx R M V rvHF_conc_s. Qed.
Definition KS_rvSW_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvSW.regs0 LibSegJs_rvSW.regs_out0).
Lemma KS_rvSW_0_ok : BG.kept_ok 48 LibSegJs_rvSW.regs0 LibSegJs_rvSW.regs_out0 KS_rvSW_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rvSW_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvSW.regs0 LibSegJs_rvSW.regs_out1).
Lemma KS_rvSW_1_ok : BG.kept_ok 48 LibSegJs_rvSW.regs0 LibSegJs_rvSW.regs_out1 KS_rvSW_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvSW_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,;v23S,12v25S,13v21S,14v22B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,2,2X#36078#363>0Y,,5X#36078#36490Y,1T,1#36394T,:v26T,;#7"%pstring.
Lemma rvSW_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvSW_0; KS_rvSW_1] fx R M V rvSW_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvSW_0; KS_rvSW_1] LibSegJs_rvSW.regs0 LibSegJs_rvSW.kn0 LibSegJs_rvSW.BR LibSegJs_rvSW.PSS LibSegJs_rvSW.NX0 LibSegJs_rvSW.F0 221304 LibSegJs_rvSW.seg_sound_ax fx R M V rvSW_conc_s. Qed.
Definition KS_rvSK : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvSK.regs0 LibSegJs_rvSK.regs_out0).
Lemma KS_rvSK_ok : BG.kept_ok 48 LibSegJs_rvSK.regs0 LibSegJs_rvSK.regs_out0 KS_rvSK = true. Proof. vm_compute. reflexivity. Qed.
Definition rvSK_conc_s := ",2<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25S,13v21S,14v22B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#48#10+v24#8#1,1,12X#363>0#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;_v2#48T,<#T,=v24T,>v26T,?#345;8T,12v2;T,13v2<T,14v2=Nb+v24#8#1Lb_v2#40v21Lb_v2#48v22"%pstring.
Lemma rvSK_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvSK] fx R M V rvSK_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvSK] LibSegJs_rvSK.regs0 LibSegJs_rvSK.kn0 LibSegJs_rvSK.BR LibSegJs_rvSK.PSS LibSegJs_rvSK.NX0 LibSegJs_rvSK.F0 222176 LibSegJs_rvSK.seg_sound_ax fx R M V rvSK_conc_s. Qed.
Definition KS_rvHB_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvHB.regs0 LibSegJs_rvHB.regs_out0).
Lemma KS_rvHB_0_ok : BG.kept_ok 48 LibSegJs_rvHB.regs0 LibSegJs_rvHB.regs_out0 KS_rvHB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rvHB_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvHB.regs0 LibSegJs_rvHB.regs_out1).
Lemma KS_rvHB_1_ok : BG.kept_ok 48 LibSegJs_rvHB.regs0 LibSegJs_rvHB.regs_out1 KS_rvHB_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvHB_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v24S,9v26S,:v23S,12v25S,13v21S,14v22B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10,,2,3X#360<0#363:<Y,C%_v23#p#2#40#1,3X#360<0#360<4Y,1D#1%_v23#p#2#40"%pstring.
Lemma rvHB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvHB_0; KS_rvHB_1] fx R M V rvHB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvHB_0; KS_rvHB_1] LibSegJs_rvHB.regs0 LibSegJs_rvHB.kn0 LibSegJs_rvHB.BR LibSegJs_rvHB.PSS LibSegJs_rvHB.NX0 LibSegJs_rvHB.F0 221376 LibSegJs_rvHB.seg_sound_ax fx R M V rvHB_conc_s. Qed.
Definition KS_rvHK3 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvHK3.regs0 LibSegJs_rvHK3.regs_out0).
Lemma KS_rvHK3_ok : BG.kept_ok 48 LibSegJs_rvHK3.regs0 LibSegJs_rvHK3.regs_out0 KS_rvHK3 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvHK3_conc_s := ",2<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25S,13v21S,14v22B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#48#10+v24#8#1,1,12X#363:<#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;_v2#48T,<#3T,=v24T,>v26T,?#345;8T,12v2;T,13v2<T,14v2=Nb+v24#8#1Lb_v2#40v21Lb_v2#48v22"%pstring.
Lemma rvHK3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvHK3] fx R M V rvHK3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvHK3] LibSegJs_rvHK3.regs0 LibSegJs_rvHK3.kn0 LibSegJs_rvHK3.BR LibSegJs_rvHK3.PSS LibSegJs_rvHK3.NX0 LibSegJs_rvHK3.F0 222124 LibSegJs_rvHK3.seg_sound_ax fx R M V rvHK3_conc_s. Qed.
Definition KS_rvHK2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvHK2.regs0 LibSegJs_rvHK2.regs_out0).
Lemma KS_rvHK2_ok : BG.kept_ok 48 LibSegJs_rvHK2.regs0 LibSegJs_rvHK2.regs_out0 KS_rvHK2 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvHK2_conc_s := ",2<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25S,13v21S,14v22B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10B#7???7?800050v25#7??????????8Hv25#8P_v2#50#50v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8Pv24#180v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,2_v2#48#10+v24#8#1,1,12X#360<4#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;_v2#48T,<#2T,=v24T,>v26T,?#345;8T,12v2;T,13v2<T,14v2=Nb+v24#8#1Lb_v2#40v21Lb_v2#48v22"%pstring.
Lemma rvHK2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvHK2] fx R M V rvHK2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvHK2] LibSegJs_rvHK2.regs0 LibSegJs_rvHK2.kn0 LibSegJs_rvHK2.BR LibSegJs_rvHK2.PSS LibSegJs_rvHK2.NX0 LibSegJs_rvHK2.F0 221380 LibSegJs_rvHK2.seg_sound_ax fx R M V rvHK2_conc_s. Qed.
Definition KS_rvA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvA0.regs0 LibSegJs_rvA0.regs_out0).
Lemma KS_rvA0_ok : BG.kept_ok 48 LibSegJs_rvA0.regs0 LibSegJs_rvA0.regs_out0 KS_rvA0 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvA0_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,,1,:X#361?8#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,12v2;T,13v2<T,14v2="%pstring.
Lemma rvA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvA0] fx R M V rvA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvA0] LibSegJs_rvA0.regs0 LibSegJs_rvA0.kn0 LibSegJs_rvA0.BR LibSegJs_rvA0.PSS LibSegJs_rvA0.NX0 LibSegJs_rvA0.F0 221688 LibSegJs_rvA0.seg_sound_ax fx R M V rvA0_conc_s. Qed.
Definition KS_rvAe : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvAe.regs0 LibSegJs_rvAe.regs_out0).
Lemma KS_rvAe_ok : BG.kept_ok 48 LibSegJs_rvAe.regs0 LibSegJs_rvAe.regs_out0 KS_rvAe = true. Proof. vm_compute. reflexivity. Qed.
Definition rvAe_conc_s := ",21A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26v27B#1v27#40I+v24#8#1,1+v24#8#1,1,;X#361?8#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:v27T,12v2;T,13v2<T,14v2=Nb+v24#8#"%pstring.
Lemma rvAe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvAe] fx R M V rvAe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvAe] LibSegJs_rvAe.regs0 LibSegJs_rvAe.kn0 LibSegJs_rvAe.BR LibSegJs_rvAe.PSS LibSegJs_rvAe.NX0 LibSegJs_rvAe.F0 221688 LibSegJs_rvAe.seg_sound_ax fx R M V rvAe_conc_s. Qed.
Definition KS_rvO0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvO0.regs0 LibSegJs_rvO0.regs_out0).
Lemma KS_rvO0_ok : BG.kept_ok 48 LibSegJs_rvO0.regs0 LibSegJs_rvO0.regs_out0 KS_rvO0 = true. Proof. vm_compute. reflexivity. Qed.
Definition rvO0_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26#,,1,:X#3603<#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,12v2;T,13v2<T,14v2="%pstring.
Lemma rvO0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvO0] fx R M V rvO0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvO0] LibSegJs_rvO0.regs0 LibSegJs_rvO0.kn0 LibSegJs_rvO0.BR LibSegJs_rvO0.PSS LibSegJs_rvO0.NX0 LibSegJs_rvO0.F0 221244 LibSegJs_rvO0.seg_sound_ax fx R M V rvO0_conc_s. Qed.
Definition KS_rvOe : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvOe.regs0 LibSegJs_rvOe.regs_out0).
Lemma KS_rvOe_ok : BG.kept_ok 48 LibSegJs_rvOe.regs0 LibSegJs_rvOe.regs_out0 KS_rvOe = true. Proof. vm_compute. reflexivity. Qed.
Definition rvOe_conc_s := ",21A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26v27B#1v27#40I+v24#8#1,1+v24#8#1,1,;X#3603<#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:v27T,12v2;T,13v2<T,14v2=Nb+v24#8#"%pstring.
Lemma rvOe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvOe] fx R M V rvOe_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvOe] LibSegJs_rvOe.regs0 LibSegJs_rvOe.kn0 LibSegJs_rvOe.BR LibSegJs_rvOe.PSS LibSegJs_rvOe.NX0 LibSegJs_rvOe.F0 221244 LibSegJs_rvOe.seg_sound_ax fx R M V rvOe_conc_s. Qed.
Definition KS_rvDfT : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvDfT.regs0 LibSegJs_rvDfT.regs_out0).
Lemma KS_rvDfT_ok : BG.kept_ok 48 LibSegJs_rvDfT.regs0 LibSegJs_rvDfT.regs_out0 KS_rvDfT = true. Proof. vm_compute. reflexivity. Qed.
Definition rvDfT_conc_s := ",21A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=Mav26v27B#1v27#40I+v24#8#1,1+v24#8#1,1,;X#363:8#36438Y,T,1v28T,2v2T,8v29T,9v2:T,:v27T,12v2;T,13v2<T,14v2=Nb+v24#8#"%pstring.
Lemma rvDfT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvDfT] fx R M V rvDfT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvDfT] LibSegJs_rvDfT.regs0 LibSegJs_rvDfT.kn0 LibSegJs_rvDfT.BR LibSegJs_rvDfT.PSS LibSegJs_rvDfT.NX0 LibSegJs_rvDfT.F0 222120 LibSegJs_rvDfT.seg_sound_ax fx R M V rvDfT_conc_s. Qed.
Definition KS_rvET : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rvET.regs0 LibSegJs_rvET.regs_out0).
Lemma KS_rvET_ok : BG.kept_ok 48 LibSegJs_rvET.regs0 LibSegJs_rvET.regs_out0 KS_rvET = true. Proof. vm_compute. reflexivity. Qed.
Definition rvET_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#50S,8v24S,9v26S,12v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800050v24#7????????>80Hv24#8P_v2#50#50v24#180B#7???7?800050v26#7??????????0Hv26#8P_v2#50#50v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=I+v24#8#1,1+v24#8#1,1,:X#36394#36438Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<T,14v2=Nb+v24#8#"%pstring.
Lemma rvET_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rvET] fx R M V rvET_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rvET] LibSegJs_rvET.regs0 LibSegJs_rvET.kn0 LibSegJs_rvET.BR LibSegJs_rvET.PSS LibSegJs_rvET.NX0 LibSegJs_rvET.F0 222100 LibSegJs_rvET.seg_sound_ax fx R M V rvET_conc_s. Qed.
End PMSRVP.
