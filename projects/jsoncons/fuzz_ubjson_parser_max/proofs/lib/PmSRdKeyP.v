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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_rkA LibSegJs_rkE LibSegJs_rkB LibSegJs_rkF LibSegJs_rkW LibSegJs_rkK LibSegJs_rkZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSRKP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_rkA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rkA.regs0 LibSegJs_rkA.regs_out0).
Lemma KS_rkA_ok : BG.kept_ok 48 LibSegJs_rkA.regs0 LibSegJs_rkA.regs_out0 KS_rkA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition rkA_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10,1_v2#40#40,1,>X#365?0#36<?8Y,T,1#36620T,2_v2#40T,8v24T,9v26T,;v26T,12v25Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rkA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rkA] fx R M V rkA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rkA] LibSegJs_rkA.regs0 LibSegJs_rkA.kn0 LibSegJs_rkA.BR LibSegJs_rkA.PSS LibSegJs_rkA.NX0 LibSegJs_rkA.F0 222704 LibSegJs_rkA.seg_sound_ax fx R M V rkA_conc_s. Qed.
Definition KS_rkE : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rkE.regs0 LibSegJs_rkE.regs_out0).
Lemma KS_rkE_ok : BG.kept_ok 48 LibSegJs_rkE.regs0 LibSegJs_rkE.regs_out0 KS_rkE = true. Proof. vm_compute. reflexivity. Qed.
Definition rkE_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#40S,8v24S,9v26S,:v21S,12v25B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10Mav26v27B#1v27#40,,1,5X#36620#36490Y,T,1#36668T,:v26T,;#<"%pstring.
Lemma rkE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rkE] fx R M V rkE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rkE] LibSegJs_rkE.regs0 LibSegJs_rkE.kn0 LibSegJs_rkE.BR LibSegJs_rkE.PSS LibSegJs_rkE.NX0 LibSegJs_rkE.F0 222752 LibSegJs_rkE.seg_sound_ax fx R M V rkE_conc_s. Qed.
Definition KS_rkB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rkB.regs0 LibSegJs_rkB.regs_out0).
Lemma KS_rkB_ok : BG.kept_ok 48 LibSegJs_rkB.regs0 LibSegJs_rkB.regs_out0 KS_rkB = true. Proof. vm_compute. reflexivity. Qed.
Definition rkB_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#40S,8v24S,9v26S,:v21S,12v25B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10Mav26#,,1,7X#36620#36?04Y,T,1#3663<T,:+v24#18T,;v21T,<+v24#150T,13v21"%pstring.
Lemma rkB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rkB] fx R M V rkB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rkB] LibSegJs_rkB.regs0 LibSegJs_rkB.kn0 LibSegJs_rkB.BR LibSegJs_rkB.PSS LibSegJs_rkB.NX0 LibSegJs_rkB.F0 222752 LibSegJs_rkB.seg_sound_ax fx R M V rkB_conc_s. Qed.
Definition KS_rkF_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rkF.regs0 LibSegJs_rkF.regs_out0).
Lemma KS_rkF_0_ok : BG.kept_ok 48 LibSegJs_rkF.regs0 LibSegJs_rkF.regs_out0 KS_rkF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rkF_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rkF.regs0 LibSegJs_rkF.regs_out1).
Lemma KS_rkF_1_ok : BG.kept_ok 48 LibSegJs_rkF.regs0 LibSegJs_rkF.regs_out1 KS_rkF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition rkF_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#40S,8v24S,9v26S,:v22S,;v23S,12v25S,13v21B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10,,2,6X#3663<#36:><Y,T,1#3664<T,;v21T,14v22C%_v23v21p#2#40#1,6X#3663<#36490Y,1T,1#36668T,:v26T,;#1D#1%_v23v21p#2#40"%pstring.
Lemma rkF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rkF_0; KS_rkF_1] fx R M V rkF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rkF_0; KS_rkF_1] LibSegJs_rkF.regs0 LibSegJs_rkF.kn0 LibSegJs_rkF.BR LibSegJs_rkF.PSS LibSegJs_rkF.NX0 LibSegJs_rkF.F0 222780 LibSegJs_rkF.seg_sound_ax fx R M V rkF_conc_s. Qed.
Definition KS_rkW_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rkW.regs0 LibSegJs_rkW.regs_out0).
Lemma KS_rkW_0_ok : BG.kept_ok 48 LibSegJs_rkW.regs0 LibSegJs_rkW.regs_out0 KS_rkW_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rkW_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rkW.regs0 LibSegJs_rkW.regs_out1).
Lemma KS_rkW_1_ok : BG.kept_ok 48 LibSegJs_rkW.regs0 LibSegJs_rkW.regs_out1 KS_rkW_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition rkW_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#40S,8v24S,9v26S,;v23S,12v25S,13v21S,14v22B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10,,2,2X#3664<#3668<Y,,5X#3664<#36490Y,1T,1#36668T,:v26T,;#7"%pstring.
Lemma rkW_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rkW_0; KS_rkW_1] fx R M V rkW_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rkW_0; KS_rkW_1] LibSegJs_rkW.regs0 LibSegJs_rkW.kn0 LibSegJs_rkW.BR LibSegJs_rkW.PSS LibSegJs_rkW.NX0 LibSegJs_rkW.F0 222796 LibSegJs_rkW.seg_sound_ax fx R M V rkW_conc_s. Qed.
Definition KS_rkK : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rkK.regs0 LibSegJs_rkK.regs_out0).
Lemma KS_rkK_ok : BG.kept_ok 48 LibSegJs_rkK.regs0 LibSegJs_rkK.regs_out0 KS_rkK = true. Proof. vm_compute. reflexivity. Qed.
Definition rkK_conc_s := ",2:A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#40S,8v24S,9v26S,12v25S,13v21S,14v22B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10B#7???7?800040v25#7??????????8Hv25#8P_v2#40#40v25#8O#10000#;60=0Lav25#:?1>8Na+v24#10#I+v24#8#1Pv24#180v25#8Pv26#10v25#8La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=,2_v2#40#10+v24#8#1,1,11X#3668<#36688Y,T,1v28T,2v2T,8v29T,9v2:T,:#1T,;_v2#40T,<v24T,=v26T,>#345:0T,12v2;T,13v2<T,14v2=Nb+v24#8#1Lb_v2#38v21Lb_v2#40v22"%pstring.
Lemma rkK_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rkK] fx R M V rkK_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rkK] LibSegJs_rkK.regs0 LibSegJs_rkK.kn0 LibSegJs_rkK.BR LibSegJs_rkK.PSS LibSegJs_rkK.NX0 LibSegJs_rkK.F0 222860 LibSegJs_rkK.seg_sound_ax fx R M V rkK_conc_s. Qed.
Definition KS_rkZ : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rkZ.regs0 LibSegJs_rkZ.regs_out0).
Lemma KS_rkZ_ok : BG.kept_ok 48 LibSegJs_rkZ.regs0 LibSegJs_rkZ.regs_out0 KS_rkZ = true. Proof. vm_compute. reflexivity. Qed.
Definition rkZ_conc_s := ",1>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#40S,8v24S,9v26S,12v25B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800040v24#7????????>80Hv24#8P_v2#40#40v24#180B#7???7?800040v26#7??????????0Hv26#8P_v2#40#40v26#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=I+v24#8#1,1+v24#8#1,1,:X#36668#36688Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<T,14v2=Nb+v24#8#"%pstring.
Lemma rkZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rkZ] fx R M V rkZ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rkZ] LibSegJs_rkZ.regs0 LibSegJs_rkZ.kn0 LibSegJs_rkZ.BR LibSegJs_rkZ.PSS LibSegJs_rkZ.NX0 LibSegJs_rkZ.F0 222824 LibSegJs_rkZ.seg_sound_ax fx R M V rkZ_conc_s. Qed.
End PMSRKP.
