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
BigLinkBase BigLinkGlue L5Defs L5Kn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_rpA LibSegJs_rpR0 LibSegJs_rpB LibSegJs_rpF LibSegJs_rpG LibSegJs_rpSS LibSegJs_rpSL LibSegJs_rpES LibSegJs_rpEL.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSRPP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcO.
Definition KS_rpA_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpA.regs0 LibSegJs_rpA.regs_out0).
Lemma KS_rpA_0_ok : BG.kept_ok 56 LibSegJs_rpA.regs0 LibSegJs_rpA.regs_out0 KS_rpA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rpA_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpA.regs0 LibSegJs_rpA.regs_out1).
Lemma KS_rpA_1_ok : BG.kept_ok 56 LibSegJs_rpA.regs0 LibSegJs_rpA.regs_out1 KS_rpA_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rpA_2 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpA.regs0 LibSegJs_rpA.regs_out2).
Lemma KS_rpA_2_ok : BG.kept_ok 56 LibSegJs_rpA.regs0 LibSegJs_rpA.regs_out2 KS_rpA_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rpA_3 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpA.regs0 LibSegJs_rpA.regs_out3).
Lemma KS_rpA_3_ok : BG.kept_ok 56 LibSegJs_rpA.regs0 LibSegJs_rpA.regs_out3 KS_rpA_3 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition rpA_conc_s := ",12A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v23S,<v22B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800000v21#7????????>=8Hv21#8P_v2#20#20v21#128La+v21#120v24B#v24#4000B#v23^#?#???????????????,1_v2#20#20,4,9X#36?04#36??0Y,T,:#T,;#C%_v23#p#2#40#1Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,>X#36?04#36?34Y,1T,2_v2#20T,8v23T,9v22T,;v24T,12v21Dv23v24D#1%_v24#p#2#40D#1%_v23#p#2#40Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,>X#36?04#36?80Y,2T,2_v2#20T,8v23T,9v22T,;v24T,12v21Cv24v23D#1%_v24#p#2#40D#1%_v23#p#2#40Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,=X#36?04#36?58Y,3T,2_v2#20T,8v23T,9v22T,;v24T,12v21C%_v24#p#2#40#1D#1%_v23#p#2#40Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma rpA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rpA_0; KS_rpA_1; KS_rpA_2; KS_rpA_3] fx R M V rpA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rpA_0; KS_rpA_1; KS_rpA_2; KS_rpA_3] LibSegJs_rpA.regs0 LibSegJs_rpA.kn0 LibSegJs_rpA.BR LibSegJs_rpA.PSS LibSegJs_rpA.NX0 LibSegJs_rpA.F0 225028 LibSegJs_rpA.seg_sound_ax fx R M V rpA_conc_s. Qed.
Definition KS_rpR0_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpR0.regs0 LibSegJs_rpR0.regs_out0).
Lemma KS_rpR0_0_ok : BG.kept_ok 56 LibSegJs_rpR0.regs0 LibSegJs_rpR0.regs_out0 KS_rpR0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rpR0_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpR0.regs0 LibSegJs_rpR0.regs_out1).
Lemma KS_rpR0_1_ok : BG.kept_ok 56 LibSegJs_rpR0.regs0 LibSegJs_rpR0.regs_out1 KS_rpR0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition rpR0_conc_s := ",12A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v2:p#2#40S,2_v2#20S,8v23S,9v22S,12v21B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800000v21#7????????>=8Hv21#8P_v2#20#20v21#128La+v21#110#4000La+v21#108v2:B#1v23^#?#???????????????,,2,4X#36?58#36?80Y,T,<#4000C#4000v23,7X#36?58#36:08Y,1T,1#36?6<T,:v21T,;v2:T,<#4000Dv23#4000"%pstring.
Lemma rpR0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rpR0_0; KS_rpR0_1] fx R M V rpR0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rpR0_0; KS_rpR0_1] LibSegJs_rpR0.regs0 LibSegJs_rpR0.kn0 LibSegJs_rpR0.BR LibSegJs_rpR0.PSS LibSegJs_rpR0.NX0 LibSegJs_rpR0.F0 225112 LibSegJs_rpR0.seg_sound_ax fx R M V rpR0_conc_s. Qed.
Definition KS_rpB_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpB.regs0 LibSegJs_rpB.regs_out0).
Lemma KS_rpB_0_ok : BG.kept_ok 56 LibSegJs_rpB.regs0 LibSegJs_rpB.regs_out0 KS_rpB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rpB_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpB.regs0 LibSegJs_rpB.regs_out1).
Lemma KS_rpB_1_ok : BG.kept_ok 56 LibSegJs_rpB.regs0 LibSegJs_rpB.regs_out1 KS_rpB_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition rpB_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v23S,9v22S,:v2;S,12v21B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800000v21#7????????>=8Hv21#8P_v2#20#20v21#128La+v21#108v2:I+v21#118#10B#v2;#4000B#1v23^#?#???????????????,1+v21#118#10,2,7X#36?6<#36?80Y,T,:v2:T,;v2;Cv2;v23Lb+v21#120v2;Lb+v21#118v2:,7X#36?6<#36?34Y,1T,:v2:T,;v2;Dv23v2;Lb+v21#120v2;Lb+v21#118v2:"%pstring.
Lemma rpB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rpB_0; KS_rpB_1] fx R M V rpB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rpB_0; KS_rpB_1] LibSegJs_rpB.regs0 LibSegJs_rpB.kn0 LibSegJs_rpB.BR LibSegJs_rpB.PSS LibSegJs_rpB.NX0 LibSegJs_rpB.F0 225132 LibSegJs_rpB.seg_sound_ax fx R M V rpB_conc_s. Qed.
Definition KS_rpF : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpF.regs0 LibSegJs_rpF.regs_out0).
Lemma KS_rpF_ok : BG.kept_ok 56 LibSegJs_rpF.regs0 LibSegJs_rpF.regs_out0 KS_rpF = true. Proof. vm_compute. reflexivity. Qed.
Definition rpF_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#20S,8v23S,9v22S,;v24S,12v21B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800000v21#7????????>=8Hv21#8P_v2#20#20v21#128La+v21#118v25La+v21#100v26B#1v23#4000B#1v24#4000,,1,6X#36?34#36?48Y,T,:v25T,;+*-1v23v24T,<+v23v26T,=+v23v25"%pstring.
Lemma rpF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rpF] fx R M V rpF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rpF] LibSegJs_rpF.regs0 LibSegJs_rpF.kn0 LibSegJs_rpF.BR LibSegJs_rpF.PSS LibSegJs_rpF.NX0 LibSegJs_rpF.F0 225076 LibSegJs_rpF.seg_sound_ax fx R M V rpF_conc_s. Qed.
Definition KS_rpG : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpG.regs0 LibSegJs_rpG.regs_out0).
Lemma KS_rpG_ok : BG.kept_ok 56 LibSegJs_rpG.regs0 LibSegJs_rpG.regs_out0 KS_rpG = true. Proof. vm_compute. reflexivity. Qed.
Definition rpG_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40S,2_v2#20S,8v23S,9v22S,:v25S,;v30S,<v31S,=v32S,12v21B#7???7?800020v2#800000000000Hv2#10I_v2#20#20La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?B#7???7?800000v21#7????????>=8Hv21#8P_v2#20#20v21#128I+v21#100#8I+v21#118#10,2+v21#100#8+v21#118#10,1,;X#36?48#36??0Y,T,1v2<T,2v2T,8v2=T,9v2>T,;v23T,12v2?Lb+v21#120v30Lb+v21#118v32Lb+v21#100v31"%pstring.
Lemma rpG_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rpG] fx R M V rpG_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rpG] LibSegJs_rpG.regs0 LibSegJs_rpG.kn0 LibSegJs_rpG.BR LibSegJs_rpG.PSS LibSegJs_rpG.NX0 LibSegJs_rpG.F0 225096 LibSegJs_rpG.seg_sound_ax fx R M V rpG_conc_s. Qed.
Definition KS_rpSS : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpSS.regs0 LibSegJs_rpSS.regs_out0).
Lemma KS_rpSS_ok : BG.kept_ok 56 LibSegJs_rpSS.regs0 LibSegJs_rpSS.regs_out0 KS_rpSS = true. Proof. vm_compute. reflexivity. Qed.
Definition rpSS_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v27p#2#40S,2_v2#20S,8v23S,9v22S,12v21B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800000v22#7?????????>8Hv22#8P_v2#20#20v22#18Nav22v27B#v27#2<Fv27#fIv22#2,1+v22##2,1,8X#36?80#378<4Y,T,1#36?;0T,:v21T,;v22T,<v23Nbv22#Nb+v22#1#"%pstring.
Lemma rpSS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rpSS] fx R M V rpSS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rpSS] LibSegJs_rpSS.regs0 LibSegJs_rpSS.kn0 LibSegJs_rpSS.BR LibSegJs_rpSS.PSS LibSegJs_rpSS.NX0 LibSegJs_rpSS.F0 225152 LibSegJs_rpSS.seg_sound_ax fx R M V rpSS_conc_s. Qed.
Definition KS_rpSL : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpSL.regs0 LibSegJs_rpSL.regs_out0).
Lemma KS_rpSL_ok : BG.kept_ok 56 LibSegJs_rpSL.regs0 LibSegJs_rpSL.regs_out0 KS_rpSL = true. Proof. vm_compute. reflexivity. Qed.
Definition rpSL_conc_s := ",19A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v27p#2#40A#v29p#2#40S,2_v2#20S,8v23S,9v22S,12v21B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800000v22#7?????????>8Hv22#8P_v2#20#20v22#18Nav22v27B#v27#??Fv27#tLa+v22#10v29B#1000v29#800000000000Iv29#1I+v22#8#8P_v2#20#20v29#1Pv22#18v29#1,2+v29##1+v22#8#8,1,8X#36?80#378<4Y,T,1#36?;0T,:v21T,;v22T,<v23Lb+v22#8#Nbv29#"%pstring.
Lemma rpSL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rpSL] fx R M V rpSL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rpSL] LibSegJs_rpSL.regs0 LibSegJs_rpSL.kn0 LibSegJs_rpSL.BR LibSegJs_rpSL.PSS LibSegJs_rpSL.NX0 LibSegJs_rpSL.F0 225152 LibSegJs_rpSL.seg_sound_ax fx R M V rpSL_conc_s. Qed.
Definition KS_rpES : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpES.regs0 LibSegJs_rpES.regs_out0).
Lemma KS_rpES_ok : BG.kept_ok 56 LibSegJs_rpES.regs0 LibSegJs_rpES.regs_out0 KS_rpES = true. Proof. vm_compute. reflexivity. Qed.
Definition rpES_conc_s := ",1:A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v27p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40S,2_v2#20S,8v23S,9v22S,12v21B#7???7?800020v2#800000000000Hv2#10I_v2#20#20La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?B#7???7?800000v22#7?????????>8Hv22#8P_v2#20#20v22#18Nav22v27B#v27#2<Fv27#f,,1,9X#36?;0#36??0Y,T,1v2<T,2v2T,8v2=T,9v2>T,:+v22#1W,;/v27#2T,12v2?"%pstring.
Lemma rpES_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rpES] fx R M V rpES_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rpES] LibSegJs_rpES.regs0 LibSegJs_rpES.kn0 LibSegJs_rpES.BR LibSegJs_rpES.PSS LibSegJs_rpES.NX0 LibSegJs_rpES.F0 225200 LibSegJs_rpES.seg_sound_ax fx R M V rpES_conc_s. Qed.
Definition KS_rpEL : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_rpEL.regs0 LibSegJs_rpEL.regs_out0).
Lemma KS_rpEL_ok : BG.kept_ok 56 LibSegJs_rpEL.regs0 LibSegJs_rpEL.regs_out0 KS_rpEL = true. Proof. vm_compute. reflexivity. Qed.
Definition rpEL_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40S,2_v2#20S,8v23S,9v22S,12v21B#7???7?800020v2#800000000000Hv2#10I_v2#20#20La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?B#7???7?800000v22#7?????????>8Hv22#8P_v2#20#20v22#18Nav22v27B#v27#??Fv27#tLa+v22#8v28La+v22#10v29,,1,9X#36?;0#36??0Y,T,1v2<T,2v2T,8v2=T,9v2>T,:v29T,;v28T,12v2?"%pstring.
Lemma rpEL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rpEL] fx R M V rpEL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rpEL] LibSegJs_rpEL.regs0 LibSegJs_rpEL.kn0 LibSegJs_rpEL.BR LibSegJs_rpEL.PSS LibSegJs_rpEL.NX0 LibSegJs_rpEL.F0 225200 LibSegJs_rpEL.seg_sound_ax fx R M V rpEL_conc_s. Qed.
End PMSRPP.
