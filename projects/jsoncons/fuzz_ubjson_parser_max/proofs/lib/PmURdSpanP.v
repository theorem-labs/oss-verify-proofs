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
BigLinkBase BigLinkGlueUb0 L5Defs L5KnU.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_urpA LibSegJu_urpR0 LibSegJu_urpB LibSegJu_urpF LibSegJu_urpG LibSegJu_urpSS LibSegJu_urpSL LibSegJu_urpES LibSegJu_urpEL.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcOU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMURPP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcOU.
Definition KS_urpA_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpA.regs0 LibSegJu_urpA.regs_out0).
Lemma KS_urpA_0_ok : BG.kept_ok 56 LibSegJu_urpA.regs0 LibSegJu_urpA.regs_out0 KS_urpA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_urpA_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpA.regs0 LibSegJu_urpA.regs_out1).
Lemma KS_urpA_1_ok : BG.kept_ok 56 LibSegJu_urpA.regs0 LibSegJu_urpA.regs_out1 KS_urpA_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_urpA_2 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpA.regs0 LibSegJu_urpA.regs_out2).
Lemma KS_urpA_2_ok : BG.kept_ok 56 LibSegJu_urpA.regs0 LibSegJu_urpA.regs_out2 KS_urpA_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_urpA_3 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpA.regs0 LibSegJu_urpA.regs_out3).
Lemma KS_urpA_3_ok : BG.kept_ok 56 LibSegJu_urpA.regs0 LibSegJu_urpA.regs_out3 KS_urpA_3 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition urpA_conc_s := ",12A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v23S,<v22B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800000v21#7????????>=8Hv21#8P_v2#20#20v21#128La+v21#120v24B#v24#4000B#v23^#?#???????????????,1_v2#20#20,4,9X#37<;0#37=:4Y,T,:#T,;#C%_v23#p#2#40#1Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,>X#37<;0#37<>0Y,1T,2_v2#20T,8v23T,9v21T,;v24T,12v22Dv23v24D#1%_v24#p#2#40D#1%_v23#p#2#40Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,>X#37<;0#37=38Y,2T,2_v2#20T,8v23T,9v21T,;v24T,12v22Cv24v23D#1%_v24#p#2#40D#1%_v23#p#2#40Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,=X#37<;0#37=10Y,3T,2_v2#20T,8v23T,9v21T,;v24T,12v22C%_v24#p#2#40#1D#1%_v23#p#2#40Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma urpA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urpA_0; KS_urpA_1; KS_urpA_2; KS_urpA_3] fx R M V urpA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urpA_0; KS_urpA_1; KS_urpA_2; KS_urpA_3] LibSegJu_urpA.regs0 LibSegJu_urpA.kn0 LibSegJu_urpA.BR LibSegJu_urpA.PSS LibSegJu_urpA.NX0 LibSegJu_urpA.F0 228528 LibSegJu_urpA.seg_sound_ax fx R M V urpA_conc_s. Qed.
Definition KS_urpR0_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpR0.regs0 LibSegJu_urpR0.regs_out0).
Lemma KS_urpR0_0_ok : BG.kept_ok 56 LibSegJu_urpR0.regs0 LibSegJu_urpR0.regs_out0 KS_urpR0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_urpR0_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpR0.regs0 LibSegJu_urpR0.regs_out1).
Lemma KS_urpR0_1_ok : BG.kept_ok 56 LibSegJu_urpR0.regs0 LibSegJu_urpR0.regs_out1 KS_urpR0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition urpR0_conc_s := ",12A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v2:p#2#40S,2_v2#20S,8v23S,9v21S,12v22B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800000v21#7????????>=8Hv21#8P_v2#20#20v21#128La+v21#110#4000La+v21#108v2:B#1v23^#?#???????????????,,2,4X#37=10#37=38Y,T,<#4000C#4000v23,7X#37=10#37720Y,1T,1#37=24T,:v21T,;v2:T,<#4000Dv23#4000"%pstring.
Lemma urpR0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urpR0_0; KS_urpR0_1] fx R M V urpR0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urpR0_0; KS_urpR0_1] LibSegJu_urpR0.regs0 LibSegJu_urpR0.kn0 LibSegJu_urpR0.BR LibSegJu_urpR0.PSS LibSegJu_urpR0.NX0 LibSegJu_urpR0.F0 228624 LibSegJu_urpR0.seg_sound_ax fx R M V urpR0_conc_s. Qed.
Definition KS_urpB_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpB.regs0 LibSegJu_urpB.regs_out0).
Lemma KS_urpB_0_ok : BG.kept_ok 56 LibSegJu_urpB.regs0 LibSegJu_urpB.regs_out0 KS_urpB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_urpB_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpB.regs0 LibSegJu_urpB.regs_out1).
Lemma KS_urpB_1_ok : BG.kept_ok 56 LibSegJu_urpB.regs0 LibSegJu_urpB.regs_out1 KS_urpB_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition urpB_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v23S,9v21S,:v2;S,12v22B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800000v21#7????????>=8Hv21#8P_v2#20#20v21#128La+v21#108v2:I+v21#118#10B#v2;#4000B#1v23^#?#???????????????,1+v21#118#10,2,7X#37=24#37=38Y,T,:v2:T,;v2;Cv2;v23Lb+v21#120v2;Lb+v21#118v2:,7X#37=24#37<>0Y,1T,:v2:T,;v2;Dv23v2;Lb+v21#120v2;Lb+v21#118v2:"%pstring.
Lemma urpB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urpB_0; KS_urpB_1] fx R M V urpB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urpB_0; KS_urpB_1] LibSegJu_urpB.regs0 LibSegJu_urpB.kn0 LibSegJu_urpB.BR LibSegJu_urpB.PSS LibSegJu_urpB.NX0 LibSegJu_urpB.F0 228644 LibSegJu_urpB.seg_sound_ax fx R M V urpB_conc_s. Qed.
Definition KS_urpF : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpF.regs0 LibSegJu_urpF.regs_out0).
Lemma KS_urpF_ok : BG.kept_ok 56 LibSegJu_urpF.regs0 LibSegJu_urpF.regs_out0 KS_urpF = true. Proof. vm_compute. reflexivity. Qed.
Definition urpF_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#20S,8v23S,9v21S,;v24S,12v22B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800000v21#7????????>=8Hv21#8P_v2#20#20v21#128La+v21#118v25La+v21#100v26B#1v23#4000B#1v24#4000B#1000v25#800000000000,,1,6X#37<>0#37=00Y,T,:v25T,;+*-1v23v24T,<+v23v25T,=+v23v26"%pstring.
Lemma urpF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urpF] fx R M V urpF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urpF] LibSegJu_urpF.regs0 LibSegJu_urpF.kn0 LibSegJu_urpF.BR LibSegJu_urpF.PSS LibSegJu_urpF.NX0 LibSegJu_urpF.F0 228576 LibSegJu_urpF.seg_sound_ax fx R M V urpF_conc_s. Qed.
Definition KS_urpG : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpG.regs0 LibSegJu_urpG.regs_out0).
Lemma KS_urpG_ok : BG.kept_ok 56 LibSegJu_urpG.regs0 LibSegJu_urpG.regs_out0 KS_urpG = true. Proof. vm_compute. reflexivity. Qed.
Definition urpG_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40S,2_v2#20S,8v23S,9v21S,:v25S,;v30S,<v32S,=v31S,12v22B#7???7?800020v2#800000000000Hv2#10I_v2#20#20La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?B#7???7?800000v21#7????????>=8Hv21#8P_v2#20#20v21#128I+v21#100#8I+v21#118#10,2+v21#100#8+v21#118#10,1,;X#37=00#37=:4Y,T,1v2<T,2v2T,8v2=T,9v2>T,;v23T,12v2?Lb+v21#120v30Lb+v21#118v32Lb+v21#100v31"%pstring.
Lemma urpG_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urpG] fx R M V urpG_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urpG] LibSegJu_urpG.regs0 LibSegJu_urpG.kn0 LibSegJu_urpG.BR LibSegJu_urpG.PSS LibSegJu_urpG.NX0 LibSegJu_urpG.F0 228608 LibSegJu_urpG.seg_sound_ax fx R M V urpG_conc_s. Qed.
Definition KS_urpSS : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpSS.regs0 LibSegJu_urpSS.regs_out0).
Lemma KS_urpSS_ok : BG.kept_ok 56 LibSegJu_urpSS.regs0 LibSegJu_urpSS.regs_out0 KS_urpSS = true. Proof. vm_compute. reflexivity. Qed.
Definition urpSS_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v27p#2#40S,2_v2#20S,8v23S,9v21S,12v22B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800000v22#7?????????>8Hv22#8P_v2#20#20v22#18Nav22v27B#v27#2<Fv27#fIv22#2,1+v22##2,1,8X#37=38#387><Y,T,1#37=6<T,:v21T,;v22T,<v23Nbv22#Nb+v22#1#"%pstring.
Lemma urpSS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urpSS] fx R M V urpSS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urpSS] LibSegJu_urpSS.regs0 LibSegJu_urpSS.kn0 LibSegJu_urpSS.BR LibSegJu_urpSS.PSS LibSegJu_urpSS.NX0 LibSegJu_urpSS.F0 228664 LibSegJu_urpSS.seg_sound_ax fx R M V urpSS_conc_s. Qed.
Definition KS_urpSL : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpSL.regs0 LibSegJu_urpSL.regs_out0).
Lemma KS_urpSL_ok : BG.kept_ok 56 LibSegJu_urpSL.regs0 LibSegJu_urpSL.regs_out0 KS_urpSL = true. Proof. vm_compute. reflexivity. Qed.
Definition urpSL_conc_s := ",19A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v27p#2#40A#v29p#2#40S,2_v2#20S,8v23S,9v21S,12v22B#7???7?800020v2#800000000000Hv2#10I_v2#20#20B#7???7?800000v22#7?????????>8Hv22#8P_v2#20#20v22#18Nav22v27B#v27#??Fv27#tLa+v22#10v29B#1000v29#800000000000Iv29#1I+v22#8#8P_v2#20#20v29#1Pv22#18v29#1,2+v29##1+v22#8#8,1,8X#37=38#387><Y,T,1#37=6<T,:v21T,;v22T,<v23Lb+v22#8#Nbv29#"%pstring.
Lemma urpSL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urpSL] fx R M V urpSL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urpSL] LibSegJu_urpSL.regs0 LibSegJu_urpSL.kn0 LibSegJu_urpSL.BR LibSegJu_urpSL.PSS LibSegJu_urpSL.NX0 LibSegJu_urpSL.F0 228664 LibSegJu_urpSL.seg_sound_ax fx R M V urpSL_conc_s. Qed.
Definition KS_urpES : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpES.regs0 LibSegJu_urpES.regs_out0).
Lemma KS_urpES_ok : BG.kept_ok 56 LibSegJu_urpES.regs0 LibSegJu_urpES.regs_out0 KS_urpES = true. Proof. vm_compute. reflexivity. Qed.
Definition urpES_conc_s := ",1:A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v27p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40S,2_v2#20S,8v23S,9v21S,12v22B#7???7?800020v2#800000000000Hv2#10I_v2#20#20La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?B#7???7?800000v22#7?????????>8Hv22#8P_v2#20#20v22#18Nav22v27B#v27#2<Fv27#f,,1,9X#37=6<#37=:4Y,T,1v2<T,2v2T,8v2=T,9v2>T,:+v22#1W,;/v27#2T,12v2?"%pstring.
Lemma urpES_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urpES] fx R M V urpES_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urpES] LibSegJu_urpES.regs0 LibSegJu_urpES.kn0 LibSegJu_urpES.BR LibSegJu_urpES.PSS LibSegJu_urpES.NX0 LibSegJu_urpES.F0 228716 LibSegJu_urpES.seg_sound_ax fx R M V urpES_conc_s. Qed.
Definition KS_urpEL : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_urpEL.regs0 LibSegJu_urpEL.regs_out0).
Lemma KS_urpEL_ok : BG.kept_ok 56 LibSegJu_urpEL.regs0 LibSegJu_urpEL.regs_out0 KS_urpEL = true. Proof. vm_compute. reflexivity. Qed.
Definition urpEL_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40S,2_v2#20S,8v23S,9v21S,12v22B#7???7?800020v2#800000000000Hv2#10I_v2#20#20La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?B#7???7?800000v22#7?????????>8Hv22#8P_v2#20#20v22#18Nav22v27B#v27#??Fv27#tLa+v22#8v28La+v22#10v29,,1,9X#37=6<#37=:4Y,T,1v2<T,2v2T,8v2=T,9v2>T,:v29T,;v28T,12v2?"%pstring.
Lemma urpEL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urpEL] fx R M V urpEL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urpEL] LibSegJu_urpEL.regs0 LibSegJu_urpEL.kn0 LibSegJu_urpEL.BR LibSegJu_urpEL.PSS LibSegJu_urpEL.NX0 LibSegJu_urpEL.F0 228716 LibSegJu_urpEL.seg_sound_ax fx R M V urpEL_conc_s. Qed.
End PMURPP.
