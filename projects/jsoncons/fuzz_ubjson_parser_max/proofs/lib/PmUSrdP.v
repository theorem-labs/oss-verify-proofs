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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_utsA LibSegJu_utsH1 LibSegJu_utsH0 LibSegJu_utsRS LibSegJu_utsRL LibSegJu_utsQS LibSegJu_utsQL LibSegJu_utsE LibSegJu_utsF LibSegJu_utsDS LibSegJu_utsDL LibSegJu_utsD2 LibSegJu_utsD3.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcOU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMUSRP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcOU.
Definition KS_utsA_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsA.regs0 LibSegJu_utsA.regs_out0).
Lemma KS_utsA_0_ok : BG.kept_ok 56 LibSegJu_utsA.regs0 LibSegJu_utsA.regs_out0 KS_utsA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_utsA_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsA.regs0 LibSegJu_utsA.regs_out1).
Lemma KS_utsA_1_ok : BG.kept_ok 56 LibSegJu_utsA.regs0 LibSegJu_utsA.regs_out1 KS_utsA_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition utsA_conc_s := ",<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#v23^#?#???????????????,1_v2#50#50,2,12X#387><#3882<Y,T,2_v2#50T,8v23T,9v22T,12v21T,15v23T,16+v22#1D#1%_v23#p#2#40Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,=X#387><#38974Y,1T,:v23C%_v23#p#2#40#1Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma utsA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsA_0; KS_utsA_1] fx R M V utsA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsA_0; KS_utsA_1] LibSegJu_utsA.regs0 LibSegJu_utsA.kn0 LibSegJu_utsA.BR LibSegJu_utsA.PSS LibSegJu_utsA.NX0 LibSegJu_utsA.F0 231404 LibSegJu_utsA.seg_sound_ax fx R M V utsA_conc_s. Qed.
Definition KS_utsH1_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsH1.regs0 LibSegJu_utsH1.regs_out0).
Lemma KS_utsH1_0_ok : BG.kept_ok 56 LibSegJu_utsH1.regs0 LibSegJu_utsH1.regs_out0 KS_utsH1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_utsH1_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsH1.regs0 LibSegJu_utsH1.regs_out1).
Lemma KS_utsH1_1_ok : BG.kept_ok 56 LibSegJu_utsH1.regs0 LibSegJu_utsH1.regs_out1 KS_utsH1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition utsH1_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#50S,8v23S,9v22S,12v21S,15v24S,16+v22#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v21#7????????>=8Hv21#8P_v2#50#50v21#128La+v21#120v25B#1v25#4000La+v21#110#4000B#1v24^#?#???????????????,,2,7X#3882<#38858Y,T,1#38834T,:#4000T,;v25T,13v24Cv24#4000,7X#3882<#38858Y,1T,1#38834T,:#4000T,;v25T,13#4000D#4000v24"%pstring.
Lemma utsH1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsH1_0; KS_utsH1_1] fx R M V utsH1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsH1_0; KS_utsH1_1] LibSegJu_utsH1.regs0 LibSegJu_utsH1.kn0 LibSegJu_utsH1.BR LibSegJu_utsH1.PSS LibSegJu_utsH1.NX0 LibSegJu_utsH1.F0 231468 LibSegJu_utsH1.seg_sound_ax fx R M V utsH1_conc_s. Qed.
Definition KS_utsH0_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsH0.regs0 LibSegJu_utsH0.regs_out0).
Lemma KS_utsH0_0_ok : BG.kept_ok 56 LibSegJu_utsH0.regs0 LibSegJu_utsH0.regs_out0 KS_utsH0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_utsH0_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsH0.regs0 LibSegJu_utsH0.regs_out1).
Lemma KS_utsH0_1_ok : BG.kept_ok 56 LibSegJu_utsH0.regs0 LibSegJu_utsH0.regs_out1 KS_utsH0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_utsH0_2 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsH0.regs0 LibSegJu_utsH0.regs_out2).
Lemma KS_utsH0_2_ok : BG.kept_ok 56 LibSegJu_utsH0.regs0 LibSegJu_utsH0.regs_out2 KS_utsH0_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition utsH0_conc_s := ",30A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v26p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#50S,8v23S,9v22S,12v21S,15v24S,16+v22#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34B#7???7?800000v21#7????????>=8Hv21#8P_v2#50#50v21#128O#10000#;7120La+v21#120#La+v21#110#4000La+v21#?0v26B#7???7?800000v26#7????????>?0Hv26#8P_v2#50#50v26#110Lav26#;3:>8Na+v26#98v36B#v36#2B#1v24^#?#???????????????,,3,8X#3882<#38858Y,T,1#38834T,:#4000T,;#T,13v24Cv24#4000C%_/%*^#4#v36p#2#40^#8##p#2#40#1,8X#3882<#388<4Y,1T,1#38834T,:#T,;#T,13#4000D#4000v24C%_/%*^#4#v36p#2#40^#8##p#2#40#1,?X#3882<#38974Y,2T,1v2<T,2v2T,8v2=T,9v2>T,:_v23v24T,;#T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34D#1%_/%*^#4#v36p#2#40^#8##p#2#40"%pstring.
Lemma utsH0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsH0_0; KS_utsH0_1; KS_utsH0_2] fx R M V utsH0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsH0_0; KS_utsH0_1; KS_utsH0_2] LibSegJu_utsH0.regs0 LibSegJu_utsH0.kn0 LibSegJu_utsH0.BR LibSegJu_utsH0.PSS LibSegJu_utsH0.NX0 LibSegJu_utsH0.F0 231468 LibSegJu_utsH0.seg_sound_ax fx R M V utsH0_conc_s. Qed.
Definition KS_utsRS : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsRS.regs0 LibSegJu_utsRS.regs_out0).
Lemma KS_utsRS_ok : BG.kept_ok 56 LibSegJu_utsRS.regs0 LibSegJu_utsRS.regs_out0 KS_utsRS = true. Proof. vm_compute. reflexivity. Qed.
Definition utsRS_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v2:p#2#40S,2_v2#50S,8v23S,9v22S,12v21S,13v2:S,15v24S,16+v22#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v22#7?????????>8Hv22#8P_v2#50#50v22#18Nav22v27B#v27#2<Fv27#fB#1v2:#4000,,1,7X#38858#57=34Y,T,1#38880T,:v22W,;%+v2:/v27#2p#2#40T,<#W,17/v27#2"%pstring.
Lemma utsRS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsRS] fx R M V utsRS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsRS] LibSegJu_utsRS.regs0 LibSegJu_utsRS.kn0 LibSegJu_utsRS.BR LibSegJu_utsRS.PSS LibSegJu_utsRS.NX0 LibSegJu_utsRS.F0 231512 LibSegJu_utsRS.seg_sound_ax fx R M V utsRS_conc_s. Qed.
Definition KS_utsRL : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsRL.regs0 LibSegJu_utsRL.regs_out0).
Lemma KS_utsRL_ok : BG.kept_ok 56 LibSegJu_utsRL.regs0 LibSegJu_utsRL.regs_out0 KS_utsRL = true. Proof. vm_compute. reflexivity. Qed.
Definition utsRL_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v28p#2#40A#v2:p#2#40S,2_v2#50S,8v23S,9v22S,12v21S,13v2:S,15v24S,16+v22#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v22#7?????????>8Hv22#8P_v2#50#50v22#18Nav22v27B#v27#??Fv27#tLa+v22#8v28B#v28#8000000B#1v2:#4000,,1,7X#38858#57=34Y,T,1#38880T,:v22T,;+v28v2:T,<#T,17v28"%pstring.
Lemma utsRL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsRL] fx R M V utsRL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsRL] LibSegJu_utsRL.regs0 LibSegJu_utsRL.kn0 LibSegJu_utsRL.BR LibSegJu_utsRL.PSS LibSegJu_utsRL.NX0 LibSegJu_utsRL.F0 231512 LibSegJu_utsRL.seg_sound_ax fx R M V utsRL_conc_s. Qed.
Definition KS_utsQS : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsQS.regs0 LibSegJu_utsQS.regs_out0).
Lemma KS_utsQS_ok : BG.kept_ok 56 LibSegJu_utsQS.regs0 LibSegJu_utsQS.regs_out0 KS_utsQS = true. Proof. vm_compute. reflexivity. Qed.
Definition utsQS_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#50S,8v23S,9v22S,12v21S,13v2:S,15v24S,16+v22#1S,17v2;B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v22#7?????????>8Hv22#8P_v2#50#50v22#18Nav22v27B#v27#2<Fv27#fB#1v2:#4000B#v2;#16,,1,6X#38880#374;8Y,T,1#388;0T,:v21T,;++v22v2;#1T,<v2:"%pstring.
Lemma utsQS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsQS] fx R M V utsQS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsQS] LibSegJu_utsQS.regs0 LibSegJu_utsQS.kn0 LibSegJu_utsQS.BR LibSegJu_utsQS.PSS LibSegJu_utsQS.NX0 LibSegJu_utsQS.F0 231552 LibSegJu_utsQS.seg_sound_ax fx R M V utsQS_conc_s. Qed.
Definition KS_utsQL : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsQL.regs0 LibSegJu_utsQL.regs_out0).
Lemma KS_utsQL_ok : BG.kept_ok 56 LibSegJu_utsQL.regs0 LibSegJu_utsQL.regs_out0 KS_utsQL = true. Proof. vm_compute. reflexivity. Qed.
Definition utsQL_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#50S,8v23S,9v22S,12v21S,13v2:S,15v24S,16+v22#1S,17v2;B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v22#7?????????>8Hv22#8P_v2#50#50v22#18Nav22v27B#v27#??Fv27#tLa+v22#10v29B#1000v29#800000000000B#1v2:#4000B#v2;#8000000,,1,6X#38880#374;8Y,T,1#388;0T,:v21T,;+v29v2;T,<v2:"%pstring.
Lemma utsQL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsQL] fx R M V utsQL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsQL] LibSegJu_utsQL.regs0 LibSegJu_utsQL.kn0 LibSegJu_utsQL.BR LibSegJu_utsQL.PSS LibSegJu_utsQL.NX0 LibSegJu_utsQL.F0 231552 LibSegJu_utsQL.seg_sound_ax fx R M V utsQL_conc_s. Qed.
Definition KS_utsE_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsE.regs0 LibSegJu_utsE.regs_out0).
Lemma KS_utsE_0_ok : BG.kept_ok 56 LibSegJu_utsE.regs0 LibSegJu_utsE.regs_out0 KS_utsE_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_utsE_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsE.regs0 LibSegJu_utsE.regs_out1).
Lemma KS_utsE_1_ok : BG.kept_ok 56 LibSegJu_utsE.regs0 LibSegJu_utsE.regs_out1 KS_utsE_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_utsE_2 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsE.regs0 LibSegJu_utsE.regs_out2).
Lemma KS_utsE_2_ok : BG.kept_ok 56 LibSegJu_utsE.regs0 LibSegJu_utsE.regs_out2 KS_utsE_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition utsE_conc_s := ",2:A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40S,2_v2#50S,8v23S,9v22S,:v35S,12v21S,13v2:S,15v24S,16+v22#1S,17v2;B#7???7?800050v2#800000000000Hv2#10I_v2#50#50La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34B#v35#4000B#1v2:#4000B#v2;#8000000B#1v24^#?#???????????????,,3,8X#388;0#57=34Y,T,1#38940T,:v22T,;+v2;v35T,<#T,14v35D#1%_v35v2:p#2#40,6X#388;0#3882<Y,1T,14v35T,15_v24v35D#1%_%+v24%*^#?#???????????????v35p#2#40p#2#40#p#2#40C%_v35v2:p#2#40#1,?X#388;0#38974Y,2T,1v2<T,2v2T,8v2=T,9v2>T,:+v23+*-1v24v35T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34C%_%+v24%*^#?#???????????????v35p#2#40p#2#40#p#2#40#1C%_v35v2:p#2#40#1"%pstring.
Lemma utsE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsE_0; KS_utsE_1; KS_utsE_2] fx R M V utsE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsE_0; KS_utsE_1; KS_utsE_2] LibSegJu_utsE.regs0 LibSegJu_utsE.kn0 LibSegJu_utsE.BR LibSegJu_utsE.PSS LibSegJu_utsE.NX0 LibSegJu_utsE.F0 231600 LibSegJu_utsE.seg_sound_ax fx R M V utsE_conc_s. Qed.
Definition KS_utsF_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsF.regs0 LibSegJu_utsF.regs_out0).
Lemma KS_utsF_0_ok : BG.kept_ok 56 LibSegJu_utsF.regs0 LibSegJu_utsF.regs_out0 KS_utsF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_utsF_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsF.regs0 LibSegJu_utsF.regs_out1).
Lemma KS_utsF_1_ok : BG.kept_ok 56 LibSegJu_utsF.regs0 LibSegJu_utsF.regs_out1 KS_utsF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition utsF_conc_s := ",24A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40S,2_v2#50S,8v23S,9v22S,12v21S,14v35S,15v24S,16+v22#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34B#v35#4000B#1v24^#?#???????????????,,2,4X#38940#3882<Y,T,15_v24v35D#1%_%+v24%*^#?#???????????????v35p#2#40p#2#40#p#2#40,>X#38940#38974Y,1T,1v2<T,2v2T,8v2=T,9v2>T,:+v23+*-1v24v35T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34C%_%+v24%*^#?#???????????????v35p#2#40p#2#40#p#2#40#1"%pstring.
Lemma utsF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsF_0; KS_utsF_1] fx R M V utsF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsF_0; KS_utsF_1] LibSegJu_utsF.regs0 LibSegJu_utsF.kn0 LibSegJu_utsF.BR LibSegJu_utsF.PSS LibSegJu_utsF.NX0 LibSegJu_utsF.F0 231744 LibSegJu_utsF.seg_sound_ax fx R M V utsF_conc_s. Qed.
Definition KS_utsDS : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsDS.regs0 LibSegJu_utsDS.regs_out0).
Lemma KS_utsDS_ok : BG.kept_ok 56 LibSegJu_utsDS.regs0 LibSegJu_utsDS.regs_out0 KS_utsDS = true. Proof. vm_compute. reflexivity. Qed.
Definition utsDS_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40S,2_v2#50S,8v23S,9v22S,12v21S,13#4000S,15v24S,16+v22#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v22#7?????????>8Hv22#8P_v2#50#50v22#18Nav22v27B#v27#2<Fv27#f,,1,7X#388<4#57=34Y,T,1#388><T,:v22W,;%+/v27#2#4000p#2#40T,<#W,17/v27#2"%pstring.
Lemma utsDS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsDS] fx R M V utsDS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsDS] LibSegJu_utsDS.regs0 LibSegJu_utsDS.kn0 LibSegJu_utsDS.BR LibSegJu_utsDS.PSS LibSegJu_utsDS.NX0 LibSegJu_utsDS.F0 231620 LibSegJu_utsDS.seg_sound_ax fx R M V utsDS_conc_s. Qed.
Definition KS_utsDL : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsDL.regs0 LibSegJu_utsDL.regs_out0).
Lemma KS_utsDL_ok : BG.kept_ok 56 LibSegJu_utsDL.regs0 LibSegJu_utsDL.regs_out0 KS_utsDL = true. Proof. vm_compute. reflexivity. Qed.
Definition utsDL_conc_s := ",19A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#50S,8v23S,9v22S,12v21S,13#4000S,15v24S,16+v22#1B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v22#7?????????>8Hv22#8P_v2#50#50v22#18Nav22v27B#v27#??Fv27#tLa+v22#8v28B#v28#8000000,,1,7X#388<4#57=34Y,T,1#388><T,:v22T,;+v28#4000T,<#T,17v28"%pstring.
Lemma utsDL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsDL] fx R M V utsDL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsDL] LibSegJu_utsDL.regs0 LibSegJu_utsDL.kn0 LibSegJu_utsDL.BR LibSegJu_utsDL.PSS LibSegJu_utsDL.NX0 LibSegJu_utsDL.F0 231620 LibSegJu_utsDL.seg_sound_ax fx R M V utsDL_conc_s. Qed.
Definition KS_utsD2 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsD2.regs0 LibSegJu_utsD2.regs_out0).
Lemma KS_utsD2_ok : BG.kept_ok 56 LibSegJu_utsD2.regs0 LibSegJu_utsD2.regs_out0 KS_utsD2 = true. Proof. vm_compute. reflexivity. Qed.
Definition utsD2_conc_s := ",1<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v29p#2#40A#v2;p#2#40S,2_v2#50S,8v23S,9v22S,12v21S,13#4000S,15v24S,16+v22#1S,17v2;B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v22#7?????????>8Hv22#8P_v2#50#50v22#18Nav22v27B#v27#??Fv27#tLa+v22#10v29B#1000v29#800000000000B#v2;#8000000,,1,6X#388><#37720Y,T,1#3891<T,:v21T,;+v29v2;T,<#4000"%pstring.
Lemma utsD2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsD2] fx R M V utsD2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsD2] LibSegJu_utsD2.regs0 LibSegJu_utsD2.kn0 LibSegJu_utsD2.BR LibSegJu_utsD2.PSS LibSegJu_utsD2.NX0 LibSegJu_utsD2.F0 231660 LibSegJu_utsD2.seg_sound_ax fx R M V utsD2_conc_s. Qed.
Definition KS_utsD3_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsD3.regs0 LibSegJu_utsD3.regs_out0).
Lemma KS_utsD3_0_ok : BG.kept_ok 56 LibSegJu_utsD3.regs0 LibSegJu_utsD3.regs_out0 KS_utsD3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_utsD3_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsD3.regs0 LibSegJu_utsD3.regs_out1).
Lemma KS_utsD3_1_ok : BG.kept_ok 56 LibSegJu_utsD3.regs0 LibSegJu_utsD3.regs_out1 KS_utsD3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_utsD3_2 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJu_utsD3.regs0 LibSegJu_utsD3.regs_out2).
Lemma KS_utsD3_2_ok : BG.kept_ok 56 LibSegJu_utsD3.regs0 LibSegJu_utsD3.regs_out2 KS_utsD3_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition utsD3_conc_s := ",2=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40S,2_v2#50S,8v23S,9v22S,:v35S,12v21S,13#4000S,15v24S,16+v22#1S,17v2;B#7???7?800050v2#800000000000Hv2#10I_v2#50#50La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34B#7???7?800000v21#7????????>=8Hv21#8P_v2#50#50v21#128Ja+v21#100#8I+v21#100#8B#v35#4000B#v2;#8000000B#1v24^#?#???????????????,1+v21#100#8,3,8X#3891<#57=34Y,T,1#38940T,:v22T,;+v2;v35T,<#T,14v35D#1%_v35#4000p#2#40,6X#3891<#3882<Y,1T,14v35T,15_v24v35D#1%_%+v24%*^#?#???????????????v35p#2#40p#2#40#p#2#40C%_v35#4000p#2#40#1,?X#3891<#38974Y,2T,1v2<T,2v2T,8v2=T,9v2>T,:+v23+*-1v24v35T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34C%_%+v24%*^#?#???????????????v35p#2#40p#2#40#p#2#40#1C%_v35#4000p#2#40#1"%pstring.
Lemma utsD3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_utsD3_0; KS_utsD3_1; KS_utsD3_2] fx R M V utsD3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_utsD3_0; KS_utsD3_1; KS_utsD3_2] LibSegJu_utsD3.regs0 LibSegJu_utsD3.kn0 LibSegJu_utsD3.BR LibSegJu_utsD3.PSS LibSegJu_utsD3.NX0 LibSegJu_utsD3.F0 231708 LibSegJu_utsD3.seg_sound_ax fx R M V utsD3_conc_s. Qed.
End PMUSRP.
