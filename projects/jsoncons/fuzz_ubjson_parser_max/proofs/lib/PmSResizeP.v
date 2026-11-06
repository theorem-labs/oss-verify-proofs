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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_rzS LibSegJs_rzL LibSegJs_rzTS LibSegJs_rzTL LibSegJs_apS0 LibSegJs_apL0 LibSegJs_fitS LibSegJs_fitL LibSegJs_apMS LibSegJs_apML LibSegJs_growS LibSegJs_growL LibSegJs_rec LibSegJs_pN LibSegJs_pDS LibSegJs_pDL LibSegJs_pF.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSRZP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_rzS_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rzS.regs0 LibSegJs_rzS.regs_out0).
Lemma KS_rzS_0_ok : BG.kept_ok 48 LibSegJs_rzS.regs0 LibSegJs_rzS.regs_out0 KS_rzS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rzS_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rzS.regs0 LibSegJs_rzS.regs_out1).
Lemma KS_rzS_1_ok : BG.kept_ok 48 LibSegJs_rzS.regs0 LibSegJs_rzS.regs_out1 KS_rzS_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition rzS_conc_s := ",<A#v2p#2#40A#v21p#2#40A#v25p#2#40S,2v2S,;v25B#7???7?800000r:#7?????????>8Hr:#8Ir:#18Nar:v21B#v21#2<Fv21#fB#v25#4004000,,2,5X#56<>0#56<?4Y,T,=#T,>/v21#2Dv25/v21#2,6X#56<>0#56764Y,1T,;_v25/v21#2T,=#T,>/v21#2C/v21#2v25"%pstring.
Lemma rzS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rzS_0; KS_rzS_1] fx R M V rzS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rzS_0; KS_rzS_1] LibSegJs_rzS.regs0 LibSegJs_rzS.kn0 LibSegJs_rzS.BR LibSegJs_rzS.PSS LibSegJs_rzS.NX0 LibSegJs_rzS.F0 355552 LibSegJs_rzS.seg_sound_ax fx R M V rzS_conc_s. Qed.
Definition KS_rzL_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rzL.regs0 LibSegJs_rzL.regs_out0).
Lemma KS_rzL_0_ok : BG.kept_ok 48 LibSegJs_rzL.regs0 LibSegJs_rzL.regs_out0 KS_rzL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rzL_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rzL.regs0 LibSegJs_rzL.regs_out1).
Lemma KS_rzL_1_ok : BG.kept_ok 48 LibSegJs_rzL.regs0 LibSegJs_rzL.regs_out1 KS_rzL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition rzL_conc_s := ",?A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v25p#2#40S,2v2S,;v25B#7???7?800000r:#7?????????>8Hr:#8Ir:#18Nar:v21B#v21#??Fv21#tLa+r:#8v22B#v22#8000000B#v25#4004000,,2,6X#56<>0#56764Y,T,;+*-1v22v25T,=#1T,>v22Cv22v25,5X#56<>0#56<?4Y,1T,=#1T,>v22Dv25v22"%pstring.
Lemma rzL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rzL_0; KS_rzL_1] fx R M V rzL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rzL_0; KS_rzL_1] LibSegJs_rzL.regs0 LibSegJs_rzL.kn0 LibSegJs_rzL.BR LibSegJs_rzL.PSS LibSegJs_rzL.NX0 LibSegJs_rzL.F0 355552 LibSegJs_rzL.seg_sound_ax fx R M V rzL_conc_s. Qed.
Definition KS_rzTS : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rzTS.regs0 LibSegJs_rzTS.regs_out0).
Lemma KS_rzTS_ok : BG.kept_ok 48 LibSegJs_rzTS.regs0 LibSegJs_rzTS.regs_out0 KS_rzTS = true. Proof. vm_compute. reflexivity. Qed.
Definition rzTS_conc_s := ",9A#v2p#2#40A#v25p#2#40S,2v2S,;v25S,=#B#7???7?800000r:#7?????????>8Hr:#8Ir:#18B#v25#16,1+r:##18,1,7X#56<?4#56=0<Y,T,;++r:v25#1T,<+r:#1T,=*#2v25Nb++r:v25#1#Nbr:*#2v25"%pstring.
Lemma rzTS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rzTS] fx R M V rzTS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rzTS] LibSegJs_rzTS.regs0 LibSegJs_rzTS.kn0 LibSegJs_rzTS.BR LibSegJs_rzTS.PSS LibSegJs_rzTS.NX0 LibSegJs_rzTS.F0 355572 LibSegJs_rzTS.seg_sound_ax fx R M V rzTS_conc_s. Qed.
Definition KS_rzTL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJs_rzTL.regs0 LibSegJs_rzTL.regs_out0).
Lemma KS_rzTL_ok : BG.kept_ok 48 LibSegJs_rzTL.regs0 LibSegJs_rzTL.regs_out0 KS_rzTL = true. Proof. vm_compute. reflexivity. Qed.
Definition rzTL_conc_s := ",>A#v2p#2#40A#v23p#2#40A#v25p#2#40S,2v2S,;v25S,=#1B#7???7?800000r:#7?????????>8Hr:#8Ir:#18B#v25#8000000La+r:#10v23B#1000v23#800000000000I+v23v25#1P+v23v25#1r:#18,2+r:#8#8++v23v25##1,1,6X#56<?4#56=30Y,T,;+v23v25T,<v23Nb+v23v25#Lb+r:#8v25"%pstring.
Lemma rzTL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rzTL] fx R M V rzTL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rzTL] LibSegJs_rzTL.regs0 LibSegJs_rzTL.kn0 LibSegJs_rzTL.BR LibSegJs_rzTL.PSS LibSegJs_rzTL.NX0 LibSegJs_rzTL.F0 355572 LibSegJs_rzTL.seg_sound_ax fx R M V rzTL_conc_s. Qed.
Definition KS_apS0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_apS0.regs0 LibSegJs_apS0.regs_out0).
Lemma KS_apS0_0_ok : BG.kept_ok 60 LibSegJs_apS0.regs0 LibSegJs_apS0.regs_out0 KS_apS0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_apS0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_apS0.regs0 LibSegJs_apS0.regs_out1).
Lemma KS_apS0_1_ok : BG.kept_ok 60 LibSegJs_apS0.regs0 LibSegJs_apS0.regs_out1 KS_apS0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition apS0_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v2;p#2#40S,2v2S,;v2;B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000r:#7?????????>8Hr:#8Ir:#18P_v2#50#50r:#18Nar:v21B#v21#2<Fv21#fLar:v24Fv24#fB#/%*#100000000000000v24p#2#40#200000000000000#16B#1v2;#4004000,1_v2#50#50,2,14X#56764#567<8Y,T,2_v2#50U,8,:T,9v2;T,:#W,;%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40W,12/%*#100000000000000v24p#2#40#200000000000000T,17#16Dv2;%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,14X#56764#567?0Y,1T,2_v2#50U,8,:T,9v2;T,:#W,;%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40W,12/%*#100000000000000v24p#2#40#200000000000000T,17#16C%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40v2;Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma apS0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apS0_0; KS_apS0_1] fx R M V apS0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apS0_0; KS_apS0_1] LibSegJs_apS0.regs0 LibSegJs_apS0.kn0 LibSegJs_apS0.BR LibSegJs_apS0.PSS LibSegJs_apS0.NX0 LibSegJs_apS0.F0 354148 LibSegJs_apS0.seg_sound_ax fx R M V apS0_conc_s. Qed.
Definition KS_apL0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_apL0.regs0 LibSegJs_apL0.regs_out0).
Lemma KS_apL0_0_ok : BG.kept_ok 60 LibSegJs_apL0.regs0 LibSegJs_apL0.regs_out0 KS_apL0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_apL0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_apL0.regs0 LibSegJs_apL0.regs_out1).
Lemma KS_apL0_1_ok : BG.kept_ok 60 LibSegJs_apL0.regs0 LibSegJs_apL0.regs_out1 KS_apL0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition apL0_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v2;p#2#40S,2v2S,;v2;B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000r:#7?????????>8Hr:#8Ir:#18P_v2#50#50r:#18Nar:v21B#v21#??Fv21#tLar:v24Fv24#tB#1;v24#8000001La+r:#8v22B#v22#8000000B#1v2;#4004000,1_v2#50#50,2,14X#56764#567<8Y,T,2_v2#50U,8,:T,9v2;T,:#1T,;_+*-1v22*#2/v24#2#1T,12v22T,17_*#2/v24#2#1Dv2;%+%+%*^#?#???????????????v22p#2#40%*#2/v24#2p#2#40p#2#40^#?#???????????????p#2#40Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,14X#56764#567?0Y,1T,2_v2#50U,8,:T,9v2;T,:#1T,;_+*-1v22*#2/v24#2#1T,12v22T,17_*#2/v24#2#1C%+%+%*^#?#???????????????v22p#2#40%*#2/v24#2p#2#40p#2#40^#?#???????????????p#2#40v2;Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma apL0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apL0_0; KS_apL0_1] fx R M V apL0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apL0_0; KS_apL0_1] LibSegJs_apL0.regs0 LibSegJs_apL0.kn0 LibSegJs_apL0.BR LibSegJs_apL0.PSS LibSegJs_apL0.NX0 LibSegJs_apL0.F0 354148 LibSegJs_apL0.seg_sound_ax fx R M V apL0_conc_s. Qed.
Definition KS_fitS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_fitS.regs0 LibSegJs_fitS.regs_out0).
Lemma KS_fitS_ok : BG.kept_ok 60 LibSegJs_fitS.regs0 LibSegJs_fitS.regs_out0 KS_fitS = true. Proof. vm_compute. reflexivity. Qed.
Definition fitS_conc_s := ",13A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#S,12v22S,17#16B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#16B#1v2;#16,,1,8X#567<8#:96>0Y,T,1#568>0T,:++v:v22#1U,;,<T,<v2;T,14+v:#1T,16+v22v2;"%pstring.
Lemma fitS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_fitS] fx R M V fitS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_fitS] LibSegJs_fitS.regs0 LibSegJs_fitS.kn0 LibSegJs_fitS.BR LibSegJs_fitS.PSS LibSegJs_fitS.NX0 LibSegJs_fitS.F0 354248 LibSegJs_fitS.seg_sound_ax fx R M V fitS_conc_s. Qed.
Definition KS_fitL : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_fitL.regs0 LibSegJs_fitL.regs_out0).
Lemma KS_fitL_ok : BG.kept_ok 60 LibSegJs_fitL.regs0 LibSegJs_fitL.regs_out0 KS_fitL = true. Proof. vm_compute. reflexivity. Qed.
Definition fitL_conc_s := ",15A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v23p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#1S,12v22B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#8000000B#1v2;#4004000La+v:#10v23B#1000v23#800000000000,,1,8X#567<8#:96>0Y,T,1#568>0T,:+v22v23U,;,<T,<v2;T,14v23T,16+v22v2;"%pstring.
Lemma fitL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_fitL] fx R M V fitL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_fitL] LibSegJs_fitL.regs0 LibSegJs_fitL.kn0 LibSegJs_fitL.BR LibSegJs_fitL.PSS LibSegJs_fitL.NX0 LibSegJs_fitL.F0 354248 LibSegJs_fitL.seg_sound_ax fx R M V fitL_conc_s. Qed.
Definition KS_apMS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_apMS.regs0 LibSegJs_apMS.regs_out0).
Lemma KS_apMS_ok : BG.kept_ok 60 LibSegJs_apMS.regs0 LibSegJs_apMS.regs_out0 KS_apMS = true. Proof. vm_compute. reflexivity. Qed.
Definition apMS_conc_s := ",29A#v2p#2#40A#v:p#2#40A#v21p#2#40A#v26p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40A#v36p#2#40S,2_v2#50S,8v:S,:v36S,14+v:#1S,16v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34La_v2#50v35Nav:v21B#v21#??Fv21#fB#1v26#16,1+v:##18,1,10X#568>0#56934Y,T,1v2<T,2v2T,8v2=T,9v2>T,:v:T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34T,18v35Nb++v:v26#1#Nbv:*#2v26"%pstring.
Lemma apMS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apMS] fx R M V apMS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apMS] LibSegJs_apMS.regs0 LibSegJs_apMS.kn0 LibSegJs_apMS.BR LibSegJs_apMS.PSS LibSegJs_apMS.NX0 LibSegJs_apMS.F0 354528 LibSegJs_apMS.seg_sound_ax fx R M V apMS_conc_s. Qed.
Definition KS_apML : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_apML.regs0 LibSegJs_apML.regs_out0).
Lemma KS_apML_ok : BG.kept_ok 60 LibSegJs_apML.regs0 LibSegJs_apML.regs_out0 KS_apML = true. Proof. vm_compute. reflexivity. Qed.
Definition apML_conc_s := ",2>A#v2p#2#40A#v:p#2#40A#v21p#2#40A#v23p#2#40A#v26p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40A#v36p#2#40S,2_v2#50S,8v:S,:v36S,14v23S,16v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34La_v2#50v35Nav:v21B#v21#??Fv21#tB#1v26#4004000B#1000v23#800000000000I+v23v26#1P+v23v26#1v:#18P+v23v26#1_v2#50#50,2+v:#8#8++v23v26##1,1,10X#568>0#56934Y,T,1v2<T,2v2T,8v2=T,9v2>T,:v:T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34T,18v35Nb+v23v26#Lb+v:#8v26"%pstring.
Lemma apML_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apML] fx R M V apML_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apML] LibSegJs_apML.regs0 LibSegJs_apML.kn0 LibSegJs_apML.BR LibSegJs_apML.PSS LibSegJs_apML.NX0 LibSegJs_apML.F0 354528 LibSegJs_apML.seg_sound_ax fx R M V apML_conc_s. Qed.
Definition KS_growS_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_growS.regs0 LibSegJs_growS.regs_out0).
Lemma KS_growS_0_ok : BG.kept_ok 60 LibSegJs_growS.regs0 LibSegJs_growS.regs_out0 KS_growS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_growS_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_growS.regs0 LibSegJs_growS.regs_out1).
Lemma KS_growS_1_ok : BG.kept_ok 60 LibSegJs_growS.regs0 LibSegJs_growS.regs_out1 KS_growS_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition growS_conc_s := ",14A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#S,12v22S,17#16B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#16B#1v2;#4004000B#1_+v22v2;#16#4004000,,2,9X#567?0#56868Y,T,:+v22v2;T,;#17T,=_+v22v2;#16T,13+v:#1T,15+*#8/+v22v2;#8#7T,16+v22v2;C#2<%+v22v2;p#2#40,;X#567?0#:>098Y,1T,1#56890T,:#30T,;#17T,=_+v22v2;#16T,13+v:#1T,15#30T,16+v22v2;U,18,<D%+v22v2;p#2#40#2<"%pstring.
Lemma growS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_growS_0; KS_growS_1] fx R M V growS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_growS_0; KS_growS_1] LibSegJs_growS.regs0 LibSegJs_growS.kn0 LibSegJs_growS.BR LibSegJs_growS.PSS LibSegJs_growS.NX0 LibSegJs_growS.F0 354288 LibSegJs_growS.seg_sound_ax fx R M V growS_conc_s. Qed.
Definition KS_growL_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_growL.regs0 LibSegJs_growL.regs_out0).
Lemma KS_growL_0_ok : BG.kept_ok 60 LibSegJs_growL.regs0 LibSegJs_growL.regs_out0 KS_growL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_growL_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_growL.regs0 LibSegJs_growL.regs_out1).
Lemma KS_growL_1_ok : BG.kept_ok 60 LibSegJs_growL.regs0 LibSegJs_growL.regs_out1 KS_growL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition growL_conc_s := ",19A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#1S,12v22S,17v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#8000000B#1v2;#4004000B#19v25#8000000B#1+v22+*-1v25v2;#4004000La+v:#10v23B#1000v23#800000000000,,2,9X#567?0#56868Y,T,:+v22v2;T,;#17T,=+v22+*-1v25v2;T,13v23T,15+*#8/+v22v2;#8#7T,16+v22v2;C%*#2v25p#2#40%+v22v2;p#2#40,;X#567?0#:>098Y,1T,1#56890T,:+*#8/*#2v25#8#8T,;#17T,=+v22+*-1v25v2;T,13v23T,15+*#8/*#2v25#8#8T,16+v22v2;U,18,<D%+v22v2;p#2#40%*#2v25p#2#40"%pstring.
Lemma growL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_growL_0; KS_growL_1] fx R M V growL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_growL_0; KS_growL_1] LibSegJs_growL.regs0 LibSegJs_growL.kn0 LibSegJs_growL.BR LibSegJs_growL.PSS LibSegJs_growL.NX0 LibSegJs_growL.F0 354288 LibSegJs_growL.seg_sound_ax fx R M V growL_conc_s. Qed.
Definition KS_rec : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_rec.regs0 LibSegJs_rec.regs_out0).
Lemma KS_rec_ok : BG.kept_ok 60 LibSegJs_rec.regs0 LibSegJs_rec.regs_out0 KS_rec = true. Proof. vm_compute. reflexivity. Qed.
Definition rec_conc_s := ",<A#v2p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#50S,:v27S,;#17S,15v28B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#2=v27#10000000B#2?v28#10000000,,1,6X#56868#:>098Y,T,1#56890T,:+v28#1T,15+v28#1U,18,<"%pstring.
Lemma rec_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_rec] fx R M V rec_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_rec] LibSegJs_rec.regs0 LibSegJs_rec.kn0 LibSegJs_rec.BR LibSegJs_rec.PSS LibSegJs_rec.NX0 LibSegJs_rec.F0 354408 LibSegJs_rec.seg_sound_ax fx R M V rec_conc_s. Qed.
Definition KS_pN_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_pN.regs0 LibSegJs_pN.regs_out0).
Lemma KS_pN_0_ok : BG.kept_ok 60 LibSegJs_pN.regs0 LibSegJs_pN.regs_out0 KS_pN_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_pN_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_pN.regs0 LibSegJs_pN.regs_out1).
Lemma KS_pN_1_ok : BG.kept_ok 60 LibSegJs_pN.regs0 LibSegJs_pN.regs_out1 KS_pN_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition pN_conc_s := ",>A#v2p#2#40A#v22p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#50S,:v29S,12v22S,13v2:B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#v22#8000000B#1000v29#800000000000B#1000v2:#800000000000,,2,7X#56890#:9564Y,T,1#568:8T,;v2:T,<v22T,14v29D#1%_v22#p#2#40,4X#56890#568:8Y,1T,14v29C%_v22#p#2#40#1"%pstring.
Lemma pN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_pN_0; KS_pN_1] fx R M V pN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_pN_0; KS_pN_1] LibSegJs_pN.regs0 LibSegJs_pN.kn0 LibSegJs_pN.BR LibSegJs_pN.PSS LibSegJs_pN.NX0 LibSegJs_pN.F0 354448 LibSegJs_pN.seg_sound_ax fx R M V pN_conc_s. Qed.
Definition KS_pDS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_pDS.regs0 LibSegJs_pDS.regs_out0).
Lemma KS_pDS_ok : BG.kept_ok 60 LibSegJs_pDS.regs0 LibSegJs_pDS.regs_out0 KS_pDS = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition pDS_conc_s := ",1<A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2;p#2#40A#v38p#2#40S,2_v2#50S,8v:S,9v2;S,:v29S,12v22S,14v29S,15v28S,16v26S,17#16S,18v38B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#16B#1000v29#800000000000B#30v28#8000000,1+v:##18,1,9X#568:8#:96>0Y,T,1#568>0T,:+v22v29T,;v38T,<v2;Lb+v:#10v29Lb+v:#8v22Lbv:+*#2/v28#2#1"%pstring.
Lemma pDS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_pDS] fx R M V pDS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_pDS] LibSegJs_pDS.regs0 LibSegJs_pDS.kn0 LibSegJs_pDS.BR LibSegJs_pDS.PSS LibSegJs_pDS.NX0 LibSegJs_pDS.F0 354472 LibSegJs_pDS.seg_sound_ax fx R M V pDS_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_pDL : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_pDL.regs0 LibSegJs_pDL.regs_out0).
Lemma KS_pDL_ok : BG.kept_ok 60 LibSegJs_pDL.regs0 LibSegJs_pDL.regs_out0 KS_pDL = true. Proof. vm_compute. reflexivity. Qed.
Definition pDL_conc_s := ",;A#v2p#2#40A#v25p#2#40A#v2:p#2#40S,2_v2#50S,13v2:S,17v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#19v25#8000000B#1000v2:#800000000000,,1,5X#568:8#54400Y,T,1#568;<T,:v2:T,;+v25#1"%pstring.
Lemma pDL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_pDL] fx R M V pDL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_pDL] LibSegJs_pDL.regs0 LibSegJs_pDL.kn0 LibSegJs_pDL.BR LibSegJs_pDL.PSS LibSegJs_pDL.NX0 LibSegJs_pDL.F0 354472 LibSegJs_pDL.seg_sound_ax fx R M V pDL_conc_s. Qed.
Definition KS_pF : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJs_pF.regs0 LibSegJs_pF.regs_out0).
Lemma KS_pF_ok : BG.kept_ok 60 LibSegJs_pF.regs0 LibSegJs_pF.regs_out0 KS_pF = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition pF_conc_s := ",1<A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2;p#2#40A#v37p#2#40A#v38p#2#40S,2_v2#50S,8v:S,9v2;S,:v37S,12v22S,14v29S,15v28S,16v26S,18v38B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#8000000B#1000v29#800000000000B#30v28#8000000,1+v:##18,1,9X#568;<#:96>0Y,T,1#568>0T,:+v22v29T,;v38T,<v2;Lb+v:#10v29Lb+v:#8v22Lbv:+*#2/v28#2#1"%pstring.
Lemma pF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_pF] fx R M V pF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_pF] LibSegJs_pF.regs0 LibSegJs_pF.kn0 LibSegJs_pF.BR LibSegJs_pF.PSS LibSegJs_pF.NX0 LibSegJs_pF.F0 354492 LibSegJs_pF.seg_sound_ax fx R M V pF_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End PMSRZP.
