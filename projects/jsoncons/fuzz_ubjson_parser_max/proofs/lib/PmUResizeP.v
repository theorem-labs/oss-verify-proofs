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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_urzS LibSegJu_urzL LibSegJu_urzTS LibSegJu_urzTL LibSegJu_uapS0 LibSegJu_uapL0 LibSegJu_ufitS LibSegJu_ufitL LibSegJu_uapMS LibSegJu_uapML LibSegJu_ugrowS LibSegJu_ugrowL LibSegJu_urec LibSegJu_upN LibSegJu_upDS LibSegJu_upDL LibSegJu_upF.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMURZP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_urzS_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urzS.regs0 LibSegJu_urzS.regs_out0).
Lemma KS_urzS_0_ok : BG.kept_ok 48 LibSegJu_urzS.regs0 LibSegJu_urzS.regs_out0 KS_urzS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_urzS_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urzS.regs0 LibSegJu_urzS.regs_out1).
Lemma KS_urzS_1_ok : BG.kept_ok 48 LibSegJu_urzS.regs0 LibSegJu_urzS.regs_out1 KS_urzS_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition urzS_conc_s := ",<A#v2p#2#40A#v21p#2#40A#v25p#2#40S,2v2S,;v25B#7???7?800000r:#7?????????>8Hr:#8Ir:#18Nar:v21B#v21#2<Fv21#fB#v25#4004000,,2,5X#57=34#57=48Y,T,=#T,>/v21#2Dv25/v21#2,6X#57=34#577;8Y,1T,;_v25/v21#2T,=#T,>/v21#2C/v21#2v25"%pstring.
Lemma urzS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urzS_0; KS_urzS_1] fx R M V urzS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urzS_0; KS_urzS_1] LibSegJu_urzS.regs0 LibSegJu_urzS.kn0 LibSegJu_urzS.BR LibSegJu_urzS.PSS LibSegJu_urzS.NX0 LibSegJu_urzS.F0 359732 LibSegJu_urzS.seg_sound_ax fx R M V urzS_conc_s. Qed.
Definition KS_urzL_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urzL.regs0 LibSegJu_urzL.regs_out0).
Lemma KS_urzL_0_ok : BG.kept_ok 48 LibSegJu_urzL.regs0 LibSegJu_urzL.regs_out0 KS_urzL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_urzL_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urzL.regs0 LibSegJu_urzL.regs_out1).
Lemma KS_urzL_1_ok : BG.kept_ok 48 LibSegJu_urzL.regs0 LibSegJu_urzL.regs_out1 KS_urzL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition urzL_conc_s := ",?A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v25p#2#40S,2v2S,;v25B#7???7?800000r:#7?????????>8Hr:#8Ir:#18Nar:v21B#v21#??Fv21#tLa+r:#8v22B#v22#8000000B#v25#4004000,,2,6X#57=34#577;8Y,T,;+*-1v22v25T,=#1T,>v22Cv22v25,5X#57=34#57=48Y,1T,=#1T,>v22Dv25v22"%pstring.
Lemma urzL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urzL_0; KS_urzL_1] fx R M V urzL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urzL_0; KS_urzL_1] LibSegJu_urzL.regs0 LibSegJu_urzL.kn0 LibSegJu_urzL.BR LibSegJu_urzL.PSS LibSegJu_urzL.NX0 LibSegJu_urzL.F0 359732 LibSegJu_urzL.seg_sound_ax fx R M V urzL_conc_s. Qed.
Definition KS_urzTS : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urzTS.regs0 LibSegJu_urzTS.regs_out0).
Lemma KS_urzTS_ok : BG.kept_ok 48 LibSegJu_urzTS.regs0 LibSegJu_urzTS.regs_out0 KS_urzTS = true. Proof. vm_compute. reflexivity. Qed.
Definition urzTS_conc_s := ",9A#v2p#2#40A#v25p#2#40S,2v2S,;v25S,=#B#7???7?800000r:#7?????????>8Hr:#8Ir:#18B#v25#16,1+r:##18,1,7X#57=48#57=60Y,T,;++r:v25#1T,<+r:#1T,=*#2v25Nb++r:v25#1#Nbr:*#2v25"%pstring.
Lemma urzTS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urzTS] fx R M V urzTS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urzTS] LibSegJu_urzTS.regs0 LibSegJu_urzTS.kn0 LibSegJu_urzTS.BR LibSegJu_urzTS.PSS LibSegJu_urzTS.NX0 LibSegJu_urzTS.F0 359752 LibSegJu_urzTS.seg_sound_ax fx R M V urzTS_conc_s. Qed.
Definition KS_urzTL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJu_urzTL.regs0 LibSegJu_urzTL.regs_out0).
Lemma KS_urzTL_ok : BG.kept_ok 48 LibSegJu_urzTL.regs0 LibSegJu_urzTL.regs_out0 KS_urzTL = true. Proof. vm_compute. reflexivity. Qed.
Definition urzTL_conc_s := ",>A#v2p#2#40A#v23p#2#40A#v25p#2#40S,2v2S,;v25S,=#1B#7???7?800000r:#7?????????>8Hr:#8Ir:#18B#v25#8000000La+r:#10v23B#1000v23#800000000000I+v23v25#1P+v23v25#1r:#18,2+r:#8#8++v23v25##1,1,6X#57=48#57=84Y,T,;+v23v25T,<v23Nb+v23v25#Lb+r:#8v25"%pstring.
Lemma urzTL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urzTL] fx R M V urzTL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urzTL] LibSegJu_urzTL.regs0 LibSegJu_urzTL.kn0 LibSegJu_urzTL.BR LibSegJu_urzTL.PSS LibSegJu_urzTL.NX0 LibSegJu_urzTL.F0 359752 LibSegJu_urzTL.seg_sound_ax fx R M V urzTL_conc_s. Qed.
Definition KS_uapS0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uapS0.regs0 LibSegJu_uapS0.regs_out0).
Lemma KS_uapS0_0_ok : BG.kept_ok 60 LibSegJu_uapS0.regs0 LibSegJu_uapS0.regs_out0 KS_uapS0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uapS0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uapS0.regs0 LibSegJu_uapS0.regs_out1).
Lemma KS_uapS0_1_ok : BG.kept_ok 60 LibSegJu_uapS0.regs0 LibSegJu_uapS0.regs_out1 KS_uapS0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uapS0_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v2;p#2#40S,2v2S,;v2;B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000r:#7?????????>8Hr:#8Ir:#18P_v2#50#50r:#18Nar:v21B#v21#2<Fv21#fLar:v24Fv24#fB#/%*#100000000000000v24p#2#40#200000000000000#16B#1v2;#4004000,1_v2#50#50,2,14X#577;8#5781<Y,T,2_v2#50U,8,:T,9v2;T,:#W,;%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40W,12/%*#100000000000000v24p#2#40#200000000000000T,17#16Dv2;%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,14X#577;8#57844Y,1T,2_v2#50U,8,:T,9v2;T,:#W,;%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40W,12/%*#100000000000000v24p#2#40#200000000000000T,17#16C%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40v2;Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uapS0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uapS0_0; KS_uapS0_1] fx R M V uapS0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uapS0_0; KS_uapS0_1] LibSegJu_uapS0.regs0 LibSegJu_uapS0.kn0 LibSegJu_uapS0.BR LibSegJu_uapS0.PSS LibSegJu_uapS0.NX0 LibSegJu_uapS0.F0 358328 LibSegJu_uapS0.seg_sound_ax fx R M V uapS0_conc_s. Qed.
Definition KS_uapL0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uapL0.regs0 LibSegJu_uapL0.regs_out0).
Lemma KS_uapL0_0_ok : BG.kept_ok 60 LibSegJu_uapL0.regs0 LibSegJu_uapL0.regs_out0 KS_uapL0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_uapL0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uapL0.regs0 LibSegJu_uapL0.regs_out1).
Lemma KS_uapL0_1_ok : BG.kept_ok 60 LibSegJu_uapL0.regs0 LibSegJu_uapL0.regs_out1 KS_uapL0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uapL0_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v2;p#2#40S,2v2S,;v2;B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000r:#7?????????>8Hr:#8Ir:#18P_v2#50#50r:#18Nar:v21B#v21#??Fv21#tLar:v24Fv24#tB#1;v24#8000001La+r:#8v22B#v22#8000000B#1v2;#4004000,1_v2#50#50,2,14X#577;8#5781<Y,T,2_v2#50U,8,:T,9v2;T,:#1T,;_+*-1v22*#2/v24#2#1T,12v22T,17_*#2/v24#2#1Dv2;%+%+%*^#?#???????????????v22p#2#40%*#2/v24#2p#2#40p#2#40^#?#???????????????p#2#40Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,14X#577;8#57844Y,1T,2_v2#50U,8,:T,9v2;T,:#1T,;_+*-1v22*#2/v24#2#1T,12v22T,17_*#2/v24#2#1C%+%+%*^#?#???????????????v22p#2#40%*#2/v24#2p#2#40p#2#40^#?#???????????????p#2#40v2;Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uapL0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uapL0_0; KS_uapL0_1] fx R M V uapL0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uapL0_0; KS_uapL0_1] LibSegJu_uapL0.regs0 LibSegJu_uapL0.kn0 LibSegJu_uapL0.BR LibSegJu_uapL0.PSS LibSegJu_uapL0.NX0 LibSegJu_uapL0.F0 358328 LibSegJu_uapL0.seg_sound_ax fx R M V uapL0_conc_s. Qed.
Definition KS_ufitS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_ufitS.regs0 LibSegJu_ufitS.regs_out0).
Lemma KS_ufitS_ok : BG.kept_ok 60 LibSegJu_ufitS.regs0 LibSegJu_ufitS.regs_out0 KS_ufitS = true. Proof. vm_compute. reflexivity. Qed.
Definition ufitS_conc_s := ",13A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#S,12v22S,17#16B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#16B#1v2;#16,,1,8X#5781<#::734Y,T,1#57934T,:++v:v22#1U,;,<T,<v2;T,14+v:#1T,16+v22v2;"%pstring.
Lemma ufitS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ufitS] fx R M V ufitS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ufitS] LibSegJu_ufitS.regs0 LibSegJu_ufitS.kn0 LibSegJu_ufitS.BR LibSegJu_ufitS.PSS LibSegJu_ufitS.NX0 LibSegJu_ufitS.F0 358428 LibSegJu_ufitS.seg_sound_ax fx R M V ufitS_conc_s. Qed.
Definition KS_ufitL : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_ufitL.regs0 LibSegJu_ufitL.regs_out0).
Lemma KS_ufitL_ok : BG.kept_ok 60 LibSegJu_ufitL.regs0 LibSegJu_ufitL.regs_out0 KS_ufitL = true. Proof. vm_compute. reflexivity. Qed.
Definition ufitL_conc_s := ",15A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v23p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#1S,12v22B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#8000000B#1v2;#4004000La+v:#10v23B#1000v23#800000000000,,1,8X#5781<#::734Y,T,1#57934T,:+v22v23U,;,<T,<v2;T,14v23T,16+v22v2;"%pstring.
Lemma ufitL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ufitL] fx R M V ufitL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ufitL] LibSegJu_ufitL.regs0 LibSegJu_ufitL.kn0 LibSegJu_ufitL.BR LibSegJu_ufitL.PSS LibSegJu_ufitL.NX0 LibSegJu_ufitL.F0 358428 LibSegJu_ufitL.seg_sound_ax fx R M V ufitL_conc_s. Qed.
Definition KS_uapMS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uapMS.regs0 LibSegJu_uapMS.regs_out0).
Lemma KS_uapMS_ok : BG.kept_ok 60 LibSegJu_uapMS.regs0 LibSegJu_uapMS.regs_out0 KS_uapMS = true. Proof. vm_compute. reflexivity. Qed.
Definition uapMS_conc_s := ",29A#v2p#2#40A#v:p#2#40A#v21p#2#40A#v26p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40A#v36p#2#40S,2_v2#50S,8v:S,:v36S,14+v:#1S,16v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34La_v2#50v35Nav:v21B#v21#??Fv21#fB#1v26#16,1+v:##18,1,10X#57934#57988Y,T,1v2<T,2v2T,8v2=T,9v2>T,:v:T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34T,18v35Nb++v:v26#1#Nbv:*#2v26"%pstring.
Lemma uapMS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uapMS] fx R M V uapMS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uapMS] LibSegJu_uapMS.regs0 LibSegJu_uapMS.kn0 LibSegJu_uapMS.BR LibSegJu_uapMS.PSS LibSegJu_uapMS.NX0 LibSegJu_uapMS.F0 358708 LibSegJu_uapMS.seg_sound_ax fx R M V uapMS_conc_s. Qed.
Definition KS_uapML : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_uapML.regs0 LibSegJu_uapML.regs_out0).
Lemma KS_uapML_ok : BG.kept_ok 60 LibSegJu_uapML.regs0 LibSegJu_uapML.regs_out0 KS_uapML = true. Proof. vm_compute. reflexivity. Qed.
Definition uapML_conc_s := ",2>A#v2p#2#40A#v:p#2#40A#v21p#2#40A#v23p#2#40A#v26p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40A#v36p#2#40S,2_v2#50S,8v:S,:v36S,14v23S,16v26B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34La_v2#50v35Nav:v21B#v21#??Fv21#tB#1v26#4004000B#1000v23#800000000000I+v23v26#1P+v23v26#1v:#18P+v23v26#1_v2#50#50,2+v:#8#8++v23v26##1,1,10X#57934#57988Y,T,1v2<T,2v2T,8v2=T,9v2>T,:v:T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34T,18v35Nb+v23v26#Lb+v:#8v26"%pstring.
Lemma uapML_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uapML] fx R M V uapML_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uapML] LibSegJu_uapML.regs0 LibSegJu_uapML.kn0 LibSegJu_uapML.BR LibSegJu_uapML.PSS LibSegJu_uapML.NX0 LibSegJu_uapML.F0 358708 LibSegJu_uapML.seg_sound_ax fx R M V uapML_conc_s. Qed.
Definition KS_ugrowS_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_ugrowS.regs0 LibSegJu_ugrowS.regs_out0).
Lemma KS_ugrowS_0_ok : BG.kept_ok 60 LibSegJu_ugrowS.regs0 LibSegJu_ugrowS.regs_out0 KS_ugrowS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ugrowS_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_ugrowS.regs0 LibSegJu_ugrowS.regs_out1).
Lemma KS_ugrowS_1_ok : BG.kept_ok 60 LibSegJu_ugrowS.regs0 LibSegJu_ugrowS.regs_out1 KS_ugrowS_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ugrowS_conc_s := ",14A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#S,12v22S,17#16B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#16B#1v2;#4004000B#1_+v22v2;#16#4004000,,2,9X#57844#578;<Y,T,:+v22v2;T,;#17T,=_+v22v2;#16T,13+v:#1T,15+*#8/+v22v2;#8#7T,16+v22v2;C#2<%+v22v2;p#2#40,;X#57844#:?0><Y,1T,1#578>4T,:#30T,;#17T,=_+v22v2;#16T,13+v:#1T,15#30T,16+v22v2;U,18,<D%+v22v2;p#2#40#2<"%pstring.
Lemma ugrowS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ugrowS_0; KS_ugrowS_1] fx R M V ugrowS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ugrowS_0; KS_ugrowS_1] LibSegJu_ugrowS.regs0 LibSegJu_ugrowS.kn0 LibSegJu_ugrowS.BR LibSegJu_ugrowS.PSS LibSegJu_ugrowS.NX0 LibSegJu_ugrowS.F0 358468 LibSegJu_ugrowS.seg_sound_ax fx R M V ugrowS_conc_s. Qed.
Definition KS_ugrowL_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_ugrowL.regs0 LibSegJu_ugrowL.regs_out0).
Lemma KS_ugrowL_0_ok : BG.kept_ok 60 LibSegJu_ugrowL.regs0 LibSegJu_ugrowL.regs_out0 KS_ugrowL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_ugrowL_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_ugrowL.regs0 LibSegJu_ugrowL.regs_out1).
Lemma KS_ugrowL_1_ok : BG.kept_ok 60 LibSegJu_ugrowL.regs0 LibSegJu_ugrowL.regs_out1 KS_ugrowL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition ugrowL_conc_s := ",19A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#1S,12v22S,17v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#8000000B#1v2;#4004000B#19v25#8000000B#1+v22+*-1v25v2;#4004000La+v:#10v23B#1000v23#800000000000,,2,9X#57844#578;<Y,T,:+v22v2;T,;#17T,=+v22+*-1v25v2;T,13v23T,15+*#8/+v22v2;#8#7T,16+v22v2;C%*#2v25p#2#40%+v22v2;p#2#40,;X#57844#:?0><Y,1T,1#578>4T,:+*#8/*#2v25#8#8T,;#17T,=+v22+*-1v25v2;T,13v23T,15+*#8/*#2v25#8#8T,16+v22v2;U,18,<D%+v22v2;p#2#40%*#2v25p#2#40"%pstring.
Lemma ugrowL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_ugrowL_0; KS_ugrowL_1] fx R M V ugrowL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_ugrowL_0; KS_ugrowL_1] LibSegJu_ugrowL.regs0 LibSegJu_ugrowL.kn0 LibSegJu_ugrowL.BR LibSegJu_ugrowL.PSS LibSegJu_ugrowL.NX0 LibSegJu_ugrowL.F0 358468 LibSegJu_ugrowL.seg_sound_ax fx R M V ugrowL_conc_s. Qed.
Definition KS_urec : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_urec.regs0 LibSegJu_urec.regs_out0).
Lemma KS_urec_ok : BG.kept_ok 60 LibSegJu_urec.regs0 LibSegJu_urec.regs_out0 KS_urec = true. Proof. vm_compute. reflexivity. Qed.
Definition urec_conc_s := ",<A#v2p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#50S,:v27S,;#17S,15v28B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#2=v27#10000000B#2?v28#10000000,,1,6X#578;<#:?0><Y,T,1#578>4T,:+v28#1T,15+v28#1U,18,<"%pstring.
Lemma urec_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_urec] fx R M V urec_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_urec] LibSegJu_urec.regs0 LibSegJu_urec.kn0 LibSegJu_urec.BR LibSegJu_urec.PSS LibSegJu_urec.NX0 LibSegJu_urec.F0 358588 LibSegJu_urec.seg_sound_ax fx R M V urec_conc_s. Qed.
Definition KS_upN_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_upN.regs0 LibSegJu_upN.regs_out0).
Lemma KS_upN_0_ok : BG.kept_ok 60 LibSegJu_upN.regs0 LibSegJu_upN.regs_out0 KS_upN_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_upN_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_upN.regs0 LibSegJu_upN.regs_out1).
Lemma KS_upN_1_ok : BG.kept_ok 60 LibSegJu_upN.regs0 LibSegJu_upN.regs_out1 KS_upN_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition upN_conc_s := ",>A#v2p#2#40A#v22p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#50S,:v29S,12v22S,13v2:B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#v22#8000000B#1000v29#800000000000B#1000v2:#800000000000,,2,7X#578>4#::5;8Y,T,1#578?<T,;v2:T,<v22T,14v29D#1%_v22#p#2#40,4X#578>4#578?<Y,1T,14v29C%_v22#p#2#40#1"%pstring.
Lemma upN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_upN_0; KS_upN_1] fx R M V upN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_upN_0; KS_upN_1] LibSegJu_upN.regs0 LibSegJu_upN.kn0 LibSegJu_upN.BR LibSegJu_upN.PSS LibSegJu_upN.NX0 LibSegJu_upN.F0 358628 LibSegJu_upN.seg_sound_ax fx R M V upN_conc_s. Qed.
Definition KS_upDS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_upDS.regs0 LibSegJu_upDS.regs_out0).
Lemma KS_upDS_ok : BG.kept_ok 60 LibSegJu_upDS.regs0 LibSegJu_upDS.regs_out0 KS_upDS = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition upDS_conc_s := ",1<A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2;p#2#40A#v38p#2#40S,2_v2#50S,8v:S,9v2;S,:v29S,12v22S,14v29S,15v28S,16v26S,17#16S,18v38B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#16B#1000v29#800000000000B#30v28#8000000,1+v:##18,1,9X#578?<#::734Y,T,1#57934T,:+v22v29T,;v38T,<v2;Lb+v:#10v29Lb+v:#8v22Lbv:+*#2/v28#2#1"%pstring.
Lemma upDS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_upDS] fx R M V upDS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_upDS] LibSegJu_upDS.regs0 LibSegJu_upDS.kn0 LibSegJu_upDS.BR LibSegJu_upDS.PSS LibSegJu_upDS.NX0 LibSegJu_upDS.F0 358652 LibSegJu_upDS.seg_sound_ax fx R M V upDS_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_upDL : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_upDL.regs0 LibSegJu_upDL.regs_out0).
Lemma KS_upDL_ok : BG.kept_ok 60 LibSegJu_upDL.regs0 LibSegJu_upDL.regs_out0 KS_upDL = true. Proof. vm_compute. reflexivity. Qed.
Definition upDL_conc_s := ",;A#v2p#2#40A#v25p#2#40A#v2:p#2#40S,2_v2#50S,13v2:S,17v25B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#19v25#8000000B#1000v2:#800000000000,,1,5X#578?<#55454Y,T,1#57910T,:v2:T,;+v25#1"%pstring.
Lemma upDL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_upDL] fx R M V upDL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_upDL] LibSegJu_upDL.regs0 LibSegJu_upDL.kn0 LibSegJu_upDL.BR LibSegJu_upDL.PSS LibSegJu_upDL.NX0 LibSegJu_upDL.F0 358652 LibSegJu_upDL.seg_sound_ax fx R M V upDL_conc_s. Qed.
Definition KS_upF : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJu_upF.regs0 LibSegJu_upF.regs_out0).
Lemma KS_upF_ok : BG.kept_ok 60 LibSegJu_upF.regs0 LibSegJu_upF.regs_out0 KS_upF = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition upF_conc_s := ",1<A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2;p#2#40A#v37p#2#40A#v38p#2#40S,2_v2#50S,8v:S,9v2;S,:v37S,12v22S,14v29S,15v28S,16v26S,18v38B#7???7?800050v2#800000000000Hv2#10I_v2#50#50B#7???7?800000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#8000000B#1000v29#800000000000B#30v28#8000000,1+v:##18,1,9X#57910#::734Y,T,1#57934T,:+v22v29T,;v38T,<v2;Lb+v:#10v29Lb+v:#8v22Lbv:+*#2/v28#2#1"%pstring.
Lemma upF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_upF] fx R M V upF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_upF] LibSegJu_upF.regs0 LibSegJu_upF.kn0 LibSegJu_upF.BR LibSegJu_upF.PSS LibSegJu_upF.NX0 LibSegJu_upF.F0 358672 LibSegJu_upF.seg_sound_ax fx R M V upF_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End PMURZP.
