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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ja0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_arzS LibSegJa_arzL LibSegJa_arzTS LibSegJa_arzTL LibSegJa_aapS0 LibSegJa_aapL0 LibSegJa_afitS LibSegJa_afitL LibSegJa_aapMS LibSegJa_aapML LibSegJa_agrowS LibSegJa_agrowL LibSegJa_arec LibSegJa_apN LibSegJa_apDS LibSegJa_apDL LibSegJa_apF.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMARZP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_arzS_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_arzS.regs0 LibSegJa_arzS.regs_out0).
Lemma KS_arzS_0_ok : BG.kept_ok 48 LibSegJa_arzS.regs0 LibSegJa_arzS.regs_out0 KS_arzS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arzS_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_arzS.regs0 LibSegJa_arzS.regs_out1).
Lemma KS_arzS_1_ok : BG.kept_ok 48 LibSegJa_arzS.regs0 LibSegJa_arzS.regs_out1 KS_arzS_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition arzS_conc_s := ",<A#v2p#2#40A#v21p#2#40A#v25p#2#40S,2v2S,;v25B#691000r:#7?????????>8Hr:#8Ir:#18Nar:v21B#v21#2<Fv21#fB#v25#4004000,,2,5X#=1338#=134<Y,T,=#T,>/v21#2Dv25/v21#2,6X#=1338#=0=;<Y,1T,;_v25/v21#2T,=#T,>/v21#2C/v21#2v25"%pstring.
Lemma arzS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arzS_0; KS_arzS_1] fx R M V arzS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arzS_0; KS_arzS_1] LibSegJa_arzS.regs0 LibSegJa_arzS.kn0 LibSegJa_arzS.BR LibSegJa_arzS.PSS LibSegJa_arzS.NX0 LibSegJa_arzS.F0 856888 LibSegJa_arzS.seg_sound_ax fx R M V arzS_conc_s. Qed.
Definition KS_arzL_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_arzL.regs0 LibSegJa_arzL.regs_out0).
Lemma KS_arzL_0_ok : BG.kept_ok 48 LibSegJa_arzL.regs0 LibSegJa_arzL.regs_out0 KS_arzL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arzL_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_arzL.regs0 LibSegJa_arzL.regs_out1).
Lemma KS_arzL_1_ok : BG.kept_ok 48 LibSegJa_arzL.regs0 LibSegJa_arzL.regs_out1 KS_arzL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition arzL_conc_s := ",?A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v25p#2#40S,2v2S,;v25B#691000r:#7?????????>8Hr:#8Ir:#18Nar:v21B#v21#??Fv21#tLa+r:#8v22B#v22#8000000B#v25#4004000,,2,6X#=1338#=0=;<Y,T,;+*-1v22v25T,=#1T,>v22Cv22v25,5X#=1338#=134<Y,1T,=#1T,>v22Dv25v22"%pstring.
Lemma arzL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arzL_0; KS_arzL_1] fx R M V arzL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arzL_0; KS_arzL_1] LibSegJa_arzL.regs0 LibSegJa_arzL.kn0 LibSegJa_arzL.BR LibSegJa_arzL.PSS LibSegJa_arzL.NX0 LibSegJa_arzL.F0 856888 LibSegJa_arzL.seg_sound_ax fx R M V arzL_conc_s. Qed.
Definition KS_arzTS : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_arzTS.regs0 LibSegJa_arzTS.regs_out0).
Lemma KS_arzTS_ok : BG.kept_ok 48 LibSegJa_arzTS.regs0 LibSegJa_arzTS.regs_out0 KS_arzTS = true. Proof. vm_compute. reflexivity. Qed.
Definition arzTS_conc_s := ",9A#v2p#2#40A#v25p#2#40S,2v2S,;v25S,=#B#691000r:#7?????????>8Hr:#8Ir:#18B#v25#16,1+r:##18,1,7X#=134<#=1364Y,T,;++r:v25#1T,<+r:#1T,=*#2v25Nb++r:v25#1#Nbr:*#2v25"%pstring.
Lemma arzTS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arzTS] fx R M V arzTS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arzTS] LibSegJa_arzTS.regs0 LibSegJa_arzTS.kn0 LibSegJa_arzTS.BR LibSegJa_arzTS.PSS LibSegJa_arzTS.NX0 LibSegJa_arzTS.F0 856908 LibSegJa_arzTS.seg_sound_ax fx R M V arzTS_conc_s. Qed.
Definition KS_arzTL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_arzTL.regs0 LibSegJa_arzTL.regs_out0).
Lemma KS_arzTL_ok : BG.kept_ok 48 LibSegJa_arzTL.regs0 LibSegJa_arzTL.regs_out0 KS_arzTL = true. Proof. vm_compute. reflexivity. Qed.
Definition arzTL_conc_s := ",>A#v2p#2#40A#v23p#2#40A#v25p#2#40S,2v2S,;v25S,=#1B#691000r:#7?????????>8Hr:#8Ir:#18B#v25#8000000La+r:#10v23B#1000v23#800000000000I+v23v25#1P+v23v25#1r:#18,2+r:#8#8++v23v25##1,1,6X#=134<#=1388Y,T,;+v23v25T,<v23Nb+v23v25#Lb+r:#8v25"%pstring.
Lemma arzTL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arzTL] fx R M V arzTL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arzTL] LibSegJa_arzTL.regs0 LibSegJa_arzTL.kn0 LibSegJa_arzTL.BR LibSegJa_arzTL.PSS LibSegJa_arzTL.NX0 LibSegJa_arzTL.F0 856908 LibSegJa_arzTL.seg_sound_ax fx R M V arzTL_conc_s. Qed.
Definition KS_aapS0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aapS0.regs0 LibSegJa_aapS0.regs_out0).
Lemma KS_aapS0_0_ok : BG.kept_ok 60 LibSegJa_aapS0.regs0 LibSegJa_aapS0.regs_out0 KS_aapS0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_aapS0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aapS0.regs0 LibSegJa_aapS0.regs_out1).
Lemma KS_aapS0_1_ok : BG.kept_ok 60 LibSegJa_aapS0.regs0 LibSegJa_aapS0.regs_out1 KS_aapS0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition aapS0_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v2;p#2#40S,2v2S,;v2;B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#691000r:#7?????????>8Hr:#8Ir:#18P_v2#50#50r:#18Nar:v21B#v21#2<Fv21#fLar:v24Fv24#fB#/%*#100000000000000v24p#2#40#200000000000000#16B#1v2;#4004000,1_v2#50#50,2,14X#=0=;<#=0>20Y,T,2_v2#50U,8,:T,9v2;T,:#W,;%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40W,12/%*#100000000000000v24p#2#40#200000000000000T,17#16Dv2;%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,14X#=0=;<#=0>48Y,1T,2_v2#50U,8,:T,9v2;T,:#W,;%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40W,12/%*#100000000000000v24p#2#40#200000000000000T,17#16C%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40v2;Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aapS0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aapS0_0; KS_aapS0_1] fx R M V aapS0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aapS0_0; KS_aapS0_1] LibSegJa_aapS0.regs0 LibSegJa_aapS0.kn0 LibSegJa_aapS0.BR LibSegJa_aapS0.PSS LibSegJa_aapS0.NX0 LibSegJa_aapS0.F0 855484 LibSegJa_aapS0.seg_sound_ax fx R M V aapS0_conc_s. Qed.
Definition KS_aapL0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aapL0.regs0 LibSegJa_aapL0.regs_out0).
Lemma KS_aapL0_0_ok : BG.kept_ok 60 LibSegJa_aapL0.regs0 LibSegJa_aapL0.regs_out0 KS_aapL0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_aapL0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aapL0.regs0 LibSegJa_aapL0.regs_out1).
Lemma KS_aapL0_1_ok : BG.kept_ok 60 LibSegJa_aapL0.regs0 LibSegJa_aapL0.regs_out1 KS_aapL0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition aapL0_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v2;p#2#40S,2v2S,;v2;B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#691000r:#7?????????>8Hr:#8Ir:#18P_v2#50#50r:#18Nar:v21B#v21#??Fv21#tLar:v24Fv24#tB#1;v24#8000001La+r:#8v22B#v22#8000000B#1v2;#4004000,1_v2#50#50,2,14X#=0=;<#=0>20Y,T,2_v2#50U,8,:T,9v2;T,:#1T,;_+*-1v22*#2/v24#2#1T,12v22T,17_*#2/v24#2#1Dv2;%+%+%*^#?#???????????????v22p#2#40%*#2/v24#2p#2#40p#2#40^#?#???????????????p#2#40Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,14X#=0=;<#=0>48Y,1T,2_v2#50U,8,:T,9v2;T,:#1T,;_+*-1v22*#2/v24#2#1T,12v22T,17_*#2/v24#2#1C%+%+%*^#?#???????????????v22p#2#40%*#2/v24#2p#2#40p#2#40^#?#???????????????p#2#40v2;Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aapL0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aapL0_0; KS_aapL0_1] fx R M V aapL0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aapL0_0; KS_aapL0_1] LibSegJa_aapL0.regs0 LibSegJa_aapL0.kn0 LibSegJa_aapL0.BR LibSegJa_aapL0.PSS LibSegJa_aapL0.NX0 LibSegJa_aapL0.F0 855484 LibSegJa_aapL0.seg_sound_ax fx R M V aapL0_conc_s. Qed.
Definition KS_afitS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_afitS.regs0 LibSegJa_afitS.regs_out0).
Lemma KS_afitS_ok : BG.kept_ok 60 LibSegJa_afitS.regs0 LibSegJa_afitS.regs_out0 KS_afitS = true. Proof. vm_compute. reflexivity. Qed.
Definition afitS_conc_s := ",13A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#S,12v22S,17#16B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#691000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#16B#1v2;#16,,1,8X#=0>20#77330Y,T,1#=0?38T,:++v:v22#1U,;,<T,<v2;T,14+v:#1T,16+v22v2;"%pstring.
Lemma afitS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_afitS] fx R M V afitS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_afitS] LibSegJa_afitS.regs0 LibSegJa_afitS.kn0 LibSegJa_afitS.BR LibSegJa_afitS.PSS LibSegJa_afitS.NX0 LibSegJa_afitS.F0 855584 LibSegJa_afitS.seg_sound_ax fx R M V afitS_conc_s. Qed.
Definition KS_afitL : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_afitL.regs0 LibSegJa_afitL.regs_out0).
Lemma KS_afitL_ok : BG.kept_ok 60 LibSegJa_afitL.regs0 LibSegJa_afitL.regs_out0 KS_afitL = true. Proof. vm_compute. reflexivity. Qed.
Definition afitL_conc_s := ",15A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v23p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#1S,12v22B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#691000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#8000000B#1v2;#4004000La+v:#10v23B#1000v23#800000000000,,1,8X#=0>20#77330Y,T,1#=0?38T,:+v22v23U,;,<T,<v2;T,14v23T,16+v22v2;"%pstring.
Lemma afitL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_afitL] fx R M V afitL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_afitL] LibSegJa_afitL.regs0 LibSegJa_afitL.kn0 LibSegJa_afitL.BR LibSegJa_afitL.PSS LibSegJa_afitL.NX0 LibSegJa_afitL.F0 855584 LibSegJa_afitL.seg_sound_ax fx R M V afitL_conc_s. Qed.
Definition KS_aapMS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aapMS.regs0 LibSegJa_aapMS.regs_out0).
Lemma KS_aapMS_ok : BG.kept_ok 60 LibSegJa_aapMS.regs0 LibSegJa_aapMS.regs_out0 KS_aapMS = true. Proof. vm_compute. reflexivity. Qed.
Definition aapMS_conc_s := ",29A#v2p#2#40A#v:p#2#40A#v21p#2#40A#v26p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40A#v36p#2#40S,2_v2#50S,8v:S,:v36S,14+v:#1S,16v26B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#691000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34La_v2#50v35Nav:v21B#v21#??Fv21#fB#1v26#16,1+v:##18,1,10X#=0?38#=0?8<Y,T,1v2<T,2v2T,8v2=T,9v2>T,:v:T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34T,18v35Nb++v:v26#1#Nbv:*#2v26"%pstring.
Lemma aapMS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aapMS] fx R M V aapMS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aapMS] LibSegJa_aapMS.regs0 LibSegJa_aapMS.kn0 LibSegJa_aapMS.BR LibSegJa_aapMS.PSS LibSegJa_aapMS.NX0 LibSegJa_aapMS.F0 855864 LibSegJa_aapMS.seg_sound_ax fx R M V aapMS_conc_s. Qed.
Definition KS_aapML : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aapML.regs0 LibSegJa_aapML.regs_out0).
Lemma KS_aapML_ok : BG.kept_ok 60 LibSegJa_aapML.regs0 LibSegJa_aapML.regs_out0 KS_aapML = true. Proof. vm_compute. reflexivity. Qed.
Definition aapML_conc_s := ",2>A#v2p#2#40A#v:p#2#40A#v21p#2#40A#v23p#2#40A#v26p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40A#v36p#2#40S,2_v2#50S,8v:S,:v36S,14v23S,16v26B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#691000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34La_v2#50v35Nav:v21B#v21#??Fv21#tB#1v26#4004000B#1000v23#800000000000I+v23v26#1P+v23v26#1v:#18P+v23v26#1_v2#50#50,2+v:#8#8++v23v26##1,1,10X#=0?38#=0?8<Y,T,1v2<T,2v2T,8v2=T,9v2>T,:v:T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34T,18v35Nb+v23v26#Lb+v:#8v26"%pstring.
Lemma aapML_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aapML] fx R M V aapML_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aapML] LibSegJa_aapML.regs0 LibSegJa_aapML.kn0 LibSegJa_aapML.BR LibSegJa_aapML.PSS LibSegJa_aapML.NX0 LibSegJa_aapML.F0 855864 LibSegJa_aapML.seg_sound_ax fx R M V aapML_conc_s. Qed.
Definition KS_agrowS_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_agrowS.regs0 LibSegJa_agrowS.regs_out0).
Lemma KS_agrowS_0_ok : BG.kept_ok 60 LibSegJa_agrowS.regs0 LibSegJa_agrowS.regs_out0 KS_agrowS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_agrowS_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_agrowS.regs0 LibSegJa_agrowS.regs_out1).
Lemma KS_agrowS_1_ok : BG.kept_ok 60 LibSegJa_agrowS.regs0 LibSegJa_agrowS.regs_out1 KS_agrowS_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition agrowS_conc_s := ",14A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#S,12v22S,17#16B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#691000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#16B#1v2;#4004000B#1_+v22v2;#16#4004000,,2,9X#=0>48#=0><0Y,T,:+v22v2;T,;#17T,=_+v22v2;#16T,13+v:#1T,15+*#8/+v22v2;#8#7T,16+v22v2;C#2<%+v22v2;p#2#40,;X#=0>48#12;3>4Y,1T,1#=0>>8T,:#30T,;#17T,=_+v22v2;#16T,13+v:#1T,15#30T,16+v22v2;U,18,<D%+v22v2;p#2#40#2<"%pstring.
Lemma agrowS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_agrowS_0; KS_agrowS_1] fx R M V agrowS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_agrowS_0; KS_agrowS_1] LibSegJa_agrowS.regs0 LibSegJa_agrowS.kn0 LibSegJa_agrowS.BR LibSegJa_agrowS.PSS LibSegJa_agrowS.NX0 LibSegJa_agrowS.F0 855624 LibSegJa_agrowS.seg_sound_ax fx R M V agrowS_conc_s. Qed.
Definition KS_agrowL_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_agrowL.regs0 LibSegJa_agrowL.regs_out0).
Lemma KS_agrowL_0_ok : BG.kept_ok 60 LibSegJa_agrowL.regs0 LibSegJa_agrowL.regs_out0 KS_agrowL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_agrowL_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_agrowL.regs0 LibSegJa_agrowL.regs_out1).
Lemma KS_agrowL_1_ok : BG.kept_ok 60 LibSegJa_agrowL.regs0 LibSegJa_agrowL.regs_out1 KS_agrowL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition agrowL_conc_s := ",19A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#1S,12v22S,17v25B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#691000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#8000000B#1v2;#4004000B#19v25#8000000B#1+v22+*-1v25v2;#4004000La+v:#10v23B#1000v23#800000000000,,2,9X#=0>48#=0><0Y,T,:+v22v2;T,;#17T,=+v22+*-1v25v2;T,13v23T,15+*#8/+v22v2;#8#7T,16+v22v2;C%*#2v25p#2#40%+v22v2;p#2#40,;X#=0>48#12;3>4Y,1T,1#=0>>8T,:+*#8/*#2v25#8#8T,;#17T,=+v22+*-1v25v2;T,13v23T,15+*#8/*#2v25#8#8T,16+v22v2;U,18,<D%+v22v2;p#2#40%*#2v25p#2#40"%pstring.
Lemma agrowL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_agrowL_0; KS_agrowL_1] fx R M V agrowL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_agrowL_0; KS_agrowL_1] LibSegJa_agrowL.regs0 LibSegJa_agrowL.kn0 LibSegJa_agrowL.BR LibSegJa_agrowL.PSS LibSegJa_agrowL.NX0 LibSegJa_agrowL.F0 855624 LibSegJa_agrowL.seg_sound_ax fx R M V agrowL_conc_s. Qed.
Definition KS_arec : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_arec.regs0 LibSegJa_arec.regs_out0).
Lemma KS_arec_ok : BG.kept_ok 60 LibSegJa_arec.regs0 LibSegJa_arec.regs_out0 KS_arec = true. Proof. vm_compute. reflexivity. Qed.
Definition arec_conc_s := ",<A#v2p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#50S,:v27S,;#17S,15v28B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#2=v27#10000000B#2?v28#10000000,,1,6X#=0><0#12;3>4Y,T,1#=0>>8T,:+v28#1T,15+v28#1U,18,<"%pstring.
Lemma arec_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arec] fx R M V arec_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arec] LibSegJa_arec.regs0 LibSegJa_arec.kn0 LibSegJa_arec.BR LibSegJa_arec.PSS LibSegJa_arec.NX0 LibSegJa_arec.F0 855744 LibSegJa_arec.seg_sound_ax fx R M V arec_conc_s. Qed.
Definition KS_apN_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_apN.regs0 LibSegJa_apN.regs_out0).
Lemma KS_apN_0_ok : BG.kept_ok 60 LibSegJa_apN.regs0 LibSegJa_apN.regs_out0 KS_apN_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_apN_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_apN.regs0 LibSegJa_apN.regs_out1).
Lemma KS_apN_1_ok : BG.kept_ok 60 LibSegJa_apN.regs0 LibSegJa_apN.regs_out1 KS_apN_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition apN_conc_s := ",>A#v2p#2#40A#v22p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#50S,:v29S,12v22S,13v2:B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#v22#8000000B#1000v29#800000000000B#1000v2:#800000000000,,2,7X#=0>>8#77334Y,T,1#=0?00T,;v2:T,<v22T,14v29D#1%_v22#p#2#40,4X#=0>>8#=0?00Y,1T,14v29C%_v22#p#2#40#1"%pstring.
Lemma apN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apN_0; KS_apN_1] fx R M V apN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apN_0; KS_apN_1] LibSegJa_apN.regs0 LibSegJa_apN.kn0 LibSegJa_apN.BR LibSegJa_apN.PSS LibSegJa_apN.NX0 LibSegJa_apN.F0 855784 LibSegJa_apN.seg_sound_ax fx R M V apN_conc_s. Qed.
Definition KS_apDS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_apDS.regs0 LibSegJa_apDS.regs_out0).
Lemma KS_apDS_ok : BG.kept_ok 60 LibSegJa_apDS.regs0 LibSegJa_apDS.regs_out0 KS_apDS = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition apDS_conc_s := ",1<A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2;p#2#40A#v38p#2#40S,2_v2#50S,8v:S,9v2;S,:v29S,12v22S,14v29S,15v28S,16v26S,17#16S,18v38B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#691000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#16B#1000v29#800000000000B#30v28#8000000,1+v:##18,1,9X#=0?00#77330Y,T,1#=0?38T,:+v22v29T,;v38T,<v2;Lb+v:#10v29Lb+v:#8v22Lbv:+*#2/v28#2#1"%pstring.
Lemma apDS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apDS] fx R M V apDS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apDS] LibSegJa_apDS.regs0 LibSegJa_apDS.kn0 LibSegJa_apDS.BR LibSegJa_apDS.PSS LibSegJa_apDS.NX0 LibSegJa_apDS.F0 855808 LibSegJa_apDS.seg_sound_ax fx R M V apDS_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_apDL : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_apDL.regs0 LibSegJa_apDL.regs_out0).
Lemma KS_apDL_ok : BG.kept_ok 60 LibSegJa_apDL.regs0 LibSegJa_apDL.regs_out0 KS_apDL = true. Proof. vm_compute. reflexivity. Qed.
Definition apDL_conc_s := ",;A#v2p#2#40A#v25p#2#40A#v2:p#2#40S,2_v2#50S,13v2:S,17v25B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#19v25#8000000B#1000v2:#800000000000,,1,5X#=0?00#<>:58Y,T,1#=0?14T,:v2:T,;+v25#1"%pstring.
Lemma apDL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apDL] fx R M V apDL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apDL] LibSegJa_apDL.regs0 LibSegJa_apDL.kn0 LibSegJa_apDL.BR LibSegJa_apDL.PSS LibSegJa_apDL.NX0 LibSegJa_apDL.F0 855808 LibSegJa_apDL.seg_sound_ax fx R M V apDL_conc_s. Qed.
Definition KS_apF : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_apF.regs0 LibSegJa_apF.regs_out0).
Lemma KS_apF_ok : BG.kept_ok 60 LibSegJa_apF.regs0 LibSegJa_apF.regs_out0 KS_apF = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition apF_conc_s := ",1<A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2;p#2#40A#v37p#2#40A#v38p#2#40S,2_v2#50S,8v:S,9v2;S,:v37S,12v22S,14v29S,15v28S,16v26S,18v38B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#691000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#8000000B#1000v29#800000000000B#30v28#8000000,1+v:##18,1,9X#=0?14#77330Y,T,1#=0?38T,:+v22v29T,;v38T,<v2;Lb+v:#10v29Lb+v:#8v22Lbv:+*#2/v28#2#1"%pstring.
Lemma apF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apF] fx R M V apF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apF] LibSegJa_apF.regs0 LibSegJa_apF.kn0 LibSegJa_apF.BR LibSegJa_apF.PSS LibSegJa_apF.NX0 LibSegJa_apF.F0 855828 LibSegJa_apF.seg_sound_ax fx R M V apF_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End PMARZP.
