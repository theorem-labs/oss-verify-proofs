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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Jb0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_arzS LibSegJb_arzL LibSegJb_arzTS LibSegJb_arzTL LibSegJb_aapS0 LibSegJb_aapL0 LibSegJb_afitS LibSegJb_afitL LibSegJb_aapMS LibSegJb_aapML LibSegJb_agrowS LibSegJb_agrowL LibSegJb_arec LibSegJb_apN LibSegJb_apDS LibSegJb_apDL LibSegJb_apF.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBRZP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_arzS_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_arzS.regs0 LibSegJb_arzS.regs_out0).
Lemma KS_arzS_0_ok : BG.kept_ok 48 LibSegJb_arzS.regs0 LibSegJb_arzS.regs_out0 KS_arzS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arzS_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_arzS.regs0 LibSegJb_arzS.regs_out1).
Lemma KS_arzS_1_ok : BG.kept_ok 48 LibSegJb_arzS.regs0 LibSegJb_arzS.regs_out1 KS_arzS_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition arzS_conc_s := ",<A#v2p#2#40A#v21p#2#40A#v25p#2#40S,2v2S,;v25B#693000r:#7?????????>8Hr:#8Ir:#18Nar:v21B#v21#2<Fv21#fB#v25#4004000,,2,5X#=3170#=3184Y,T,=#T,>/v21#2Dv25/v21#2,6X#=3170#=2;?4Y,1T,;_v25/v21#2T,=#T,>/v21#2C/v21#2v25"%pstring.
Lemma arzS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arzS_0; KS_arzS_1] fx R M V arzS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arzS_0; KS_arzS_1] LibSegJb_arzS.regs0 LibSegJb_arzS.kn0 LibSegJb_arzS.BR LibSegJb_arzS.PSS LibSegJb_arzS.NX0 LibSegJb_arzS.F0 864624 LibSegJb_arzS.seg_sound_ax fx R M V arzS_conc_s. Qed.
Definition KS_arzL_0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_arzL.regs0 LibSegJb_arzL.regs_out0).
Lemma KS_arzL_0_ok : BG.kept_ok 48 LibSegJb_arzL.regs0 LibSegJb_arzL.regs_out0 KS_arzL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arzL_1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_arzL.regs0 LibSegJb_arzL.regs_out1).
Lemma KS_arzL_1_ok : BG.kept_ok 48 LibSegJb_arzL.regs0 LibSegJb_arzL.regs_out1 KS_arzL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition arzL_conc_s := ",?A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v25p#2#40S,2v2S,;v25B#693000r:#7?????????>8Hr:#8Ir:#18Nar:v21B#v21#??Fv21#tLa+r:#8v22B#v22#8000000B#v25#4004000,,2,6X#=3170#=2;?4Y,T,;+*-1v22v25T,=#1T,>v22Cv22v25,5X#=3170#=3184Y,1T,=#1T,>v22Dv25v22"%pstring.
Lemma arzL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arzL_0; KS_arzL_1] fx R M V arzL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arzL_0; KS_arzL_1] LibSegJb_arzL.regs0 LibSegJb_arzL.kn0 LibSegJb_arzL.BR LibSegJb_arzL.PSS LibSegJb_arzL.NX0 LibSegJb_arzL.F0 864624 LibSegJb_arzL.seg_sound_ax fx R M V arzL_conc_s. Qed.
Definition KS_arzTS : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_arzTS.regs0 LibSegJb_arzTS.regs_out0).
Lemma KS_arzTS_ok : BG.kept_ok 48 LibSegJb_arzTS.regs0 LibSegJb_arzTS.regs_out0 KS_arzTS = true. Proof. vm_compute. reflexivity. Qed.
Definition arzTS_conc_s := ",9A#v2p#2#40A#v25p#2#40S,2v2S,;v25S,=#B#693000r:#7?????????>8Hr:#8Ir:#18B#v25#16,1+r:##18,1,7X#=3184#=319<Y,T,;++r:v25#1T,<+r:#1T,=*#2v25Nb++r:v25#1#Nbr:*#2v25"%pstring.
Lemma arzTS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arzTS] fx R M V arzTS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arzTS] LibSegJb_arzTS.regs0 LibSegJb_arzTS.kn0 LibSegJb_arzTS.BR LibSegJb_arzTS.PSS LibSegJb_arzTS.NX0 LibSegJb_arzTS.F0 864644 LibSegJb_arzTS.seg_sound_ax fx R M V arzTS_conc_s. Qed.
Definition KS_arzTL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_arzTL.regs0 LibSegJb_arzTL.regs_out0).
Lemma KS_arzTL_ok : BG.kept_ok 48 LibSegJb_arzTL.regs0 LibSegJb_arzTL.regs_out0 KS_arzTL = true. Proof. vm_compute. reflexivity. Qed.
Definition arzTL_conc_s := ",>A#v2p#2#40A#v23p#2#40A#v25p#2#40S,2v2S,;v25S,=#1B#693000r:#7?????????>8Hr:#8Ir:#18B#v25#8000000La+r:#10v23B#1000v23#800000000000I+v23v25#1P+v23v25#1r:#18,2+r:#8#8++v23v25##1,1,6X#=3184#=31<0Y,T,;+v23v25T,<v23Nb+v23v25#Lb+r:#8v25"%pstring.
Lemma arzTL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arzTL] fx R M V arzTL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arzTL] LibSegJb_arzTL.regs0 LibSegJb_arzTL.kn0 LibSegJb_arzTL.BR LibSegJb_arzTL.PSS LibSegJb_arzTL.NX0 LibSegJb_arzTL.F0 864644 LibSegJb_arzTL.seg_sound_ax fx R M V arzTL_conc_s. Qed.
Definition KS_aapS0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_aapS0.regs0 LibSegJb_aapS0.regs_out0).
Lemma KS_aapS0_0_ok : BG.kept_ok 60 LibSegJb_aapS0.regs0 LibSegJb_aapS0.regs_out0 KS_aapS0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_aapS0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_aapS0.regs0 LibSegJb_aapS0.regs_out1).
Lemma KS_aapS0_1_ok : BG.kept_ok 60 LibSegJb_aapS0.regs0 LibSegJb_aapS0.regs_out1 KS_aapS0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition aapS0_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v2;p#2#40S,2v2S,;v2;B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000r:#7?????????>8Hr:#8Ir:#18P_v2#50#50r:#18Nar:v21B#v21#2<Fv21#fLar:v24Fv24#fB#/%*#100000000000000v24p#2#40#200000000000000#16B#1v2;#4004000,1_v2#50#50,2,14X#=2;?4#=2<58Y,T,2_v2#50U,8,:T,9v2;T,:#W,;%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40W,12/%*#100000000000000v24p#2#40#200000000000000T,17#16Dv2;%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,14X#=2;?4#=2<80Y,1T,2_v2#50U,8,:T,9v2;T,:#W,;%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40W,12/%*#100000000000000v24p#2#40#200000000000000T,17#16C%+%*^#?#???????????????/%*#100000000000000v24p#2#40#200000000000000p#2#40#16p#2#40v2;Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aapS0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aapS0_0; KS_aapS0_1] fx R M V aapS0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aapS0_0; KS_aapS0_1] LibSegJb_aapS0.regs0 LibSegJb_aapS0.kn0 LibSegJb_aapS0.BR LibSegJb_aapS0.PSS LibSegJb_aapS0.NX0 LibSegJb_aapS0.F0 863220 LibSegJb_aapS0.seg_sound_ax fx R M V aapS0_conc_s. Qed.
Definition KS_aapL0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_aapL0.regs0 LibSegJb_aapL0.regs_out0).
Lemma KS_aapL0_0_ok : BG.kept_ok 60 LibSegJb_aapL0.regs0 LibSegJb_aapL0.regs_out0 KS_aapL0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_aapL0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_aapL0.regs0 LibSegJb_aapL0.regs_out1).
Lemma KS_aapL0_1_ok : BG.kept_ok 60 LibSegJb_aapL0.regs0 LibSegJb_aapL0.regs_out1 KS_aapL0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition aapL0_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v2;p#2#40S,2v2S,;v2;B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000r:#7?????????>8Hr:#8Ir:#18P_v2#50#50r:#18Nar:v21B#v21#??Fv21#tLar:v24Fv24#tB#1;v24#8000001La+r:#8v22B#v22#8000000B#1v2;#4004000,1_v2#50#50,2,14X#=2;?4#=2<58Y,T,2_v2#50U,8,:T,9v2;T,:#1T,;_+*-1v22*#2/v24#2#1T,12v22T,17_*#2/v24#2#1Dv2;%+%+%*^#?#???????????????v22p#2#40%*#2/v24#2p#2#40p#2#40^#?#???????????????p#2#40Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,14X#=2;?4#=2<80Y,1T,2_v2#50U,8,:T,9v2;T,:#1T,;_+*-1v22*#2/v24#2#1T,12v22T,17_*#2/v24#2#1C%+%+%*^#?#???????????????v22p#2#40%*#2/v24#2p#2#40p#2#40^#?#???????????????p#2#40v2;Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aapL0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aapL0_0; KS_aapL0_1] fx R M V aapL0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aapL0_0; KS_aapL0_1] LibSegJb_aapL0.regs0 LibSegJb_aapL0.kn0 LibSegJb_aapL0.BR LibSegJb_aapL0.PSS LibSegJb_aapL0.NX0 LibSegJb_aapL0.F0 863220 LibSegJb_aapL0.seg_sound_ax fx R M V aapL0_conc_s. Qed.
Definition KS_afitS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_afitS.regs0 LibSegJb_afitS.regs_out0).
Lemma KS_afitS_ok : BG.kept_ok 60 LibSegJb_afitS.regs0 LibSegJb_afitS.regs_out0 KS_afitS = true. Proof. vm_compute. reflexivity. Qed.
Definition afitS_conc_s := ",13A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#S,12v22S,17#16B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#16B#1v2;#16,,1,8X#=2<58#77600Y,T,1#=2=70T,:++v:v22#1U,;,<T,<v2;T,14+v:#1T,16+v22v2;"%pstring.
Lemma afitS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_afitS] fx R M V afitS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_afitS] LibSegJb_afitS.regs0 LibSegJb_afitS.kn0 LibSegJb_afitS.BR LibSegJb_afitS.PSS LibSegJb_afitS.NX0 LibSegJb_afitS.F0 863320 LibSegJb_afitS.seg_sound_ax fx R M V afitS_conc_s. Qed.
Definition KS_afitL : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_afitL.regs0 LibSegJb_afitL.regs_out0).
Lemma KS_afitL_ok : BG.kept_ok 60 LibSegJb_afitL.regs0 LibSegJb_afitL.regs_out0 KS_afitL = true. Proof. vm_compute. reflexivity. Qed.
Definition afitL_conc_s := ",15A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v23p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#1S,12v22B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#8000000B#1v2;#4004000La+v:#10v23B#1000v23#800000000000,,1,8X#=2<58#77600Y,T,1#=2=70T,:+v22v23U,;,<T,<v2;T,14v23T,16+v22v2;"%pstring.
Lemma afitL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_afitL] fx R M V afitL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_afitL] LibSegJb_afitL.regs0 LibSegJb_afitL.kn0 LibSegJb_afitL.BR LibSegJb_afitL.PSS LibSegJb_afitL.NX0 LibSegJb_afitL.F0 863320 LibSegJb_afitL.seg_sound_ax fx R M V afitL_conc_s. Qed.
Definition KS_aapMS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_aapMS.regs0 LibSegJb_aapMS.regs_out0).
Lemma KS_aapMS_ok : BG.kept_ok 60 LibSegJb_aapMS.regs0 LibSegJb_aapMS.regs_out0 KS_aapMS = true. Proof. vm_compute. reflexivity. Qed.
Definition aapMS_conc_s := ",29A#v2p#2#40A#v:p#2#40A#v21p#2#40A#v26p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40A#v36p#2#40S,2_v2#50S,8v:S,:v36S,14+v:#1S,16v26B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34La_v2#50v35Nav:v21B#v21#??Fv21#fB#1v26#16,1+v:##18,1,10X#=2=70#=2=<4Y,T,1v2<T,2v2T,8v2=T,9v2>T,:v:T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34T,18v35Nb++v:v26#1#Nbv:*#2v26"%pstring.
Lemma aapMS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aapMS] fx R M V aapMS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aapMS] LibSegJb_aapMS.regs0 LibSegJb_aapMS.kn0 LibSegJb_aapMS.BR LibSegJb_aapMS.PSS LibSegJb_aapMS.NX0 LibSegJb_aapMS.F0 863600 LibSegJb_aapMS.seg_sound_ax fx R M V aapMS_conc_s. Qed.
Definition KS_aapML : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_aapML.regs0 LibSegJb_aapML.regs_out0).
Lemma KS_aapML_ok : BG.kept_ok 60 LibSegJb_aapML.regs0 LibSegJb_aapML.regs_out0 KS_aapML = true. Proof. vm_compute. reflexivity. Qed.
Definition aapML_conc_s := ",2>A#v2p#2#40A#v:p#2#40A#v21p#2#40A#v23p#2#40A#v26p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40A#v36p#2#40S,2_v2#50S,8v:S,:v36S,14v23S,16v26B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34La_v2#50v35Nav:v21B#v21#??Fv21#tB#1v26#4004000B#1000v23#800000000000I+v23v26#1P+v23v26#1v:#18P+v23v26#1_v2#50#50,2+v:#8#8++v23v26##1,1,10X#=2=70#=2=<4Y,T,1v2<T,2v2T,8v2=T,9v2>T,:v:T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34T,18v35Nb+v23v26#Lb+v:#8v26"%pstring.
Lemma aapML_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aapML] fx R M V aapML_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aapML] LibSegJb_aapML.regs0 LibSegJb_aapML.kn0 LibSegJb_aapML.BR LibSegJb_aapML.PSS LibSegJb_aapML.NX0 LibSegJb_aapML.F0 863600 LibSegJb_aapML.seg_sound_ax fx R M V aapML_conc_s. Qed.
Definition KS_agrowS_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_agrowS.regs0 LibSegJb_agrowS.regs_out0).
Lemma KS_agrowS_0_ok : BG.kept_ok 60 LibSegJb_agrowS.regs0 LibSegJb_agrowS.regs_out0 KS_agrowS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_agrowS_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_agrowS.regs0 LibSegJb_agrowS.regs_out1).
Lemma KS_agrowS_1_ok : BG.kept_ok 60 LibSegJb_agrowS.regs0 LibSegJb_agrowS.regs_out1 KS_agrowS_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition agrowS_conc_s := ",14A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#S,12v22S,17#16B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#16B#1v2;#4004000B#1_+v22v2;#16#4004000,,2,9X#=2<80#=2<?8Y,T,:+v22v2;T,;#17T,=_+v22v2;#16T,13+v:#1T,15+*#8/+v22v2;#8#7T,16+v22v2;C#2<%+v22v2;p#2#40,;X#=2<80#12=21<Y,1T,1#=2=20T,:#30T,;#17T,=_+v22v2;#16T,13+v:#1T,15#30T,16+v22v2;U,18,<D%+v22v2;p#2#40#2<"%pstring.
Lemma agrowS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_agrowS_0; KS_agrowS_1] fx R M V agrowS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_agrowS_0; KS_agrowS_1] LibSegJb_agrowS.regs0 LibSegJb_agrowS.kn0 LibSegJb_agrowS.BR LibSegJb_agrowS.PSS LibSegJb_agrowS.NX0 LibSegJb_agrowS.F0 863360 LibSegJb_agrowS.seg_sound_ax fx R M V agrowS_conc_s. Qed.
Definition KS_agrowL_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_agrowL.regs0 LibSegJb_agrowL.regs_out0).
Lemma KS_agrowL_0_ok : BG.kept_ok 60 LibSegJb_agrowL.regs0 LibSegJb_agrowL.regs_out0 KS_agrowL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_agrowL_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_agrowL.regs0 LibSegJb_agrowL.regs_out1).
Lemma KS_agrowL_1_ok : BG.kept_ok 60 LibSegJb_agrowL.regs0 LibSegJb_agrowL.regs_out1 KS_agrowL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition agrowL_conc_s := ",19A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v2;p#2#40S,2_v2#50S,8v:S,9v2;S,:#1S,12v22S,17v25B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#8000000B#1v2;#4004000B#19v25#8000000B#1+v22+*-1v25v2;#4004000La+v:#10v23B#1000v23#800000000000,,2,9X#=2<80#=2<?8Y,T,:+v22v2;T,;#17T,=+v22+*-1v25v2;T,13v23T,15+*#8/+v22v2;#8#7T,16+v22v2;C%*#2v25p#2#40%+v22v2;p#2#40,;X#=2<80#12=21<Y,1T,1#=2=20T,:+*#8/*#2v25#8#8T,;#17T,=+v22+*-1v25v2;T,13v23T,15+*#8/*#2v25#8#8T,16+v22v2;U,18,<D%+v22v2;p#2#40%*#2v25p#2#40"%pstring.
Lemma agrowL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_agrowL_0; KS_agrowL_1] fx R M V agrowL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_agrowL_0; KS_agrowL_1] LibSegJb_agrowL.regs0 LibSegJb_agrowL.kn0 LibSegJb_agrowL.BR LibSegJb_agrowL.PSS LibSegJb_agrowL.NX0 LibSegJb_agrowL.F0 863360 LibSegJb_agrowL.seg_sound_ax fx R M V agrowL_conc_s. Qed.
Definition KS_arec : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arec.regs0 LibSegJb_arec.regs_out0).
Lemma KS_arec_ok : BG.kept_ok 60 LibSegJb_arec.regs0 LibSegJb_arec.regs_out0 KS_arec = true. Proof. vm_compute. reflexivity. Qed.
Definition arec_conc_s := ",<A#v2p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#50S,:v27S,;#17S,15v28B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#2=v27#10000000B#2?v28#10000000,,1,6X#=2<?8#12=21<Y,T,1#=2=20T,:+v28#1T,15+v28#1U,18,<"%pstring.
Lemma arec_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arec] fx R M V arec_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arec] LibSegJb_arec.regs0 LibSegJb_arec.kn0 LibSegJb_arec.BR LibSegJb_arec.PSS LibSegJb_arec.NX0 LibSegJb_arec.F0 863480 LibSegJb_arec.seg_sound_ax fx R M V arec_conc_s. Qed.
Definition KS_apN_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_apN.regs0 LibSegJb_apN.regs_out0).
Lemma KS_apN_0_ok : BG.kept_ok 60 LibSegJb_apN.regs0 LibSegJb_apN.regs_out0 KS_apN_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_apN_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_apN.regs0 LibSegJb_apN.regs_out1).
Lemma KS_apN_1_ok : BG.kept_ok 60 LibSegJb_apN.regs0 LibSegJb_apN.regs_out1 KS_apN_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition apN_conc_s := ",>A#v2p#2#40A#v22p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#50S,:v29S,12v22S,13v2:B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#v22#8000000B#1000v29#800000000000B#1000v2:#800000000000,,2,7X#=2=20#77604Y,T,1#=2=38T,;v2:T,<v22T,14v29D#1%_v22#p#2#40,4X#=2=20#=2=38Y,1T,14v29C%_v22#p#2#40#1"%pstring.
Lemma apN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apN_0; KS_apN_1] fx R M V apN_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apN_0; KS_apN_1] LibSegJb_apN.regs0 LibSegJb_apN.kn0 LibSegJb_apN.BR LibSegJb_apN.PSS LibSegJb_apN.NX0 LibSegJb_apN.F0 863520 LibSegJb_apN.seg_sound_ax fx R M V apN_conc_s. Qed.
Definition KS_apDS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_apDS.regs0 LibSegJb_apDS.regs_out0).
Lemma KS_apDS_ok : BG.kept_ok 60 LibSegJb_apDS.regs0 LibSegJb_apDS.regs_out0 KS_apDS = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition apDS_conc_s := ",1<A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2;p#2#40A#v38p#2#40S,2_v2#50S,8v:S,9v2;S,:v29S,12v22S,14v29S,15v28S,16v26S,17#16S,18v38B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#16B#1000v29#800000000000B#30v28#8000000,1+v:##18,1,9X#=2=38#77600Y,T,1#=2=70T,:+v22v29T,;v38T,<v2;Lb+v:#10v29Lb+v:#8v22Lbv:+*#2/v28#2#1"%pstring.
Lemma apDS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apDS] fx R M V apDS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apDS] LibSegJb_apDS.regs0 LibSegJb_apDS.kn0 LibSegJb_apDS.BR LibSegJb_apDS.PSS LibSegJb_apDS.NX0 LibSegJb_apDS.F0 863544 LibSegJb_apDS.seg_sound_ax fx R M V apDS_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_apDL : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_apDL.regs0 LibSegJb_apDL.regs_out0).
Lemma KS_apDL_ok : BG.kept_ok 60 LibSegJb_apDL.regs0 LibSegJb_apDL.regs_out0 KS_apDL = true. Proof. vm_compute. reflexivity. Qed.
Definition apDL_conc_s := ",;A#v2p#2#40A#v25p#2#40A#v2:p#2#40S,2_v2#50S,13v2:S,17v25B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#19v25#8000000B#1000v2:#800000000000,,1,5X#=2=38#=0890Y,T,1#=2=4<T,:v2:T,;+v25#1"%pstring.
Lemma apDL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apDL] fx R M V apDL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apDL] LibSegJb_apDL.regs0 LibSegJb_apDL.kn0 LibSegJb_apDL.BR LibSegJb_apDL.PSS LibSegJb_apDL.NX0 LibSegJb_apDL.F0 863544 LibSegJb_apDL.seg_sound_ax fx R M V apDL_conc_s. Qed.
Definition KS_apF : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_apF.regs0 LibSegJb_apF.regs_out0).
Lemma KS_apF_ok : BG.kept_ok 60 LibSegJb_apF.regs0 LibSegJb_apF.regs_out0 KS_apF = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition apF_conc_s := ",1<A#v2p#2#40A#v:p#2#40A#v22p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v2;p#2#40A#v37p#2#40A#v38p#2#40S,2_v2#50S,8v:S,9v2;S,:v37S,12v22S,14v29S,15v28S,16v26S,18v38B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v:#7?????????>8Hv:#8Iv:#18P_v2#50#50v:#18B#v22#8000000B#1000v29#800000000000B#30v28#8000000,1+v:##18,1,9X#=2=4<#77600Y,T,1#=2=70T,:+v22v29T,;v38T,<v2;Lb+v:#10v29Lb+v:#8v22Lbv:+*#2/v28#2#1"%pstring.
Lemma apF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apF] fx R M V apF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apF] LibSegJb_apF.regs0 LibSegJb_apF.kn0 LibSegJb_apF.BR LibSegJb_apF.PSS LibSegJb_apF.NX0 LibSegJb_apF.F0 863564 LibSegJb_apF.seg_sound_ax fx R M V apF_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End PMBRZP.
