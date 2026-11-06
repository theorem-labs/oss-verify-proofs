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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bstE0 LibSegJb_bstE1 LibSegJb_bstE2 LibSegJb_bstE3 LibSegJb_bstJ LibSegJb_bstK.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBSLTP1.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_bstE0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstE0.regs0 LibSegJb_bstE0.regs_out0).
Lemma KS_bstE0_ok : BG.kept_ok 60 LibSegJb_bstE0.regs0 LibSegJb_bstE0.regs_out0 KS_bstE0 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bstE0_conc_s := ",1:A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21#La+v21#8#La+v21#10#,1_v2#<0#<0,1,21X#;3780#12=21<Y,T,1#:<900T,2_v2#;0T,8_v2#50T,9#1T,:#20T,;#1T,<#13<:38T,=v21T,>#T,12_v2#68T,13#T,14+/_v2#50#8#7???8000T,15#7???8000T,16#7???8000Lb_v2#48v21Lb_v2#50#Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;3848Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bstE0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstE0] fx R M V bstE0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstE0] LibSegJb_bstE0.regs0 LibSegJb_bstE0.kn0 LibSegJb_bstE0.BR LibSegJb_bstE0.PSS LibSegJb_bstE0.NX0 LibSegJb_bstE0.F0 735104 LibSegJb_bstE0.seg_sound_ax fx R M V bstE0_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bstE1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstE1.regs0 LibSegJb_bstE1.regs_out0).
Lemma KS_bstE1_ok : BG.kept_ok 60 LibSegJb_bstE1.regs0 LibSegJb_bstE1.regs_out0 KS_bstE1 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bstE1_conc_s := ",5>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v34p#2#40A#v35p#2#40S,2_v2#;0S,8_v2#50S,9#1S,:v28S,12_v2#68S,13#S,14+/_v2#50#8#7???8000S,15#7???8000S,16#7???8000B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21#La+v21#8#La+v21#10#B#693000v22#7??????????<Hv22#4P#7???7000#100000001000v22#4Ka+/v22#8#7???8000#1Mav22v26P_v2#1000#1000v22#4B#693000v23#7??????????8Hv23#8P#7???7000#100000001000v23#8Ka+/v23#8#7???8000#1Lav23v27P_v2#1000#1000v23#8Pv21#18v22#4Pv21#18v23#8B#v26#7???????B#v27^#?#???????????????B#693000v34#7???????????P#7???7000#100000001000v34#1Nav34v35P_v2#1000#1000v34#1Hv34#8Na+/v34#8#7???8000#1Pv21#18v34#1B#v35#??B#1000v28#7?????????>0Hv28#10P#7???7000#100000001000v28#20Ka+/v28#8#7???8000#4Iv28#20P_v2#1000#1000v28#20Pv21#18v28#20Pv22#4v28#20Pv23#8v28#20P#10000#683000v28#20Pv34#1v28#20La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#28v2?La_v2#30v30La_v2#38v31La_v2#40v32La_v2#78#;3848La_v2#80+v21#8La_v2#88v21La_v2#90v34La_v2#98v23La_v2#:0v22La_v2#:8+/+v21#8#8#7???8000La_v2#50#La_v2#48v21,2_v2#?0#?0+v28##20,1,2=X#:<900#7760<Y,T,1#:<:=<T,2_v2#<0T,8_v2#68T,9v21T,;#T,<#T,=#T,>#T,?#1T,10/+v21#10#8T,12+v21#8T,13_v2#60T,14v28T,16+/+v21#8#8#7???8000T,17+/_v2#60#8#7???8000T,18+/v21#8#7???8000Lb_v2#<0r18Lb_v2#;8r17Lb_v2#;0#7???8000Lb_v2#:8+/+v21#8#8#7???8000Lb_v2#:0v22Lb_v2#98v23Lb_v2#90v34Lb_v2#88v21Lb_v2#80+v21#8Lb_v2#78#;390<Lb_v2#58+v28#20Lb+v28#18#Nb+v28#10v35Lb+v28#8v27Mbv28v26Lb_v2#50+v28#20Lb_v2#60v28Lb_v2#68v28Lb_v2#8v2;Lb_v2#10v2<Lb_v2#18v2=Lb_v2#20v2>Lb_v2#28v2?Lb_v2#30v30Lb_v2#38v31Lb_v2#40v32Lb_v2#48v21"%pstring.
Lemma bstE1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstE1] fx R M V bstE1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstE1] LibSegJb_bstE1.regs0 LibSegJb_bstE1.kn0 LibSegJb_bstE1.BR LibSegJb_bstE1.PSS LibSegJb_bstE1.NX0 LibSegJb_bstE1.F0 706816 LibSegJb_bstE1.seg_sound_ax fx R M V bstE1_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_bstE2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstE2.regs0 LibSegJb_bstE2.regs_out0).
Lemma KS_bstE2_ok : BG.kept_ok 60 LibSegJb_bstE2.regs0 LibSegJb_bstE2.regs_out0 KS_bstE2 = true. Proof. vm_compute. reflexivity. Qed.
Definition bstE2_conc_s := ",4=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v28p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#<0S,8_v2#68S,9v21S,12+v21#8S,13_v2#60S,14v28S,15#7???8000S,16+/+v21#8#8#7???8000S,17+/_v2#60#8#7???8000S,18+/v21#8#7???8000B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Iv21#18Lav21#La+v21#8#La+v21#10#B#1000v28#7?????????>0Hv28#10P#7???7000#100000001000v28#20Ka+/v28#8#7???8000#4Iv28#20P_v2#1000#1000v28#20Pv21#18v28#20Pv22#4v28#20Pv23#8v28#20P#10000#683000v28#20Pv34#1v28#20La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#28v2?La_v2#30v30La_v2#38v31La_v2#40v32La_v2#78#;390<La_v2#80+v21#8La_v2#88v21La_v2#90v34La_v2#98v23La_v2#:0v22La_v2#:8+/+v21#8#8#7???8000La_v2#;0#7???8000La_v2#;8v33La_v2#<0v36La_v2#68v28La_v2#60v28La_v2#58+v28#20La_v2#50+v28#20La_v2#48v21,2_v2#<0#<0+v21##18,1,25X#:<:=<#7;3?4Y,T,1#:<=?<T,2_v2#80T,8+v21#8T,:v28T,;+v28#20T,<+v28#20T,=+v28#20T,>#1T,?#T,10#T,12v34T,13v23T,14v22T,15+/+v21#8#8#7???8000T,16#7???8000T,17v33T,18v36Lb_v2#80+v21#8Lb_v2#78#;390<Lb_v2#68#Lb_v2#50#Lb+v21#10+v28#20Lb_v2#58#Lb+v21#8+v28#20Lb_v2#60#Lbv21v28Lb_v2#8v2;Lb_v2#10v2<Lb_v2#18v2=Lb_v2#20v2>Lb_v2#28v2?Lb_v2#30v30Lb_v2#38v31Lb_v2#40v32Lb_v2#48v21"%pstring.
Lemma bstE2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstE2] fx R M V bstE2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstE2] LibSegJb_bstE2.regs0 LibSegJb_bstE2.kn0 LibSegJb_bstE2.BR LibSegJb_bstE2.PSS LibSegJb_bstE2.NX0 LibSegJb_bstE2.F0 707292 LibSegJb_bstE2.seg_sound_ax fx R M V bstE2_conc_s. Qed.
Definition KS_bstE3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstE3.regs0 LibSegJb_bstE3.regs_out0).
Lemma KS_bstE3_ok : BG.kept_ok 60 LibSegJb_bstE3.regs0 LibSegJb_bstE3.regs_out0 KS_bstE3 = true. Proof. vm_compute. reflexivity. Qed.
Definition bstE3_conc_s := ",3<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v28p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#80S,8+v21#8S,9v21S,12v34S,13v23S,14v22S,15+/+v21#8#8#7???8000S,16#7???8000S,17v33S,18v36B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Iv21#18Lav21v28La+v21#8+v28#20La+v21#10+v28#20B#1000v28#7?????????<0Hv28#10La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#28v2?La_v2#30v30La_v2#38v31La_v2#40v32La_v2#78#;390<La_v2#80+v21#8La_v2#68#La_v2#60#La_v2#58#La_v2#50#La_v2#48v21,1_v2#<0#<0,1,13X#:<=?<#;3948Y,T,1v2;T,2v2T,8v2<T,9v2=T,:+v28#20T,;_v2#48T,<#T,=#7???8000T,>/_v2#48#8T,?+/_v2#58#8#7???8000T,10#T,11#T,12v2>T,13v2?T,14v30T,15v31T,16v32"%pstring.
Lemma bstE3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstE3] fx R M V bstE3_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstE3] LibSegJb_bstE3.regs0 LibSegJb_bstE3.kn0 LibSegJb_bstE3.BR LibSegJb_bstE3.PSS LibSegJb_bstE3.NX0 LibSegJb_bstE3.F0 708092 LibSegJb_bstE3.seg_sound_ax fx R M V bstE3_conc_s. Qed.
Definition KS_bstJ : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstJ.regs0 LibSegJb_bstJ.regs_out0).
Lemma KS_bstJ_ok : BG.kept_ok 60 LibSegJb_bstJ.regs0 LibSegJb_bstJ.regs_out0 KS_bstJ = true. Proof. vm_compute. reflexivity. Qed.
Definition bstJ_conc_s := ",44A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v36p#2#40S,2_v2#80S,8+v21#8S,9v21S,12v34S,13v23S,14v22S,15+/+v21#8#8#7???8000S,16#7???8000S,17v33S,18v36B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Iv21#18Lav21v28La+v21#8++v28v25#20La+v21#10+v28*#20v2:B#1000v24#7?????????>0Hv24#10B#1000v28#7?????????<0Hv28#10B#20v25#8000Hv25#20B#2v2:#800La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#28v2?La_v2#30v30La_v2#38v31La_v2#40v32La_v2#78#;390<La_v2#80+v21#8La_v2#68v24La_v2#60v24La_v2#58v24La_v2#50+v24v25La_v2#48v21,1_v2#<0#<0,1,1:X#:<=?<#=0890Y,T,1#;3920T,2_v2#70T,8++v28v25#20T,:v24T,;v25T,<v24T,=#7???8000T,>#T,?+/_v2#58#8#7???8000T,10v24T,11v24Lb_v2#8v2;Lb_v2#10v2<Lb_v2#18v2=Lb_v2#20v2>Lb_v2#28v2?Lb_v2#30v30Lb_v2#38v31Lb_v2#40v32Lb_v2#68v24Lb_v2#60v24Lb_v2#58v24Lb_v2#50+v24v25Lb_v2#48v21"%pstring.
Lemma bstJ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bstJ] fx R M V bstJ_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bstJ] LibSegJb_bstJ.regs0 LibSegJb_bstJ.kn0 LibSegJb_bstJ.BR LibSegJb_bstJ.PSS LibSegJb_bstJ.NX0 LibSegJb_bstJ.F0 708092 LibSegJb_bstJ.seg_sound_ax fx R M V bstJ_conc_s. Qed.
Definition KS_bstK : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bstK.regs0 LibSegJb_bstK.regs_out0).
Lemma KS_bstK_ok : BG.kept_ok 60 LibSegJb_bstK.regs0 LibSegJb_bstK.regs_out0 KS_bstK = true. Proof. vm_compute. reflexivity. Qed.
Definition bstK_conc_s := ",17A#v2p#2#40A#v29p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40S,2_v2#70S,8v29B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#28v2?La_v2#30v30La_v2#38v31La_v2#40v32,,1,<X#;3920#;3948Y,T,1v2;T,2v2T,8v2<T,9v2=T,:v29T,12v2>T,13v2?T,14v30T,15v31T,16v32"%pstring.
Lemma bstK_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bstK] fx R M V bstK_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bstK] LibSegJb_bstK.regs0 LibSegJb_bstK.kn0 LibSegJb_bstK.BR LibSegJb_bstK.PSS LibSegJb_bstK.NX0 LibSegJb_bstK.F0 735520 LibSegJb_bstK.seg_sound_ax fx R M V bstK_conc_s. Qed.
End PMBSLTP1.
