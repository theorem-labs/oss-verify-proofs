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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_arpA LibSegJb_arpR0 LibSegJb_arpB LibSegJb_arpF LibSegJb_arpSS LibSegJb_arpSL LibSegJb_arpES LibSegJb_arpEL.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBRSPP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_arpA_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpA.regs0 LibSegJb_arpA.regs_out0).
Lemma KS_arpA_0_ok : BG.kept_ok 60 LibSegJb_arpA.regs0 LibSegJb_arpA.regs_out0 KS_arpA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arpA_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpA.regs0 LibSegJb_arpA.regs_out1).
Lemma KS_arpA_1_ok : BG.kept_ok 60 LibSegJb_arpA.regs0 LibSegJb_arpA.regs_out1 KS_arpA_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arpA_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpA.regs0 LibSegJb_arpA.regs_out2).
Lemma KS_arpA_2_ok : BG.kept_ok 60 LibSegJb_arpA.regs0 LibSegJb_arpA.regs_out2 KS_arpA_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arpA_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpA.regs0 LibSegJb_arpA.regs_out3).
Lemma KS_arpA_3_ok : BG.kept_ok 60 LibSegJb_arpA.regs0 LibSegJb_arpA.regs_out3 KS_arpA_3 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition arpA_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v26S,<v25O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#50#50v24#128La+v24#120v21B#v21#4000B#v26^#?#???????????????,1_v2#50#50,4,>X#;1<08#;1>64Y,T,:#T,;#C%_v26#p#2#40#1Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,17X#;1<08#;1=28Y,1T,2_v2#50T,8v26T,9v25T,:#T,<v21T,12v24T,13+v24#120T,15#7???8000T,16+/+v24#120#8#7???8000Dv26v21D#1%_v21#p#2#40D#1%_v26#p#2#40Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,17X#;1<08#;1<>4Y,2T,2_v2#50T,8v26T,9v25T,:#T,<v21T,12v24T,13+v24#120T,15#7???8000T,16+/+v24#120#8#7???8000Cv21v26D#1%_v21#p#2#40D#1%_v26#p#2#40Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,15X#;1<08#;1<68Y,3T,2_v2#50T,8v26T,9v25T,:v21T,12v24T,13+v24#120T,15#7???8000T,16+/+v24#120#8#7???8000C%_v21#p#2#40#1D#1%_v26#p#2#40Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma arpA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arpA_0; KS_arpA_1; KS_arpA_2; KS_arpA_3] fx R M V arpA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arpA_0; KS_arpA_1; KS_arpA_2; KS_arpA_3] LibSegJb_arpA.regs0 LibSegJb_arpA.kn0 LibSegJb_arpA.BR LibSegJb_arpA.PSS LibSegJb_arpA.NX0 LibSegJb_arpA.F0 728072 LibSegJb_arpA.seg_sound_ax fx R M V arpA_conc_s. Qed.
Definition KS_arpR0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpR0.regs0 LibSegJb_arpR0.regs_out0).
Lemma KS_arpR0_0_ok : BG.kept_ok 60 LibSegJb_arpR0.regs0 LibSegJb_arpR0.regs_out0 KS_arpR0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arpR0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpR0.regs0 LibSegJb_arpR0.regs_out1).
Lemma KS_arpR0_1_ok : BG.kept_ok 60 LibSegJb_arpR0.regs0 LibSegJb_arpR0.regs_out1 KS_arpR0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition arpR0_conc_s := ",1<A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#50S,8v26S,9v25S,12v24S,13+v24#120S,15#7???8000S,16+/+v24#120#8#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#50#50v24#128La+v24#120#La+v24#110#4000La+v24#108v22B#1v26^#?#???????????????,,2,6X#;1<68#;1<>4Y,T,:#T,;#T,<#C#4000v26,9X#;1<68#;0>58Y,1T,1#;1<:4T,:v24T,;v22T,<#4000T,14+v24#108T,17+/+v24#108#8#7???8000Dv26#4000"%pstring.
Lemma arpR0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arpR0_0; KS_arpR0_1] fx R M V arpR0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arpR0_0; KS_arpR0_1] LibSegJb_arpR0.regs0 LibSegJb_arpR0.kn0 LibSegJb_arpR0.BR LibSegJb_arpR0.PSS LibSegJb_arpR0.NX0 LibSegJb_arpR0.F0 728168 LibSegJb_arpR0.seg_sound_ax fx R M V arpR0_conc_s. Qed.
Definition KS_arpB_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpB.regs0 LibSegJb_arpB.regs_out0).
Lemma KS_arpB_0_ok : BG.kept_ok 60 LibSegJb_arpB.regs0 LibSegJb_arpB.regs_out0 KS_arpB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arpB_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpB.regs0 LibSegJb_arpB.regs_out1).
Lemma KS_arpB_1_ok : BG.kept_ok 60 LibSegJb_arpB.regs0 LibSegJb_arpB.regs_out1 KS_arpB_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition arpB_conc_s := ",1?A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2;p#2#40S,2_v2#50S,8v26S,9v25S,:v2;S,12v24S,13+v24#120S,14+v24#108S,15#7???8000S,16+/+v24#120#8#7???8000S,17+/+v24#108#8#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#50#50v24#128La+v24#108v22B#v2;#4000B#1v26^#?#???????????????,1+v24#118#10,2,8X#;1<:4#;1<>4Y,T,:#T,;v22T,<v2;Cv2;v26Lb+v24#118v22Lb+v24#120v2;,8X#;1<:4#;1=28Y,1T,:#T,;v22T,<v2;Dv26v2;Lb+v24#118v22Lb+v24#120v2;"%pstring.
Lemma arpB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arpB_0; KS_arpB_1] fx R M V arpB_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arpB_0; KS_arpB_1] LibSegJb_arpB.regs0 LibSegJb_arpB.kn0 LibSegJb_arpB.BR LibSegJb_arpB.PSS LibSegJb_arpB.NX0 LibSegJb_arpB.F0 728228 LibSegJb_arpB.seg_sound_ax fx R M V arpB_conc_s. Qed.
Definition KS_arpF : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpF.regs0 LibSegJb_arpF.regs_out0).
Lemma KS_arpF_ok : BG.kept_ok 60 LibSegJb_arpF.regs0 LibSegJb_arpF.regs_out0 KS_arpF = true. Proof. vm_compute. reflexivity. Qed.
Definition arpF_conc_s := ",32A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40S,2_v2#50S,8v26S,9v25S,<v21S,12v24S,13+v24#120S,15#7???8000S,16+/+v24#120#8#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801050v2#800000000000Hv2#10I_v2#50#50La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#50#50v24#128La+v24#118v23B#1v23#800000000000Ja+v24#100#8B#1v21#4000B#1v26#4000B#_v21v26#3???,2+v24#100#8+v24#118#10,1,12X#;1=28#;1>64Y,T,1v2<T,2v2T,8v2=T,9v2>T,:v23T,;v26T,=#T,>+v23v26T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34Lb+v24#120_v21v26Lb+v24#118+v23v26"%pstring.
Lemma arpF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arpF] fx R M V arpF_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arpF] LibSegJb_arpF.regs0 LibSegJb_arpF.kn0 LibSegJb_arpF.BR LibSegJb_arpF.PSS LibSegJb_arpF.NX0 LibSegJb_arpF.F0 728360 LibSegJb_arpF.seg_sound_ax fx R M V arpF_conc_s. Qed.
Definition KS_arpSS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpSS.regs0 LibSegJb_arpSS.regs_out0).
Lemma KS_arpSS_ok : BG.kept_ok 60 LibSegJb_arpSS.regs0 LibSegJb_arpSS.regs_out0 KS_arpSS = true. Proof. vm_compute. reflexivity. Qed.
Definition arpSS_conc_s := ",24A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#50S,8v26S,9v25S,12v24S,13+v24#120S,15#7???8000S,16+/+v24#120#8#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#50#50v24#128B#693000v25#7?????????>8Hv25#8P#7???7000#100000001000v25#18Ka+/v25#8#7???8000#3Iv25#18P_v2#50#50v25#18Pv24#128v25#18Nav25v27B#v27#??Fv27#fKa+/+v25#1#8#7???8000#1B#1v26^#?#???????????????,1+v25##2,1,9X#;1<>4#;31;4Y,T,1#;1=>8T,:v24T,;v25T,<v26T,13+/v25#8#7???8000Nbv25#Nb+v25#1#"%pstring.
Lemma arpSS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arpSS] fx R M V arpSS_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arpSS] LibSegJb_arpSS.regs0 LibSegJb_arpSS.kn0 LibSegJb_arpSS.BR LibSegJb_arpSS.PSS LibSegJb_arpSS.NX0 LibSegJb_arpSS.F0 728292 LibSegJb_arpSS.seg_sound_ax fx R M V arpSS_conc_s. Qed.
Definition KS_arpSL : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpSL.regs0 LibSegJb_arpSL.regs_out0).
Lemma KS_arpSL_ok : BG.kept_ok 60 LibSegJb_arpSL.regs0 LibSegJb_arpSL.regs_out0 KS_arpSL = true. Proof. vm_compute. reflexivity. Qed.
Definition arpSL_conc_s := ",2?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#50S,8v26S,9v25S,12v24S,13+v24#120S,15#7???8000S,16+/+v24#120#8#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#50#50v24#128B#693000v25#7?????????>8Hv25#8P#7???7000#100000001000v25#18Ka+/v25#8#7???8000#3Iv25#18P_v2#50#50v25#18Pv24#128v25#18Nav25v27B#v27#??Fv27#tLa+v25#8v28La+v25#10v29B#1000v29#7??????????8Hv29#8P#7???7000#100000001000v29#1Ka+/v29#8#7???8000#1Iv29#1P_v2#50#50v29#1Pv29#1v25#18Pv29#1v24#128B#1v26^#?#???????????????,2+v29##1+v25#8#8,1,9X#;1<>4#;31;4Y,T,1#;1=>8T,:v24T,;v25T,<v26T,13+/v25#8#7???8000Lb+v25#8#Nbv29#"%pstring.
Lemma arpSL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arpSL] fx R M V arpSL_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arpSL] LibSegJb_arpSL.regs0 LibSegJb_arpSL.kn0 LibSegJb_arpSL.BR LibSegJb_arpSL.PSS LibSegJb_arpSL.NX0 LibSegJb_arpSL.F0 728292 LibSegJb_arpSL.seg_sound_ax fx R M V arpSL_conc_s. Qed.
Definition KS_arpES : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpES.regs0 LibSegJb_arpES.regs_out0).
Lemma KS_arpES_ok : BG.kept_ok 60 LibSegJb_arpES.regs0 LibSegJb_arpES.regs_out0 KS_arpES = true. Proof. vm_compute. reflexivity. Qed.
Definition arpES_conc_s := ",35A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40S,2_v2#50S,8v26S,9v25S,12v24S,13+/v25#8#7???8000S,15#7???8000S,16+/+v24#120#8#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801050v2#800000000000Hv2#10I_v2#50#50La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#50#50v24#128B#693000v25#7?????????>8Hv25#8P#7???7000#100000001000v25#18Ka+/v25#8#7???8000#3Iv25#18P_v2#50#50v25#18Pv24#128v25#18Nav25v27B#v27#??Fv27#fB#1v26^#?#???????????????,,1,>X#;1=>8#;1>64Y,T,1v2<T,2v2T,8v2=T,9v2>T,:+v25#1T,;/v27#2T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34"%pstring.
Lemma arpES_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arpES] fx R M V arpES_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arpES] LibSegJb_arpES.regs0 LibSegJb_arpES.kn0 LibSegJb_arpES.BR LibSegJb_arpES.PSS LibSegJb_arpES.NX0 LibSegJb_arpES.F0 728552 LibSegJb_arpES.seg_sound_ax fx R M V arpES_conc_s. Qed.
Definition KS_arpEL : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_arpEL.regs0 LibSegJb_arpEL.regs_out0).
Lemma KS_arpEL_ok : BG.kept_ok 60 LibSegJb_arpEL.regs0 LibSegJb_arpEL.regs_out0 KS_arpEL = true. Proof. vm_compute. reflexivity. Qed.
Definition arpEL_conc_s := ",39A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40S,2_v2#50S,8v26S,9v25S,12v24S,13+/v25#8#7???8000S,15#7???8000S,16+/+v24#120#8#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801050v2#800000000000Hv2#10I_v2#50#50La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#50#50v24#128B#693000v25#7?????????>8Hv25#8P#7???7000#100000001000v25#18Ka+/v25#8#7???8000#3Iv25#18P_v2#50#50v25#18Pv24#128v25#18Nav25v27B#v27#??Fv27#tLa+v25#8v28La+v25#10v29B#1v26^#?#???????????????,,1,>X#;1=>8#;1>64Y,T,1v2<T,2v2T,8v2=T,9v2>T,:v29T,;v28T,12v2?T,13v30T,14v31T,15v32T,16v33T,17v34"%pstring.
Lemma arpEL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arpEL] fx R M V arpEL_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arpEL] LibSegJb_arpEL.regs0 LibSegJb_arpEL.kn0 LibSegJb_arpEL.BR LibSegJb_arpEL.PSS LibSegJb_arpEL.NX0 LibSegJb_arpEL.F0 728552 LibSegJb_arpEL.seg_sound_ax fx R M V arpEL_conc_s. Qed.
End PMBRSPP.
