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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_apkA0 LibSegJa_apkA1 LibSegJa_apkB0 LibSegJa_apkB1 LibSegJa_apkT LibSegJa_aigA1a LibSegJa_aigA1b LibSegJa_aigA0 LibSegJa_aigB0 LibSegJa_aigB1a LibSegJa_aigB1b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAPKP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_apkA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_apkA0.regs0 LibSegJa_apkA0.regs_out0).
Lemma KS_apkA0_ok : BG.kept_ok 48 LibSegJa_apkA0.regs0 LibSegJa_apkA0.regs_out0 KS_apkA0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition apkA0_conc_s := ",17A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8,2_v2#30#30+v24#100#28,1,15X#:>850#:?7?0Y,T,1#:>8=<T,2_v2#30T,8+v24#118T,9+v24#120T,;v22T,<#4000T,=#T,12#7???8000T,13+/+v24#120#8#7???8000Lb+v24#118v22Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000Lb+v24#120#Jb+v24#100#8"%pstring.
Lemma apkA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_apkA0] fx R M V apkA0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_apkA0] LibSegJa_apkA0.regs0 LibSegJa_apkA0.kn0 LibSegJa_apkA0.BR LibSegJa_apkA0.PSS LibSegJa_apkA0.NX0 LibSegJa_apkA0.F0 714832 LibSegJa_apkA0.seg_sound_ax fx R M V apkA0_conc_s. Qed.
Definition KS_apkA1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_apkA1.regs0 LibSegJa_apkA1.regs_out0).
Lemma KS_apkA1_ok : BG.kept_ok 48 LibSegJa_apkA1.regs0 LibSegJa_apkA1.regs_out0 KS_apkA1 = true. Proof. vm_compute. reflexivity. Qed.
Definition apkA1_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8B#1v21#4000B#1000v23#7???????<000Jav23#1P#7???7000#100000001000v23#1Ka+/v23#8#7???8000#1P_v2#30#30v23#1Pv24#128v23#1,1_v2#30#30,1,>X#:>850#:>910Y,T,2_v2#30T,8+v24#118T,9+v24#120T,:v23T,;#T,12#7???8000T,13+/+v24#120#8#7???8000Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma apkA1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_apkA1] fx R M V apkA1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_apkA1] LibSegJa_apkA1.regs0 LibSegJa_apkA1.kn0 LibSegJa_apkA1.BR LibSegJa_apkA1.PSS LibSegJa_apkA1.NX0 LibSegJa_apkA1.F0 714832 LibSegJa_apkA1.seg_sound_ax fx R M V apkA1_conc_s. Qed.
Definition KS_apkB0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_apkB0.regs0 LibSegJa_apkB0.regs_out0).
Lemma KS_apkB0_ok : BG.kept_ok 48 LibSegJa_apkB0.regs0 LibSegJa_apkB0.regs_out0 KS_apkB0 = true. Proof. vm_compute. reflexivity. Qed.
Definition apkB0_conc_s := ",24A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8+v24#118S,9+v24#120S,:#S,12#7???8000S,13+/+v24#120#8#7???8000O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,2_v2#30#30+v24#100#28,1,14X#:>8=<#:>92<Y,T,1v28T,2v2T,8v29T,9v2:T,:#100T,;#T,12v2;T,13v2<Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma apkB0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_apkB0] fx R M V apkB0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_apkB0] LibSegJa_apkB0.regs0 LibSegJa_apkB0.kn0 LibSegJa_apkB0.BR LibSegJa_apkB0.PSS LibSegJa_apkB0.NX0 LibSegJa_apkB0.F0 714972 LibSegJa_apkB0.seg_sound_ax fx R M V apkB0_conc_s. Qed.
Definition KS_apkB1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_apkB1.regs0 LibSegJa_apkB1.regs_out0).
Lemma KS_apkB1_ok : BG.kept_ok 48 LibSegJa_apkB1.regs0 LibSegJa_apkB1.regs_out0 KS_apkB1 = true. Proof. vm_compute. reflexivity. Qed.
Definition apkB1_conc_s := ",2<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8+v24#118S,9+v24#120S,:v21S,12#7???8000S,13+/+v24#120#8#7???8000O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8B#1v21#4000B#1000v22#7???????<000Jav22#1P#7???7000#100000001000v22#1Ka+/v22#8#7???8000#1P_v2#30#30v22#1Pv24#128v22#1La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,2_v2#30#30+v24#100#28,1,>X#:>8=<#:>910Y,T,:v22T,;#Lb+v24#120v21Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma apkB1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_apkB1] fx R M V apkB1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_apkB1] LibSegJa_apkB1.regs0 LibSegJa_apkB1.kn0 LibSegJa_apkB1.BR LibSegJa_apkB1.PSS LibSegJa_apkB1.NX0 LibSegJa_apkB1.F0 714972 LibSegJa_apkB1.seg_sound_ax fx R M V apkB1_conc_s. Qed.
Definition KS_apkT : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_apkT.regs0 LibSegJa_apkT.regs_out0).
Lemma KS_apkT_ok : BG.kept_ok 48 LibSegJa_apkT.regs0 LibSegJa_apkT.regs_out0 KS_apkT = true. Proof. vm_compute. reflexivity. Qed.
Definition apkT_conc_s := ",12A#v2p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,,1,8X#:>914#:>92<Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<"%pstring.
Lemma apkT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apkT] fx R M V apkT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apkT] LibSegJa_apkT.regs0 LibSegJa_apkT.kn0 LibSegJa_apkT.BR LibSegJa_apkT.PSS LibSegJa_apkT.NX0 LibSegJa_apkT.F0 715028 LibSegJa_apkT.seg_sound_ax fx R M V apkT_conc_s. Qed.
Definition KS_aigA1a : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aigA1a.regs0 LibSegJa_aigA1a.regs_out0).
Lemma KS_aigA1a_ok : BG.kept_ok 48 LibSegJa_aigA1a.regs0 LibSegJa_aigA1a.regs_out0 KS_aigA1a = true. Proof. vm_compute. reflexivity. Qed.
Definition aigA1a_conc_s := ",19A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24S,;#1O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801070v2#800000000000Hv2#10I_v2#70#70B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#70#70v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#1Ja+v24#100#8B#1000v23#7???????<000,2_v2#70#70+v24#100#28,1,16X#:>:50#:><10Y,T,:#T,;#T,<#7???8000Lb+v24#120#Lb+v24#118+v23#1Lb_v2#68r1;Lb_v2#60r1:Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000"%pstring.
Lemma aigA1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aigA1a] fx R M V aigA1a_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aigA1a] LibSegJa_aigA1a.regs0 LibSegJa_aigA1a.kn0 LibSegJa_aigA1a.BR LibSegJa_aigA1a.PSS LibSegJa_aigA1a.NX0 LibSegJa_aigA1a.F0 715344 LibSegJa_aigA1a.seg_sound_ax fx R M V aigA1a_conc_s. Qed.
Definition KS_aigA1b : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aigA1b.regs0 LibSegJa_aigA1b.regs_out0).
Lemma KS_aigA1b_ok : BG.kept_ok 48 LibSegJa_aigA1b.regs0 LibSegJa_aigA1b.regs_out0 KS_aigA1b = true. Proof. vm_compute. reflexivity. Qed.
Definition aigA1b_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24S,;#1O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801070v2#800000000000Hv2#10I_v2#70#70B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#70#70v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8B#2v21#4000B#1000v23#7???????<000,2_v2#70#70+v24#100#28,1,16X#:>:50#:><10Y,T,:_v21#1T,;#T,<#7???8000Lb+v24#120_v21#1Lb+v24#118+v23#1Lb_v2#68r1;Lb_v2#60r1:Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000"%pstring.
Lemma aigA1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aigA1b] fx R M V aigA1b_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aigA1b] LibSegJa_aigA1b.regs0 LibSegJa_aigA1b.kn0 LibSegJa_aigA1b.BR LibSegJa_aigA1b.PSS LibSegJa_aigA1b.NX0 LibSegJa_aigA1b.F0 715344 LibSegJa_aigA1b.seg_sound_ax fx R M V aigA1b_conc_s. Qed.
Definition KS_aigA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aigA0.regs0 LibSegJa_aigA0.regs_out0).
Lemma KS_aigA0_ok : BG.kept_ok 48 LibSegJa_aigA0.regs0 LibSegJa_aigA0.regs_out0 KS_aigA0 = true. Proof. vm_compute. reflexivity. Qed.
Definition aigA0_conc_s := ",18A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24S,;#1O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801070v2#800000000000Hv2#10I_v2#70#70B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#70#70v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8,2_v2#70#70+v24#100#28,1,25X#:>:50#:?7?0Y,T,1#:>;7<T,2_v2#70T,8+v24#120T,9v24T,;v22T,<#4000T,12+v24#118T,13#1T,14+v24#100T,15+v24#108T,16+/+v24#100#8#7???8000T,17+/+v24#120#8#7???8000T,18#T,19+/+v24#118#8#7???8000T,1:+/+v24#108#8#7???8000T,1;+/+v24#110#8#7???8000Lb+v24#118v22Lb_v2#70+v24#110Lb_v2#68r1;Lb_v2#60r1:Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000Lb+v24#120#Jb+v24#100#8"%pstring.
Lemma aigA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aigA0] fx R M V aigA0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aigA0] LibSegJa_aigA0.regs0 LibSegJa_aigA0.kn0 LibSegJa_aigA0.BR LibSegJa_aigA0.PSS LibSegJa_aigA0.NX0 LibSegJa_aigA0.F0 715344 LibSegJa_aigA0.seg_sound_ax fx R M V aigA0_conc_s. Qed.
Definition KS_aigB0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aigB0.regs0 LibSegJa_aigB0.regs_out0).
Lemma KS_aigB0_ok : BG.kept_ok 60 LibSegJa_aigB0.regs0 LibSegJa_aigB0.regs_out0 KS_aigB0 = true. Proof. vm_compute. reflexivity. Qed.
Definition aigB0_conc_s := ",3=A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40S,2_v2#70S,8+v24#120S,9v24S,:#S,12+v24#118S,13#1S,14+v24#100S,15+v24#108S,16+/+v24#100#8#7???8000S,17+/+v24#120#8#7???8000S,18#S,19+/+v24#118#8#7???8000S,1:+/+v24#108#8#7???8000S,1;+/+v24#110#8#7???8000O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801070v2#800000000000Hv2#10I_v2#70#70B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#70#70v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8La_v2#70+v24#110La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?La_v2#48v30La_v2#50v31La_v2#58v32La_v2#60v33La_v2#68v34,2_v2#70#70+v24#100#28,1,24X#:>;7<#:><10Y,T,1v28T,2v2T,8v29T,9v2:T,;#T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?T,17v30T,18v31T,19v32T,1:v33T,1;v34Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#70+v24#110Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<Lb_v2#30v2=Lb_v2#38v2>Lb_v2#40v2?Lb_v2#48v30Lb_v2#50v31Lb_v2#58v32Lb_v2#60v33Lb_v2#68v34"%pstring.
Lemma aigB0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aigB0] fx R M V aigB0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aigB0] LibSegJa_aigB0.regs0 LibSegJa_aigB0.kn0 LibSegJa_aigB0.BR LibSegJa_aigB0.PSS LibSegJa_aigB0.NX0 LibSegJa_aigB0.F0 715644 LibSegJa_aigB0.seg_sound_ax fx R M V aigB0_conc_s. Qed.
Definition KS_aigB1a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aigB1a.regs0 LibSegJa_aigB1a.regs_out0).
Lemma KS_aigB1a_ok : BG.kept_ok 60 LibSegJa_aigB1a.regs0 LibSegJa_aigB1a.regs_out0 KS_aigB1a = true. Proof. vm_compute. reflexivity. Qed.
Definition aigB1a_conc_s := ",3>A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40S,2_v2#70S,8+v24#120S,9v24S,:#1S,12+v24#118S,13#1S,14+v24#100S,15+v24#108S,16+/+v24#100#8#7???8000S,17+/+v24#120#8#7???8000S,18#S,19+/+v24#118#8#7???8000S,1:+/+v24#108#8#7???8000S,1;+/+v24#110#8#7???8000O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801070v2#800000000000Hv2#10I_v2#70#70B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#70#70v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8B#1000v22#7???????<000La_v2#70+v24#110La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?La_v2#48v30La_v2#50v31La_v2#58v32La_v2#60v33La_v2#68v34,2_v2#70#70+v24#100#28,1,25X#:>;7<#:><10Y,T,1v28T,2v2T,8v29T,9v2:T,:#T,;#1T,<#T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?T,17v30T,18v31T,19v32T,1:v33T,1;v34Lb+v24#120#Lb+v24#118+v22#1Lb+v24#108v22Lb+v24#110#4000Lb_v2#70+v24#110Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<Lb_v2#30v2=Lb_v2#38v2>Lb_v2#40v2?Lb_v2#48v30Lb_v2#50v31Lb_v2#58v32Lb_v2#60v33Lb_v2#68v34"%pstring.
Lemma aigB1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aigB1a] fx R M V aigB1a_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aigB1a] LibSegJa_aigB1a.regs0 LibSegJa_aigB1a.kn0 LibSegJa_aigB1a.BR LibSegJa_aigB1a.PSS LibSegJa_aigB1a.NX0 LibSegJa_aigB1a.F0 715644 LibSegJa_aigB1a.seg_sound_ax fx R M V aigB1a_conc_s. Qed.
Definition KS_aigB1b : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aigB1b.regs0 LibSegJa_aigB1b.regs_out0).
Lemma KS_aigB1b_ok : BG.kept_ok 60 LibSegJa_aigB1b.regs0 LibSegJa_aigB1b.regs_out0 KS_aigB1b = true. Proof. vm_compute. reflexivity. Qed.
Definition aigB1b_conc_s := ",40A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40S,2_v2#70S,8+v24#120S,9v24S,:v21S,12+v24#118S,13#1S,14+v24#100S,15+v24#108S,16+/+v24#100#8#7???8000S,17+/+v24#120#8#7???8000S,18#S,19+/+v24#118#8#7???8000S,1:+/+v24#108#8#7???8000S,1;+/+v24#110#8#7???8000O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801070v2#800000000000Hv2#10I_v2#70#70B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#70#70v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8B#2v21#4000B#1000v22#7???????<000La_v2#70+v24#110La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?La_v2#48v30La_v2#50v31La_v2#58v32La_v2#60v33La_v2#68v34,2_v2#70#70+v24#100#28,1,25X#:>;7<#:><10Y,T,1v28T,2v2T,8v29T,9v2:T,:_v21#1T,;#1T,<#T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?T,17v30T,18v31T,19v32T,1:v33T,1;v34Lb+v24#120_v21#1Lb+v24#118+v22#1Lb+v24#108v22Lb+v24#110#4000Lb_v2#70+v24#110Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<Lb_v2#30v2=Lb_v2#38v2>Lb_v2#40v2?Lb_v2#48v30Lb_v2#50v31Lb_v2#58v32Lb_v2#60v33Lb_v2#68v34"%pstring.
Lemma aigB1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aigB1b] fx R M V aigB1b_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aigB1b] LibSegJa_aigB1b.regs0 LibSegJa_aigB1b.kn0 LibSegJa_aigB1b.BR LibSegJa_aigB1b.PSS LibSegJa_aigB1b.NX0 LibSegJa_aigB1b.F0 715644 LibSegJa_aigB1b.seg_sound_ax fx R M V aigB1b_conc_s. Qed.
End PMAPKP.
