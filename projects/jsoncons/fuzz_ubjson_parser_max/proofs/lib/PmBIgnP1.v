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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bigA LibSegJb_bigA2 LibSegJb_bigB1a LibSegJb_bigB1b LibSegJb_bigB1b2 LibSegJb_bigB0.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBIGP1.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_bigA : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bigA.regs0 LibSegJb_bigA.regs_out0).
Lemma KS_bigA_ok : BG.kept_ok 80 LibSegJb_bigA.regs0 LibSegJb_bigA.regs_out0 KS_bigA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bigA_conc_s := ",8A#v2p#2#40A#v24p#2#40S,2v2S,:v24S,;#1B#7???7?8010<0v2#800000000000Hv2#10I_v2#<0#<0,1_v2#<0#<0,1,12X#:?:?4#:?;34Y,T,2_v2#<0T,8v2Lb_v2#68r1;Lb_v2#60r1:Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb_v2#<0#"%pstring.
Lemma bigA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bigA] fx R M V bigA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bigA] LibSegJb_bigA.regs0 LibSegJb_bigA.kn0 LibSegJb_bigA.BR LibSegJb_bigA.PSS LibSegJb_bigA.NX0 LibSegJb_bigA.F0 719604 LibSegJb_bigA.seg_sound_ax fx R M V bigA_conc_s. Qed.
Definition KS_bigA2 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bigA2.regs0 LibSegJb_bigA2.regs_out0).
Lemma KS_bigA2_ok : BG.kept_ok 80 LibSegJb_bigA2.regs0 LibSegJb_bigA2.regs_out0 KS_bigA2 = true. Proof. vm_compute. reflexivity. Qed.
Definition bigA2_conc_s := ",=A#v2p#2#40A#v24p#2#40A#v32p#2#40S,2v32S,8v2S,:v24S,;#1O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????40Hv32#20Iv32#60,1+v32#38#8,1,;X#:?;38#5=670Y,T,1#:?;6<T,9v32T,:#60T,;#13<:38T,<#1T,11#7???8000T,13v24T,17#1Lb+v32#38#7???8000"%pstring.
Lemma bigA2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bigA2] fx R M V bigA2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bigA2] LibSegJb_bigA2.regs0 LibSegJb_bigA2.kn0 LibSegJb_bigA2.BR LibSegJb_bigA2.PSS LibSegJb_bigA2.NX0 LibSegJb_bigA2.F0 719672 LibSegJb_bigA2.seg_sound_ax fx R M V bigA2_conc_s. Qed.
Definition KS_bigB1a : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bigB1a.regs0 LibSegJb_bigB1a.regs_out0).
Lemma KS_bigB1a_ok : BG.kept_ok 80 LibSegJb_bigB1a.regs0 LibSegJb_bigB1a.regs_out0 KS_bigB1a = true. Proof. vm_compute. reflexivity. Qed.
Definition bigB1a_conc_s := ",32A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40S,2v32S,8v2S,9v32S,:v2?S,13v24S,17#1O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????40Hv32#20Iv32#60La+v32#38#7???8000B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#60v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v23La+v24#120#1B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10Ka+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#60v2?#80Pv32#60v30#1Pv2?#80#10000#126000B#1000v23#7???????<000,5+v32##58+v2?##18+v2?#20#8++/v2?#8#7???8000##10+v24#100#28,1,2=X#:?;6<#:?>04Y,T,5v2?T,:#1T,;#1T,<+v23#1T,=#1T,>#T,?^#?#??????????????3T,10v2?T,11#7???8000T,12+v2?#20T,14+v24#120T,15+v24#118T,16+v24#100T,19+/+v24#120#8#7???8000T,1:+/v2?#8#7???8000T,1;#1Lb+v24#120#Lb+v24#118+v23#1Lb+v32#10v2?Lb+v32#8v2?Lb+v32#50v2?Lb+v2?#20#1Nb+/v2?#8#7???800;#?3Nb+/v2?#8#7???800:#?3Nb+/v2?#8#7???8009#?3Nb+/v2?#8#7???8008#?8Nb+/v2?#8#7???8003#?1Nb+/v2?#8#7???8002#?1Nb+/v2?#8#7???8001#?1Nb+/v2?#8#7???8000#?1Nb+/v2?#8#7???8007#?2Nb+/v2?#8#7???8006#?2Nb+/v2?#8#7???8005#?2Nb+/v2?#8#7???8004#Lb+v2?#10#:?:?4Lb+v2?#8#20=7=Lbv2?#41;58:;3Lb+v32#38#7???8000Lb+v24#108v22Lb+v24#110#4000Jb+v2?#18#8Jb+v2?#28#58Kb+/v2?#8#7???800<#4"%pstring.
Lemma bigB1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bigB1a] fx R M V bigB1a_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bigB1a] LibSegJb_bigB1a.regs0 LibSegJb_bigB1a.kn0 LibSegJb_bigB1a.BR LibSegJb_bigB1a.PSS LibSegJb_bigB1a.NX0 LibSegJb_bigB1a.F0 719724 LibSegJb_bigB1a.seg_sound_ax fx R M V bigB1a_conc_s. Qed.
Definition KS_bigB1b : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bigB1b.regs0 LibSegJb_bigB1b.regs_out0).
Lemma KS_bigB1b_ok : BG.kept_ok 80 LibSegJb_bigB1b.regs0 LibSegJb_bigB1b.regs_out0 KS_bigB1b = true. Proof. vm_compute. reflexivity. Qed.
Definition bigB1b_conc_s := ",34A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40S,2v32S,8v2S,9v32S,:v2?S,13v24S,17#1O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????40Hv32#20Iv32#60La+v32#38#7???8000B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#60v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v23La+v24#120v21B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10Ka+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#60v2?#80Pv32#60v30#1Pv2?#80#10000#126000B#2v21#4000B#1000v23#7???????<000,5+v32##58+v2?##18+v2?#20#8++/v2?#8#7???8000##10+v24#100#28,1,2=X#:?;6<#:?<50Y,T,5v2?T,:+v2?#20T,;v21T,<#:?:?4T,=^#?#??????????????2T,>^#?#??????????????1T,?^#?#??????????????3T,10v2?T,11#7???8000T,12+v2?#20T,14+v24#120T,15+v24#118T,16+v24#100T,19+/+v24#120#8#7???8000T,1:+/v2?#8#7???8000Lb+v32#10v2?Lb+v32#8v2?Lb+v32#50v2?Lb+v2?#20#1Nb+/v2?#8#7???800;#?3Nb+/v2?#8#7???800:#?3Nb+/v2?#8#7???8009#?3Nb+/v2?#8#7???8008#?8Nb+/v2?#8#7???8003#?1Nb+/v2?#8#7???8002#?1Nb+/v2?#8#7???8001#?1Nb+/v2?#8#7???8000#?1Nb+/v2?#8#7???8007#?2Nb+/v2?#8#7???8006#?2Nb+/v2?#8#7???8005#?2Nb+/v2?#8#7???8004#Lb+v2?#10#:?:?4Lb+v2?#8#20=7=Lbv2?#41;58:;3Lb+v32#38#7???8000Lb+v24#108v22Lb+v24#110#4000Jb+v24#100#8Lb+v24#118v23Lb+v24#120v21Jb+v2?#18#8Jb+v2?#28#58Kb+/v2?#8#7???800<#4"%pstring.
Lemma bigB1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bigB1b] fx R M V bigB1b_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bigB1b] LibSegJb_bigB1b.regs0 LibSegJb_bigB1b.kn0 LibSegJb_bigB1b.BR LibSegJb_bigB1b.PSS LibSegJb_bigB1b.NX0 LibSegJb_bigB1b.F0 719724 LibSegJb_bigB1b.seg_sound_ax fx R M V bigB1b_conc_s. Qed.
Definition KS_bigB1b2 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bigB1b2.regs0 LibSegJb_bigB1b2.regs_out0).
Lemma KS_bigB1b2_ok : BG.kept_ok 80 LibSegJb_bigB1b2.regs0 LibSegJb_bigB1b2.regs_out0 KS_bigB1b2 = true. Proof. vm_compute. reflexivity. Qed.
Definition bigB1b2_conc_s := ",3<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40S,2v32S,8v2S,9v32S,:+v2?#20S,;v21S,11#7???8000S,12+v2?#20S,13v24S,14+v24#120S,15+v24#118S,16+v24#100S,17#1S,19+/+v24#120#8#7???8000S,1:+/v2?#8#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????40Hv32#20Iv32#60B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#60v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v23La+v24#120v21B#2v21#4000B#1000v23#7???????<000B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#60v2?#80Pv32#60v30#1Pv2?#80#10000#126000La+v2?#20#1Ka+/+v2?#20#8#7???8000#1,1+v24#100#28,1,;X#:?<50#:?>04Y,T,:#1T,<+v23#1T,=#1T,>#T,1;#1Lb+v24#120_v21#1Lb+v24#118+v23#1Lb+v24#108v22Lb+v24#110#4000"%pstring.
Lemma bigB1b2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bigB1b2] fx R M V bigB1b2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bigB1b2] LibSegJb_bigB1b2.regs0 LibSegJb_bigB1b2.kn0 LibSegJb_bigB1b2.BR LibSegJb_bigB1b2.PSS LibSegJb_bigB1b2.NX0 LibSegJb_bigB1b2.F0 719952 LibSegJb_bigB1b2.seg_sound_ax fx R M V bigB1b2_conc_s. Qed.
Definition KS_bigB0 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bigB0.regs0 LibSegJb_bigB0.regs_out0).
Lemma KS_bigB0_ok : BG.kept_ok 80 LibSegJb_bigB0.regs0 LibSegJb_bigB0.regs_out0 KS_bigB0 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition bigB0_conc_s := ",31A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40S,2v32S,8v2S,9v32S,:v2?S,13v24S,17#1O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????40Hv32#20Iv32#60La+v32#38#7???8000B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#60v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v23La+v24#120#B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10Ka+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#60v2?#80Pv32#60v30#1Pv2?#80#10000#126000,5+v32##58+v2?##18+v2?#20#8++/v2?#8#7???8000##10+v24#100#28,1,36X#:?;6<#;0>58Y,T,1#:?=54T,5v2?T,:v24T,;v22T,<#4000T,=^#?#??????????????2T,>^#?#??????????????1T,?^#?#??????????????3T,10v2?T,11#7???8000T,12+v2?#20T,14+v24#120T,15+v24#118T,16+v24#100T,17+/+v24#118#8#7???8000T,18+v2?#40T,19+/+v24#120#8#7???8000T,1:+/v2?#8#7???8000T,1;#Lb+v24#118v22Lb+v32#18+/+v24#100#8#7???8000Lb+v32#20+/+v24#110#8#7???8000Lb+v32#28+/+v24#108#8#7???8000Lbv32+v24#110Lb+v32#30+v24#108Lb+v32#10v2?Lb+v32#8v2?Lb+v32#50v2?Lb+v2?#20#1Nb+/v2?#8#7???800;#?3Nb+/v2?#8#7???800:#?3Nb+/v2?#8#7???8009#?3Nb+/v2?#8#7???8008#?8Nb+/v2?#8#7???8003#?1Nb+/v2?#8#7???8002#?1Nb+/v2?#8#7???8001#?1Nb+/v2?#8#7???8000#?1Nb+/v2?#8#7???8007#?2Nb+/v2?#8#7???8006#?2Nb+/v2?#8#7???8005#?2Nb+/v2?#8#7???8004#Lb+v2?#10#:?:?4Lb+v2?#8#20=7=Lbv2?#41;58:;3Lb+v32#38#7???8000Lb+v24#108v22Lb+v24#110#4000Jb+v24#100#8Lb+v24#120#Jb+v2?#18#8Jb+v2?#28#58Kb+/v2?#8#7???800<#4"%pstring.
Lemma bigB0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bigB0] fx R M V bigB0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bigB0] LibSegJb_bigB0.regs0 LibSegJb_bigB0.kn0 LibSegJb_bigB0.BR LibSegJb_bigB0.PSS LibSegJb_bigB0.NX0 LibSegJb_bigB0.F0 719724 LibSegJb_bigB0.seg_sound_ax fx R M V bigB0_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End PMBIGP1.
