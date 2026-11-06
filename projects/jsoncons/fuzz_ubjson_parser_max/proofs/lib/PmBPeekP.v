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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_apkA0 LibSegJb_apkA1 LibSegJb_apkB0 LibSegJb_apkB1 LibSegJb_apkT.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBPKP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_apkA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_apkA0.regs0 LibSegJb_apkA0.regs_out0).
Lemma KS_apkA0_ok : BG.kept_ok 48 LibSegJb_apkA0.regs0 LibSegJb_apkA0.regs_out0 KS_apkA0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition apkA0_conc_s := ",17A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120#Ja+v24#100#8,2_v2#30#30+v24#100#28,1,15X#:?8><#;0>58Y,T,1#:?978T,2_v2#30T,8+v24#118T,9+v24#120T,;v22T,<#4000T,=#T,12#7???8000T,13+/+v24#120#8#7???8000Lb+v24#118v22Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+v24#108v22Lb+v24#110#4000Lb+v24#120#Jb+v24#100#8"%pstring.
Lemma apkA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_apkA0] fx R M V apkA0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_apkA0] LibSegJb_apkA0.regs0 LibSegJb_apkA0.kn0 LibSegJb_apkA0.BR LibSegJb_apkA0.PSS LibSegJb_apkA0.NX0 LibSegJb_apkA0.F0 719084 LibSegJb_apkA0.seg_sound_ax fx R M V apkA0_conc_s. Qed.
Definition KS_apkA1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_apkA1.regs0 LibSegJb_apkA1.regs_out0).
Lemma KS_apkA1_ok : BG.kept_ok 48 LibSegJb_apkA1.regs0 LibSegJb_apkA1.regs_out0 KS_apkA1 = true. Proof. vm_compute. reflexivity. Qed.
Definition apkA1_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v24O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v23La+v24#120v21Ja+v24#100#8B#1v21#4000B#1000v23#7???????<000Jav23#1P#7???7000#100000001000v23#1Ka+/v23#8#7???8000#1P_v2#30#30v23#1Pv24#128v23#1,1_v2#30#30,1,>X#:?8><#:?9;0Y,T,2_v2#30T,8+v24#118T,9+v24#120T,:v23T,;#T,12#7???8000T,13+/+v24#120#8#7???8000Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma apkA1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_apkA1] fx R M V apkA1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_apkA1] LibSegJb_apkA1.regs0 LibSegJb_apkA1.kn0 LibSegJb_apkA1.BR LibSegJb_apkA1.PSS LibSegJb_apkA1.NX0 LibSegJb_apkA1.F0 719084 LibSegJb_apkA1.seg_sound_ax fx R M V apkA1_conc_s. Qed.
Definition KS_apkB0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_apkB0.regs0 LibSegJb_apkB0.regs_out0).
Lemma KS_apkB0_ok : BG.kept_ok 48 LibSegJb_apkB0.regs0 LibSegJb_apkB0.regs_out0 KS_apkB0 = true. Proof. vm_compute. reflexivity. Qed.
Definition apkB0_conc_s := ",24A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8+v24#118S,9+v24#120S,:#S,12#7???8000S,13+/+v24#120#8#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,2_v2#30#30+v24#100#28,1,14X#:?978#:?9<<Y,T,1v28T,2v2T,8v29T,9v2:T,:#100T,;#T,12v2;T,13v2<Lb+v24#120#Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma apkB0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_apkB0] fx R M V apkB0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_apkB0] LibSegJb_apkB0.regs0 LibSegJb_apkB0.kn0 LibSegJb_apkB0.BR LibSegJb_apkB0.PSS LibSegJb_apkB0.NX0 LibSegJb_apkB0.F0 719224 LibSegJb_apkB0.seg_sound_ax fx R M V apkB0_conc_s. Qed.
Definition KS_apkB1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_apkB1.regs0 LibSegJb_apkB1.regs_out0).
Lemma KS_apkB1_ok : BG.kept_ok 48 LibSegJb_apkB1.regs0 LibSegJb_apkB1.regs_out0 KS_apkB1 = true. Proof. vm_compute. reflexivity. Qed.
Definition apkB1_conc_s := ",2<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30S,8+v24#118S,9+v24#120S,:v21S,12#7???8000S,13+/+v24#120#8#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#30#30v24#128La+v24#108v22La+v24#110#4000La+v24#118v22La+v24#120#Ja+v24#100#8B#1v21#4000B#1000v22#7???????<000Jav22#1P#7???7000#100000001000v22#1Ka+/v22#8#7???8000#1P_v2#30#30v22#1Pv24#128v22#1La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,2_v2#30#30+v24#100#28,1,>X#:?978#:?9;0Y,T,:v22T,;#Lb+v24#120v21Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v22Jb+v24#100#8Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<"%pstring.
Lemma apkB1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_apkB1] fx R M V apkB1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_apkB1] LibSegJb_apkB1.regs0 LibSegJb_apkB1.kn0 LibSegJb_apkB1.BR LibSegJb_apkB1.PSS LibSegJb_apkB1.NX0 LibSegJb_apkB1.F0 719224 LibSegJb_apkB1.seg_sound_ax fx R M V apkB1_conc_s. Qed.
Definition KS_apkT : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_apkT.regs0 LibSegJb_apkT.regs_out0).
Lemma KS_apkT_ok : BG.kept_ok 48 LibSegJb_apkT.regs0 LibSegJb_apkT.regs_out0 KS_apkT = true. Proof. vm_compute. reflexivity. Qed.
Definition apkT_conc_s := ",12A#v2p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#30O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<,,1,8X#:?9;4#:?9<<Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<"%pstring.
Lemma apkT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_apkT] fx R M V apkT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_apkT] LibSegJb_apkT.regs0 LibSegJb_apkT.kn0 LibSegJb_apkT.BR LibSegJb_apkT.PSS LibSegJb_apkT.NX0 LibSegJb_apkT.F0 719284 LibSegJb_apkT.seg_sound_ax fx R M V apkT_conc_s. Qed.
End PMBPKP.
