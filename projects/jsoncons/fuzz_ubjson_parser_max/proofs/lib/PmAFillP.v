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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_afbA LibSegJa_afbE LibSegJa_afbB1 LibSegJa_afbB2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAFBP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_afbA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_afbA.regs0 LibSegJa_afbA.regs_out0).
Lemma KS_afbA_ok : BG.kept_ok 48 LibSegJa_afbA.regs0 LibSegJa_afbA.regs_out0 KS_afbA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition afbA_conc_s := ",24A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24S,;v22S,<#4000O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#30#30v24#128B#691000v25#7????????>?0Hv25#8P#7???7000#100000001000v25#110Ka+/v25#8#7???8000#22Iv25#110P_v2#30#30v25#110Pv24#128v25#110La+v24#?0v25La+v24#?8+v25#10Lav25#1302:8La+v25#10#1301;8Ma+v25#98#Ma+v25#9<#La+v25#:0+v25#10Ka#8001>052#1Ka#8001>03?#1,1_v2#30#30,1,11X#:?7?0#=58:<Y,T,1#:?8=0T,2_v2#30T,8+v24#?0T,9#4000T,:+v25#10T,=#=58:<T,>#T,13#7???8000T,14+/+v24#?0#8#7???8000Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma afbA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_afbA] fx R M V afbA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_afbA] LibSegJa_afbA.regs0 LibSegJa_afbA.kn0 LibSegJa_afbA.BR LibSegJa_afbA.PSS LibSegJa_afbA.NX0 LibSegJa_afbA.F0 718832 LibSegJa_afbA.seg_sound_ax fx R M V afbA_conc_s. Qed.
Definition KS_afbE : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_afbE.regs0 LibSegJa_afbE.regs_out0).
Lemma KS_afbE_ok : BG.kept_ok 48 LibSegJa_afbE.regs0 LibSegJa_afbE.regs_out0 KS_afbE = true. Proof. vm_compute. reflexivity. Qed.
Definition afbE_conc_s := ",24A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24S,;v22S,<#4000O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#30#30v24#128B#691000v25#7????????>?0Hv25#8P#7???7000#100000001000v25#110Ka+/v25#8#7???8000#22Iv25#110P_v2#30#30v25#110Pv24#128v25#110La+v24#?0v25La+v24#?8+v25#10Lav25#1302:8La+v25#10#1301;8Ma+v25#98#2Ma+v25#9<#La+v25#:0+v25#10Ka#8001>052#1Ka#8001>03?#1,1_v2#30#30,1,<X#:?7?0#:?:3<Y,T,:#T,<#2T,=#T,>#Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma afbE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_afbE] fx R M V afbE_conc_s).
Proof. r1pf L5KA.zeros_at [KS_afbE] LibSegJa_afbE.regs0 LibSegJa_afbE.kn0 LibSegJa_afbE.BR LibSegJa_afbE.PSS LibSegJa_afbE.NX0 LibSegJa_afbE.F0 718832 LibSegJa_afbE.seg_sound_ax fx R M V afbE_conc_s. Qed.
Definition KS_afbB1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_afbB1.regs0 LibSegJa_afbB1.regs_out0).
Lemma KS_afbB1_ok : BG.kept_ok 60 LibSegJa_afbB1.regs0 LibSegJa_afbB1.regs_out0 KS_afbB1 = true. Proof. vm_compute. reflexivity. Qed.
Definition afbB1_conc_s := ",31A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#30S,8+v24#?0S,9#4000S,:#4000S,13#7???8000S,14+/+v24#?0#8#7???8000O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#30#30v24#128B#691000v25#7????????>?0Hv25#8P#7???7000#100000001000v25#110Ka+/v25#8#7???8000#22Iv25#110P_v2#30#30v25#110Pv24#128v25#110La+v24#?0v25La+v24#?8+v25#10Lav25#1302:8La+v25#10#1301;8Ma+v25#98#Ma+v25#9<#La+v25#:0+v25#10Ka#8001>052#1Ka#8001>03?#1La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=,1_v2#30#30,1,?X#:?8=0#:?:3<Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<T,14v2=Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<Lb_v2#30v2="%pstring.
Lemma afbB1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_afbB1] fx R M V afbB1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_afbB1] LibSegJa_afbB1.regs0 LibSegJa_afbB1.kn0 LibSegJa_afbB1.BR LibSegJa_afbB1.PSS LibSegJa_afbB1.NX0 LibSegJa_afbB1.F0 719056 LibSegJa_afbB1.seg_sound_ax fx R M V afbB1_conc_s. Qed.
Definition KS_afbB2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_afbB2.regs0 LibSegJa_afbB2.regs_out0).
Lemma KS_afbB2_ok : BG.kept_ok 60 LibSegJa_afbB2.regs0 LibSegJa_afbB2.regs_out0 KS_afbB2 = true. Proof. vm_compute. reflexivity. Qed.
Definition afbB2_conc_s := ",33A#v2p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40S,2_v2#30S,8+v24#?0S,9#4000S,:v23S,13#7???8000S,14+/+v24#?0#8#7???8000O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128P_v2#30#30v24#128B#691000v25#7????????>?0Hv25#8P#7???7000#100000001000v25#110Ka+/v25#8#7???8000#22Iv25#110P_v2#30#30v25#110Pv24#128v25#110La+v24#?0v25La+v24#?8+v25#10Lav25#1302:8La+v25#10#1301;8Ma+v25#98#Ma+v25#9<#La+v25#:0+v25#10Ka#8001>052#1Ka#8001>03?#1La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=B#v23#3???,2_v2#30#30+v25#98#4,1,13X#:?8=0#:?:3<Y,T,1v28T,2v2T,8v29T,9v2:T,;#2T,<#T,=#T,12v2;T,13v2<T,14v2=Mb+v25#98#2Lb_v2#8v28Lb_v2#10v29Lb_v2#18v2:Lb_v2#20v2;Lb_v2#28v2<Lb_v2#30v2="%pstring.
Lemma afbB2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_afbB2] fx R M V afbB2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_afbB2] LibSegJa_afbB2.regs0 LibSegJa_afbB2.kn0 LibSegJa_afbB2.BR LibSegJa_afbB2.PSS LibSegJa_afbB2.NX0 LibSegJa_afbB2.F0 719056 LibSegJa_afbB2.seg_sound_ax fx R M V afbB2_conc_s. Qed.
End PMAFBP.
