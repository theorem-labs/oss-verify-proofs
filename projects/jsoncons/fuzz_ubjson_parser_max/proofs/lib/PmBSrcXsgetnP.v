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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_axgA0 LibSegJb_axgA1 LibSegJb_axgA2 LibSegJb_axgC1 LibSegJb_axgC2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBXGP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_axgA0 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_axgA0.regs0 LibSegJb_axgA0.regs_out0).
Lemma KS_axgA0_ok : BG.kept_ok 48 LibSegJb_axgA0.regs0 LibSegJb_axgA0.regs_out0 KS_axgA0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition axgA0_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24S,;v25S,<#4000B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v24#7?????????00Hv24#8P_v2#50#50v24#100O#10000#136000Lav24#131?20La+v24#18v21La+v24#20v21La+v24#30#La+v24#58v21Ma+v24#60#8B#1000v21#800000000000,1_v2#50#50,1,10X#=76>4#=77><Y,T,:#T,;^#?#???????????????T,<v21T,=v21Lb_v2#50#Lb_v2#48#=777<Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma axgA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_axgA0] fx R M V axgA0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_axgA0] LibSegJb_axgA0.regs0 LibSegJb_axgA0.kn0 LibSegJb_axgA0.BR LibSegJb_axgA0.PSS LibSegJb_axgA0.NX0 LibSegJb_axgA0.F0 882404 LibSegJb_axgA0.seg_sound_ax fx R M V axgA0_conc_s. Qed.
Definition KS_axgA1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_axgA1.regs0 LibSegJb_axgA1.regs_out0).
Lemma KS_axgA1_ok : BG.kept_ok 48 LibSegJb_axgA1.regs0 LibSegJb_axgA1.regs_out0 KS_axgA1 = true. Proof. vm_compute. reflexivity. Qed.
Definition axgA1_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24S,;v25S,<#4000B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v24#7?????????00Hv24#8P_v2#50#50v24#100O#10000#136000Lav24#131?20La+v24#18v21La+v24#20+v21v23La+v24#30#La+v24#58+v21v23Ma+v24#60#8B#1000v21#800000000000B#1v23#4000,1_v2#50#50,1,16X#=76>4#77604Y,T,1#=77;8T,2_v2#40T,8#T,9#4000T,:v25T,;v21T,<v23T,12v25T,13v24T,14v23T,15#7???????T,16^#?#???????????????Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma axgA1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_axgA1] fx R M V axgA1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_axgA1] LibSegJb_axgA1.regs0 LibSegJb_axgA1.kn0 LibSegJb_axgA1.BR LibSegJb_axgA1.PSS LibSegJb_axgA1.NX0 LibSegJb_axgA1.F0 882404 LibSegJb_axgA1.seg_sound_ax fx R M V axgA1_conc_s. Qed.
Definition KS_axgA2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_axgA2.regs0 LibSegJb_axgA2.regs_out0).
Lemma KS_axgA2_ok : BG.kept_ok 48 LibSegJb_axgA2.regs0 LibSegJb_axgA2.regs_out0 KS_axgA2 = true. Proof. vm_compute. reflexivity. Qed.
Definition axgA2_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2v2S,:v24S,;v25S,<#4000B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v24#7?????????00Hv24#8P_v2#50#50v24#100O#10000#136000Lav24#131?20La+v24#18v21La+v24#20+v21v23La+v24#30#La+v24#58+v21v23Ma+v24#60#8B#1000v21#800000000000B#4001v23#8000000,1_v2#50#50,1,15X#=76>4#77604Y,T,1#=77;8T,2_v2#40T,8#T,9#4000T,:v25T,;v21T,12v25T,13v24T,14#4000T,15#7???????T,16^#?#???????????????Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma axgA2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_axgA2] fx R M V axgA2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_axgA2] LibSegJb_axgA2.regs0 LibSegJb_axgA2.kn0 LibSegJb_axgA2.BR LibSegJb_axgA2.PSS LibSegJb_axgA2.NX0 LibSegJb_axgA2.F0 882404 LibSegJb_axgA2.seg_sound_ax fx R M V axgA2_conc_s. Qed.
Definition KS_axgC1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_axgC1.regs0 LibSegJb_axgC1.regs_out0).
Lemma KS_axgC1_ok : BG.kept_ok 48 LibSegJb_axgC1.regs0 LibSegJb_axgC1.regs_out0 KS_axgC1 = true. Proof. vm_compute. reflexivity. Qed.
Definition axgC1_conc_s := ",2:A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8#S,9#4000S,13v24S,14#4000S,15#7???????S,16^#?#???????????????B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v24#7?????????00Hv24#8P_v2#50#50v24#100O#10000#136000Lav24#131?20La+v24#18v21La+v24#20v22La+v24#30#La+v24#58v22Ma+v24#60#8I+v24#18#8La_v2#8v25La_v2#10v26La_v2#18v27La_v2#20v28La_v2#28v29La_v2#30v2:La_v2#38v2;La_v2#40v2<B#1000v21#800000000000,2_v2#50#50+v24#18#8,1,16X#=77;8#=77><Y,T,1v25T,2v2T,8v26T,9v27T,:#4000T,;v21T,12v28T,13v29T,14v2:T,15v2;T,16v2<Lb+v24#18+v21#4000Lb_v2#8v25Lb_v2#10v26Lb_v2#18v27Lb_v2#20v28Lb_v2#28v29Lb_v2#30v2:Lb_v2#38v2;Lb_v2#40v2<"%pstring.
Lemma axgC1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_axgC1] fx R M V axgC1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_axgC1] LibSegJb_axgC1.regs0 LibSegJb_axgC1.kn0 LibSegJb_axgC1.BR LibSegJb_axgC1.PSS LibSegJb_axgC1.NX0 LibSegJb_axgC1.F0 882616 LibSegJb_axgC1.seg_sound_ax fx R M V axgC1_conc_s. Qed.
Definition KS_axgC2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_axgC2.regs0 LibSegJb_axgC2.regs_out0).
Lemma KS_axgC2_ok : BG.kept_ok 48 LibSegJb_axgC2.regs0 LibSegJb_axgC2.regs_out0 KS_axgC2 = true. Proof. vm_compute. reflexivity. Qed.
Definition axgC2_conc_s := ",2;A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40S,2_v2#40S,8#S,9#4000S,13v24S,14v23S,15#7???????S,16^#?#???????????????B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v24#7?????????00Hv24#8P_v2#50#50v24#100O#10000#136000Lav24#131?20La+v24#18v21La+v24#20+v21v23La+v24#30#La+v24#58+v21v23Ma+v24#60#8I+v24#18#8La_v2#8v25La_v2#10v26La_v2#18v27La_v2#20v28La_v2#28v29La_v2#30v2:La_v2#38v2;La_v2#40v2<B#1000v21#800000000000B#1v23#3???,2_v2#50#50+v24#18#8,1,1:X#=77;8#=77><Y,T,1v25T,2v2T,8v26T,9v27T,:v23T,;^#?#???????????????T,<+v21v23T,=+v21v23T,12v28T,13v29T,14v2:T,15v2;T,16v2<Lb_v2#50v23Lb_v2#48#=777<Lb+v24#18+v21v23Lb_v2#8v25Lb_v2#10v26Lb_v2#18v27Lb_v2#20v28Lb_v2#28v29Lb_v2#30v2:Lb_v2#38v2;Lb_v2#40v2<"%pstring.
Lemma axgC2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_axgC2] fx R M V axgC2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_axgC2] LibSegJb_axgC2.regs0 LibSegJb_axgC2.kn0 LibSegJb_axgC2.BR LibSegJb_axgC2.PSS LibSegJb_axgC2.NX0 LibSegJb_axgC2.F0 882616 LibSegJb_axgC2.seg_sound_ax fx R M V axgC2_conc_s. Qed.
End PMBXGP.
