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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_dpA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DRVP_dpA.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_dpA : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJb_dpA.regs0 LibSegJb_dpA.regs_out0).
Lemma KS_dpA_ok : BG.kept_ok 56 LibSegJb_dpA.regs0 LibSegJb_dpA.regs_out0 KS_dpA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition dpA_conc_s := ",2:A#v2p#2#40A#v28p#2#40S,1#:7910S,2v2S,:#14==<S,;+v2#18B#7???7?811000v2#800000000000Hv2#10I_v2#<:0#<:0Ja_v2#<:0#<:0O#10000#136000Ka+/v2#8#7???7?8:#18La#7???:9;8#La#800<:258#I#138<98#4I#138<:0#8I#138<:8#8I#138<;8#8I#138<<0#8I#138<=0#8I#138<>0#8I#138=20#4I#6912>0#1Na#13=718#1Na#1<>5;<#1La#13<:38#7???8000La#136228#1242>0La#136230#11=??<La#690;00v28Ma#138=24#????????Ma#138<98#5La#138<?8#400La#138<;8#Ma#138=20#La#138<?0#6912>0Ma#138=28#:Na#13=719#1La#1363:8#1267>4Ma+v2#18#La#1363;0#126;>8La#138<>0#11==:0Ma#138=10#1,:_v2#<:0#<:0#138<98#4#138<:0#8#138<:8#8#138<;8#8#138<<0#8#138<=0#8#138<>0#8#138=20#4#6912>0#1,1,6:X#62=24#11==?<Y,T,1#11=;94T,2_v2#450T,5#T,8#690;00T,9#1T,:#1T,;#5413T,<_v2#450T,=#14==>T,>#5413T,?#1T,10#138<98T,11#1=T,12#14==>T,13#1T,14#T,15#14==?T,16#1T,17#14==>T,18#1T,19#T,1:#1T,1;#1Lb#138<>0#11=0;4Lb_v2#448v28Lb_v2#440#138<98Lb_v2#438#11=;94Lb_v2#428#14==?Lb_v2#420#138<98Lb_v2#418#1Lb_v2#410#7??????>Lb_v2#408#7???????Lb_v2#400#25Lb_v2#3?8#11>2?4Lb#138<<0#6912>1Lb_v2#450_v2#340Nb#6912>0#30Nb_v2#340#30Lb_v2#430#Lb_v2#3>8#Lb_v2#3=0#1Lb_v2#3>0#Lb_v2#3?0#10=<3Lb_v2#3=8#Lb_v2#380#Lb_v2#1=0+v2#20Lb_v2#3<8^#?#???????<<<<<<<=Lb_v2#3<0^#?#??????????>????Lb_v2#388#<<<<<<<Lb_v2#3:0#12889Lb_v2#240v28Lb_v2#390#690;00Lb_v2#398#Lb_v2#3:8_v2#1=0Lb_v2#3;8_v2#170Lb_v2#3;0_v2#<8Lb_v2#238r1;Lb_v2#230r1:Lb_v2#228r19Lb_v2#220r18Lb_v2#218r17Lb_v2#210r16Lb_v2#208#5Lb_v2#200#Lb_v2#1?8#1Lb_v2#1?0#690;00Lb_v2#1>8#14==<Lb_v2#1>0#138<98Lb_v2#1=8#11>104Lb#138<;8#6916>0Lb#138<:8#Lb#138<:0#Lb#138<=0#6912>0Mb#138=20^#?#???????????????Mb#138<98#5Lb_v2#;0#Lb_v2#;8#Lb_v2#<0#Lb_v2#<8#Lb_v2#:8#Lb_v2#1<8+v2#18Lb_v2#:0v28Lb_v2#98r15Lb_v2#90r14Lb_v2#88r13Lb_v2#80+v2#18Lb_v2#78#138<98Lb_v2#70#14==<Lb_v2#68#67438Lb_v2#60+v2#18Lb_v2#58+v2#18Lb_v2#50r12Lb_v2#48+v2#18Lb_v2#40#14==<Lb_v2#38#668<8Lb_v2#28+v2#18Lb_v2#20+v2#18Lb_v2#18r9Lb_v2#10r8Lb_v2#8#:7910Jb_v2#378#38Jb_v2#33?#??Jb_v2#1<0#?8Jb_v2#30#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma dpA_conc : ltac:(r1mk L5KA.zeros_at [KS_dpA] fx R M V dpA_conc_s).
Proof.
r1pf L5KA.zeros_at [KS_dpA] LibSegJb_dpA.regs0 LibSegJb_dpA.kn0 LibSegJb_dpA.BR LibSegJb_dpA.PSS LibSegJb_dpA.NX0 LibSegJb_dpA.F0 404772 LibSegJb_dpA.seg_sound_ax fx R M V dpA_conc_s. Qed.
End SE.
End AS0DRVP_dpA.
