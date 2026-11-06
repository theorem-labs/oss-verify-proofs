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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_dpA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DRVP_dpA.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_dpA : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJa_dpA.regs0 LibSegJa_dpA.regs_out0).
Lemma KS_dpA_ok : BG.kept_ok 56 LibSegJa_dpA.regs0 LibSegJa_dpA.regs_out0 KS_dpA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition dpA_conc_s := ",2:A#v2p#2#40A#v28p#2#40S,1#:7640S,2v2S,:#14><<S,;+v2#18B#7???7?811000v2#800000000000Hv2#10I_v2#<:0#<:0Ja_v2#<:0#<:0O#10000#134000Ka+/v2#8#7???7?8:#18La#7???:9=8#La#800<9>;0#I#136?30#4I#136?38#8I#136?40#8I#136?50#8I#136?58#8I#136?68#8I#136?78#8I#136?;8#4I#68?5:0#1Na#13;9=8#1Na#1<<87<#1La#13:<?8#7???8000La#1344<0#1224:8La#1344<8#11<1<4La#68>=<0v28Ma#136?;<#????????Ma#136?30#5La#136?90#400La#136?50#Ma#136?;8#La#136?88#68?5:0Ma#136?<0#:Na#13;9=9#1La#134640#1249:<Ma+v2#18#La#134648#124=;0La#136?78#11;?68Ma#136?:8#1,:_v2#<:0#<:0#136?30#4#136?38#8#136?40#8#136?50#8#136?58#8#136?68#8#136?78#8#136?;8#4#68?5:0#1,1,6:X#62:54#11;?<4Y,T,1#11;=5<T,2_v2#450T,5#T,8#68>=<0T,9#1T,:#1T,;#5413T,<_v2#450T,=#14><>T,>#5413T,?#1T,10#136?30T,11#1=T,12#14><>T,13#1T,14#T,15#14><?T,16#1T,17#14><>T,18#1T,19#T,1:#1T,1;#1Lb#136?78#11;27<Lb_v2#448v28Lb_v2#440#136?30Lb_v2#438#11;=5<Lb_v2#428#14><?Lb_v2#420#136?30Lb_v2#418#1Lb_v2#410#7??????>Lb_v2#408#7???????Lb_v2#400#25Lb_v2#3?8#11<4;<Lb#136?58#68?5:1Lb_v2#450_v2#340Nb#68?5:0#30Nb_v2#340#30Lb_v2#430#Lb_v2#3>8#Lb_v2#3=0#1Lb_v2#3>0#Lb_v2#3?0#10=<3Lb_v2#3=8#Lb_v2#380#Lb_v2#1=0+v2#20Lb_v2#3<8^#?#???????<<<<<<<=Lb_v2#3<0^#?#??????????>????Lb_v2#388#<<<<<<<Lb_v2#3:0#12889Lb_v2#240v28Lb_v2#390#68>=<0Lb_v2#398#Lb_v2#3:8_v2#1=0Lb_v2#3;8_v2#170Lb_v2#3;0_v2#<8Lb_v2#238r1;Lb_v2#230r1:Lb_v2#228r19Lb_v2#220r18Lb_v2#218r17Lb_v2#210r16Lb_v2#208#5Lb_v2#200#Lb_v2#1?8#1Lb_v2#1?0#68>=<0Lb_v2#1>8#14><<Lb_v2#1>0#136?30Lb_v2#1=8#11<2<<Lb#136?50#68?9:0Lb#136?40#Lb#136?38#Lb#136?68#68?5:0Mb#136?;8^#?#???????????????Mb#136?30#5Lb_v2#;0#Lb_v2#;8#Lb_v2#<0#Lb_v2#<8#Lb_v2#:8#Lb_v2#1<8+v2#18Lb_v2#:0v28Lb_v2#98r15Lb_v2#90r14Lb_v2#88r13Lb_v2#80+v2#18Lb_v2#78#136?30Lb_v2#70#14><<Lb_v2#68#67168Lb_v2#60+v2#18Lb_v2#58+v2#18Lb_v2#50r12Lb_v2#48+v2#18Lb_v2#40#14><<Lb_v2#38#665?8Lb_v2#28+v2#18Lb_v2#20+v2#18Lb_v2#18r9Lb_v2#10r8Lb_v2#8#:7640Jb_v2#378#38Jb_v2#33?#??Jb_v2#1<0#?8Jb_v2#30#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma dpA_conc : ltac:(r1mk L5KA.zeros_at [KS_dpA] fx R M V dpA_conc_s).
Proof.
r1pf L5KA.zeros_at [KS_dpA] LibSegJa_dpA.regs0 LibSegJa_dpA.kn0 LibSegJa_dpA.BR LibSegJa_dpA.PSS LibSegJa_dpA.NX0 LibSegJa_dpA.F0 404052 LibSegJa_dpA.seg_sound_ax fx R M V dpA_conc_s. Qed.
End SE.
End AS0DRVP_dpA.
