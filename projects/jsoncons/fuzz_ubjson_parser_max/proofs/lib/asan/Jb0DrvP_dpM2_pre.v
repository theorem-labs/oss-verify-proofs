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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_dpM2_pre.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DRVP_dpM2_pre.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_dpM2_pre : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJb_dpM2_pre.regs0 LibSegJb_dpM2_pre.regs_out0).
Lemma KS_dpM2_pre_ok : BG.kept_ok 56 LibSegJb_dpM2_pre.regs0 LibSegJb_dpM2_pre.regs_out0 KS_dpM2_pre = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition dpM2_pre_conc_s := ",1>A#v2p#2#40A#v28p#2#40S,1#:7670S,2v2S,:#16233S,;#1?S,<#1S,=#138;:8B#7???7?811000v2#800000000000Hv2#10I_v2#900#900Ja_v2#900#900O#10000#136000I#138;;0#8I#138;;8#8I#138;<8#8I#138;=0#8I#138;>0#8I#138<30#4Na#13=718#1La#136200#11=;>4Ma#138<34#????????La#138;<8#Ma#138<30#Ma#138;:8#5La#138<00#6912=8La#138<08#La#138;?0#11=0;4La#690;00v28Ma#138<20#2,7_v2#900#900#138;;0#8#138;;8#8#138;<8#8#138;=0#8#138;>0#8#138<30#4,1,35X#62=0<#11=13<Y,T,1#11=<6<T,2_v2#900T,6#11=0;4T,8#1?T,9#138;:8T,:#2T,;_v2#8>8T,=#T,>#11=;>4T,11#42T,12#1T,13_v2#8>8T,14#1T,15#690;00T,16#1?Lb_v2#8>0#1?Lb_v2#8>8#16233Lb_v2#8?0#Lb_v2#8?8#6912=8Lb_v2#8=8v28Lb_v2#8=0r16Lb_v2#8<8#1Lb_v2#8<0#1Lb_v2#8;8#138;:8Lb_v2#8;0#1?Lb_v2#8:8#1?Lb_v2#8:0#1Lb_v2#898#11=<6<Lb#138;=0#6912=8Lb#138;<8#6912=8Lb#138;;8#Lb#138;;0#Lb#138;>0#6912=8Mb#138<30^#?#???????????????Lb_v2#888#1Lb_v2#880#1Lb_v2#878#138;:8Lb_v2#870#16233Lb_v2#868#1?Lb_v2#860v2Lb_v2#858#651;0Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8#:7670Jb_v2#900#8Jb_v2#890#8Jb_v2#850#818"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma dpM2_pre_conc : ltac:(r1mk L5.defined [KS_dpM2_pre] fx R M V dpM2_pre_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_dpM2_pre] LibSegJb_dpM2_pre.regs0 LibSegJb_dpM2_pre.kn0 LibSegJb_dpM2_pre.BR LibSegJb_dpM2_pre.PSS LibSegJb_dpM2_pre.NX0 LibSegJb_dpM2_pre.F0 404748 LibSegJb_dpM2_pre.seg_sound_ax fx R M V dpM2_pre_conc_s. Qed.
End SE.
End AS0DRVP_dpM2_pre.
