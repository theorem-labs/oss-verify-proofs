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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_dpB_notty.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DRVP_dpB_notty.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_dpB_notty : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJb_dpB_notty.regs0 LibSegJb_dpB_notty.regs_out0).
Lemma KS_dpB_notty_ok : BG.kept_ok 56 LibSegJb_dpB_notty.regs0 LibSegJb_dpB_notty.regs_out0 KS_dpB_notty = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition dpB_notty_conc_s := ",18A#v2p#2#40A#v28p#2#40S,2v2S,8#690;00S,9#1S,:^#?#?????????????>7S,=#14==>S,?#1S,10#138<98S,12#14==>S,13#1S,14#S,15#14==?S,16#1B#7???7?811000v2#800000000000Hv2#10I_v2#70#70Ja_v2#70#70O#10000#136000I#138=28#4La#690;00v28La#138<<0#6912>1La#138<=0#6912>0Ma#138=10#1,2_v2#70#70#138=28#4,1,1>X#11=>00#11=13<Y,T,1#11=>20T,2_v2#70T,8#1T,9#138<98T,:#1T,;_v2#68T,<#2T,=#1T,11#42T,12#2T,13_v2#68T,15#690;00T,16#2Lb_v2#50#1Lb_v2#58#14==>Lb_v2#60#1Lb_v2#68#6912>0Lb_v2#48v28Lb_v2#40#1Lb_v2#38#14==?Lb_v2#30#Lb_v2#28#1Lb_v2#20#14==>Lb_v2#18#1Lb_v2#10#690;00Lb_v2#8#11=>20Mb#138=28^#?#???????????????Jb_v2#70#8"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma dpB_notty_conc : ltac:(r1mk L5.defined [KS_dpB_notty] fx R M V dpB_notty_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_dpB_notty] LibSegJb_dpB_notty.regs0 LibSegJb_dpB_notty.kn0 LibSegJb_dpB_notty.BR LibSegJb_dpB_notty.PSS LibSegJb_dpB_notty.NX0 LibSegJb_dpB_notty.F0 1170944 LibSegJb_dpB_notty.seg_sound_ax fx R M V dpB_notty_conc_s. Qed.
End SE.
End AS0DRVP_dpB_notty.
