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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_dpXd_2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DRVP_dpXd_2.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_dpXd_2 : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_dpXd_2.regs0 LibSegJb_dpXd_2.regs_out0).
Lemma KS_dpXd_2_ok : BG.kept_ok 140 LibSegJb_dpXd_2.regs0 LibSegJb_dpXd_2.regs_out0 KS_dpXd_2 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition dpXd_2_conc_s := ",35A#v2p#2#40A#v9p#2#40A#v:p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v28p#2#40A#v6>p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v7:p#2#40S,2v2S,8#S,9#138<98S,:v6>S,12v76S,13v77S,14v78S,15#690;00S,16v7:B#7???7?811000v2#800000000000Hv2#10I_v2#10#10Ja_v2#10#10O#10000#136000I#138<;8#8I#138<<0#8I#138<=0#8La#138<?0#6912>0La#138<?8#400La#690;00v28La+v2#28v28La+v2#68#11=744La+v2#60#138<98La+v2#58v9La+v2#50v12La+v2#48v13La+v2#40v14La+v2#38v15La+v2#30v16La#138<:0#La#138<:8#La#138<90#138;:8Ma#138<34#????????La#138;=0#La#138;>0#La#138;;0#La#138;;8#La+v2#78#1157<8La+v2#70v:,4_v2#10#10#138<;8#8#138<<0#8#138<=0#8,1,12X#11=148#11546<Y,T,1#1157=0T,2+v2#80T,8v:T,9v9T,:v:T,;v:T,<v28T,11#5>T,12v12T,13v13T,14v14T,15v15T,16v16Lb#138<=0#6912>0Lb#138<<0#6912>0Lb#138<;8#6916>0"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma dpXd_2_conc : ltac:(r1mk L5.defined [KS_dpXd_2] fx R M V dpXd_2_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_dpXd_2] LibSegJb_dpXd_2.regs0 LibSegJb_dpXd_2.kn0 LibSegJb_dpXd_2.BR LibSegJb_dpXd_2.PSS LibSegJb_dpXd_2.NX0 LibSegJb_dpXd_2.F0 1167688 LibSegJb_dpXd_2.seg_sound_ax fx R M V dpXd_2_conc_s. Qed.
End SE.
End AS0DRVP_dpXd_2.
