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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_dpM2d.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DRVP_dpM2d.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_dpM2d : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJa_dpM2d.regs0 LibSegJa_dpM2d.regs_out0).
Lemma KS_dpM2d_ok : BG.kept_ok 140 LibSegJa_dpM2d.regs0 LibSegJa_dpM2d.regs_out0 KS_dpM2d = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition dpM2d_conc_s := ",46A#v2p#2#40A#v8p#2#40A#v9p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v6>p#2#40A#v6?p#2#40A#v70p#2#40A#v71p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v7:p#2#40S,2v2S,8#1?S,9#136>40S,:v6>S,;v6?S,<v70S,=v71S,12v76S,13v77S,14v78S,15#68>=<0S,16v7:B#7???7?811000v2#800000000000Hv2#10I_v2#10#10Ja_v2#10#10O#10000#134000B#7???7?811000v21#7?????????>?B#v22#1????P_v2#10#10v21+v22#1La#7???:<38#I#136>60#8I#136>68#8I#136>78#8La#136>98#68?598La#136>:0#La#68>=<0v28La+v2#28v28La+v2#68#11;>34La+v2#60#1La+v2#58#1?La+v2#50#1?La+v2#48#136>40La+v2#40#1La+v2#38#1La+v2#30v16La+v2#:8#64>>0La+v2#:0+v2#900La+v2#98#1?La+v2#90#161<6La+v2#88#136>40La+v2#80#1La+v2#78#1La#13:<?8#7???8000La+v2#8?8#:73:0La+v2#8?0v8La+v2#8>8v9La+v2#8>0v12La+v2#8=8v13La+v2#8=0v14La+v2#8<8v15,4_v2#10#10#136>60#8#136>68#8#136>78#8,1,14X#11;310#:73:0Y,T,1#:73:0T,2+v2#900T,8v8T,9v9T,:#1T,;#7???:<38T,<#7???:<3<T,=#161>4T,>#T,?#T,12v12T,13v13T,14v14T,15v15T,16v16Lb#136>78#68?598Lb#136>68#68?598Lb#136>60#68?598"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma dpM2d_conc : ltac:(r1mk L5.defined [KS_dpM2d] fx R M V dpM2d_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_dpM2d] LibSegJa_dpM2d.regs0 LibSegJa_dpM2d.kn0 LibSegJa_dpM2d.BR LibSegJa_dpM2d.PSS LibSegJa_dpM2d.NX0 LibSegJa_dpM2d.F0 1159952 LibSegJa_dpM2d.seg_sound_ax fx R M V dpM2d_conc_s. Qed.
End SE.
End AS0DRVP_dpM2d.
