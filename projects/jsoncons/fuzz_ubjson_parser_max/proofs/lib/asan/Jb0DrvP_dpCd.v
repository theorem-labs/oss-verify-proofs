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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_dpCd.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DRVP_dpCd.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_dpCd : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJb_dpCd.regs0 LibSegJb_dpCd.regs_out0).
Lemma KS_dpCd_ok : BG.kept_ok 140 LibSegJb_dpCd.regs0 LibSegJb_dpCd.regs_out0 KS_dpCd = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition dpCd_conc_s := ",61A#v2p#2#40A#v8p#2#40A#v9p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v17p#2#40A#v18p#2#40A#v19p#2#40A#v1:p#2#40A#v1;p#2#40A#v28p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v7:p#2#40A#v7=p#2#40A#v7?p#2#40S,2v2S,8#1S,9#138<98S,12v76S,13v77S,14v78S,15#690;00S,16v7:S,17#14==>S,18#1S,19v7=S,1:#1S,1;v7?B#7???7?811000v2#800000000000Hv2#10I_v2#7>0#870Ja_v2#7>0#870O#10000#136000I#138<98#4I#138<;8#8I#138<<0#8I#138<=0#8La#138<?0#6912>0La#138<?8#400La#690;00v28La+v2#28v28La+v2#68#11=>20La+v2#60#690;00La+v2#58#1La+v2#50#14==>La+v2#48#1La+v2#40#La+v2#38#14==?La+v2#30#1La+v2#78v28La+v2#88#11=;94La+v2#80#138<98Na#13=719#1La#1363:8#1267>4La+v2#<8#11>2?4La+v2#<0#25La+v2#;8#7???????La+v2#;0#7??????>La+v2#:8#1La+v2#:0#138<98La+v2#98#14==?La+v2#130#690;00La+v2#280v28La+v2#2>8#11>104La+v2#2>0#138<98La+v2#2=8#14==<La+v2#2=0#690;00La+v2#2<8#1La+v2#2<0#La+v2#2;8#5La+v2#2;0v16La+v2#2:8v17La+v2#2:0v18La+v2#298v19La+v2#290v1:La+v2#288v1;Ma#138<98#5La+v2#420v28La+v2#458#67438La+v2#450#14==<La+v2#448#138<98La+v2#440+v2#4=8La+v2#438v13La+v2#430v14La+v2#428v15La+v2#488#668<8La+v2#480#14==<La+v2#478+v2#4=8La+v2#470v12La+v2#4;8#:7910La+v2#4;0v8La+v2#4:8v9,5_v2#7>0#870#138<98#4#138<;8#8#138<<0#8#138<=0#8,1,1:X#11=148#:7910Y,T,1#:7910T,2+v2#4<0T,8v8T,9v9T,:#2T,;v28T,<v28T,=#6912>0T,>#T,?#T,12v12T,13v13T,14v14T,15v15T,16v16T,17v17T,18v18T,19v19T,1:v1:T,1;v1;Mb#138<98#5Lb#138<<0#6912>0Lb#138<=0#6912>0Lb#138<;8#6916>0"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma dpCd_conc : ltac:(r1mk L5.defined [KS_dpCd] fx R M V dpCd_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_dpCd] LibSegJb_dpCd.regs0 LibSegJb_dpCd.kn0 LibSegJb_dpCd.BR LibSegJb_dpCd.PSS LibSegJb_dpCd.NX0 LibSegJb_dpCd.F0 1167688 LibSegJb_dpCd.seg_sound_ax fx R M V dpCd_conc_s. Qed.
End SE.
End AS0DRVP_dpCd.
