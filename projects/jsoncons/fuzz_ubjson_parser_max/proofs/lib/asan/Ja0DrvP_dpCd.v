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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_dpCd.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DRVP_dpCd.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_dpCd : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJa_dpCd.regs0 LibSegJa_dpCd.regs_out0).
Lemma KS_dpCd_ok : BG.kept_ok 140 LibSegJa_dpCd.regs0 LibSegJa_dpCd.regs_out0 KS_dpCd = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition dpCd_conc_s := ",61A#v2p#2#40A#v8p#2#40A#v9p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v17p#2#40A#v18p#2#40A#v19p#2#40A#v1:p#2#40A#v1;p#2#40A#v28p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v7:p#2#40A#v7=p#2#40A#v7?p#2#40S,2v2S,8#1S,9#136?30S,12v76S,13v77S,14v78S,15#68>=<0S,16v7:S,17#14><>S,18#1S,19v7=S,1:#1S,1;v7?B#7???7?811000v2#800000000000Hv2#10I_v2#7>0#870Ja_v2#7>0#870O#10000#134000I#136?30#4I#136?50#8I#136?58#8I#136?68#8La#136?88#68?5:0La#136?90#400La#68>=<0v28La+v2#28v28La+v2#68#11;?>8La+v2#60#68>=<0La+v2#58#1La+v2#50#14><>La+v2#48#1La+v2#40#La+v2#38#14><?La+v2#30#1La+v2#78v28La+v2#88#11;=5<La+v2#80#136?30Na#13;9=9#1La#134640#1249:<La+v2#<8#11<4;<La+v2#<0#25La+v2#;8#7???????La+v2#;0#7??????>La+v2#:8#1La+v2#:0#136?30La+v2#98#14><?La+v2#130#68>=<0La+v2#280v28La+v2#2>8#11<2<<La+v2#2>0#136?30La+v2#2=8#14><<La+v2#2=0#68>=<0La+v2#2<8#1La+v2#2<0#La+v2#2;8#5La+v2#2;0v16La+v2#2:8v17La+v2#2:0v18La+v2#298v19La+v2#290v1:La+v2#288v1;Ma#136?30#5La+v2#420v28La+v2#458#67168La+v2#450#14><<La+v2#448#136?30La+v2#440+v2#4=8La+v2#438v13La+v2#430v14La+v2#428v15La+v2#488#665?8La+v2#480#14><<La+v2#478+v2#4=8La+v2#470v12La+v2#4;8#:7640La+v2#4;0v8La+v2#4:8v9,5_v2#7>0#870#136?30#4#136?50#8#136?58#8#136?68#8,1,1:X#11;310#:7640Y,T,1#:7640T,2+v2#4<0T,8v8T,9v9T,:#2T,;v28T,<v28T,=#68?5:0T,>#T,?#T,12v12T,13v13T,14v14T,15v15T,16v16T,17v17T,18v18T,19v19T,1:v1:T,1;v1;Mb#136?30#5Lb#136?58#68?5:0Lb#136?68#68?5:0Lb#136?50#68?9:0"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma dpCd_conc : ltac:(r1mk L5.defined [KS_dpCd] fx R M V dpCd_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_dpCd] LibSegJa_dpCd.regs0 LibSegJa_dpCd.kn0 LibSegJa_dpCd.BR LibSegJa_dpCd.PSS LibSegJa_dpCd.NX0 LibSegJa_dpCd.F0 1159952 LibSegJa_dpCd.seg_sound_ax fx R M V dpCd_conc_s. Qed.
End SE.
End AS0DRVP_dpCd.
