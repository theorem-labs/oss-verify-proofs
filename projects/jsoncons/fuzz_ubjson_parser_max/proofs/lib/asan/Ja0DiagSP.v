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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_sC1 LibSegJa_sC3 LibSegJa_sC4.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module AS0DIAGSP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_sC1 : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJa_sC1.regs0 LibSegJa_sC1.regs_out0).
Lemma KS_sC1_ok : BG.kept_ok 140 LibSegJa_sC1.regs0 LibSegJa_sC1.regs_out0 KS_sC1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition sC1_conc_s := ",12A#v2p#2#40A#v21p#2#40A#v22p#2#40S,1#11<98<S,2v2S,:v21S,;#7???????B#7???7?811000v2#800000000000Hv2#10I_v2#10>0#10>0Ja_v2#10>0#10>0O#10000#134000B#7???7?811000v21#7?????????>?B#v22#1????P_v2#10>0#10>0v21+v22#1Na#13;9=8#1La#1345?0#1254=0La#134480#1248;0,1_v2#10>0#10>0,1,21X#62:18#1248;0Y,T,1#64728T,2_v2#10=0T,8_v2#880T,9#7???????T,;#T,<#7???????T,=#1248;0T,12v21T,13#T,14#1Lb_v2#8;8r15Lb_v2#8;0r14Lb_v2#8:8#7???????Lb_v2#8:0v21Lb_v2#898v21Lb_v2#890#7???????Lb_v2#888#1254?4Lb_v2#878#1Lb_v2#870v2Lb_v2#868#62==<Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8#11<98<Jb_v2#10=0#818Jb_v2#880#8Jb_v2#860#820"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma sC1_conc : ltac:(r1mk L5.defined [KS_sC1] fx R M V sC1_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_sC1] LibSegJa_sC1.regs0 LibSegJa_sC1.kn0 LibSegJa_sC1.BR LibSegJa_sC1.PSS LibSegJa_sC1.NX0 LibSegJa_sC1.F0 403992 LibSegJa_sC1.seg_sound_ax fx R M V sC1_conc_s. Qed.
End SE.
Definition KS_sC3 : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJa_sC3.regs0 LibSegJa_sC3.regs_out0).
Lemma KS_sC3_ok : BG.kept_ok 140 LibSegJa_sC3.regs0 LibSegJa_sC3.regs_out0 KS_sC3 = true. Proof. vm_compute. reflexivity. Qed.
Definition sC3_conc_s := ",1=A#v2p#2#40A#v14p#2#40A#v15p#2#40A#v21p#2#40A#v22p#2#40A#v78p#2#40A#v79p#2#40S,2v2S,:+v21v22S,14v78S,15v79B#7???7?811000v2#800000000000Hv2#10I_v2#10#10Ja_v2#10#10O#10000#134000B#7???7?811000v21#7?????????>?B#v22#1????P_v2#10#10v21+v22#1La+v2#848#1254?4La+v2#840#7???????La+v2#838v21La+v2#830v21La+v2#828#7???????La+v2#820v14La+v2#818v15La+v2#868#62==<La+v2#860+v2#10=0La+v2#858#1,1_v2#10#10,1,;X#64788#62==<Y,T,1#62==<T,2+v2#870T,8+v2#10=0T,9#1T,:v22T,12v21T,13#7???????T,14v14T,15v15"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma sC3_conc : ltac:(r1mk L5.defined [KS_sC3] fx R M V sC3_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_sC3] LibSegJa_sC3.regs0 LibSegJa_sC3.kn0 LibSegJa_sC3.BR LibSegJa_sC3.PSS LibSegJa_sC3.NX0 LibSegJa_sC3.F0 411528 LibSegJa_sC3.seg_sound_ax fx R M V sC3_conc_s. Qed.
End SE.
Definition KS_sC4 : list nat := Eval vm_compute in (BG.kept_list 140 LibSegJa_sC4.regs0 LibSegJa_sC4.regs_out0).
Lemma KS_sC4_ok : BG.kept_ok 140 LibSegJa_sC4.regs0 LibSegJa_sC4.regs_out0 KS_sC4 = true. Proof. vm_compute. reflexivity. Qed.
Definition sC4_conc_s := ",29A#v2p#2#40A#v8p#2#40A#v9p#2#40A#v12p#2#40A#v13p#2#40A#v14p#2#40A#v15p#2#40A#v16p#2#40A#v21p#2#40A#v22p#2#40A#v6<p#2#40A#v6=p#2#40A#v76p#2#40A#v77p#2#40A#v78p#2#40A#v79p#2#40A#v7:p#2#40S,2v2S,8v6<S,9v6=S,12v76S,13v77S,14v78S,15v79S,16v7:B#7???7?811000v2#800000000000Hv2#10I_v2#10#10Ja_v2#10#10O#10000#134000B#7???7?811000v21#7?????????>?B#v22#1????P_v2#10#10v21+v22#1La+v2#858#11<98<La+v2#850v8La+v2#848v9La+v2#840v12La+v2#838v13La+v2#830v14La+v2#828v15La+v2#820v16,1_v2#10#10,1,;X#62>50#11<98<Y,T,1#11<98<T,2+v2#860T,8v8T,9v9T,12v12T,13v13T,14v14T,15v15T,16v16"%pstring.
Section SE.
Variables (fx : FPState).
Variables (R : PStmt.RTY).
Variables (M : PStmt.MTY).
Variables (V : PStmt.VTY).
Lemma sC4_conc : ltac:(r1mk L5.defined [KS_sC4] fx R M V sC4_conc_s).
Proof.
r1pf PConcR.PR.zeros_r [KS_sC4] LibSegJa_sC4.regs0 LibSegJa_sC4.kn0 LibSegJa_sC4.BR LibSegJa_sC4.PSS LibSegJa_sC4.NX0 LibSegJa_sC4.F0 405072 LibSegJa_sC4.seg_sound_ax fx R M V sC4_conc_s. Qed.
End SE.
End AS0DIAGSP.
