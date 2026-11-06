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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bcmA LibSegJb_bcmB LibSegJb_bcsA LibSegJb_bcsB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBCOP1.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_bcmA : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bcmA.regs0 LibSegJb_bcmA.regs_out0).
Lemma KS_bcmA_ok : BG.kept_ok 60 LibSegJb_bcmA.regs0 LibSegJb_bcmA.regs_out0 KS_bcmA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bcmA_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v29p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24v25La+v21#10v29B#1000v24#7?????????>0Hv24#10B#v25#??>0Hv25#20B#1020v29#7???????????B#20_v29+v24v25#10000B#20_v29v24#10000,1_v2#60#60,1,16X#:<324#7;3?4Y,T,1#:<858T,2_v2#50T,8v23T,9v22T,:v24T,;v29T,<+v24v25T,=++v24v25#20T,>#1T,?#T,12#7???8000Lb_v2#50v23Lb_v2#48#:<388Lb_v2#28++v24v25#20Lb_v2#30+v24v25Lb_v2#38v21Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bcmA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bcmA] fx R M V bcmA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bcmA] LibSegJb_bcmA.regs0 LibSegJb_bcmA.kn0 LibSegJb_bcmA.BR LibSegJb_bcmA.PSS LibSegJb_bcmA.NX0 LibSegJb_bcmA.F0 705316 LibSegJb_bcmA.seg_sound_ax fx R M V bcmA_conc_s. Qed.
Definition KS_bcmB : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bcmB.regs0 LibSegJb_bcmB.regs_out0).
Lemma KS_bcmB_ok : BG.kept_ok 60 LibSegJb_bcmB.regs0 LibSegJb_bcmB.regs_out0 KS_bcmB = true. Proof. vm_compute. reflexivity. Qed.
Definition bcmB_conc_s := ",4;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v29p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40S,2_v2#50S,8v23S,9v22S,12#7???8000B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Iv21#18Lav21v24La+v21#8+v24v25La+v21#10v29B#1000v24#7?????????>0Hv24#10B#693000v22#7??????????<Hv22#4P#7???7000#100000001000v22#4Ka+/v22#8#7???8000#1Mav22v26P_v2#1000#1000v22#4B#693000v23#7??????????<Hv23#4P#7???7000#100000001000v23#4Ka+/v23#8#7???8000#1Mav23v27P_v2#1000#1000v23#4Pv21#18v22#4Pv21#18v23#4B#v26#7???????B#v27#7???????La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#38v21La_v2#30+v24v25La_v2#28++v24v25#20La_v2#48#:<388La_v2#50v23B#v25#??>0Hv25#20B#1020v29#7???????????B#20_v29+v24v25#10000B#20_v29v24#10000Ka+/+v24v25#8#7???8000#4I+v24v25#20P#7???7000#100000001000+v24v25#20B#1000+v24v25#7?????????>0P_v2#1000#1000+v24v25#20Pv21#18+v24v25#20Pv22#4+v24v25#20Pv23#4+v24v25#20P#10000#683000+v24v25#20,4++v24v25##20_v2#50#10_v2#30#8+v21#8#8,1,12X#:<858#:<448Y,T,1v2;T,2v2T,8v2<T,9v2=T,:v21T,;++v24v25#20T,<#T,=++v24v25#20T,>#7???8000T,?#T,12v2>Lb+v21#8++v24v25#20Lb++v24v25#18#Nb++v24v25#10#Lb++v24v25#8v27Mb+v24v25v26"%pstring.
Lemma bcmB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bcmB] fx R M V bcmB_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bcmB] LibSegJb_bcmB.regs0 LibSegJb_bcmB.kn0 LibSegJb_bcmB.BR LibSegJb_bcmB.PSS LibSegJb_bcmB.NX0 LibSegJb_bcmB.F0 706648 LibSegJb_bcmB.seg_sound_ax fx R M V bcmB_conc_s. Qed.
Definition KS_bcsA : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bcsA.regs0 LibSegJb_bcsA.regs_out0).
Lemma KS_bcsA_ok : BG.kept_ok 60 LibSegJb_bcsA.regs0 LibSegJb_bcsA.regs_out0 KS_bcsA = true. Proof. vm_compute. reflexivity. Qed.
Definition bcsA_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v29p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24v25La+v21#10v29B#1000v24#7?????????>0Hv24#10B#v25#??>0Hv25#20B#1020v29#7???????????B#20_v29+v24v25#10000B#20_v29v24#10000,1_v2#60#60,1,16X#;39>4#7;3?4Y,T,1#:<858T,2_v2#50T,8v23T,9v22T,:v24T,;v29T,<+v24v25T,=++v24v25#20T,>#1T,?#T,12#7???8000Lb_v2#50v23Lb_v2#48#;3:48Lb_v2#28++v24v25#20Lb_v2#30+v24v25Lb_v2#38v21Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bcsA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bcsA] fx R M V bcsA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bcsA] LibSegJb_bcsA.regs0 LibSegJb_bcsA.kn0 LibSegJb_bcsA.BR LibSegJb_bcsA.PSS LibSegJb_bcsA.NX0 LibSegJb_bcsA.F0 735716 LibSegJb_bcsA.seg_sound_ax fx R M V bcsA_conc_s. Qed.
Definition KS_bcsB : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bcsB.regs0 LibSegJb_bcsB.regs_out0).
Lemma KS_bcsB_ok : BG.kept_ok 60 LibSegJb_bcsB.regs0 LibSegJb_bcsB.regs_out0 KS_bcsB = true. Proof. vm_compute. reflexivity. Qed.
Definition bcsB_conc_s := ",4;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40A#v29p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40S,2_v2#50S,8v23S,9v22S,12#7???8000B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Iv21#18Lav21v24La+v21#8+v24v25La+v21#10v29B#1000v24#7?????????>0Hv24#10B#693000v22#7??????????<Hv22#4P#7???7000#100000001000v22#4Ka+/v22#8#7???8000#1Mav22v26P_v2#1000#1000v22#4B#693000v23#7??????????8Hv23#8P#7???7000#100000001000v23#8Ka+/v23#8#7???8000#1Lav23v27P_v2#1000#1000v23#8Pv21#18v22#4Pv21#18v23#8B#v26#7???????B#v27^#?#???????????????La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#38v21La_v2#30+v24v25La_v2#28++v24v25#20La_v2#48#;3:48La_v2#50v23B#v25#??>0Hv25#20B#1020v29#7???????????B#20_v29+v24v25#10000B#20_v29v24#10000Ka+/+v24v25#8#7???8000#4I+v24v25#20P#7???7000#100000001000+v24v25#20B#1000+v24v25#7?????????>0P_v2#1000#1000+v24v25#20Pv21#18+v24v25#20Pv22#4+v24v25#20Pv23#8+v24v25#20P#10000#683000+v24v25#20,4++v24v25##20_v2#50#10_v2#30#8+v21#8#8,1,12X#:<858#;3;08Y,T,1v2;T,2v2T,8v2<T,9v2=T,:v21T,;++v24v25#20T,<#T,=++v24v25#20T,>#7???8000T,?#T,12v2>Lb+v21#8++v24v25#20Lb++v24v25#18#Nb++v24v25#10#Lb++v24v25#8v27Mb+v24v25v26"%pstring.
Lemma bcsB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bcsB] fx R M V bcsB_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bcsB] LibSegJb_bcsB.regs0 LibSegJb_bcsB.kn0 LibSegJb_bcsB.BR LibSegJb_bcsB.PSS LibSegJb_bcsB.NX0 LibSegJb_bcsB.F0 706648 LibSegJb_bcsB.seg_sound_ax fx R M V bcsB_conc_s. Qed.
End PMBCOP1.
