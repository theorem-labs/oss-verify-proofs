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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ju0PlanKit AsanPlanCore
BigLinkBase BigLinkGlueUb0 L5Defs L5KnU L5KnAU.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJu_uicA LibSegJu_uicB LibSegJu_uicCs1 LibSegJu_uicCs2 LibSegJu_uicCl1a LibSegJu_uicCl1b LibSegJu_uicCl2 LibSegJu_uicCl3 LibSegJu_uicCl4.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConcU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMISUP.
Module BG := BigLinkGlueUb0.BGU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConcU.
Definition KS_uicA : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uicA.regs0 LibSegJu_uicA.regs_out0).
Lemma KS_uicA_ok : BG.kept_ok 52 LibSegJu_uicA.regs0 LibSegJu_uicA.regs_out0 KS_uicA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition uicA_conc_s := ",11A#v2p#2#40A#v21p#2#40A#v27p#2#40S,2v2S,:v21S,;+v21v27S,<#8B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8O#10000#;7120,3_v2#=0#=0+v21##10+v21#78#88,1,21X#34550#80910Y,T,1#345=8T,2_v2#50T,8v21T,9+v21v27T,:+v21#:8T,12#8T,13+v21#10T,14+v21#78T,15#;3;20T,16#;3;10T,17#;3:=0Kb+v21#;0#50Mb+v21#98#Lb+v21#90#Lb+v21#88#6Mb+v21#80#1002Lb+v21#:0+v21#10Mb+v21#9<#Lb+v21#8#Lb+v21#78#;3;80Lbv21#;3;58Lb+v21#:8#Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma uicA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_uicA] fx R M V uicA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_uicA] LibSegJu_uicA.regs0 LibSegJu_uicA.kn0 LibSegJu_uicA.BR LibSegJu_uicA.PSS LibSegJu_uicA.NX0 LibSegJu_uicA.F0 214352 LibSegJu_uicA.seg_sound_ax fx R M V uicA_conc_s. Qed.
Definition KS_uicB : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uicB.regs0 LibSegJu_uicB.regs_out0).
Lemma KS_uicB_ok : BG.kept_ok 52 LibSegJu_uicB.regs0 LibSegJu_uicB.regs_out0 KS_uicB = true. Proof. vm_compute. reflexivity. Qed.
Definition uicB_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v27p#2#40S,2_v2#50S,8v21S,9+v21v27S,12#8S,13+v21#10S,14+v21#78S,15#;3;20S,16#;3;10S,17#;3:=0B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8O#10000#;7120,5_v2#90#40+v21##8+v21#10#8+v21#78#8+v21#100#<,1,1<X#345=8#80910Y,T,1#35<;0T,2_v2#90T,8+v21#10T,9+v21#18T,:+v21#18T,;+v21v27T,<#8T,13#8T,14+v21v27T,15#;3978T,17#;3:>8Lb+v21#10#;3978Lb_v2#88#;3;20Lb_v2#80+v21#78Lb_v2#78+v21#10Lb_v2#70#8Lb_v2#68+v21v27Lb_v2#60v21Lb_v2#58#3460<Lb+v21#78#;3;10Lbv21#;3:>8Nb+v21#10:#??Nb+v21#109#??Nb+v21#108#??Lb+v21#100#Nb+v21#10;#??"%pstring.
Lemma uicB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uicB] fx R M V uicB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uicB] LibSegJu_uicB.regs0 LibSegJu_uicB.kn0 LibSegJu_uicB.BR LibSegJu_uicB.PSS LibSegJu_uicB.NX0 LibSegJu_uicB.F0 214488 LibSegJu_uicB.seg_sound_ax fx R M V uicB_conc_s. Qed.
Definition KS_uicCs1 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uicCs1.regs0 LibSegJu_uicCs1.regs_out0).
Lemma KS_uicCs1_ok : BG.kept_ok 52 LibSegJu_uicCs1.regs0 LibSegJu_uicCs1.regs_out0 KS_uicCs1 = true. Proof. vm_compute. reflexivity. Qed.
Definition uicCs1_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#90S,8+v21#10S,9+v21#18S,13#8S,14+v21v27S,15#;3978B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8O#10000#;7120Na+v21v27v26B#v26#??Fv26#fLa+v21v27v23La++v21v27#8v24La++v21v27#10v25,2+v21#10#8+v21#20#54,1,10X#35<;0#35<?4Y,T,1#35<?4T,:+v21#50T,;v23T,<v24T,=#T,>#T,12+v21#50Lb+v21#50v23Lb+v21#58v24Lb+v21#60v25Mb+v21#70#8Lb+v21#68#Lb+v21#10#;39?8Kb+v21#20#30"%pstring.
Lemma uicCs1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_uicCs1] fx R M V uicCs1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_uicCs1] LibSegJu_uicCs1.regs0 LibSegJu_uicCs1.kn0 LibSegJu_uicCs1.BR LibSegJu_uicCs1.PSS LibSegJu_uicCs1.NX0 LibSegJu_uicCs1.F0 220336 LibSegJu_uicCs1.seg_sound_ax fx R M V uicCs1_conc_s. Qed.
Definition KS_uicCs2 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uicCs2.regs0 LibSegJu_uicCs2.regs_out0).
Lemma KS_uicCs2_ok : BG.kept_ok 52 LibSegJu_uicCs2.regs0 LibSegJu_uicCs2.regs_out0 KS_uicCs2 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition uicCs2_conc_s := ",2<A#v2p#2#40A#v21p#2#40A#v26p#2#40A#v27p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40S,2_v2#90S,8+v21#10B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8La_v2#58#3460<La_v2#60v21La_v2#68+v21v27La_v2#70#8La_v2#78+v21#10La_v2#80+v21#78La_v2#88#;3;20La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#28v2?La_v2#30v30La_v2#38v31La_v2#40v32La_v2#48v33Na+v21#50v26B#v26#2<Fv26#fMa+v21#70#8,3_v2#<0#30+v21#20#18+v21#68#8,1,15X#35<?4#34634Y,T,1v2;T,2v2T,8v2<T,9v2=T,:#T,;#T,<++v21/v26#2#51T,=#1T,>#T,12v2>T,13v2?T,14v30T,15v31T,16v32T,17v33Lb+v21#68++v21/v26#2#51Lb+v21#30++v21/v26#2#51Lb+v21#28+v21#51Lb+v21#20+v21#51"%pstring.
Lemma uicCs2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uicCs2] fx R M V uicCs2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uicCs2] LibSegJu_uicCs2.regs0 LibSegJu_uicCs2.kn0 LibSegJu_uicCs2.BR LibSegJu_uicCs2.PSS LibSegJu_uicCs2.NX0 LibSegJu_uicCs2.F0 220404 LibSegJu_uicCs2.seg_sound_ax fx R M V uicCs2_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_uicCl1a : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uicCl1a.regs0 LibSegJu_uicCl1a.regs_out0).
Lemma KS_uicCl1a_ok : BG.kept_ok 52 LibSegJu_uicCl1a.regs0 LibSegJu_uicCl1a.regs_out0 KS_uicCl1a = true. Proof. vm_compute. reflexivity. Qed.
Definition uicCl1a_conc_s := ",1<A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#90S,8+v21#10S,9+v21#18S,13#8S,14+v21v27S,15#;3978B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8O#10000#;7120Na+v21v27v26B#v26#??Fv26#tLa++v21v27#8v28La++v21v27#10v24B#17v28#2<,3_v2#<0#30+v21#10#8+v21#20#54,1,1;X#35<;0#:?0><Y,T,1#57;88T,2_v2#<0T,8v28T,9+v21#50T,:#30T,;#2<T,<#1>T,=#T,>#1T,12+v21#50T,13v24T,14#2?Lb_v2#<0+v21v27Lb_v2#;8#8Lb_v2#;0+v21#50Lb_v2#:8+v21#18Lb_v2#:0+v21#10Lb_v2#98#35<?4Mb+v21#70#8Lb+v21#68#Lb+v21#60#Lb+v21#58#Lb+v21#50#Lb+v21#10#;39?8Kb+v21#20#30"%pstring.
Lemma uicCl1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_uicCl1a] fx R M V uicCl1a_conc_s).
Proof. r1pf L5KA.zeros_at [KS_uicCl1a] LibSegJu_uicCl1a.regs0 LibSegJu_uicCl1a.kn0 LibSegJu_uicCl1a.BR LibSegJu_uicCl1a.PSS LibSegJu_uicCl1a.NX0 LibSegJu_uicCl1a.F0 220336 LibSegJu_uicCl1a.seg_sound_ax fx R M V uicCl1a_conc_s. Qed.
Definition KS_uicCl1b : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uicCl1b.regs0 LibSegJu_uicCl1b.regs_out0).
Lemma KS_uicCl1b_ok : BG.kept_ok 52 LibSegJu_uicCl1b.regs0 LibSegJu_uicCl1b.regs_out0 KS_uicCl1b = true. Proof. vm_compute. reflexivity. Qed.
Definition uicCl1b_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#90S,8+v21#10S,9+v21#18S,13#8S,14+v21v27S,15#;3978B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8O#10000#;7120Na+v21v27v26B#v26#??Fv26#tLa++v21v27#8v28La++v21v27#10v24B#2=v28#3??????B#2?|v28#7#4000007,3_v2#<0#30+v21#10#8+v21#20#54,1,1;X#35<;0#:?0><Y,T,1#57;88T,2_v2#<0T,8v28T,9+v21#50T,:+*#8/v28#8#8T,;#2<T,<#1>T,=#T,>#1T,12+v21#50T,13v24T,14+*#8/v28#8#7Lb_v2#<0+v21v27Lb_v2#;8#8Lb_v2#;0+v21#50Lb_v2#:8+v21#18Lb_v2#:0+v21#10Lb_v2#98#35<?4Mb+v21#70#8Lb+v21#68#Lb+v21#60#Lb+v21#58#Lb+v21#50#Lb+v21#10#;39?8Kb+v21#20#30"%pstring.
Lemma uicCl1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_uicCl1b] fx R M V uicCl1b_conc_s).
Proof. r1pf L5KA.zeros_at [KS_uicCl1b] LibSegJu_uicCl1b.regs0 LibSegJu_uicCl1b.kn0 LibSegJu_uicCl1b.BR LibSegJu_uicCl1b.PSS LibSegJu_uicCl1b.NX0 LibSegJu_uicCl1b.F0 220336 LibSegJu_uicCl1b.seg_sound_ax fx R M V uicCl1b_conc_s. Qed.
Definition KS_uicCl2 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uicCl2.regs0 LibSegJu_uicCl2.regs_out0).
Lemma KS_uicCl2_ok : BG.kept_ok 52 LibSegJu_uicCl2.regs0 LibSegJu_uicCl2.regs_out0 KS_uicCl2 = true. Proof. vm_compute. reflexivity. Qed.
Definition uicCl2_conc_s := ",8A#v2p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#<0S,8v28S,:v29S,13v24,,1,6X#57;88#::1;4Y,T,1#57;98T,;v24T,<v28T,12v29"%pstring.
Lemma uicCl2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uicCl2] fx R M V uicCl2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uicCl2] LibSegJu_uicCl2.regs0 LibSegJu_uicCl2.kn0 LibSegJu_uicCl2.BR LibSegJu_uicCl2.PSS LibSegJu_uicCl2.NX0 LibSegJu_uicCl2.F0 359304 LibSegJu_uicCl2.seg_sound_ax fx R M V uicCl2_conc_s. Qed.
Definition KS_uicCl3 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uicCl3.regs0 LibSegJu_uicCl3.regs_out0).
Lemma KS_uicCl3_ok : BG.kept_ok 52 LibSegJu_uicCl3.regs0 LibSegJu_uicCl3.regs_out0 KS_uicCl3 = true. Proof. vm_compute. reflexivity. Qed.
Definition uicCl3_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#<0S,8v28S,9+v21#50S,12v29S,14v2:B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8La_v2#98#35<?4La_v2#:0+v21#10La_v2#:8+v21#18La_v2#;0+v21#50La_v2#;8#8La_v2#<0+v21v27B#1000v29#800000000000B#17v28#3??????B#2?v2:#4000007I+v29v28#1P_v2#=0#=0+v29v28#1Pv21#110+v29v28#1,2+v21#50#18++v29v28##1,1,>X#57;98#35<?4Y,T,1#35<?4T,2_v2#90T,8+v21#10T,9+v21#18T,:+v21#50T,12+v21#50T,13#8T,14+v21v27Nb+v28v29#Lb+v21#60v29Lb+v21#58v28Lb+v21#50+v2:#2"%pstring.
Lemma uicCl3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uicCl3] fx R M V uicCl3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uicCl3] LibSegJu_uicCl3.regs0 LibSegJu_uicCl3.kn0 LibSegJu_uicCl3.BR LibSegJu_uicCl3.PSS LibSegJu_uicCl3.NX0 LibSegJu_uicCl3.F0 359320 LibSegJu_uicCl3.seg_sound_ax fx R M V uicCl3_conc_s. Qed.
Definition KS_uicCl4 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJu_uicCl4.regs0 LibSegJu_uicCl4.regs_out0).
Lemma KS_uicCl4_ok : BG.kept_ok 52 LibSegJu_uicCl4.regs0 LibSegJu_uicCl4.regs_out0 KS_uicCl4 = true. Proof. vm_compute. reflexivity. Qed.
Definition uicCl4_conc_s := ",32A#v2p#2#40A#v21p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40S,2_v2#90S,8+v21#10B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8La_v2#58#3460<La_v2#60v21La_v2#68+v21v27La_v2#70#8La_v2#78+v21#10La_v2#80+v21#78La_v2#88#;3;20La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#28v2?La_v2#30v30La_v2#38v31La_v2#40v32La_v2#48v33Na+v21#50v26B#v26#??Fv26#tLa+v21#58v28La+v21#60v29Ma+v21#70#8B#1000v29#800000000000B#17v28#3??????,3_v2#<0#30+v21#20#18+v21#68#8,1,15X#35<?4#34634Y,T,1v2;T,2v2T,8v2<T,9v2=T,:#T,;#1T,<+v28v29T,=#1T,>#T,12v2>T,13v2?T,14v30T,15v31T,16v32T,17v33Lb+v21#68+v28v29Lb+v21#30+v28v29Lb+v21#28v29Lb+v21#20v29"%pstring.
Lemma uicCl4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_uicCl4] fx R M V uicCl4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_uicCl4] LibSegJu_uicCl4.regs0 LibSegJu_uicCl4.kn0 LibSegJu_uicCl4.BR LibSegJu_uicCl4.PSS LibSegJu_uicCl4.NX0 LibSegJu_uicCl4.F0 220404 LibSegJu_uicCl4.seg_sound_ax fx R M V uicCl4_conc_s. Qed.
End PMISUP.
