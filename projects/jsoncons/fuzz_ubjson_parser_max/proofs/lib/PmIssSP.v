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
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Js0PlanKit AsanPlanCore
BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_icA LibSegJs_icB LibSegJs_icCs1 LibSegJs_icCs2 LibSegJs_icCl1a LibSegJs_icCl1b LibSegJs_icCl2 LibSegJs_icCl3 LibSegJs_icCl4.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMISP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_icA : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_icA.regs0 LibSegJs_icA.regs_out0).
Lemma KS_icA_ok : BG.kept_ok 52 LibSegJs_icA.regs0 LibSegJs_icA.regs_out0 KS_icA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition icA_conc_s := ",11A#v2p#2#40A#v21p#2#40A#v27p#2#40S,2v2S,:v21S,;+v21v27S,<#8B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8O#10000#;60=0,3_v2#=0#=0+v21##10+v21#78#88,1,21X#342>4#7?8;<Y,T,1#3436<T,2_v2#50T,8v21T,9+v21v27T,:+v21#:8T,12#8T,13+v21#10T,14+v21#78T,15#;2:=0T,16#;2:<0T,17#;2:80Kb+v21#;0#50Mb+v21#98#Lb+v21#90#Lb+v21#88#6Mb+v21#80#1002Lb+v21#:0+v21#10Mb+v21#9<#Lb+v21#8#Lb+v21#78#;2;30Lbv21#;2;08Lb+v21#:8#Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma icA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_icA] fx R M V icA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_icA] LibSegJs_icA.regs0 LibSegJs_icA.kn0 LibSegJs_icA.BR LibSegJs_icA.PSS LibSegJs_icA.NX0 LibSegJs_icA.F0 213732 LibSegJs_icA.seg_sound_ax fx R M V icA_conc_s. Qed.
Definition KS_icB : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_icB.regs0 LibSegJs_icB.regs_out0).
Lemma KS_icB_ok : BG.kept_ok 52 LibSegJs_icB.regs0 LibSegJs_icB.regs_out0 KS_icB = true. Proof. vm_compute. reflexivity. Qed.
Definition icB_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v27p#2#40S,2_v2#50S,8v21S,9+v21v27S,12#8S,13+v21#10S,14+v21#78S,15#;2:=0S,16#;2:<0S,17#;2:80B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8O#10000#;60=0,5_v2#90#40+v21##8+v21#10#8+v21#78#8+v21#100#<,1,1<X#3436<#7?8;<Y,T,1#35414T,2_v2#90T,8+v21#10T,9+v21#18T,:+v21#18T,;+v21v27T,<#8T,13#8T,14+v21v27T,15#;2928T,17#;2:98Lb+v21#10#;2928Lb_v2#88#;2:=0Lb_v2#80+v21#78Lb_v2#78+v21#10Lb_v2#70#8Lb_v2#68+v21v27Lb_v2#60v21Lb_v2#58#343:0Lb+v21#78#;2:<0Lbv21#;2:98Nb+v21#10:#??Nb+v21#109#??Nb+v21#108#??Lb+v21#100#Nb+v21#10;#??"%pstring.
Lemma icB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_icB] fx R M V icB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_icB] LibSegJs_icB.regs0 LibSegJs_icB.kn0 LibSegJs_icB.BR LibSegJs_icB.PSS LibSegJs_icB.NX0 LibSegJs_icB.F0 213868 LibSegJs_icB.seg_sound_ax fx R M V icB_conc_s. Qed.
Definition KS_icCs1 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_icCs1.regs0 LibSegJs_icCs1.regs_out0).
Lemma KS_icCs1_ok : BG.kept_ok 52 LibSegJs_icCs1.regs0 LibSegJs_icCs1.regs_out0 KS_icCs1 = true. Proof. vm_compute. reflexivity. Qed.
Definition icCs1_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v27p#2#40S,2_v2#90S,8+v21#10S,9+v21#18S,13#8S,14+v21v27S,15#;2928B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8O#10000#;60=0Na+v21v27v26B#v26#??Fv26#fLa+v21v27v23La++v21v27#8v24La++v21v27#10v25,2+v21#10#8+v21#20#54,1,10X#35414#35458Y,T,1#35458T,:+v21#50T,;v23T,<v24T,=#T,>#T,12+v21#50Lb+v21#50v23Lb+v21#58v24Lb+v21#60v25Mb+v21#70#8Lb+v21#68#Lb+v21#10#;29:8Kb+v21#20#30"%pstring.
Lemma icCs1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_icCs1] fx R M V icCs1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_icCs1] LibSegJs_icCs1.regs0 LibSegJs_icCs1.kn0 LibSegJs_icCs1.BR LibSegJs_icCs1.PSS LibSegJs_icCs1.NX0 LibSegJs_icCs1.F0 218132 LibSegJs_icCs1.seg_sound_ax fx R M V icCs1_conc_s. Qed.
Definition KS_icCs2 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_icCs2.regs0 LibSegJs_icCs2.regs_out0).
Lemma KS_icCs2_ok : BG.kept_ok 52 LibSegJs_icCs2.regs0 LibSegJs_icCs2.regs_out0 KS_icCs2 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Definition icCs2_conc_s := ",2<A#v2p#2#40A#v21p#2#40A#v26p#2#40A#v27p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40S,2_v2#90S,8+v21#10B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8La_v2#58#343:0La_v2#60v21La_v2#68+v21v27La_v2#70#8La_v2#78+v21#10La_v2#80+v21#78La_v2#88#;2:=0La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#28v2?La_v2#30v30La_v2#38v31La_v2#40v32La_v2#48v33Na+v21#50v26B#v26#2<Fv26#fMa+v21#70#8,3_v2#;0#20+v21#20#18+v21#68#8,1,14X#35458#343<8Y,T,1v2;T,2v2T,8v2<T,9v2=T,:#T,;#T,<++v21/v26#2#51T,=#8T,12v2>T,13v2?T,14v30T,15v31T,16v32T,17v33Lb+v21#68++v21/v26#2#51Lb+v21#30++v21/v26#2#51Lb+v21#28+v21#51Lb+v21#20+v21#51"%pstring.
Lemma icCs2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_icCs2] fx R M V icCs2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_icCs2] LibSegJs_icCs2.regs0 LibSegJs_icCs2.kn0 LibSegJs_icCs2.BR LibSegJs_icCs2.PSS LibSegJs_icCs2.NX0 LibSegJs_icCs2.F0 218200 LibSegJs_icCs2.seg_sound_ax fx R M V icCs2_conc_s. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition KS_icCl1a : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_icCl1a.regs0 LibSegJs_icCl1a.regs_out0).
Lemma KS_icCl1a_ok : BG.kept_ok 52 LibSegJs_icCl1a.regs0 LibSegJs_icCl1a.regs_out0 KS_icCl1a = true. Proof. vm_compute. reflexivity. Qed.
Definition icCl1a_conc_s := ",1<A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#90S,8+v21#10S,9+v21#18S,13#8S,14+v21v27S,15#;2928B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8O#10000#;60=0Na+v21v27v26B#v26#??Fv26#tLa++v21v27#8v28La++v21v27#10v24B#17v28#2<,3_v2#<0#30+v21#10#8+v21#20#54,1,1;X#35414#:>098Y,T,1#56;34T,2_v2#<0T,8v28T,9+v21#50T,:#30T,;#2<T,<#1>T,=#T,>#1T,12+v21#50T,13v24T,14#2?Lb_v2#<0+v21v27Lb_v2#;8#8Lb_v2#;0+v21#50Lb_v2#:8+v21#18Lb_v2#:0+v21#10Lb_v2#98#35458Mb+v21#70#8Lb+v21#68#Lb+v21#60#Lb+v21#58#Lb+v21#50#Lb+v21#10#;29:8Kb+v21#20#30"%pstring.
Lemma icCl1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_icCl1a] fx R M V icCl1a_conc_s).
Proof. r1pf L5KA.zeros_at [KS_icCl1a] LibSegJs_icCl1a.regs0 LibSegJs_icCl1a.kn0 LibSegJs_icCl1a.BR LibSegJs_icCl1a.PSS LibSegJs_icCl1a.NX0 LibSegJs_icCl1a.F0 218132 LibSegJs_icCl1a.seg_sound_ax fx R M V icCl1a_conc_s. Qed.
Definition KS_icCl1b : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_icCl1b.regs0 LibSegJs_icCl1b.regs_out0).
Lemma KS_icCl1b_ok : BG.kept_ok 52 LibSegJs_icCl1b.regs0 LibSegJs_icCl1b.regs_out0 KS_icCl1b = true. Proof. vm_compute. reflexivity. Qed.
Definition icCl1b_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#90S,8+v21#10S,9+v21#18S,13#8S,14+v21v27S,15#;2928B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8O#10000#;60=0Na+v21v27v26B#v26#??Fv26#tLa++v21v27#8v28La++v21v27#10v24B#2=v28#3??????B#2?|v28#7#4000007,3_v2#<0#30+v21#10#8+v21#20#54,1,1;X#35414#:>098Y,T,1#56;34T,2_v2#<0T,8v28T,9+v21#50T,:+*#8/v28#8#8T,;#2<T,<#1>T,=#T,>#1T,12+v21#50T,13v24T,14+*#8/v28#8#7Lb_v2#<0+v21v27Lb_v2#;8#8Lb_v2#;0+v21#50Lb_v2#:8+v21#18Lb_v2#:0+v21#10Lb_v2#98#35458Mb+v21#70#8Lb+v21#68#Lb+v21#60#Lb+v21#58#Lb+v21#50#Lb+v21#10#;29:8Kb+v21#20#30"%pstring.
Lemma icCl1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_icCl1b] fx R M V icCl1b_conc_s).
Proof. r1pf L5KA.zeros_at [KS_icCl1b] LibSegJs_icCl1b.regs0 LibSegJs_icCl1b.kn0 LibSegJs_icCl1b.BR LibSegJs_icCl1b.PSS LibSegJs_icCl1b.NX0 LibSegJs_icCl1b.F0 218132 LibSegJs_icCl1b.seg_sound_ax fx R M V icCl1b_conc_s. Qed.
Definition KS_icCl2 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_icCl2.regs0 LibSegJs_icCl2.regs_out0).
Lemma KS_icCl2_ok : BG.kept_ok 52 LibSegJs_icCl2.regs0 LibSegJs_icCl2.regs_out0 KS_icCl2 = true. Proof. vm_compute. reflexivity. Qed.
Definition icCl2_conc_s := ",8A#v2p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40S,2_v2#<0S,8v28S,:v29S,13v24,,1,6X#56;34#:9160Y,T,1#56;44T,;v24T,<v28T,12v29"%pstring.
Lemma icCl2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_icCl2] fx R M V icCl2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_icCl2] LibSegJs_icCl2.regs0 LibSegJs_icCl2.kn0 LibSegJs_icCl2.BR LibSegJs_icCl2.PSS LibSegJs_icCl2.NX0 LibSegJs_icCl2.F0 355124 LibSegJs_icCl2.seg_sound_ax fx R M V icCl2_conc_s. Qed.
Definition KS_icCl3 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_icCl3.regs0 LibSegJs_icCl3.regs_out0).
Lemma KS_icCl3_ok : BG.kept_ok 52 LibSegJs_icCl3.regs0 LibSegJs_icCl3.regs_out0 KS_icCl3 = true. Proof. vm_compute. reflexivity. Qed.
Definition icCl3_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#<0S,8v28S,9+v21#50S,12v29S,14v2:B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8La_v2#98#35458La_v2#:0+v21#10La_v2#:8+v21#18La_v2#;0+v21#50La_v2#;8#8La_v2#<0+v21v27B#1000v29#800000000000B#17v28#3??????B#2?v2:#4000007I+v29v28#1P_v2#=0#=0+v29v28#1Pv21#110+v29v28#1,2+v21#50#18++v29v28##1,1,>X#56;44#35458Y,T,1#35458T,2_v2#90T,8+v21#10T,9+v21#18T,:+v21#50T,12+v21#50T,13#8T,14+v21v27Nb+v28v29#Lb+v21#60v29Lb+v21#58v28Lb+v21#50+v2:#2"%pstring.
Lemma icCl3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_icCl3] fx R M V icCl3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_icCl3] LibSegJs_icCl3.regs0 LibSegJs_icCl3.kn0 LibSegJs_icCl3.BR LibSegJs_icCl3.PSS LibSegJs_icCl3.NX0 LibSegJs_icCl3.F0 355140 LibSegJs_icCl3.seg_sound_ax fx R M V icCl3_conc_s. Qed.
Definition KS_icCl4 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJs_icCl4.regs0 LibSegJs_icCl4.regs_out0).
Lemma KS_icCl4_ok : BG.kept_ok 52 LibSegJs_icCl4.regs0 LibSegJs_icCl4.regs_out0 KS_icCl4 = true. Proof. vm_compute. reflexivity. Qed.
Definition icCl4_conc_s := ",32A#v2p#2#40A#v21p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40S,2_v2#90S,8+v21#10B#7???7?8000=0v2#800000000000Hv2#10I_v2#=0#=0B#7???7?8000=0v21#7????????>?0Hv21#8P_v2#=0#=0v21#110Iv21#110B#110v27#800000Hv27#8La_v2#58#343:0La_v2#60v21La_v2#68+v21v27La_v2#70#8La_v2#78+v21#10La_v2#80+v21#78La_v2#88#;2:=0La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>La_v2#28v2?La_v2#30v30La_v2#38v31La_v2#40v32La_v2#48v33Na+v21#50v26B#v26#??Fv26#tLa+v21#58v28La+v21#60v29Ma+v21#70#8B#1000v29#800000000000B#17v28#3??????,3_v2#;0#20+v21#20#18+v21#68#8,1,14X#35458#343<8Y,T,1v2;T,2v2T,8v2<T,9v2=T,:#T,;#1T,<+v28v29T,=#8T,12v2>T,13v2?T,14v30T,15v31T,16v32T,17v33Lb+v21#68+v28v29Lb+v21#30+v28v29Lb+v21#28v29Lb+v21#20v29"%pstring.
Lemma icCl4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_icCl4] fx R M V icCl4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_icCl4] LibSegJs_icCl4.regs0 LibSegJs_icCl4.kn0 LibSegJs_icCl4.BR LibSegJs_icCl4.PSS LibSegJs_icCl4.NX0 LibSegJs_icCl4.F0 218200 LibSegJs_icCl4.seg_sound_ax fx R M V icCl4_conc_s. Qed.
End PMISP.
