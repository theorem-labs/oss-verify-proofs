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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_haNs LibSegJb_haNl LibSegJb_haO LibSegJb_haQt LibSegJb_haR0 LibSegJb_haR16.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBHP4.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_haNs : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJb_haNs.regs0 LibSegJb_haNs.regs_out0).
Lemma KS_haNs_ok : BG.kept_ok 64 LibSegJb_haNs.regs0 LibSegJb_haNs.regs_out0 KS_haNs = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition haNs_conc_s := ",24A#v2p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16#132048S,17+v28#1=0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1Na+v28#20v24B#v24#??Fv24#f,1+/v28#8#7???800<#22,1,26X#:7??<#:80:4Y,T,:#T,15^#?#??????????????8Nb+/v28#8#7???802=#?8Nb+/v28#8#7???802<#?8Nb+/v28#8#7???8027#?8Nb+/v28#8#7???8026#?8Nb+/v28#8#7???8025#?8Nb+/v28#8#7???8024#?8Nb+/v28#8#7???802;#?8Nb+/v28#8#7???802:#?8Nb+/v28#8#7???8029#?8Nb+/v28#8#7???8028#?8Nb+/v28#8#7???801?#?8Nb+/v28#8#7???801>#?8Nb+/v28#8#7???801=#?8Nb+/v28#8#7???801<#?8Nb+/v28#8#7???8023#?8Nb+/v28#8#7???8022#?8Nb+/v28#8#7???8021#?8Nb+/v28#8#7???8020#?8Nb+/v28#8#7???8017#?8Nb+/v28#8#7???8016#?8Nb+/v28#8#7???8015#?8Nb+/v28#8#7???8014#?8Nb+/v28#8#7???801;#?8Nb+/v28#8#7???801:#?8Nb+/v28#8#7???8019#?8Nb+/v28#8#7???8018#?8Nb+/v28#8#7???800?#?8Nb+/v28#8#7???800>#?8Nb+/v28#8#7???800=#?8Nb+/v28#8#7???800<#?8Nb+/v28#8#7???8013#?8Nb+/v28#8#7???8012#?8Nb+/v28#8#7???8011#?8Nb+/v28#8#7???8010#?8"%pstring.
Lemma haNs_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haNs] fx R M V haNs_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haNs] LibSegJb_haNs.regs0 LibSegJb_haNs.kn0 LibSegJb_haNs.BR LibSegJb_haNs.PSS LibSegJb_haNs.NX0 LibSegJb_haNs.F0 688124 LibSegJb_haNs.seg_sound_ax fx R M V haNs_conc_s. Qed.
Definition KS_haNl : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJb_haNl.regs0 LibSegJb_haNl.regs_out0).
Lemma KS_haNl_ok : BG.kept_ok 64 LibSegJb_haNl.regs0 LibSegJb_haNl.regs_out0 KS_haNl = true. Proof. vm_compute. reflexivity. Qed.
Definition haNl_conc_s := ",28A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16#132048S,17+v28#1=0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1Na+v28#20v24B#v24#??Fv24#tLa+v28#20v25La+v28#30v26,1+/v28#8#7???800<#22,1,28X#:7??<#=0890Y,T,1#:80:4T,:v26T,;*#2/v25#2T,15^#?#??????????????8Nb+/v28#8#7???802=#?8Nb+/v28#8#7???802<#?8Nb+/v28#8#7???8027#?8Nb+/v28#8#7???8026#?8Nb+/v28#8#7???8025#?8Nb+/v28#8#7???8024#?8Nb+/v28#8#7???802;#?8Nb+/v28#8#7???802:#?8Nb+/v28#8#7???8029#?8Nb+/v28#8#7???8028#?8Nb+/v28#8#7???801?#?8Nb+/v28#8#7???801>#?8Nb+/v28#8#7???801=#?8Nb+/v28#8#7???801<#?8Nb+/v28#8#7???8023#?8Nb+/v28#8#7???8022#?8Nb+/v28#8#7???8021#?8Nb+/v28#8#7???8020#?8Nb+/v28#8#7???8017#?8Nb+/v28#8#7???8016#?8Nb+/v28#8#7???8015#?8Nb+/v28#8#7???8014#?8Nb+/v28#8#7???801;#?8Nb+/v28#8#7???801:#?8Nb+/v28#8#7???8019#?8Nb+/v28#8#7???8018#?8Nb+/v28#8#7???800?#?8Nb+/v28#8#7???800>#?8Nb+/v28#8#7???800=#?8Nb+/v28#8#7???800<#?8Nb+/v28#8#7???8013#?8Nb+/v28#8#7???8012#?8Nb+/v28#8#7???8011#?8Nb+/v28#8#7???8010#?8"%pstring.
Lemma haNl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haNl] fx R M V haNl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haNl] LibSegJb_haNl.regs0 LibSegJb_haNl.kn0 LibSegJb_haNl.BR LibSegJb_haNl.PSS LibSegJb_haNl.NX0 LibSegJb_haNl.F0 688124 LibSegJb_haNl.seg_sound_ax fx R M V haNl_conc_s. Qed.
Definition KS_haO : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJb_haO.regs0 LibSegJb_haO.regs_out0).
Lemma KS_haO_ok : BG.kept_ok 64 LibSegJb_haO.regs0 LibSegJb_haO.regs_out0 KS_haO = true. Proof. vm_compute. reflexivity. Qed.
Definition haO_conc_s := ",20A#v2p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15^#?#??????????????8S,16#132048S,17+v28#1=0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1,2+/v28#8#7???8004#3+v28##8,1,:X#:80:4#7;284Y,T,1#:80<<T,:+/v28#8#7???8000T,;#80Lbv28#45>0360>Nb+/v28#8#7???8006#?8Nb+/v28#8#7???8005#?8Nb+/v28#8#7???8004#?8Jb+v28#8#3?8"%pstring.
Lemma haO_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haO] fx R M V haO_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haO] LibSegJb_haO.regs0 LibSegJb_haO.kn0 LibSegJb_haO.BR LibSegJb_haO.PSS LibSegJb_haO.NX0 LibSegJb_haO.F0 688292 LibSegJb_haO.seg_sound_ax fx R M V haO_conc_s. Qed.
Definition KS_haQt : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJb_haQt.regs0 LibSegJb_haQt.regs_out0).
Lemma KS_haQt_ok : BG.kept_ok 64 LibSegJb_haQt.regs0 LibSegJb_haQt.regs_out0 KS_haQt = true. Proof. vm_compute. reflexivity. Qed.
Definition haQt_conc_s := ",6A#v2p#2#40S,2v2O#12=000#136000La#13<:38#7???8000Ma#13<:40#1La#1363;0#126;>8,,1,5X#7;284#126;>8Y,T,6#126;>8T,;#?5U,<,;"%pstring.
Lemma haQt_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haQt] fx R M V haQt_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haQt] LibSegJb_haQt.regs0 LibSegJb_haQt.kn0 LibSegJb_haQt.BR LibSegJb_haQt.PSS LibSegJb_haQt.NX0 LibSegJb_haQt.F0 504452 LibSegJb_haQt.seg_sound_ax fx R M V haQt_conc_s. Qed.
Definition KS_haR0 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJb_haR0.regs0 LibSegJb_haR0.regs_out0).
Lemma KS_haR0_ok : BG.kept_ok 64 LibSegJb_haR0.regs0 LibSegJb_haR0.regs_out0 KS_haR0 = true. Proof. vm_compute. reflexivity. Qed.
Definition haR0_conc_s := ",39A#v2p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,8v2S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15^#?#??????????????8S,16#132048S,17+v28#1=0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1La_v2#8v2:La_v2#10v2;La_v2#18v2<La_v2#20v2=La_v2#28v2>La_v2#30v2?La_v2#38v30La_v2#40v31La_v2#48v32La_v2#50v33La_v2#58v34La_v2#60v35,1+v29##1,1,11X#:80<<#:8118Y,T,1v2:T,2v2T,8v2;T,9v2<T,:#T,12v2=T,13v2>T,14v2?T,15v30T,16v31T,17v32T,18v33T,19v34T,1:v35Nbv29#"%pstring.
Lemma haR0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haR0] fx R M V haR0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haR0] LibSegJb_haR0.regs0 LibSegJb_haR0.kn0 LibSegJb_haR0.BR LibSegJb_haR0.PSS LibSegJb_haR0.NX0 LibSegJb_haR0.F0 688332 LibSegJb_haR0.seg_sound_ax fx R M V haR0_conc_s. Qed.
Definition KS_haR16 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJb_haR16.regs0 LibSegJb_haR16.regs_out0).
Lemma KS_haR16_ok : BG.kept_ok 64 LibSegJb_haR16.regs0 LibSegJb_haR16.regs_out0 KS_haR16 = true. Proof. vm_compute. reflexivity. Qed.
Definition haR16_conc_s := ",39A#v2p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40A#v35p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,8+v2#10S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15^#?#??????????????8S,16#132048S,17+v28#1=0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#7??????????0Hv2#20I_v2#80#90B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1La+v2#8v2:Lav2v2;La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33La_v2#48v34La_v2#50v35,1+v29##1,1,11X#:80<<#:8118Y,T,1v2:T,2+v2#10T,8v2;T,9v2<T,:#T,12v2=T,13v2>T,14v2?T,15v30T,16v31T,17v32T,18v33T,19v34T,1:v35Nbv29#"%pstring.
Lemma haR16_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haR16] fx R M V haR16_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haR16] LibSegJb_haR16.regs0 LibSegJb_haR16.kn0 LibSegJb_haR16.BR LibSegJb_haR16.PSS LibSegJb_haR16.NX0 LibSegJb_haR16.F0 688332 LibSegJb_haR16.seg_sound_ax fx R M V haR16_conc_s. Qed.
End PMBHP4.
