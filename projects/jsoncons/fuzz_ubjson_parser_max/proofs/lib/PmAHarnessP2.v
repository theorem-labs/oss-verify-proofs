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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_haC LibSegJa_haD LibSegJa_haE LibSegJa_haF LibSegJa_haG LibSegJa_haH.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAHP2.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_haC : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haC.regs0 LibSegJa_haC.regs_out0).
Lemma KS_haC_ok : BG.kept_ok 64 LibSegJa_haC.regs0 LibSegJa_haC.regs_out0 KS_haC = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition haC_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16v22S,17v21S,18v28S,19#7???8000B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1,1+/v28#8#7???800<#22,1,28X#:7944#:81<0Y,T,1#:79=<T,:+v28#60T,;+v28#20T,<#8Nb+/v28#8#7???802=#Nb+/v28#8#7???802<#Nb+/v28#8#7???8027#Nb+/v28#8#7???8026#Nb+/v28#8#7???8025#Nb+/v28#8#7???8024#Nb+/v28#8#7???802;#Nb+/v28#8#7???802:#Nb+/v28#8#7???8029#Nb+/v28#8#7???8028#Nb+/v28#8#7???801?#Nb+/v28#8#7???801>#Nb+/v28#8#7???801=#Nb+/v28#8#7???801<#Nb+/v28#8#7???8023#Nb+/v28#8#7???8022#Nb+/v28#8#7???8021#Nb+/v28#8#7???8020#Nb+/v28#8#7???8017#Nb+/v28#8#7???8016#Nb+/v28#8#7???8015#Nb+/v28#8#7???8014#Nb+/v28#8#7???801;#Nb+/v28#8#7???801:#Nb+/v28#8#7???8019#Nb+/v28#8#7???8018#Nb+/v28#8#7???800?#Nb+/v28#8#7???800>#Nb+/v28#8#7???800=#Nb+/v28#8#7???800<#Nb+/v28#8#7???8013#Nb+/v28#8#7???8012#Nb+/v28#8#7???8011#Nb+/v28#8#7???8010#"%pstring.
Lemma haC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haC] fx R M V haC_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haC] LibSegJa_haC.regs0 LibSegJa_haC.kn0 LibSegJa_haC.BR LibSegJa_haC.PSS LibSegJa_haC.NX0 LibSegJa_haC.F0 686404 LibSegJa_haC.seg_sound_ax fx R M V haC_conc_s. Qed.
Definition KS_haD : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haD.regs0 LibSegJa_haD.regs_out0).
Lemma KS_haD_ok : BG.kept_ok 64 LibSegJa_haD.regs0 LibSegJa_haD.regs_out0 KS_haD = true. Proof. vm_compute. reflexivity. Qed.
Definition haD_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16v22S,17v21S,18v28S,19#7???8000B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1,5+v28#1;0#8+v28#3:0#20+/v28#8#7???8036#1+/v28#8#7???803:#31+/v28#8#7???8074#4,1,4:X#:79=<#:;1;<Y,T,1#:7;08T,:+v28#1=0T,;+v28#60T,<+v28#3:0T,=_v2#68T,>#12<:98T,?#12<940T,17+v28#1=0T,1:+v28#1;0Mb+v28#3;8#400Mb+v28#3;<#Lb+v28#3;0#12<:<0Lb+v28#3:8#1000000Lb+v28#3:0#12<:98Nb+/v28#8#7???8076#Nb+/v28#8#7???8075#Nb+/v28#8#7???8074#Nb+/v28#8#7???806:#Nb+/v28#8#7???8077#Nb+/v28#8#7???8065#Nb+/v28#8#7???8064#Nb+/v28#8#7???8063#Nb+/v28#8#7???8062#Nb+/v28#8#7???8069#Nb+/v28#8#7???8068#Nb+/v28#8#7???8067#Nb+/v28#8#7???8066#Nb+/v28#8#7???805=#Nb+/v28#8#7???805<#Nb+/v28#8#7???805;#Nb+/v28#8#7???805:#Nb+/v28#8#7???8061#Nb+/v28#8#7???8060#Nb+/v28#8#7???805?#Nb+/v28#8#7???805>#Nb+/v28#8#7???8055#Nb+/v28#8#7???8054#Nb+/v28#8#7???8053#Nb+/v28#8#7???8052#Nb+/v28#8#7???8059#Nb+/v28#8#7???8058#Nb+/v28#8#7???8057#Nb+/v28#8#7???8056#Nb+/v28#8#7???804=#Nb+/v28#8#7???804<#Nb+/v28#8#7???804;#Nb+/v28#8#7???804:#Nb+/v28#8#7???8051#Nb+/v28#8#7???8050#Nb+/v28#8#7???804?#Nb+/v28#8#7???804>#Nb+/v28#8#7???8045#Nb+/v28#8#7???8044#Nb+/v28#8#7???8043#Nb+/v28#8#7???8042#Nb+/v28#8#7???8049#Nb+/v28#8#7???8048#Nb+/v28#8#7???8047#Nb+/v28#8#7???8046#Nb+/v28#8#7???803=#Nb+/v28#8#7???803<#Nb+/v28#8#7???803;#Nb+/v28#8#7???803:#Nb+/v28#8#7???8041#Nb+/v28#8#7???8040#Nb+/v28#8#7???803?#Nb+/v28#8#7???803>#Lb+v28#1;0#12<940Nb+/v28#8#7???8036#Jbv28#1;0Jb+v28#1;8#1>8Jb+v28#3<0#40"%pstring.
Lemma haD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haD] fx R M V haD_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haD] LibSegJa_haD.regs0 LibSegJa_haD.kn0 LibSegJa_haD.BR LibSegJa_haD.PSS LibSegJa_haD.NX0 LibSegJa_haD.F0 686556 LibSegJa_haD.seg_sound_ax fx R M V haD_conc_s. Qed.
Definition KS_haE : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haE.regs0 LibSegJa_haE.regs_out0).
Lemma KS_haE_ok : BG.kept_ok 64 LibSegJa_haE.regs0 LibSegJa_haE.regs_out0 KS_haE = true. Proof. vm_compute. reflexivity. Qed.
Definition haE_conc_s := ",22A#v2p#2#40A#v22p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16v22S,17+v28#1=0S,18v28S,19#7???8000S,1:+v28#1;0B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1Ka+/v28#8#7???806:#1,4+v28#350#8+v28#3>0#4+/v28#8#7???8074#4+/v28#8#7???807<#2,1,12X#:7;08#=45;8Y,T,1#:7;48T,:+v28#350T,;#T,16+v28#3>0T,1:^#?#??????????????8Mb+v28#3>0#Nb+/v28#8#7???8077#?8Nb+/v28#8#7???8076#?8Nb+/v28#8#7???8075#?8Nb+/v28#8#7???8074#?8Nb+/v28#8#7???807=#Nb+/v28#8#7???807<#Lb+v28#350+v28#1;0Jbv28#350Jb+v28#358#88Jb+v28#3>4#1<"%pstring.
Lemma haE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_haE] fx R M V haE_conc_s).
Proof. r1pf L5KA.zeros_at [KS_haE] LibSegJa_haE.regs0 LibSegJa_haE.kn0 LibSegJa_haE.BR LibSegJa_haE.PSS LibSegJa_haE.NX0 LibSegJa_haE.F0 686856 LibSegJa_haE.seg_sound_ax fx R M V haE_conc_s. Qed.
Definition KS_haF : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haF.regs0 LibSegJa_haF.regs_out0).
Lemma KS_haF_ok : BG.kept_ok 64 LibSegJa_haF.regs0 LibSegJa_haF.regs_out0 KS_haF = true. Proof. vm_compute. reflexivity. Qed.
Definition haF_conc_s := ",20A#v2p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16+v28#3>0S,17+v28#1=0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1,1+v28#3>8#8,1,7X#:7;48#:;?84Y,T,1#:7;54T,:+v28#1=0Lb+v28#3>8r:Jbv28#3>8Jb+v28#3?0#10"%pstring.
Lemma haF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haF] fx R M V haF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haF] LibSegJa_haF.regs0 LibSegJa_haF.kn0 LibSegJa_haF.BR LibSegJa_haF.PSS LibSegJa_haF.NX0 LibSegJa_haF.F0 686920 LibSegJa_haF.seg_sound_ax fx R M V haF_conc_s. Qed.
Definition KS_haG : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haG.regs0 LibSegJa_haG.regs_out0).
Lemma KS_haG_ok : BG.kept_ok 64 LibSegJa_haG.regs0 LibSegJa_haG.regs_out0 KS_haG = true. Proof. vm_compute. reflexivity. Qed.
Definition haG_conc_s := ",22A#v2p#2#40A#v23p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16+v28#3>0S,17+v28#1=0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1La+v28#350v23,,1,6X#:7;54#:<16<Y,T,1#:7;64T,:+v28#1=0T,;v23T,<+v28#3>0"%pstring.
Lemma haG_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haG] fx R M V haG_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haG] LibSegJa_haG.regs0 LibSegJa_haG.kn0 LibSegJa_haG.BR LibSegJa_haG.PSS LibSegJa_haG.NX0 LibSegJa_haG.F0 686932 LibSegJa_haG.seg_sound_ax fx R M V haG_conc_s. Qed.
Definition KS_haH : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haH.regs0 LibSegJa_haH.regs_out0).
Lemma KS_haH_ok : BG.kept_ok 64 LibSegJa_haH.regs0 LibSegJa_haH.regs_out0 KS_haH = true. Proof. vm_compute. reflexivity. Qed.
Definition haH_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16v22S,17+v28#1=0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1,3_v2#68#8+v28#1=0#8+/v28#8#7???807<#2,1,;X#:7;64#::5;4Y,T,1#:7;8<T,:_v2#68T,16^#?#??????????????8Lb_v2#68+v28#338Lb+v28#1=0#12<;18Nb+/v28#8#7???807=#?8Nb+/v28#8#7???807<#?8Jbv28#1=0Jb+v28#1=8#228"%pstring.
Lemma haH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haH] fx R M V haH_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haH] LibSegJa_haH.regs0 LibSegJa_haH.kn0 LibSegJa_haH.BR LibSegJa_haH.PSS LibSegJa_haH.NX0 LibSegJa_haH.F0 686948 LibSegJa_haH.seg_sound_ax fx R M V haH_conc_s. Qed.
End PMAHP2.
