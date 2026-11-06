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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_haIs LibSegJa_haIl LibSegJa_haJ LibSegJa_haK1 LibSegJa_haK2s LibSegJa_haK2l LibSegJa_haL LibSegJa_haM.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAHP3.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_haIs : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haIs.regs0 LibSegJa_haIs.regs_out0).
Lemma KS_haIs_ok : BG.kept_ok 64 LibSegJa_haIs.regs0 LibSegJa_haIs.regs_out0 KS_haIs = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition haIs_conc_s := ",25A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16v22S,17+v28#1=0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1Na+v28#320v24B#v24#??Fv24#f,,1,4X#:7;8<#::34<Y,T,1#:7;;0T,:+v28#1>8"%pstring.
Lemma haIs_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haIs] fx R M V haIs_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haIs] LibSegJa_haIs.regs0 LibSegJa_haIs.kn0 LibSegJa_haIs.BR LibSegJa_haIs.PSS LibSegJa_haIs.NX0 LibSegJa_haIs.F0 686988 LibSegJa_haIs.seg_sound_ax fx R M V haIs_conc_s. Qed.
Definition KS_haIl : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haIl.regs0 LibSegJa_haIl.regs_out0).
Lemma KS_haIl_ok : BG.kept_ok 64 LibSegJa_haIl.regs0 LibSegJa_haIl.regs_out0 KS_haIl = true. Proof. vm_compute. reflexivity. Qed.
Definition haIl_conc_s := ",29A#v2p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16v22S,17+v28#1=0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1Na+v28#320v24B#v24#??Fv24#tLa+v28#320v25La+v28#330v26,,1,5X#:7;8<#<>:58Y,T,1#:7;:8T,:v26T,;*#2/v25#2"%pstring.
Lemma haIl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haIl] fx R M V haIl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haIl] LibSegJa_haIl.regs0 LibSegJa_haIl.kn0 LibSegJa_haIl.BR LibSegJa_haIl.PSS LibSegJa_haIl.NX0 LibSegJa_haIl.F0 686988 LibSegJa_haIl.seg_sound_ax fx R M V haIl_conc_s. Qed.
Definition KS_haJ : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haJ.regs0 LibSegJa_haJ.regs_out0).
Lemma KS_haJ_ok : BG.kept_ok 64 LibSegJa_haJ.regs0 LibSegJa_haJ.regs_out0 KS_haJ = true. Proof. vm_compute. reflexivity. Qed.
Definition haJ_conc_s := ",21A#v2p#2#40A#v22p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16v22S,17+v28#1=0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1,,1,4X#:7;:8#::34<Y,T,1#:7;;0T,:+v28#1>8"%pstring.
Lemma haJ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haJ] fx R M V haJ_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haJ] LibSegJa_haJ.regs0 LibSegJa_haJ.kn0 LibSegJa_haJ.BR LibSegJa_haJ.PSS LibSegJa_haJ.NX0 LibSegJa_haJ.F0 687016 LibSegJa_haJ.seg_sound_ax fx R M V haJ_conc_s. Qed.
Definition KS_haK1 : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haK1.regs0 LibSegJa_haK1.regs_out0).
Lemma KS_haK1_ok : BG.kept_ok 64 LibSegJa_haK1.regs0 LibSegJa_haK1.regs_out0 KS_haK1 = true. Proof. vm_compute. reflexivity. Qed.
Definition haK1_conc_s := ",25A#v2p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16^#?#??????????????8S,17+v28#1=0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1P#10000#681000v28#400P#10000#681000v29#1,2+/v28#8#7???8036#1+/v28#8#7???803:#31,1,36X#:7;;0#:7<80Y,T,:#132<60T,17#1302>0Nb+/v28#8#7???806:#?8Nb+/v28#8#7???8069#?8Nb+/v28#8#7???8064#?8Nb+/v28#8#7???8063#?8Nb+/v28#8#7???8062#?8Nb+/v28#8#7???8061#?8Nb+/v28#8#7???8068#?8Nb+/v28#8#7???8067#?8Nb+/v28#8#7???8066#?8Nb+/v28#8#7???8065#?8Nb+/v28#8#7???805<#?8Nb+/v28#8#7???805;#?8Nb+/v28#8#7???805:#?8Nb+/v28#8#7???8059#?8Nb+/v28#8#7???8060#?8Nb+/v28#8#7???805?#?8Nb+/v28#8#7???805>#?8Nb+/v28#8#7???805=#?8Nb+/v28#8#7???8054#?8Nb+/v28#8#7???8053#?8Nb+/v28#8#7???8052#?8Nb+/v28#8#7???8051#?8Nb+/v28#8#7???8058#?8Nb+/v28#8#7???8057#?8Nb+/v28#8#7???8056#?8Nb+/v28#8#7???8055#?8Nb+/v28#8#7???804<#?8Nb+/v28#8#7???804;#?8Nb+/v28#8#7???804:#?8Nb+/v28#8#7???8049#?8Nb+/v28#8#7???8050#?8Nb+/v28#8#7???804?#?8Nb+/v28#8#7???804>#?8Nb+/v28#8#7???804=#?8Nb+/v28#8#7???8044#?8Nb+/v28#8#7???8043#?8Nb+/v28#8#7???8042#?8Nb+/v28#8#7???8041#?8Nb+/v28#8#7???8048#?8Nb+/v28#8#7???8047#?8Nb+/v28#8#7???8046#?8Nb+/v28#8#7???8045#?8Nb+/v28#8#7???803<#?8Nb+/v28#8#7???803;#?8Nb+/v28#8#7???803:#?8Nb+/v28#8#7???8036#?8Nb+/v28#8#7???8040#?8Nb+/v28#8#7???803?#?8Nb+/v28#8#7???803>#?8Nb+/v28#8#7???803=#?8"%pstring.
Lemma haK1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haK1] fx R M V haK1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haK1] LibSegJa_haK1.regs0 LibSegJa_haK1.kn0 LibSegJa_haK1.BR LibSegJa_haK1.PSS LibSegJa_haK1.NX0 LibSegJa_haK1.F0 687024 LibSegJa_haK1.seg_sound_ax fx R M V haK1_conc_s. Qed.
Definition KS_haK2s : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haK2s.regs0 LibSegJa_haK2s.regs_out0).
Lemma KS_haK2s_ok : BG.kept_ok 64 LibSegJa_haK2s.regs0 LibSegJa_haK2s.regs_out0 KS_haK2s = true. Proof. vm_compute. reflexivity. Qed.
Definition haK2s_conc_s := ",2=A#v2p#2#40A#v24p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16^#?#??????????????8S,17#1302>0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1P#10000#681000v28#400P#10000#681000v29#1Ka+/v28#8#7???800<#22Ka#8001>05<#1Ka#8001>05?#1Ka#8001>052#1Na+v28#;0v24B#v24#??Fv24#f,3+v28#60#8+v28#70#8+v28#=8#8,1,=X#:7<80#?9?><Y,T,1#:7=24T,:+v28#78T,;#T,<#Lb+v28#70#130138Lb+v28#=8#1302=0Lb+v28#60#1302:8Jbv28#60Jb+v28#68#8Jb+v28#78#60Jb+v28#>0#320"%pstring.
Lemma haK2s_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_haK2s] fx R M V haK2s_conc_s).
Proof. r1pf L5KA.zeros_at [KS_haK2s] LibSegJa_haK2s.regs0 LibSegJa_haK2s.kn0 LibSegJa_haK2s.BR LibSegJa_haK2s.PSS LibSegJa_haK2s.NX0 LibSegJa_haK2s.F0 687232 LibSegJa_haK2s.seg_sound_ax fx R M V haK2s_conc_s. Qed.
Definition KS_haK2l : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haK2l.regs0 LibSegJa_haK2l.regs_out0).
Lemma KS_haK2l_ok : BG.kept_ok 64 LibSegJa_haK2l.regs0 LibSegJa_haK2l.regs_out0 KS_haK2l = true. Proof. vm_compute. reflexivity. Qed.
Definition haK2l_conc_s := ",31A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16^#?#??????????????8S,17#1302>0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1P#10000#681000v28#400P#10000#681000v29#1Ka+/v28#8#7???800<#22Ka#8001>05<#1Ka#8001>05?#1Ka#8001>052#1Na+v28#;0v24B#v24#??Fv24#tLa+v28#;0v25La+v28#<0v26,3+v28#60#8+v28#70#8+v28#=8#8,1,=X#:7<80#<>:58Y,T,1#:7=0<T,:v26T,;*#2/v25#2T,<#Lb+v28#70#1301;8Lb+v28#=8#1302=0Lb+v28#60#1302:8Jbv28#60Jb+v28#68#8Jb+v28#78#60Jb+v28#>0#320"%pstring.
Lemma haK2l_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_haK2l] fx R M V haK2l_conc_s).
Proof. r1pf L5KA.zeros_at [KS_haK2l] LibSegJa_haK2l.regs0 LibSegJa_haK2l.kn0 LibSegJa_haK2l.BR LibSegJa_haK2l.PSS LibSegJa_haK2l.NX0 LibSegJa_haK2l.F0 687232 LibSegJa_haK2l.seg_sound_ax fx R M V haK2l_conc_s. Qed.
Definition KS_haL : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haL.regs0 LibSegJa_haL.regs_out0).
Lemma KS_haL_ok : BG.kept_ok 64 LibSegJa_haL.regs0 LibSegJa_haL.regs_out0 KS_haL = true. Proof. vm_compute. reflexivity. Qed.
Definition haL_conc_s := ",25A#v2p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16^#?#??????????????8S,17#1302>0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1P#10000#681000v28#400P#10000#681000v29#1,1+v28#70#8,1,7X#:7=0<#?9?><Y,T,1#:7=24T,:+v28#78Lb+v28#70#130138Jbv28#70Jb+v28#78#388"%pstring.
Lemma haL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haL] fx R M V haL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haL] LibSegJa_haL.regs0 LibSegJa_haL.kn0 LibSegJa_haL.BR LibSegJa_haL.PSS LibSegJa_haL.NX0 LibSegJa_haL.F0 687372 LibSegJa_haL.seg_sound_ax fx R M V haL_conc_s. Qed.
Definition KS_haM : list nat := Eval vm_compute in (BG.kept_list 64 LibSegJa_haM.regs0 LibSegJa_haM.regs_out0).
Lemma KS_haM_ok : BG.kept_ok 64 LibSegJa_haM.regs0 LibSegJa_haM.regs_out0 KS_haM = true. Proof. vm_compute. reflexivity. Qed.
Definition haM_conc_s := ",20A#v2p#2#40A#v28p#2#40A#v29p#2#40A#v3:p#2#40S,1v3:S,2_v2#80S,9_v2#80S,12v28S,13+/v28#8#7???8000S,14+v28#20S,15+v28#60S,16^#?#??????????????8S,17#1302>0S,18v28S,19#7???8000S,1:^#?#??????????????8B#7???7?8010<0v2#800000000000Hv2#20I_v2#80#80B#1000v28#7????????<00Hv28#20Jav28#400Iv28#400P#7???7000#100000001000v28#400I+/v28#8#7???8000#80La+v28#3?8v29B#1000v29#7???????????Iv29#1P#7???7000#100000001000v29#1Pv28#400v29#1P_v2#80#90v28#400P_v2#80#90v29#1,,1,5X#:7=24#=5808Y,T,1#:7=38T,:+v28#=8T,;#1302>8"%pstring.
Lemma haM_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_haM] fx R M V haM_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_haM] LibSegJa_haM.regs0 LibSegJa_haM.kn0 LibSegJa_haM.BR LibSegJa_haM.PSS LibSegJa_haM.NX0 LibSegJa_haM.F0 687396 LibSegJa_haM.seg_sound_ax fx R M V haM_conc_s. Qed.
End PMAHP3.
