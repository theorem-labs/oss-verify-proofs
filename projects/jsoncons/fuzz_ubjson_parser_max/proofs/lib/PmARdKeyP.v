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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_arkA LibSegJa_arkB LibSegJa_arkC0 LibSegJa_arkCe LibSegJa_arkF LibSegJa_arkW LibSegJa_arkK1 LibSegJa_arkK2 LibSegJa_arkZ1 LibSegJa_arkZ7 LibSegJa_arkZ12.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMARKP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_arkA : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkA.regs0 LibSegJa_arkA.regs_out0).
Lemma KS_arkA_ok : BG.kept_ok 80 LibSegJa_arkA.regs0 LibSegJa_arkA.regs_out0 KS_arkA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition arkA_conc_s := ",>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801080v2#800000000000Hv2#20I_v2#80#80,1_v2#80#80,1,1:X#:><6<#5=22<Y,T,1#:><>0T,2_v2#80T,8v2T,9_v2#80T,:#40T,;#13:<?8T,<#1T,13v24T,14v26T,15v25T,1:#7???8000Lb_v2#60r1:Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb_v2#80#"%pstring.
Lemma arkA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arkA] fx R M V arkA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arkA] LibSegJa_arkA.regs0 LibSegJa_arkA.kn0 LibSegJa_arkA.BR LibSegJa_arkA.PSS LibSegJa_arkA.NX0 LibSegJa_arkA.F0 715884 LibSegJa_arkA.seg_sound_ax fx R M V arkA_conc_s. Qed.
Definition KS_arkB : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkB.regs0 LibSegJa_arkB.regs_out0).
Lemma KS_arkB_ok : BG.kept_ok 80 LibSegJa_arkB.regs0 LibSegJa_arkB.regs_out0 KS_arkB = true. Proof. vm_compute. reflexivity. Qed.
Definition arkB_conc_s := ",1?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v2?S,13v24S,14v26S,15v25S,1:#7???8000B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v2?#7?????????<0Hv2?#20Jav2?#40Iv2?#40P#7???7000#100000001000v2?#40I+/v2?#8#7???8000#8Ka+/v2?#8#7???8000#8La+v2?#38v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#40v30#1P_v2#80#80v2?#40P_v2#80#80v30#1,3_v2#68#8+v2?##18++/v2?#8#7???8000##8,1,17X#:><>0#:?>2<Y,T,1#:>=78T,:v24T,;v26T,<#:><6<T,=^#?#??????????????3T,12v2?T,18v2?T,19+/v2?#8#7???8000Nb+/v2?#8#7???8003#?1Nb+/v2?#8#7???8002#?1Nb+/v2?#8#7???8001#?1Nb+/v2?#8#7???8000#?1Nb+/v2?#8#7???8007#?3Nb+/v2?#8#7???8006#?3Nb+/v2?#8#7???8005#?8Nb+/v2?#8#7???8004#?8Lb+v2?#10#:><6<Lb+v2?#8#20=3;Lbv2?#41;58:;3Lb_v2#68v2?Jb+v2?#18#28"%pstring.
Lemma arkB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arkB] fx R M V arkB_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arkB] LibSegJa_arkB.regs0 LibSegJa_arkB.kn0 LibSegJa_arkB.BR LibSegJa_arkB.PSS LibSegJa_arkB.NX0 LibSegJa_arkB.F0 716000 LibSegJa_arkB.seg_sound_ax fx R M V arkB_conc_s. Qed.
Definition KS_arkC0 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkC0.regs0 LibSegJa_arkC0.regs_out0).
Lemma KS_arkC0_ok : BG.kept_ok 80 LibSegJa_arkC0.regs0 LibSegJa_arkC0.regs_out0 KS_arkC0 = true. Proof. vm_compute. reflexivity. Qed.
Definition arkC0_conc_s := ",18A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15v25S,18v2?S,19+/v2?#8#7???8000S,1:#7???8000B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Mav26#,,1,7X#:>=78#;0428Y,T,1#:>=:4T,:+v24#18T,;v31T,<+v24#150T,16v31"%pstring.
Lemma arkC0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arkC0] fx R M V arkC0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arkC0] LibSegJa_arkC0.regs0 LibSegJa_arkC0.kn0 LibSegJa_arkC0.BR LibSegJa_arkC0.PSS LibSegJa_arkC0.NX0 LibSegJa_arkC0.F0 716152 LibSegJa_arkC0.seg_sound_ax fx R M V arkC0_conc_s. Qed.
Definition KS_arkCe : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkCe.regs0 LibSegJa_arkCe.regs_out0).
Lemma KS_arkCe_ok : BG.kept_ok 80 LibSegJa_arkCe.regs0 LibSegJa_arkCe.regs_out0 KS_arkCe = true. Proof. vm_compute. reflexivity. Qed.
Definition arkCe_conc_s := ",1:A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40A#v32p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15v25S,18v2?S,19+/v2?#8#7???8000S,1:#7???8000B#691000v26#7??????????0Hv26#8P#7???7000#100000001000v26#10Ka+/v26#8#7???8000#2Iv26#10P_v2#80#80v26#10Mav26v32B#1v32#40,,1,6X#:>=78#:>974Y,T,1#:>?4<T,:v26T,;#<T,16v31"%pstring.
Lemma arkCe_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arkCe] fx R M V arkCe_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arkCe] LibSegJa_arkCe.regs0 LibSegJa_arkCe.kn0 LibSegJa_arkCe.BR LibSegJa_arkCe.PSS LibSegJa_arkCe.NX0 LibSegJa_arkCe.F0 716152 LibSegJa_arkCe.seg_sound_ax fx R M V arkCe_conc_s. Qed.
Definition KS_arkF_0 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkF.regs0 LibSegJa_arkF.regs_out0).
Lemma KS_arkF_0_ok : BG.kept_ok 80 LibSegJa_arkF.regs0 LibSegJa_arkF.regs_out0 KS_arkF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arkF_1 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkF.regs0 LibSegJa_arkF.regs_out1).
Lemma KS_arkF_1_ok : BG.kept_ok 80 LibSegJa_arkF.regs0 LibSegJa_arkF.regs_out1 KS_arkF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition arkF_conc_s := ",15A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40A#v33p#2#40A#v34p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v33S,;v34S,12v2?S,13v24S,14v26S,15v25S,16v31S,18v2?S,19+/v2?#8#7???8000S,1:#7???8000,,2,6X#:>=:4#:?:88Y,T,1#:>=;4T,;v31T,17v33C%_v34v31p#2#40#1,6X#:>=:4#:>974Y,1T,1#:>=?4T,:v26T,;#1D#1%_v34v31p#2#40"%pstring.
Lemma arkF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arkF_0; KS_arkF_1] fx R M V arkF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arkF_0; KS_arkF_1] LibSegJa_arkF.regs0 LibSegJa_arkF.kn0 LibSegJa_arkF.BR LibSegJa_arkF.PSS LibSegJa_arkF.NX0 LibSegJa_arkF.F0 716196 LibSegJa_arkF.seg_sound_ax fx R M V arkF_conc_s. Qed.
Definition KS_arkW_0 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkW.regs0 LibSegJa_arkW.regs_out0).
Lemma KS_arkW_0_ok : BG.kept_ok 80 LibSegJa_arkW.regs0 LibSegJa_arkW.regs_out0 KS_arkW_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arkW_1 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkW.regs0 LibSegJa_arkW.regs_out1).
Lemma KS_arkW_1_ok : BG.kept_ok 80 LibSegJa_arkW.regs0 LibSegJa_arkW.regs_out1 KS_arkW_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition arkW_conc_s := ",15A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#80S,8v2S,9_v2#80S,;v35S,12v2?S,13v24S,14v26S,15v25S,16v31S,17v33S,18v2?S,19+/v2?#8#7???8000S,1:#7???8000,,2,2X#:>=;4#:>>:8Y,,5X#:>=;4#:>974Y,1T,1#:>=<8T,:v26T,;#7"%pstring.
Lemma arkW_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arkW_0; KS_arkW_1] fx R M V arkW_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arkW_0; KS_arkW_1] LibSegJa_arkW.regs0 LibSegJa_arkW.kn0 LibSegJa_arkW.BR LibSegJa_arkW.PSS LibSegJa_arkW.NX0 LibSegJa_arkW.F0 716212 LibSegJa_arkW.seg_sound_ax fx R M V arkW_conc_s. Qed.
Definition KS_arkK1 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkK1.regs0 LibSegJa_arkK1.regs_out0).
Lemma KS_arkK1_ok : BG.kept_ok 80 LibSegJa_arkK1.regs0 LibSegJa_arkK1.regs_out0 KS_arkK1 = true. Proof. vm_compute. reflexivity. Qed.
Definition arkK1_conc_s := ",2?A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v33p#2#40S,2_v2#80S,8v2S,9_v2#80S,12v2?S,13v24S,14v26S,15v25S,16v31S,17v33S,18v2?S,19+/v2?#8#7???8000S,1:#7???8000O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v2?#7?????????<0Hv2?#20Jav2?#40Iv2?#40P#7???7000#100000001000v2?#40I+/v2?#8#7???8000#8La+v2?#38v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#40v30#1P_v2#80#80v2?#40P_v2#80#80v30#1B#691000v25#7??????????8Hv25#8P#7???7000#100000001000v25#8Ka+/v25#8#7???8000#1Iv25#8P_v2#80#80v25#8Lav25#12<940Ka#8001=934#1P+/v2?#8#7???8000#8#8001=934#1P+/v25#8#7???8000#1+/v2?#8#7???8000#8Pv25#8v2?#40,2+v2?#20#10++/v2?#8#7???8000#4#2,1,>X#:>>:8#:>>?8Y,T,1#:>>?8T,:#1T,;+v2?#20T,<v24T,=v26T,>#:87?8Lb+v2?#28v31Lb+v2?#20v33Nb+/v2?#8#7???8005#Nb+/v2?#8#7???8004#Jbv2?#20Jb+v2?#30#10"%pstring.
Lemma arkK1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arkK1] fx R M V arkK1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arkK1] LibSegJa_arkK1.regs0 LibSegJa_arkK1.kn0 LibSegJa_arkK1.BR LibSegJa_arkK1.PSS LibSegJa_arkK1.NX0 LibSegJa_arkK1.F0 716456 LibSegJa_arkK1.seg_sound_ax fx R M V arkK1_conc_s. Qed.
Definition KS_arkK2 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkK2.regs0 LibSegJa_arkK2.regs_out0).
Lemma KS_arkK2_ok : BG.kept_ok 80 LibSegJa_arkK2.regs0 LibSegJa_arkK2.regs_out0 KS_arkK2 = true. Proof. vm_compute. reflexivity. Qed.
Definition arkK2_conc_s := ",47A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v40p#2#40A#v41p#2#40A#v42p#2#40A#v43p#2#40A#v44p#2#40A#v45p#2#40A#v46p#2#40A#v47p#2#40A#v48p#2#40A#v49p#2#40A#v4:p#2#40A#v4;p#2#40S,2_v2#80S,8v2S,9_v2#80S,12v2?S,13v24S,14v26S,15v25S,18v2?S,19+/v2?#8#7???8000S,1:#7???8000B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8B#691000v2?#7?????????<0Hv2?#20Jav2?#40Iv2?#40P#7???7000#100000001000v2?#40I+/v2?#8#7???8000#8La+v2?#38v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#40v30#1P_v2#80#80v2?#40P_v2#80#80v30#1Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8La_v2#8v40La_v2#10v41La_v2#18v42La_v2#20v43La_v2#28v44La_v2#30v45La_v2#38v46La_v2#40v47La_v2#48v48La_v2#50v49La_v2#58v4:La_v2#60v4;Na+v24#10#,4+v24#8#1+v2?##8++/v2?#8#7???8000##8+v30##1,1,1>X#:>>?8#:>>:4Y,T,1v40T,2v2T,8v41T,9v42T,:v30T,;#1T,<#T,12v43T,13v44T,14v45T,15v46T,16v47T,17v48T,18v49T,19v4:T,1:v4;Nbv30#Nb+/v2?#8#7???8003#?5Nb+/v2?#8#7???8002#?5Nb+/v2?#8#7???8001#?5Nb+/v2?#8#7???8000#?5Nb+/v2?#8#7???8007#?5Nb+/v2?#8#7???8006#?5Nb+/v2?#8#7???8005#?5Nb+/v2?#8#7???8004#?5Lbv2?#45>0360>Nb+v24#8#1Jb+v2?#8#38"%pstring.
Lemma arkK2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arkK2] fx R M V arkK2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arkK2] LibSegJa_arkK2.regs0 LibSegJa_arkK2.kn0 LibSegJa_arkK2.BR LibSegJa_arkK2.PSS LibSegJa_arkK2.NX0 LibSegJa_arkK2.F0 716536 LibSegJa_arkK2.seg_sound_ax fx R M V arkK2_conc_s. Qed.
Definition KS_arkZ1 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkZ1.regs0 LibSegJa_arkZ1.regs_out0).
Lemma KS_arkZ1_ok : BG.kept_ok 80 LibSegJa_arkZ1.regs0 LibSegJa_arkZ1.regs_out0 KS_arkZ1 = true. Proof. vm_compute. reflexivity. Qed.
Definition arkZ1_conc_s := ",46A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v40p#2#40A#v41p#2#40A#v42p#2#40A#v43p#2#40A#v44p#2#40A#v45p#2#40A#v46p#2#40A#v47p#2#40A#v48p#2#40A#v49p#2#40A#v4:p#2#40A#v4;p#2#40S,2_v2#80S,8v2S,9_v2#80S,12v2?S,13v24S,14v26S,15v25S,18v2?S,19+/v2?#8#7???8000S,1:#7???8000B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8B#691000v2?#7?????????<0Hv2?#20Jav2?#40Iv2?#40P#7???7000#100000001000v2?#40I+/v2?#8#7???8000#8La+v2?#38v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#40v30#1P_v2#80#80v2?#40P_v2#80#80v30#1Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8La_v2#8v40La_v2#10v41La_v2#18v42La_v2#20v43La_v2#28v44La_v2#30v45La_v2#38v46La_v2#40v47La_v2#48v48La_v2#50v49La_v2#58v4:La_v2#60v4;,4+v24#8#1+v2?##8++/v2?#8#7???8000##8+v30##1,1,1=X#:>=?4#:>>:4Y,T,1v40T,2v2T,8v41T,9v42T,:v30T,;#T,12v43T,13v44T,14v45T,15v46T,16v47T,17v48T,18v49T,19v4:T,1:v4;Nbv30#Nb+/v2?#8#7???8003#?5Nb+/v2?#8#7???8002#?5Nb+/v2?#8#7???8001#?5Nb+/v2?#8#7???8000#?5Nb+/v2?#8#7???8007#?5Nb+/v2?#8#7???8006#?5Nb+/v2?#8#7???8005#?5Nb+/v2?#8#7???8004#?5Lbv2?#45>0360>Nb+v24#8#Jb+v2?#8#38"%pstring.
Lemma arkZ1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arkZ1] fx R M V arkZ1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arkZ1] LibSegJa_arkZ1.regs0 LibSegJa_arkZ1.kn0 LibSegJa_arkZ1.BR LibSegJa_arkZ1.PSS LibSegJa_arkZ1.NX0 LibSegJa_arkZ1.F0 716276 LibSegJa_arkZ1.seg_sound_ax fx R M V arkZ1_conc_s. Qed.
Definition KS_arkZ7 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkZ7.regs0 LibSegJa_arkZ7.regs_out0).
Lemma KS_arkZ7_ok : BG.kept_ok 80 LibSegJa_arkZ7.regs0 LibSegJa_arkZ7.regs_out0 KS_arkZ7 = true. Proof. vm_compute. reflexivity. Qed.
Definition arkZ7_conc_s := ",46A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v40p#2#40A#v41p#2#40A#v42p#2#40A#v43p#2#40A#v44p#2#40A#v45p#2#40A#v46p#2#40A#v47p#2#40A#v48p#2#40A#v49p#2#40A#v4:p#2#40A#v4;p#2#40S,2_v2#80S,8v2S,9_v2#80S,12v2?S,13v24S,14v26S,15v25S,18v2?S,19+/v2?#8#7???8000S,1:#7???8000B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8B#691000v2?#7?????????<0Hv2?#20Jav2?#40Iv2?#40P#7???7000#100000001000v2?#40I+/v2?#8#7???8000#8La+v2?#38v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#40v30#1P_v2#80#80v2?#40P_v2#80#80v30#1Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8La_v2#8v40La_v2#10v41La_v2#18v42La_v2#20v43La_v2#28v44La_v2#30v45La_v2#38v46La_v2#40v47La_v2#48v48La_v2#50v49La_v2#58v4:La_v2#60v4;,4+v24#8#1+v2?##8++/v2?#8#7???8000##8+v30##1,1,1=X#:>=<8#:>>:4Y,T,1v40T,2v2T,8v41T,9v42T,:v30T,;#T,12v43T,13v44T,14v45T,15v46T,16v47T,17v48T,18v49T,19v4:T,1:v4;Nbv30#Nb+/v2?#8#7???8003#?5Nb+/v2?#8#7???8002#?5Nb+/v2?#8#7???8001#?5Nb+/v2?#8#7???8000#?5Nb+/v2?#8#7???8007#?5Nb+/v2?#8#7???8006#?5Nb+/v2?#8#7???8005#?5Nb+/v2?#8#7???8004#?5Lbv2?#45>0360>Nb+v24#8#Jb+v2?#8#38"%pstring.
Lemma arkZ7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arkZ7] fx R M V arkZ7_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arkZ7] LibSegJa_arkZ7.regs0 LibSegJa_arkZ7.kn0 LibSegJa_arkZ7.BR LibSegJa_arkZ7.PSS LibSegJa_arkZ7.NX0 LibSegJa_arkZ7.F0 716232 LibSegJa_arkZ7.seg_sound_ax fx R M V arkZ7_conc_s. Qed.
Definition KS_arkZ12 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_arkZ12.regs0 LibSegJa_arkZ12.regs_out0).
Lemma KS_arkZ12_ok : BG.kept_ok 80 LibSegJa_arkZ12.regs0 LibSegJa_arkZ12.regs_out0 KS_arkZ12 = true. Proof. vm_compute. reflexivity. Qed.
Definition arkZ12_conc_s := ",46A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v40p#2#40A#v41p#2#40A#v42p#2#40A#v43p#2#40A#v44p#2#40A#v45p#2#40A#v46p#2#40A#v47p#2#40A#v48p#2#40A#v49p#2#40A#v4:p#2#40A#v4;p#2#40S,2_v2#80S,8v2S,9_v2#80S,12v2?S,13v24S,14v26S,15v25S,18v2?S,19+/v2?#8#7???8000S,1:#7???8000B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#80#80v24#180Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8B#691000v2?#7?????????<0Hv2?#20Jav2?#40Iv2?#40P#7???7000#100000001000v2?#40I+/v2?#8#7???8000#8La+v2?#38v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#40v30#1P_v2#80#80v2?#40P_v2#80#80v30#1Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8La_v2#8v40La_v2#10v41La_v2#18v42La_v2#20v43La_v2#28v44La_v2#30v45La_v2#38v46La_v2#40v47La_v2#48v48La_v2#50v49La_v2#58v4:La_v2#60v4;,4+v24#8#1+v2?##8++/v2?#8#7???8000##8+v30##1,1,1=X#:>?4<#:>>:4Y,T,1v40T,2v2T,8v41T,9v42T,:v30T,;#T,12v43T,13v44T,14v45T,15v46T,16v47T,17v48T,18v49T,19v4:T,1:v4;Nbv30#Nb+/v2?#8#7???8003#?5Nb+/v2?#8#7???8002#?5Nb+/v2?#8#7???8001#?5Nb+/v2?#8#7???8000#?5Nb+/v2?#8#7???8007#?5Nb+/v2?#8#7???8006#?5Nb+/v2?#8#7???8005#?5Nb+/v2?#8#7???8004#?5Lbv2?#45>0360>Nb+v24#8#Jb+v2?#8#38"%pstring.
Lemma arkZ12_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arkZ12] fx R M V arkZ12_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arkZ12] LibSegJa_arkZ12.regs0 LibSegJa_arkZ12.kn0 LibSegJa_arkZ12.BR LibSegJa_arkZ12.PSS LibSegJa_arkZ12.NX0 LibSegJa_arkZ12.F0 716620 LibSegJa_arkZ12.seg_sound_ax fx R M V arkZ12_conc_s. Qed.
End PMARKP.
