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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_artA LibSegJb_artB0 LibSegJb_artB2 LibSegJb_artC LibSegJb_artD LibSegJb_artE0 LibSegJb_artE LibSegJb_artZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBRTP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_artA : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_artA.regs0 LibSegJb_artA.regs_out0).
Lemma KS_artA_ok : BG.kept_ok 80 LibSegJb_artA.regs0 LibSegJb_artA.regs_out0 KS_artA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition artA_conc_s := ",>A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801060v2#800000000000Hv2#20I_v2#60#60,1_v2#60#60,1,19X#:>168#5=4?<Y,T,1#:>1=8T,2_v2#60T,8v2T,9_v2#60T,:#40T,;#13<:38T,<#1T,13v26T,14v24T,15v25T,19#7???8000Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb_v2#60#"%pstring.
Lemma artA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_artA] fx R M V artA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_artA] LibSegJb_artA.regs0 LibSegJb_artA.kn0 LibSegJb_artA.BR LibSegJb_artA.PSS LibSegJb_artA.NX0 LibSegJb_artA.F0 713064 LibSegJb_artA.seg_sound_ax fx R M V artA_conc_s. Qed.
Definition KS_artB0 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_artB0.regs0 LibSegJb_artB0.regs_out0).
Lemma KS_artB0_ok : BG.kept_ok 80 LibSegJb_artB0.regs0 LibSegJb_artB0.regs_out0 KS_artB0 = true. Proof. vm_compute. reflexivity. Qed.
Definition artB0_conc_s := ",43A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2=p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#60S,8v2S,9_v2#60S,:v2?S,13v26S,14v24S,15v25S,19#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801060v2#800000000000Hv2#20I_v2#60#60B#693000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#60#60v24#180Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8B#693000v2?#7?????????<0Hv2?#20Jav2?#40Iv2?#40P#7???7000#100000001000v2?#40I+/v2?#8#7???8000#8Ka+/v2?#8#7???8000#8La+v2?#38v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#40v30#1P_v2#60#60v2?#40P_v2#60#60v30#1Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8Pv2=#110v2?#40Pv2=#110v30#1P+/v2=#8#7???8000#22+/v2?#8#7???8000#8B#693000v2=#7????????>?0Hv2=#8P#7???7000#100000001000v2=#110Ka+/v2=#8#7???8000#22Iv2=#110P_v2#60#60v2=#110La+v24#108v2=Lav2=#132010Ma+v2=#98#Pv24#180v2=#110Ka#8001>3??#1Pv2=#110v2?#40Pv2=#110v30#1P+/v2?#8#7???8000#8#8001>3??#1Pv2?#40#10000#126000,3_v2#60#8+v2?##18++/v2?#8#7???8000##8,1,19X#:>1=8#;065<Y,T,1#:>2?8T,:+v24#18T,;+v2?#20T,<#1T,=^#?#??????????????3T,>^#?#??????????????8T,12v2?T,16+v2?#20T,17v2?T,18+/v2?#8#7???8000Nb+/v2?#8#7???8004#1Lb_v2#60v2?Nb+/v2?#8#7???8003#?1Nb+/v2?#8#7???8002#?1Nb+/v2?#8#7???8001#?1Nb+/v2?#8#7???8000#?1Nb+/v2?#8#7???8007#?3Nb+/v2?#8#7???8006#?3Nb+/v2?#8#7???8005#?3Lb+v2?#10#:>168Lb+v2?#8#21763Lbv2?#41;58:;3Jb+v2?#18#28"%pstring.
Lemma artB0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_artB0] fx R M V artB0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_artB0] LibSegJb_artB0.regs0 LibSegJb_artB0.kn0 LibSegJb_artB0.BR LibSegJb_artB0.PSS LibSegJb_artB0.NX0 LibSegJb_artB0.F0 713176 LibSegJb_artB0.seg_sound_ax fx R M V artB0_conc_s. Qed.
Definition KS_artB2 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_artB2.regs0 LibSegJb_artB2.regs_out0).
Lemma KS_artB2_ok : BG.kept_ok 80 LibSegJb_artB2.regs0 LibSegJb_artB2.regs_out0 KS_artB2 = true. Proof. vm_compute. reflexivity. Qed.
Definition artB2_conc_s := ",43A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2=p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#60S,8v2S,9_v2#60S,:v2?S,13v26S,14v24S,15v25S,19#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801060v2#800000000000Hv2#20I_v2#60#60B#693000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#60#60v24#180Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8B#693000v2?#7?????????<0Hv2?#20Jav2?#40Iv2?#40P#7???7000#100000001000v2?#40I+/v2?#8#7???8000#8Ka+/v2?#8#7???8000#8La+v2?#38v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#40v30#1P_v2#60#60v2?#40P_v2#60#60v30#1Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8Pv2=#110v2?#40Pv2=#110v30#1P+/v2=#8#7???8000#22+/v2?#8#7???8000#8B#693000v2=#7????????>?0Hv2=#8P#7???7000#100000001000v2=#110Ka+/v2=#8#7???8000#22Iv2=#110P_v2#60#60v2=#110La+v24#108v2=Lav2=#132010Ma+v2=#98#2Pv24#180v2=#110Ka#8001>3??#1Pv2=#110v2?#40Pv2=#110v30#1P+/v2?#8#7???8000#8#8001>3??#1Pv2?#40#10000#126000,3_v2#60#8+v2?##18++/v2?#8#7???8000##8,1,19X#:>1=8#;065<Y,T,1#:>2?8T,:+v24#18T,;+v2?#20T,<#1T,=^#?#??????????????3T,>^#?#??????????????8T,12v2?T,16+v2?#20T,17v2?T,18+/v2?#8#7???8000Nb+/v2?#8#7???8004#1Lb_v2#60v2?Nb+/v2?#8#7???8003#?1Nb+/v2?#8#7???8002#?1Nb+/v2?#8#7???8001#?1Nb+/v2?#8#7???8000#?1Nb+/v2?#8#7???8007#?3Nb+/v2?#8#7???8006#?3Nb+/v2?#8#7???8005#?3Lb+v2?#10#:>168Lb+v2?#8#21763Lbv2?#41;58:;3Jb+v2?#18#28"%pstring.
Lemma artB2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_artB2] fx R M V artB2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_artB2] LibSegJb_artB2.regs0 LibSegJb_artB2.kn0 LibSegJb_artB2.BR LibSegJb_artB2.PSS LibSegJb_artB2.NX0 LibSegJb_artB2.F0 713176 LibSegJb_artB2.seg_sound_ax fx R M V artB2_conc_s. Qed.
Definition KS_artC : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_artC.regs0 LibSegJb_artC.regs_out0).
Lemma KS_artC_ok : BG.kept_ok 80 LibSegJb_artC.regs0 LibSegJb_artC.regs_out0 KS_artC = true. Proof. vm_compute. reflexivity. Qed.
Definition artC_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40S,2_v2#60S,8v2S,9_v2#60S,:#1S,12v2?S,13v26S,14v24S,15v25S,16+v2?#20S,17v2?S,18+/v2?#8#7???8000S,19#7???8000,,1,2X#:>2?8#:>2?<Y,"%pstring.
Lemma artC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_artC] fx R M V artC_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_artC] LibSegJb_artC.regs0 LibSegJb_artC.kn0 LibSegJb_artC.BR LibSegJb_artC.PSS LibSegJb_artC.NX0 LibSegJb_artC.F0 713464 LibSegJb_artC.seg_sound_ax fx R M V artC_conc_s. Qed.
Definition KS_artD : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_artD.regs0 LibSegJb_artD.regs_out0).
Lemma KS_artD_ok : BG.kept_ok 80 LibSegJb_artD.regs0 LibSegJb_artD.regs_out0 KS_artD = true. Proof. vm_compute. reflexivity. Qed.
Definition artD_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#60S,8v2S,9_v2#60S,<v31S,12v2?S,13v26S,14v24S,15v25S,16+v2?#20S,17v2?S,18+/v2?#8#7???8000S,19#7???8000B#v31#??,,1,6X#:>300#:>618Y,T,1#:>310T,:v24T,;v25T,=v26"%pstring.
Lemma artD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_artD] fx R M V artD_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_artD] LibSegJb_artD.regs0 LibSegJb_artD.kn0 LibSegJb_artD.BR LibSegJb_artD.PSS LibSegJb_artD.NX0 LibSegJb_artD.F0 713472 LibSegJb_artD.seg_sound_ax fx R M V artD_conc_s. Qed.
Definition KS_artE0 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_artE0.regs0 LibSegJb_artE0.regs_out0).
Lemma KS_artE0_ok : BG.kept_ok 80 LibSegJb_artE0.regs0 LibSegJb_artE0.regs_out0 KS_artE0 = true. Proof. vm_compute. reflexivity. Qed.
Definition artE0_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40S,2_v2#60S,8v2S,9_v2#60S,:#S,12v2?S,13v26S,14v24S,15v25S,16+v2?#20S,17v2?S,18+/v2?#8#7???8000S,19#7???8000,,1,5X#:>2?8#:?:18Y,T,1#:>348T,:v26T,;#1"%pstring.
Lemma artE0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_artE0] fx R M V artE0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_artE0] LibSegJb_artE0.regs0 LibSegJb_artE0.kn0 LibSegJb_artE0.BR LibSegJb_artE0.PSS LibSegJb_artE0.NX0 LibSegJb_artE0.F0 713464 LibSegJb_artE0.seg_sound_ax fx R M V artE0_conc_s. Qed.
Definition KS_artE : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_artE.regs0 LibSegJb_artE.regs_out0).
Lemma KS_artE_ok : BG.kept_ok 80 LibSegJb_artE.regs0 LibSegJb_artE.regs_out0 KS_artE = true. Proof. vm_compute. reflexivity. Qed.
Definition artE_conc_s := ",37A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v40p#2#40A#v41p#2#40A#v42p#2#40A#v43p#2#40A#v44p#2#40A#v45p#2#40A#v46p#2#40A#v47p#2#40A#v48p#2#40A#v49p#2#40A#v4:p#2#40S,2_v2#60S,8v2S,9_v2#60S,12v2?S,13v26S,14v24S,15v25S,16+v2?#20S,17v2?S,18+/v2?#8#7???8000S,19#7???8000B#7???7?801060v2#800000000000Hv2#20I_v2#60#60B#693000v2?#7?????????<0Hv2?#20Jav2?#40Iv2?#40P#7???7000#100000001000v2?#40I+/v2?#8#7???8000#8La+v2?#38v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#40v30#1P_v2#60#60v2?#40P_v2#60#60v30#1La_v2#8v40La_v2#10v41La_v2#18v42La_v2#20v43La_v2#28v44La_v2#30v45La_v2#38v46La_v2#40v47La_v2#48v48La_v2#50v49La_v2#58v4:,3+v2?##8++/v2?#8#7???8000##8+v30##1,1,1:X#:>310#:>3?<Y,T,1v40T,2v2T,8v41T,9v42T,:v30T,12v43T,13v44T,14v45T,15v46T,16v47T,17v48T,18v49T,19v4:Nbv30#Nb+/v2?#8#7???8003#?5Nb+/v2?#8#7???8002#?5Nb+/v2?#8#7???8001#?5Nb+/v2?#8#7???8000#?5Nb+/v2?#8#7???8007#?5Nb+/v2?#8#7???8006#?5Nb+/v2?#8#7???8005#?5Nb+/v2?#8#7???8004#?5Lbv2?#45>0360>Jb+v2?#8#38"%pstring.
Lemma artE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_artE] fx R M V artE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_artE] LibSegJb_artE.regs0 LibSegJb_artE.kn0 LibSegJb_artE.BR LibSegJb_artE.PSS LibSegJb_artE.NX0 LibSegJb_artE.F0 713488 LibSegJb_artE.seg_sound_ax fx R M V artE_conc_s. Qed.
Definition KS_artZ : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_artZ.regs0 LibSegJb_artZ.regs_out0).
Lemma KS_artZ_ok : BG.kept_ok 80 LibSegJb_artZ.regs0 LibSegJb_artZ.regs_out0 KS_artZ = true. Proof. vm_compute. reflexivity. Qed.
Definition artZ_conc_s := ",45A#v2p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40A#v40p#2#40A#v41p#2#40A#v42p#2#40A#v43p#2#40A#v44p#2#40A#v45p#2#40A#v46p#2#40A#v47p#2#40A#v48p#2#40A#v49p#2#40A#v4:p#2#40S,2_v2#60S,8v2S,9_v2#60S,12v2?S,13v26S,14v24S,15v25S,16+v2?#20S,17v2?S,18+/v2?#8#7???8000S,19#7???8000B#7???7?801060v2#800000000000Hv2#20I_v2#60#60B#693000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#60#60v24#180Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8B#693000v2?#7?????????<0Hv2?#20Jav2?#40Iv2?#40P#7???7000#100000001000v2?#40I+/v2?#8#7???8000#8La+v2?#38v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#40v30#1P_v2#60#60v2?#40P_v2#60#60v30#1Pv24#180v2?#40Pv24#180v30#1P+/v24#8#7???8000#30+/v2?#8#7???8000#8La_v2#8v40La_v2#10v41La_v2#18v42La_v2#20v43La_v2#28v44La_v2#30v45La_v2#38v46La_v2#40v47La_v2#48v48La_v2#50v49La_v2#58v4:,4+v24#8#1+v2?##8++/v2?#8#7???8000##8+v30##1,1,1<X#:>348#:>3?<Y,T,1v40T,2v2T,8v41T,9v42T,:v30T,;#T,12v43T,13v44T,14v45T,15v46T,16v47T,17v48T,18v49T,19v4:Nbv30#Nb+/v2?#8#7???8003#?5Nb+/v2?#8#7???8002#?5Nb+/v2?#8#7???8001#?5Nb+/v2?#8#7???8000#?5Nb+/v2?#8#7???8007#?5Nb+/v2?#8#7???8006#?5Nb+/v2?#8#7???8005#?5Nb+/v2?#8#7???8004#?5Lbv2?#45>0360>Nb+v24#8#Jb+v2?#8#38"%pstring.
Lemma artZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_artZ] fx R M V artZ_conc_s).
Proof. r1pf L5KA.zeros_at [KS_artZ] LibSegJb_artZ.regs0 LibSegJb_artZ.kn0 LibSegJb_artZ.BR LibSegJb_artZ.PSS LibSegJb_artZ.NX0 LibSegJb_artZ.F0 713544 LibSegJb_artZ.seg_sound_ax fx R M V artZ_conc_s. Qed.
End PMBRTP.
