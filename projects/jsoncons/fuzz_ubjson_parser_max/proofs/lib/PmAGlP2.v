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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_aglTd4 LibSegJa_aglTd5 LibSegJa_aglTd6 LibSegJa_aglNi_c1 LibSegJa_aglNU LibSegJa_aglNl_c1 LibSegJa_aglNI LibSegJa_aglNL LibSegJa_aglVi_c1 LibSegJa_aglVl_c1 LibSegJa_aglVI LibSegJa_aglVL.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAGL2.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aglTd4 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglTd4.regs0 LibSegJa_aglTd4.regs_out0).
Lemma KS_aglTd4_ok : BG.kept_ok 80 LibSegJa_aglTd4.regs0 LibSegJa_aglTd4.regs_out0 KS_aglTd4 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aglTd4_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#56v31#68,,1,5X#:??80#:>974Y,T,1#;019<T,:v26T,;#5"%pstring.
Lemma aglTd4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglTd4] fx R M V aglTd4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglTd4] LibSegJa_aglTd4.regs0 LibSegJa_aglTd4.kn0 LibSegJa_aglTd4.BR LibSegJa_aglTd4.PSS LibSegJa_aglTd4.NX0 LibSegJa_aglTd4.F0 720768 LibSegJa_aglTd4.seg_sound_ax fx R M V aglTd4_conc_s. Qed.
Definition KS_aglTd5 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglTd5.regs0 LibSegJa_aglTd5.regs_out0).
Lemma KS_aglTd5_ok : BG.kept_ok 80 LibSegJa_aglTd5.regs0 LibSegJa_aglTd5.regs_out0 KS_aglTd5 = true. Proof. vm_compute. reflexivity. Qed.
Definition aglTd5_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#6:v31#6;,,1,5X#:??80#:>974Y,T,1#;019<T,:v26T,;#5"%pstring.
Lemma aglTd5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglTd5] fx R M V aglTd5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglTd5] LibSegJa_aglTd5.regs0 LibSegJa_aglTd5.kn0 LibSegJa_aglTd5.BR LibSegJa_aglTd5.PSS LibSegJa_aglTd5.NX0 LibSegJa_aglTd5.F0 720768 LibSegJa_aglTd5.seg_sound_ax fx R M V aglTd5_conc_s. Qed.
Definition KS_aglTd6 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglTd6.regs0 LibSegJa_aglTd6.regs_out0).
Lemma KS_aglTd6_ok : BG.kept_ok 80 LibSegJa_aglTd6.regs0 LibSegJa_aglTd6.regs_out0 KS_aglTd6 = true. Proof. vm_compute. reflexivity. Qed.
Definition aglTd6_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#6=v31#??,,1,5X#:??80#:>974Y,T,1#;019<T,:v26T,;#5"%pstring.
Lemma aglTd6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglTd6] fx R M V aglTd6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglTd6] LibSegJa_aglTd6.regs0 LibSegJa_aglTd6.kn0 LibSegJa_aglTd6.BR LibSegJa_aglTd6.PSS LibSegJa_aglTd6.NX0 LibSegJa_aglTd6.F0 720768 LibSegJa_aglTd6.seg_sound_ax fx R M V aglTd6_conc_s. Qed.
Definition KS_aglNi : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglNi_c1.regs0 LibSegJa_aglNi_c1.regs_out0).
Lemma KS_aglNi_ok : BG.kept_ok 80 LibSegJa_aglNi_c1.regs0 LibSegJa_aglNi_c1.regs_out0 KS_aglNi = true. Proof. vm_compute. reflexivity. Qed.
Definition aglNi_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#S,12v2?S,13v24S,14v26S,15+v24#18S,16#1S,17+v2?#30S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000,,1,5X#:??;<#:>974Y,T,1#:??=8T,:v26T,;#1"%pstring.
Lemma aglNi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglNi] fx R M V aglNi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglNi] LibSegJa_aglNi_c1.regs0 LibSegJa_aglNi_c1.kn0 LibSegJa_aglNi_c1.BR LibSegJa_aglNi_c1.PSS LibSegJa_aglNi_c1.NX0 LibSegJa_aglNi_c1.F0 720828 LibSegJa_aglNi_c1.seg_sound_ax fx R M V aglNi_conc_s. Qed.
Definition KS_aglNU : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglNU.regs0 LibSegJa_aglNU.regs_out0).
Lemma KS_aglNU_ok : BG.kept_ok 80 LibSegJa_aglNU.regs0 LibSegJa_aglNU.regs_out0 KS_aglNU = true. Proof. vm_compute. reflexivity. Qed.
Definition aglNU_conc_s := ",10A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#S,12v2?S,13v24S,14v26S,15+v24#18S,16+v2?#40S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000,,1,5X#;00?0#:>974Y,T,1#;036<T,:v26T,;#1"%pstring.
Lemma aglNU_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglNU] fx R M V aglNU_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglNU] LibSegJa_aglNU.regs0 LibSegJa_aglNU.kn0 LibSegJa_aglNU.BR LibSegJa_aglNU.PSS LibSegJa_aglNU.NX0 LibSegJa_aglNU.F0 721136 LibSegJa_aglNU.seg_sound_ax fx R M V aglNU_conc_s. Qed.
Definition KS_aglNl : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglNl_c1.regs0 LibSegJa_aglNl_c1.regs_out0).
Lemma KS_aglNl_ok : BG.kept_ok 80 LibSegJa_aglNl_c1.regs0 LibSegJa_aglNl_c1.regs_out0 KS_aglNl = true. Proof. vm_compute. reflexivity. Qed.
Definition aglNl_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,16#4S,17+v2?#60S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#v31#3,,1,6X#;0118#:>974Y,T,1#;02?<T,:v26T,;#1T,16#1"%pstring.
Lemma aglNl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglNl] fx R M V aglNl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglNl] LibSegJa_aglNl_c1.regs0 LibSegJa_aglNl_c1.kn0 LibSegJa_aglNl_c1.BR LibSegJa_aglNl_c1.PSS LibSegJa_aglNl_c1.NX0 LibSegJa_aglNl_c1.F0 721176 LibSegJa_aglNl_c1.seg_sound_ax fx R M V aglNl_conc_s. Qed.
Definition KS_aglNI : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglNI.regs0 LibSegJa_aglNI.regs_out0).
Lemma KS_aglNI_ok : BG.kept_ok 80 LibSegJa_aglNI.regs0 LibSegJa_aglNI.regs_out0 KS_aglNI = true. Proof. vm_compute. reflexivity. Qed.
Definition aglNI_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,16+v2?#50S,17#2S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#v31#1,,1,5X#;0170#:>974Y,T,1#;03:0T,:v26T,;#1"%pstring.
Lemma aglNI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglNI] fx R M V aglNI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglNI] LibSegJa_aglNI.regs0 LibSegJa_aglNI.kn0 LibSegJa_aglNI.BR LibSegJa_aglNI.PSS LibSegJa_aglNI.NX0 LibSegJa_aglNI.F0 721264 LibSegJa_aglNI.seg_sound_ax fx R M V aglNI_conc_s. Qed.
Definition KS_aglNL : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglNL.regs0 LibSegJa_aglNL.regs_out0).
Lemma KS_aglNL_ok : BG.kept_ok 80 LibSegJa_aglNL.regs0 LibSegJa_aglNL.regs_out0 KS_aglNL = true. Proof. vm_compute. reflexivity. Qed.
Definition aglNL_conc_s := ",13A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,16+v2?#70S,17#8S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#v31#7,,1,5X#;005<#:>974Y,T,1#;0338T,:v26T,;#1"%pstring.
Lemma aglNL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglNL] fx R M V aglNL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglNL] LibSegJa_aglNL.regs0 LibSegJa_aglNL.kn0 LibSegJa_aglNL.BR LibSegJa_aglNL.PSS LibSegJa_aglNL.NX0 LibSegJa_aglNL.F0 720988 LibSegJa_aglNL.seg_sound_ax fx R M V aglNL_conc_s. Qed.
Definition KS_aglVi : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglVi_c1.regs0 LibSegJa_aglVi_c1.regs_out0).
Lemma KS_aglVi_ok : BG.kept_ok 80 LibSegJa_aglVi_c1.regs0 LibSegJa_aglVi_c1.regs_out0 KS_aglVi = true. Proof. vm_compute. reflexivity. Qed.
Definition aglVi_conc_s := ",20A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#1S,12v2?S,13v24S,14v26S,15+v24#18S,16#1S,17+v2?#30S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#691000v2?#7?????????00Hv2?#20Jav2?#100Iv2?#100P#7???7000#100000001000v2?#100I+/v2?#8#7???8000#20La+v2?#?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#100v30#1P_v2#80#80v2?#100P_v2#80#80v30#1Ja+v2?#30#1,,1,2X#:??;<#:??<4Y,"%pstring.
Lemma aglVi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglVi] fx R M V aglVi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglVi] LibSegJa_aglVi_c1.regs0 LibSegJa_aglVi_c1.kn0 LibSegJa_aglVi_c1.BR LibSegJa_aglVi_c1.PSS LibSegJa_aglVi_c1.NX0 LibSegJa_aglVi_c1.F0 720828 LibSegJa_aglVi_c1.seg_sound_ax fx R M V aglVi_conc_s. Qed.
Definition KS_aglVl : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglVl_c1.regs0 LibSegJa_aglVl_c1.regs_out0).
Lemma KS_aglVl_ok : BG.kept_ok 80 LibSegJa_aglVl_c1.regs0 LibSegJa_aglVl_c1.regs_out0 KS_aglVl = true. Proof. vm_compute. reflexivity. Qed.
Definition aglVl_conc_s := ",20A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#4S,12v2?S,13v24S,14v26S,15+v24#18S,16#4S,17+v2?#60S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#691000v2?#7?????????00Hv2?#20Jav2?#100Iv2?#100P#7???7000#100000001000v2?#100I+/v2?#8#7???8000#20La+v2?#?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#100v30#1P_v2#80#80v2?#100P_v2#80#80v30#1Ja+v2?#60#4,,1,2X#;0118#;014<Y,"%pstring.
Lemma aglVl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglVl] fx R M V aglVl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglVl] LibSegJa_aglVl_c1.regs0 LibSegJa_aglVl_c1.kn0 LibSegJa_aglVl_c1.BR LibSegJa_aglVl_c1.PSS LibSegJa_aglVl_c1.NX0 LibSegJa_aglVl_c1.F0 721176 LibSegJa_aglVl_c1.seg_sound_ax fx R M V aglVl_conc_s. Qed.
Definition KS_aglVI : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglVI.regs0 LibSegJa_aglVI.regs_out0).
Lemma KS_aglVI_ok : BG.kept_ok 80 LibSegJa_aglVI.regs0 LibSegJa_aglVI.regs_out0 KS_aglVI = true. Proof. vm_compute. reflexivity. Qed.
Definition aglVI_conc_s := ",20A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#2S,12v2?S,13v24S,14v26S,15+v24#18S,16+v2?#50S,17#2S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#691000v2?#7?????????00Hv2?#20Jav2?#100Iv2?#100P#7???7000#100000001000v2?#100I+/v2?#8#7???8000#20La+v2?#?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#100v30#1P_v2#80#80v2?#100P_v2#80#80v30#1Ja+v2?#50#2,,1,2X#;0170#;0184Y,"%pstring.
Lemma aglVI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglVI] fx R M V aglVI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglVI] LibSegJa_aglVI.regs0 LibSegJa_aglVI.kn0 LibSegJa_aglVI.BR LibSegJa_aglVI.PSS LibSegJa_aglVI.NX0 LibSegJa_aglVI.F0 721264 LibSegJa_aglVI.seg_sound_ax fx R M V aglVI_conc_s. Qed.
Definition KS_aglVL : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglVL.regs0 LibSegJa_aglVL.regs_out0).
Lemma KS_aglVL_ok : BG.kept_ok 80 LibSegJa_aglVL.regs0 LibSegJa_aglVL.regs_out0 KS_aglVL = true. Proof. vm_compute. reflexivity. Qed.
Definition aglVL_conc_s := ",20A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#8S,12v2?S,13v24S,14v26S,15+v24#18S,16+v2?#70S,17#8S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#691000v2?#7?????????00Hv2?#20Jav2?#100Iv2?#100P#7???7000#100000001000v2?#100I+/v2?#8#7???8000#20La+v2?#?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#100v30#1P_v2#80#80v2?#100P_v2#80#80v30#1Ja+v2?#70#8,,1,2X#;005<#;00<8Y,"%pstring.
Lemma aglVL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglVL] fx R M V aglVL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglVL] LibSegJa_aglVL.regs0 LibSegJa_aglVL.kn0 LibSegJa_aglVL.BR LibSegJa_aglVL.PSS LibSegJa_aglVL.NX0 LibSegJa_aglVL.F0 720988 LibSegJa_aglVL.seg_sound_ax fx R M V aglVL_conc_s. Qed.
End PMAGL2.
