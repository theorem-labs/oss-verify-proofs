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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_aglA LibSegJa_aglB LibSegJa_aglE0 LibSegJa_aglB1 LibSegJa_aglTi_c1 LibSegJa_aglTU LibSegJa_aglTl_c1 LibSegJa_aglTI LibSegJa_aglTL LibSegJa_aglTd1 LibSegJa_aglTd2 LibSegJa_aglTd3.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAGL1.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aglA : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglA.regs0 LibSegJa_aglA.regs_out0).
Lemma KS_aglA_ok : BG.kept_ok 80 LibSegJa_aglA.regs0 LibSegJa_aglA.regs_out0 KS_aglA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aglA_conc_s := ",<A#v2p#2#40A#v24p#2#40A#v26p#2#40S,2v2S,:v24S,;v26O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801080v2#800000000000Hv2#20I_v2#80#80,1_v2#80#80,1,19X#:?>2<#5=530Y,T,1#:?>9<T,2_v2#80T,8v2T,9_v2#80T,:#:0T,;#13:<?8T,<#1T,13v24T,14v26T,1:#7???8000Lb_v2#60r1:Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb_v2#80#"%pstring.
Lemma aglA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglA] fx R M V aglA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglA] LibSegJa_aglA.regs0 LibSegJa_aglA.kn0 LibSegJa_aglA.BR LibSegJa_aglA.PSS LibSegJa_aglA.NX0 LibSegJa_aglA.F0 720428 LibSegJa_aglA.seg_sound_ax fx R M V aglA_conc_s. Qed.
Definition KS_aglB : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglB.regs0 LibSegJa_aglB.regs_out0).
Lemma KS_aglB_ok : BG.kept_ok 80 LibSegJa_aglB.regs0 LibSegJa_aglB.regs_out0 KS_aglB = true. Proof. vm_compute. reflexivity. Qed.
Definition aglB_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v2?S,13v24S,14v26S,1:#7???8000B#7???7?801080v2#800000000000Hv2#20I_v2#80#80B#691000v2?#7?????????00Hv2?#20Jav2?#100Iv2?#100P#7???7000#100000001000v2?#100I+/v2?#8#7???8000#20Ka+/v2?#8#7???8000#20La+v2?#?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#100v30#1P_v2#80#80v2?#100P_v2#80#80v30#1,3_v2#68#8+v2?##18++/v2?#8#7???8000##14,1,28X#:?>9<#:?334Y,T,1#:??78T,:+v24#18T,;+v2?#20T,<#1T,=^#?#??????????????2T,>^#?#??????????????8T,?^#?#??????????????1T,12v2?T,15+v24#18T,16+v2?#20T,18+/v2?#8#7???8000T,19v2?Nb+/v2?#8#7???8013#?3Nb+/v2?#8#7???8012#?3Nb+/v2?#8#7???8011#?3Nb+/v2?#8#7???8010#?3Nb+/v2?#8#7???800;#?2Nb+/v2?#8#7???800:#?8Nb+/v2?#8#7???8009#?2Nb+/v2?#8#7???8008#?8Nb+/v2?#8#7???800?#?3Nb+/v2?#8#7???800>#?8Nb+/v2?#8#7???800=#?2Nb+/v2?#8#7???800<#?8Nb+/v2?#8#7???8007#?2Nb+/v2?#8#7???8006#?8Nb+/v2?#8#7???8005#?2Nb+/v2?#8#7???8004#1Nb+/v2?#8#7???8003#?1Nb+/v2?#8#7???8002#?1Nb+/v2?#8#7???8001#?1Nb+/v2?#8#7???8000#?1Lb+v2?#10#:?>2<Lb+v2?#8#1>14=Lbv2?#41;58:;3Lb_v2#68v2?Jb+v2?#18#>8Kb+/v2?#8#7???8014#<"%pstring.
Lemma aglB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aglB] fx R M V aglB_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aglB] LibSegJa_aglB.regs0 LibSegJa_aglB.kn0 LibSegJa_aglB.BR LibSegJa_aglB.PSS LibSegJa_aglB.NX0 LibSegJa_aglB.F0 720540 LibSegJa_aglB.seg_sound_ax fx R M V aglB_conc_s. Qed.
Definition KS_aglE0 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglE0.regs0 LibSegJa_aglE0.regs_out0).
Lemma KS_aglE0_ok : BG.kept_ok 80 LibSegJa_aglE0.regs0 LibSegJa_aglE0.regs_out0 KS_aglE0 = true. Proof. vm_compute. reflexivity. Qed.
Definition aglE0_conc_s := ",10A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#S,12v2?S,13v24S,14v26S,15+v24#18S,16+v2?#20S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000,,1,5X#:??78#:>974Y,T,1#;000<T,:v26T,;#1"%pstring.
Lemma aglE0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglE0] fx R M V aglE0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglE0] LibSegJa_aglE0.regs0 LibSegJa_aglE0.kn0 LibSegJa_aglE0.BR LibSegJa_aglE0.PSS LibSegJa_aglE0.NX0 LibSegJa_aglE0.F0 720760 LibSegJa_aglE0.seg_sound_ax fx R M V aglE0_conc_s. Qed.
Definition KS_aglB1 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglB1.regs0 LibSegJa_aglB1.regs_out0).
Lemma KS_aglB1_ok : BG.kept_ok 80 LibSegJa_aglB1.regs0 LibSegJa_aglB1.regs_out0 KS_aglB1 = true. Proof. vm_compute. reflexivity. Qed.
Definition aglB1_conc_s := ",10A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#1S,12v2?S,13v24S,14v26S,15+v24#18S,16+v2?#20S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000,,1,2X#:??78#:??7<Y,"%pstring.
Lemma aglB1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglB1] fx R M V aglB1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglB1] LibSegJa_aglB1.regs0 LibSegJa_aglB1.kn0 LibSegJa_aglB1.BR LibSegJa_aglB1.PSS LibSegJa_aglB1.NX0 LibSegJa_aglB1.F0 720760 LibSegJa_aglB1.seg_sound_ax fx R M V aglB1_conc_s. Qed.
Definition KS_aglTi : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglTi_c1.regs0 LibSegJa_aglTi_c1.regs_out0).
Lemma KS_aglTi_ok : BG.kept_ok 80 LibSegJa_aglTi_c1.regs0 LibSegJa_aglTi_c1.regs_out0 KS_aglTi = true. Proof. vm_compute. reflexivity. Qed.
Definition aglTi_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#69S,12v2?S,13v24S,14v26S,15+v24#18S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#691000v2?#7?????????00Hv2?#20Jav2?#100Iv2?#100P#7???7000#100000001000v2?#100I+/v2?#8#7???8000#20La+v2?#?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#100v30#1P_v2#80#80v2?#100P_v2#80#80v30#1,1++/v2?#8#7???8000#6#1,1,9X#:??80#:?334Y,T,1#:??;<T,:+v24#18T,;+v2?#30T,<#1T,16#1T,17+v2?#30Nb+/v2?#8#7???8006#1"%pstring.
Lemma aglTi_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglTi] fx R M V aglTi_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglTi] LibSegJa_aglTi_c1.regs0 LibSegJa_aglTi_c1.kn0 LibSegJa_aglTi_c1.BR LibSegJa_aglTi_c1.PSS LibSegJa_aglTi_c1.NX0 LibSegJa_aglTi_c1.F0 720768 LibSegJa_aglTi_c1.seg_sound_ax fx R M V aglTi_conc_s. Qed.
Definition KS_aglTU : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglTU.regs0 LibSegJa_aglTU.regs_out0).
Lemma KS_aglTU_ok : BG.kept_ok 80 LibSegJa_aglTU.regs0 LibSegJa_aglTU.regs_out0 KS_aglTU = true. Proof. vm_compute. reflexivity. Qed.
Definition aglTU_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#55S,12v2?S,13v24S,14v26S,15+v24#18S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#691000v2?#7?????????00Hv2?#20Jav2?#100Iv2?#100P#7???7000#100000001000v2?#100I+/v2?#8#7???8000#20La+v2?#?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#100v30#1P_v2#80#80v2?#100P_v2#80#80v30#1,1++/v2?#8#7???8000#8#1,1,8X#:??80#:?334Y,T,1#;00?0T,:+v24#18T,;+v2?#40T,<#1T,16+v2?#40Nb+/v2?#8#7???8008#1"%pstring.
Lemma aglTU_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglTU] fx R M V aglTU_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglTU] LibSegJa_aglTU.regs0 LibSegJa_aglTU.kn0 LibSegJa_aglTU.BR LibSegJa_aglTU.PSS LibSegJa_aglTU.NX0 LibSegJa_aglTU.F0 720768 LibSegJa_aglTU.seg_sound_ax fx R M V aglTU_conc_s. Qed.
Definition KS_aglTl : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglTl_c1.regs0 LibSegJa_aglTl_c1.regs_out0).
Lemma KS_aglTl_ok : BG.kept_ok 80 LibSegJa_aglTl_c1.regs0 LibSegJa_aglTl_c1.regs_out0 KS_aglTl = true. Proof. vm_compute. reflexivity. Qed.
Definition aglTl_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#6<S,12v2?S,13v24S,14v26S,15+v24#18S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#691000v2?#7?????????00Hv2?#20Jav2?#100Iv2?#100P#7???7000#100000001000v2?#100I+/v2?#8#7???8000#20La+v2?#?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#100v30#1P_v2#80#80v2?#100P_v2#80#80v30#1,1++/v2?#8#7???8000#<#1,1,9X#:??80#:?334Y,T,1#;0118T,:+v24#18T,;+v2?#60T,<#4T,16#4T,17+v2?#60Nb+/v2?#8#7???800<#4"%pstring.
Lemma aglTl_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglTl] fx R M V aglTl_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglTl] LibSegJa_aglTl_c1.regs0 LibSegJa_aglTl_c1.kn0 LibSegJa_aglTl_c1.BR LibSegJa_aglTl_c1.PSS LibSegJa_aglTl_c1.NX0 LibSegJa_aglTl_c1.F0 720768 LibSegJa_aglTl_c1.seg_sound_ax fx R M V aglTl_conc_s. Qed.
Definition KS_aglTI : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglTI.regs0 LibSegJa_aglTI.regs_out0).
Lemma KS_aglTI_ok : BG.kept_ok 80 LibSegJa_aglTI.regs0 LibSegJa_aglTI.regs_out0 KS_aglTI = true. Proof. vm_compute. reflexivity. Qed.
Definition aglTI_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#49S,12v2?S,13v24S,14v26S,15+v24#18S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#691000v2?#7?????????00Hv2?#20Jav2?#100Iv2?#100P#7???7000#100000001000v2?#100I+/v2?#8#7???8000#20La+v2?#?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#100v30#1P_v2#80#80v2?#100P_v2#80#80v30#1,1++/v2?#8#7???8000#:#1,1,9X#:??80#:?334Y,T,1#;0170T,:+v24#18T,;+v2?#50T,<#2T,16+v2?#50T,17#2Nb+/v2?#8#7???800:#2"%pstring.
Lemma aglTI_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglTI] fx R M V aglTI_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglTI] LibSegJa_aglTI.regs0 LibSegJa_aglTI.kn0 LibSegJa_aglTI.BR LibSegJa_aglTI.PSS LibSegJa_aglTI.NX0 LibSegJa_aglTI.F0 720768 LibSegJa_aglTI.seg_sound_ax fx R M V aglTI_conc_s. Qed.
Definition KS_aglTL : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglTL.regs0 LibSegJa_aglTL.regs_out0).
Lemma KS_aglTL_ok : BG.kept_ok 80 LibSegJa_aglTL.regs0 LibSegJa_aglTL.regs_out0 KS_aglTL = true. Proof. vm_compute. reflexivity. Qed.
Definition aglTL_conc_s := ",1=A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v30p#2#40S,2_v2#80S,8v2S,9_v2#80S,:#4<S,12v2?S,13v24S,14v26S,15+v24#18S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#691000v2?#7?????????00Hv2?#20Jav2?#100Iv2?#100P#7???7000#100000001000v2?#100I+/v2?#8#7???8000#20La+v2?#?8v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#100v30#1P_v2#80#80v2?#100P_v2#80#80v30#1,1++/v2?#8#7???8000#>#1,1,9X#:??80#:?334Y,T,1#;005<T,:+v24#18T,;+v2?#70T,<#8T,16+v2?#70T,17#8Nb+/v2?#8#7???800>#"%pstring.
Lemma aglTL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglTL] fx R M V aglTL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglTL] LibSegJa_aglTL.regs0 LibSegJa_aglTL.kn0 LibSegJa_aglTL.BR LibSegJa_aglTL.PSS LibSegJa_aglTL.NX0 LibSegJa_aglTL.F0 720768 LibSegJa_aglTL.seg_sound_ax fx R M V aglTL_conc_s. Qed.
Definition KS_aglTd1 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglTd1.regs0 LibSegJa_aglTd1.regs_out0).
Lemma KS_aglTd1_ok : BG.kept_ok 80 LibSegJa_aglTd1.regs0 LibSegJa_aglTd1.regs_out0 KS_aglTd1 = true. Proof. vm_compute. reflexivity. Qed.
Definition aglTd1_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#v31#48,,1,5X#:??80#:>974Y,T,1#;019<T,:v26T,;#5"%pstring.
Lemma aglTd1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglTd1] fx R M V aglTd1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglTd1] LibSegJa_aglTd1.regs0 LibSegJa_aglTd1.kn0 LibSegJa_aglTd1.BR LibSegJa_aglTd1.PSS LibSegJa_aglTd1.NX0 LibSegJa_aglTd1.F0 720768 LibSegJa_aglTd1.seg_sound_ax fx R M V aglTd1_conc_s. Qed.
Definition KS_aglTd2 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglTd2.regs0 LibSegJa_aglTd2.regs_out0).
Lemma KS_aglTd2_ok : BG.kept_ok 80 LibSegJa_aglTd2.regs0 LibSegJa_aglTd2.regs_out0 KS_aglTd2 = true. Proof. vm_compute. reflexivity. Qed.
Definition aglTd2_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#4:v31#4;,,1,5X#:??80#:>974Y,T,1#;019<T,:v26T,;#5"%pstring.
Lemma aglTd2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglTd2] fx R M V aglTd2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglTd2] LibSegJa_aglTd2.regs0 LibSegJa_aglTd2.kn0 LibSegJa_aglTd2.BR LibSegJa_aglTd2.PSS LibSegJa_aglTd2.NX0 LibSegJa_aglTd2.F0 720768 LibSegJa_aglTd2.seg_sound_ax fx R M V aglTd2_conc_s. Qed.
Definition KS_aglTd3 : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJa_aglTd3.regs0 LibSegJa_aglTd3.regs_out0).
Lemma KS_aglTd3_ok : BG.kept_ok 80 LibSegJa_aglTd3.regs0 LibSegJa_aglTd3.regs_out0 KS_aglTd3 = true. Proof. vm_compute. reflexivity. Qed.
Definition aglTd3_conc_s := ",11A#v2p#2#40A#v24p#2#40A#v26p#2#40A#v2?p#2#40A#v31p#2#40S,2_v2#80S,8v2S,9_v2#80S,:v31S,12v2?S,13v24S,14v26S,15+v24#18S,18+/v2?#8#7???8000S,19v2?S,1:#7???8000B#4=v31#54,,1,5X#:??80#:>974Y,T,1#;019<T,:v26T,;#5"%pstring.
Lemma aglTd3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aglTd3] fx R M V aglTd3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aglTd3] LibSegJa_aglTd3.regs0 LibSegJa_aglTd3.kn0 LibSegJa_aglTd3.BR LibSegJa_aglTd3.PSS LibSegJa_aglTd3.NX0 LibSegJa_aglTd3.F0 720768 LibSegJa_aglTd3.seg_sound_ax fx R M V aglTd3_conc_s. Qed.
End PMAGL1.
