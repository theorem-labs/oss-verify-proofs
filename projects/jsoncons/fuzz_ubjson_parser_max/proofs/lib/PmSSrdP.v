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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJs_tsA LibSegJs_tsH1 LibSegJs_tsH0 LibSegJs_tsRS LibSegJs_tsRL LibSegJs_tsQS LibSegJs_tsQL LibSegJs_tsE LibSegJs_tsF LibSegJs_tsDS LibSegJs_tsDL LibSegJs_tsD2 LibSegJs_tsD3.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMSSRP.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_tsA_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsA.regs0 LibSegJs_tsA.regs_out0).
Lemma KS_tsA_0_ok : BG.kept_ok 56 LibSegJs_tsA.regs0 LibSegJs_tsA.regs_out0 KS_tsA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsA_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsA.regs0 LibSegJs_tsA.regs_out1).
Lemma KS_tsA_1_ok : BG.kept_ok 56 LibSegJs_tsA.regs0 LibSegJs_tsA.regs_out1 KS_tsA_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition tsA_conc_s := ",<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#v23^#?#???????????????,1_v2#40#40,2,11X#378<4#37900Y,T,2_v2#40T,8v23T,9v22T,12v21T,14v23T,15+v22#1D#1%_v23#p#2#40Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,<X#378<4#37:40Y,1T,:v23C%_v23#p#2#40#1Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma tsA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsA_0; KS_tsA_1] fx R M V tsA_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsA_0; KS_tsA_1] LibSegJs_tsA.regs0 LibSegJs_tsA.kn0 LibSegJs_tsA.BR LibSegJs_tsA.PSS LibSegJs_tsA.NX0 LibSegJs_tsA.F0 227524 LibSegJs_tsA.seg_sound_ax fx R M V tsA_conc_s. Qed.
Definition KS_tsH1_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsH1.regs0 LibSegJs_tsH1.regs_out0).
Lemma KS_tsH1_0_ok : BG.kept_ok 56 LibSegJs_tsH1.regs0 LibSegJs_tsH1.regs_out0 KS_tsH1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsH1_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsH1.regs0 LibSegJs_tsH1.regs_out1).
Lemma KS_tsH1_1_ok : BG.kept_ok 56 LibSegJs_tsH1.regs0 LibSegJs_tsH1.regs_out1 KS_tsH1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition tsH1_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v23S,9v22S,12v21S,14v24S,15+v22#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800000v21#7????????>=8Hv21#8P_v2#40#40v21#128La+v21#120v25B#1v25#4000La+v21#110#4000B#1v24^#?#???????????????,,2,5X#37900#37944Y,T,:#4000T,13v24Cv24#4000,5X#37900#37944Y,1T,:#4000T,13#4000D#4000v24"%pstring.
Lemma tsH1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsH1_0; KS_tsH1_1] fx R M V tsH1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsH1_0; KS_tsH1_1] LibSegJs_tsH1.regs0 LibSegJs_tsH1.kn0 LibSegJs_tsH1.BR LibSegJs_tsH1.PSS LibSegJs_tsH1.NX0 LibSegJs_tsH1.F0 227584 LibSegJs_tsH1.seg_sound_ax fx R M V tsH1_conc_s. Qed.
Definition KS_tsH0_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsH0.regs0 LibSegJs_tsH0.regs_out0).
Lemma KS_tsH0_0_ok : BG.kept_ok 56 LibSegJs_tsH0.regs0 LibSegJs_tsH0.regs_out0 KS_tsH0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsH0_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsH0.regs0 LibSegJs_tsH0.regs_out1).
Lemma KS_tsH0_1_ok : BG.kept_ok 56 LibSegJs_tsH0.regs0 LibSegJs_tsH0.regs_out1 KS_tsH0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsH0_2 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsH0.regs0 LibSegJs_tsH0.regs_out2).
Lemma KS_tsH0_2_ok : BG.kept_ok 56 LibSegJs_tsH0.regs0 LibSegJs_tsH0.regs_out2 KS_tsH0_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition tsH0_conc_s := ",2>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v26p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40S,2_v2#40S,8v23S,9v22S,12v21S,14v24S,15+v22#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33B#7???7?800000v21#7????????>=8Hv21#8P_v2#40#40v21#128O#10000#;60=0La+v21#120#La+v21#110#4000La+v21#?0v26B#7???7?800000v26#7????????>?0Hv26#8P_v2#40#40v26#110Lav26#;2:98Na+v26#98v34B#v34#2B#1v24^#?#???????????????,,3,7X#37900#37944Y,T,:#4000T,;#78T,13v24Cv24#4000C%_%*#2/v34#2p#2#40#p#2#40#1,7X#37900#379:0Y,1T,:*#2/v34#2T,;#78T,13#4000D#4000v24C%_%*#2/v34#2p#2#40#p#2#40#1,>X#37900#37:40Y,2T,1v2<T,2v2T,8v2=T,9v2>T,:_v23v24T,;#78T,12v2?T,13v30T,14v31T,15v32T,16v33D#1%_%*#2/v34#2p#2#40#p#2#40"%pstring.
Lemma tsH0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsH0_0; KS_tsH0_1; KS_tsH0_2] fx R M V tsH0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsH0_0; KS_tsH0_1; KS_tsH0_2] LibSegJs_tsH0.regs0 LibSegJs_tsH0.kn0 LibSegJs_tsH0.BR LibSegJs_tsH0.PSS LibSegJs_tsH0.NX0 LibSegJs_tsH0.F0 227584 LibSegJs_tsH0.seg_sound_ax fx R M V tsH0_conc_s. Qed.
Definition KS_tsRS : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsRS.regs0 LibSegJs_tsRS.regs_out0).
Lemma KS_tsRS_ok : BG.kept_ok 56 LibSegJs_tsRS.regs0 LibSegJs_tsRS.regs_out0 KS_tsRS = true. Proof. vm_compute. reflexivity. Qed.
Definition tsRS_conc_s := ",18A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v2:p#2#40S,2_v2#40S,8v23S,9v22S,12v21S,13v2:S,14v24S,15+v22#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800000v22#7?????????>8Hv22#8P_v2#40#40v22#18Nav22v27B#v27#2<Fv27#fB#1v2:#4000,,1,7X#37944#56<>0Y,T,1#3796<T,:v22T,;+v2:/v27#2T,<#T,16/v27#2"%pstring.
Lemma tsRS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsRS] fx R M V tsRS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsRS] LibSegJs_tsRS.regs0 LibSegJs_tsRS.kn0 LibSegJs_tsRS.BR LibSegJs_tsRS.PSS LibSegJs_tsRS.NX0 LibSegJs_tsRS.F0 227652 LibSegJs_tsRS.seg_sound_ax fx R M V tsRS_conc_s. Qed.
Definition KS_tsRL : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsRL.regs0 LibSegJs_tsRL.regs_out0).
Lemma KS_tsRL_ok : BG.kept_ok 56 LibSegJs_tsRL.regs0 LibSegJs_tsRL.regs_out0 KS_tsRL = true. Proof. vm_compute. reflexivity. Qed.
Definition tsRL_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v28p#2#40A#v2:p#2#40S,2_v2#40S,8v23S,9v22S,12v21S,13v2:S,14v24S,15+v22#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800000v22#7?????????>8Hv22#8P_v2#40#40v22#18Nav22v27B#v27#??Fv27#tLa+v22#8v28B#v28#8000000B#1v2:#4000,,1,7X#37944#56<>0Y,T,1#3796<T,:v22T,;+v28v2:T,<#T,16v28"%pstring.
Lemma tsRL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsRL] fx R M V tsRL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsRL] LibSegJs_tsRL.regs0 LibSegJs_tsRL.kn0 LibSegJs_tsRL.BR LibSegJs_tsRL.PSS LibSegJs_tsRL.NX0 LibSegJs_tsRL.F0 227652 LibSegJs_tsRL.seg_sound_ax fx R M V tsRL_conc_s. Qed.
Definition KS_tsQS : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsQS.regs0 LibSegJs_tsQS.regs_out0).
Lemma KS_tsQS_ok : BG.kept_ok 56 LibSegJs_tsQS.regs0 LibSegJs_tsQS.regs_out0 KS_tsQS = true. Proof. vm_compute. reflexivity. Qed.
Definition tsQS_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#40S,8v23S,9v22S,12v21S,13v2:S,14v24S,15+v22#1S,16v2;B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800000v22#7?????????>8Hv22#8P_v2#40#40v22#18Nav22v27B#v27#2<Fv27#fB#1v2:#4000B#v2;#16,,1,6X#3796<#36830Y,T,1#37990T,:v21T,;++v22v2;#1T,<v2:"%pstring.
Lemma tsQS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsQS] fx R M V tsQS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsQS] LibSegJs_tsQS.regs0 LibSegJs_tsQS.kn0 LibSegJs_tsQS.BR LibSegJs_tsQS.PSS LibSegJs_tsQS.NX0 LibSegJs_tsQS.F0 227692 LibSegJs_tsQS.seg_sound_ax fx R M V tsQS_conc_s. Qed.
Definition KS_tsQL : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsQL.regs0 LibSegJs_tsQL.regs_out0).
Lemma KS_tsQL_ok : BG.kept_ok 56 LibSegJs_tsQL.regs0 LibSegJs_tsQL.regs_out0 KS_tsQL = true. Proof. vm_compute. reflexivity. Qed.
Definition tsQL_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#40S,8v23S,9v22S,12v21S,13v2:S,14v24S,15+v22#1S,16v2;B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800000v22#7?????????>8Hv22#8P_v2#40#40v22#18Nav22v27B#v27#??Fv27#tLa+v22#10v29B#1000v29#800000000000B#1v2:#4000B#v2;#8000000,,1,6X#3796<#36830Y,T,1#37990T,:v21T,;+v29v2;T,<v2:"%pstring.
Lemma tsQL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsQL] fx R M V tsQL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsQL] LibSegJs_tsQL.regs0 LibSegJs_tsQL.kn0 LibSegJs_tsQL.BR LibSegJs_tsQL.PSS LibSegJs_tsQL.NX0 LibSegJs_tsQL.F0 227692 LibSegJs_tsQL.seg_sound_ax fx R M V tsQL_conc_s. Qed.
Definition KS_tsE_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsE.regs0 LibSegJs_tsE.regs_out0).
Lemma KS_tsE_0_ok : BG.kept_ok 56 LibSegJs_tsE.regs0 LibSegJs_tsE.regs_out0 KS_tsE_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsE_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsE.regs0 LibSegJs_tsE.regs_out1).
Lemma KS_tsE_1_ok : BG.kept_ok 56 LibSegJs_tsE.regs0 LibSegJs_tsE.regs_out1 KS_tsE_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsE_2 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsE.regs0 LibSegJs_tsE.regs_out2).
Lemma KS_tsE_2_ok : BG.kept_ok 56 LibSegJs_tsE.regs0 LibSegJs_tsE.regs_out2 KS_tsE_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition tsE_conc_s := ",28A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#40S,8v23S,9v22S,:v35S,12v21S,13v2:S,14v24S,15+v22#1S,16v2;B#7???7?800040v2#800000000000Hv2#10I_v2#40#40La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33B#v35#4000B#1v2:#4000B#v2;#8000000B#1v24^#?#???????????????,,3,8X#37990#56<>0Y,T,1#37:10T,:v22T,;+v2;v35T,<#T,13v35D#1%_v35v2:p#2#40,5X#37990#37900Y,1T,14_v24v2:D#1%_%+v24%*^#?#???????????????v2:p#2#40p#2#40#p#2#40C%_v35v2:p#2#40#1,>X#37990#37:40Y,2T,1v2<T,2v2T,8v2=T,9v2>T,:+v23+*-1v24v2:T,12v2?T,13v30T,14v31T,15v32T,16v33C%_%+v24%*^#?#???????????????v2:p#2#40p#2#40#p#2#40#1C%_v35v2:p#2#40#1"%pstring.
Lemma tsE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsE_0; KS_tsE_1; KS_tsE_2] fx R M V tsE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsE_0; KS_tsE_1; KS_tsE_2] LibSegJs_tsE.regs0 LibSegJs_tsE.kn0 LibSegJs_tsE.BR LibSegJs_tsE.PSS LibSegJs_tsE.NX0 LibSegJs_tsE.F0 227728 LibSegJs_tsE.seg_sound_ax fx R M V tsE_conc_s. Qed.
Definition KS_tsF_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsF.regs0 LibSegJs_tsF.regs_out0).
Lemma KS_tsF_0_ok : BG.kept_ok 56 LibSegJs_tsF.regs0 LibSegJs_tsF.regs_out0 KS_tsF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsF_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsF.regs0 LibSegJs_tsF.regs_out1).
Lemma KS_tsF_1_ok : BG.kept_ok 56 LibSegJs_tsF.regs0 LibSegJs_tsF.regs_out1 KS_tsF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition tsF_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v2:p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40S,2_v2#40S,8v23S,9v22S,12v21S,13v2:S,14v24S,15+v22#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33B#v2:#4000B#1v24^#?#???????????????,,2,4X#37:10#37900Y,T,14_v24v2:D#1%_%+v24%*^#?#???????????????v2:p#2#40p#2#40#p#2#40,=X#37:10#37:40Y,1T,1v2<T,2v2T,8v2=T,9v2>T,:+v23+*-1v24v2:T,12v2?T,13v30T,14v31T,15v32T,16v33C%_%+v24%*^#?#???????????????v2:p#2#40p#2#40#p#2#40#1"%pstring.
Lemma tsF_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsF_0; KS_tsF_1] fx R M V tsF_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsF_0; KS_tsF_1] LibSegJs_tsF.regs0 LibSegJs_tsF.kn0 LibSegJs_tsF.BR LibSegJs_tsF.PSS LibSegJs_tsF.NX0 LibSegJs_tsF.F0 227856 LibSegJs_tsF.seg_sound_ax fx R M V tsF_conc_s. Qed.
Definition KS_tsDS : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsDS.regs0 LibSegJs_tsDS.regs_out0).
Lemma KS_tsDS_ok : BG.kept_ok 56 LibSegJs_tsDS.regs0 LibSegJs_tsDS.regs_out0 KS_tsDS = true. Proof. vm_compute. reflexivity. Qed.
Definition tsDS_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40S,2_v2#40S,8v23S,9v22S,12v21S,13#4000S,14v24S,15+v22#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800000v22#7?????????>8Hv22#8P_v2#40#40v22#18Nav22v27B#v27#2<Fv27#f,,1,7X#379:0#56<>0Y,T,1#379<8T,:v22T,;+/v27#2#4000T,<#T,16/v27#2"%pstring.
Lemma tsDS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsDS] fx R M V tsDS_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsDS] LibSegJs_tsDS.regs0 LibSegJs_tsDS.kn0 LibSegJs_tsDS.BR LibSegJs_tsDS.PSS LibSegJs_tsDS.NX0 LibSegJs_tsDS.F0 227744 LibSegJs_tsDS.seg_sound_ax fx R M V tsDS_conc_s. Qed.
Definition KS_tsDL : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsDL.regs0 LibSegJs_tsDL.regs_out0).
Lemma KS_tsDL_ok : BG.kept_ok 56 LibSegJs_tsDL.regs0 LibSegJs_tsDL.regs_out0 KS_tsDL = true. Proof. vm_compute. reflexivity. Qed.
Definition tsDL_conc_s := ",19A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v28p#2#40S,2_v2#40S,8v23S,9v22S,12v21S,13#4000S,14v24S,15+v22#1B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800000v22#7?????????>8Hv22#8P_v2#40#40v22#18Nav22v27B#v27#??Fv27#tLa+v22#8v28B#v28#8000000,,1,7X#379:0#56<>0Y,T,1#379<8T,:v22T,;+v28#4000T,<#T,16v28"%pstring.
Lemma tsDL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsDL] fx R M V tsDL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsDL] LibSegJs_tsDL.regs0 LibSegJs_tsDL.kn0 LibSegJs_tsDL.BR LibSegJs_tsDL.PSS LibSegJs_tsDL.NX0 LibSegJs_tsDL.F0 227744 LibSegJs_tsDL.seg_sound_ax fx R M V tsDL_conc_s. Qed.
Definition KS_tsD2 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsD2.regs0 LibSegJs_tsD2.regs_out0).
Lemma KS_tsD2_ok : BG.kept_ok 56 LibSegJs_tsD2.regs0 LibSegJs_tsD2.regs_out0 KS_tsD2 = true. Proof. vm_compute. reflexivity. Qed.
Definition tsD2_conc_s := ",1<A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v27p#2#40A#v29p#2#40A#v2;p#2#40S,2_v2#40S,8v23S,9v22S,12v21S,13#4000S,14v24S,15+v22#1S,16v2;B#7???7?800040v2#800000000000Hv2#10I_v2#40#40B#7???7?800000v22#7?????????>8Hv22#8P_v2#40#40v22#18Nav22v27B#v27#??Fv27#tLa+v22#10v29B#1000v29#800000000000B#v2;#8000000,,1,6X#379<8#36:08Y,T,1#379><T,:v21T,;+v29v2;T,<#4000"%pstring.
Lemma tsD2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsD2] fx R M V tsD2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsD2] LibSegJs_tsD2.regs0 LibSegJs_tsD2.kn0 LibSegJs_tsD2.BR LibSegJs_tsD2.PSS LibSegJs_tsD2.NX0 LibSegJs_tsD2.F0 227784 LibSegJs_tsD2.seg_sound_ax fx R M V tsD2_conc_s. Qed.
Definition KS_tsD3_0 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsD3.regs0 LibSegJs_tsD3.regs_out0).
Lemma KS_tsD3_0_ok : BG.kept_ok 56 LibSegJs_tsD3.regs0 LibSegJs_tsD3.regs_out0 KS_tsD3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsD3_1 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsD3.regs0 LibSegJs_tsD3.regs_out1).
Lemma KS_tsD3_1_ok : BG.kept_ok 56 LibSegJs_tsD3.regs0 LibSegJs_tsD3.regs_out1 KS_tsD3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsD3_2 : list nat := Eval vm_compute in (BG.kept_list 56 LibSegJs_tsD3.regs0 LibSegJs_tsD3.regs_out2).
Lemma KS_tsD3_2_ok : BG.kept_ok 56 LibSegJs_tsD3.regs0 LibSegJs_tsD3.regs_out2 KS_tsD3_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition tsD3_conc_s := ",2;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v35p#2#40S,2_v2#40S,8v23S,9v22S,:v35S,12v21S,13#4000S,14v24S,15+v22#1S,16v2;B#7???7?800040v2#800000000000Hv2#10I_v2#40#40La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32La_v2#40v33B#7???7?800000v21#7????????>=8Hv21#8P_v2#40#40v21#128Ja+v21#100#8I+v21#100#8B#v35#4000B#v2;#8000000B#1v24^#?#???????????????,1+v21#100#8,3,8X#379><#56<>0Y,T,1#37:10T,:v22T,;+v2;v35T,<#T,13v35D#1%_v35#4000p#2#40,5X#379><#37900Y,1T,14_v24#4000D#1%_%+v24^#?#???????????<000p#2#40#p#2#40C%_v35#4000p#2#40#1,>X#379><#37:40Y,2T,1v2<T,2v2T,8v2=T,9v2>T,:+_v23v24#4000T,12v2?T,13v30T,14v31T,15v32T,16v33C%_%+v24^#?#???????????<000p#2#40#p#2#40#1C%_v35#4000p#2#40#1"%pstring.
Lemma tsD3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_tsD3_0; KS_tsD3_1; KS_tsD3_2] fx R M V tsD3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_tsD3_0; KS_tsD3_1; KS_tsD3_2] LibSegJs_tsD3.regs0 LibSegJs_tsD3.kn0 LibSegJs_tsD3.BR LibSegJs_tsD3.PSS LibSegJs_tsD3.NX0 LibSegJs_tsD3.F0 227820 LibSegJs_tsD3.seg_sound_ax fx R M V tsD3_conc_s. Qed.
End PMSSRP.
