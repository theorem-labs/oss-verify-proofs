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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_avlE LibSegJa_avlHf LibSegJa_avlHsZ LibSegJa_avlHsP1 LibSegJa_avlHsP2 LibSegJa_avlHsP3 LibSegJa_avlHsP4 LibSegJa_avlHsP5 LibSegJa_avlHsP6 LibSegJa_avlHsP7 LibSegJa_avlS LibSegJa_avlT0 LibSegJa_avlT1a LibSegJa_avlT1b LibSegJa_avlT2a LibSegJa_avlT2b LibSegJa_avlT3a LibSegJa_avlT3b LibSegJa_avlTbig LibSegJa_avlL LibSegJa_avlB LibSegJa_avlX.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAVALP1.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Lemma land_byte a m : 0 <= a -> 0 <= m <= 255 -> 0 <= Z.land a m < 256.
Proof. intros Ha Hm. pose proof (L5K.land_le_r a m Ha ltac:(lia)). lia. Qed.
Definition KS_avlE_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlE.regs0 LibSegJa_avlE.regs_out0).
Lemma KS_avlE_0_ok : BG.kept_ok 60 LibSegJa_avlE.regs0 LibSegJa_avlE.regs_out0 KS_avlE_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlE_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlE.regs0 LibSegJa_avlE.regs_out1).
Lemma KS_avlE_1_ok : BG.kept_ok 60 LibSegJa_avlE.regs0 LibSegJa_avlE.regs_out1 KS_avlE_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition avlE_conc_s := ",>A#v2p#2#40A#v21p#2#40A#v23p#2#40S,2v2S,:v21S,;v23O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801060v2#800000000000Hv2#10I_v2#60#60B#v21#800000000000B#v23#3??????,1_v2#60#60,2,10X#:?:88#:?=;8Y,T,2_v2#60C%_v23#p#2#40#1Lb_v2#60r1:Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1,24X#:?:88#:?;14Y,1T,2_v2#60T,5#?5T,6^#?#?????????????;?T,7#>?T,8#?0T,9#90T,;#13:<?8T,<v21T,>+v21v23T,?#8T,10#1T,11^#?#?????????????<2T,12#7???8000T,13#?4T,14#8?T,15#2T,16#3T,1<#>0T,1=#:0T,1>#>=T,1?#9?D#1%_v23#p#2#40Lb_v2#60r1:Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma avlE_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlE_0; KS_avlE_1] fx R M V avlE_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlE_0; KS_avlE_1] LibSegJa_avlE.regs0 LibSegJa_avlE.kn0 LibSegJa_avlE.BR LibSegJa_avlE.PSS LibSegJa_avlE.NX0 LibSegJa_avlE.F0 719496 LibSegJa_avlE.seg_sound_ax fx R M V avlE_conc_s. Qed.
Definition KS_avlHf_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlHf.regs0 LibSegJa_avlHf.regs_out0).
Lemma KS_avlHf_0_ok : BG.kept_ok 60 LibSegJa_avlHf.regs0 LibSegJa_avlHf.regs_out0 KS_avlHf_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlHf_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlHf.regs0 LibSegJa_avlHf.regs_out1).
Lemma KS_avlHf_1_ok : BG.kept_ok 60 LibSegJa_avlHf.regs0 LibSegJa_avlHf.regs_out1 KS_avlHf_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlHf_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Nav21v24B#v24#??Ka+/v21#8#7???8000#1,,2,3X#:?;14#:?<04Y,T,:v21,3X#:?;14#:?;34Y,1T,:v23"%pstring.
Lemma avlHf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlHf_0; KS_avlHf_1] fx R M V avlHf_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlHf_0; KS_avlHf_1] LibSegJa_avlHf.regs0 LibSegJa_avlHf.kn0 LibSegJa_avlHf.BR LibSegJa_avlHf.PSS LibSegJa_avlHf.NX0 LibSegJa_avlHf.F0 719636 LibSegJa_avlHf.seg_sound_ax fx R M V avlHf_conc_s. Qed.
Definition KS_avlHsZ : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlHsZ.regs0 LibSegJa_avlHsZ.regs_out0).
Lemma KS_avlHsZ_ok : BG.kept_ok 60 LibSegJa_avlHsZ.regs0 LibSegJa_avlHsZ.regs_out0 KS_avlHsZ = true. Proof. vm_compute. reflexivity. Qed.
Definition avlHsZ_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#7B#1+v21v23#800000000000Nav21v24B#v24#??Ka+/v21#8#7???8000#1,,1,3X#:?;14#:?<04Y,T,:v21"%pstring.
Lemma avlHsZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlHsZ] fx R M V avlHsZ_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlHsZ] LibSegJa_avlHsZ.regs0 LibSegJa_avlHsZ.kn0 LibSegJa_avlHsZ.BR LibSegJa_avlHsZ.PSS LibSegJa_avlHsZ.NX0 LibSegJa_avlHsZ.F0 719636 LibSegJa_avlHsZ.seg_sound_ax fx R M V avlHsZ_conc_s. Qed.
Definition KS_avlHsP1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlHsP1.regs0 LibSegJa_avlHsP1.regs_out0).
Lemma KS_avlHsP1_ok : BG.kept_ok 60 LibSegJa_avlHsP1.regs0 LibSegJa_avlHsP1.regs_out0 KS_avlHsP1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlHsP1_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#7B#1+v21v23#800000000000Nav21v24B#v24#??Na+/v21#8#7???8000#1B#&v21#7#,,1,4X#:?;14#:?<04Y,T,:v21T,;#"%pstring.
Lemma avlHsP1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlHsP1] fx R M V avlHsP1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlHsP1] LibSegJa_avlHsP1.regs0 LibSegJa_avlHsP1.kn0 LibSegJa_avlHsP1.BR LibSegJa_avlHsP1.PSS LibSegJa_avlHsP1.NX0 LibSegJa_avlHsP1.F0 719636 LibSegJa_avlHsP1.seg_sound_ax fx R M V avlHsP1_conc_s. Qed.
Definition KS_avlHsP2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlHsP2.regs0 LibSegJa_avlHsP2.regs_out0).
Lemma KS_avlHsP2_ok : BG.kept_ok 60 LibSegJa_avlHsP2.regs0 LibSegJa_avlHsP2.regs_out0 KS_avlHsP2 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlHsP2_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#7B#1+v21v23#800000000000Nav21v24B#v24#??Na+/v21#8#7???8000#2B#&v21#7#1,,1,4X#:?;14#:?<04Y,T,:v21W,;&v21#7"%pstring.
Lemma avlHsP2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlHsP2] fx R M V avlHsP2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlHsP2] LibSegJa_avlHsP2.regs0 LibSegJa_avlHsP2.kn0 LibSegJa_avlHsP2.BR LibSegJa_avlHsP2.PSS LibSegJa_avlHsP2.NX0 LibSegJa_avlHsP2.F0 719636 LibSegJa_avlHsP2.seg_sound_ax fx R M V avlHsP2_conc_s. Qed.
Definition KS_avlHsP3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlHsP3.regs0 LibSegJa_avlHsP3.regs_out0).
Lemma KS_avlHsP3_ok : BG.kept_ok 60 LibSegJa_avlHsP3.regs0 LibSegJa_avlHsP3.regs_out0 KS_avlHsP3 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlHsP3_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#7B#1+v21v23#800000000000Nav21v24B#v24#??Na+/v21#8#7???8000#3B#&v21#7#2,,1,4X#:?;14#:?<04Y,T,:v21W,;&v21#7"%pstring.
Lemma avlHsP3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlHsP3] fx R M V avlHsP3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlHsP3] LibSegJa_avlHsP3.regs0 LibSegJa_avlHsP3.kn0 LibSegJa_avlHsP3.BR LibSegJa_avlHsP3.PSS LibSegJa_avlHsP3.NX0 LibSegJa_avlHsP3.F0 719636 LibSegJa_avlHsP3.seg_sound_ax fx R M V avlHsP3_conc_s. Qed.
Definition KS_avlHsP4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlHsP4.regs0 LibSegJa_avlHsP4.regs_out0).
Lemma KS_avlHsP4_ok : BG.kept_ok 60 LibSegJa_avlHsP4.regs0 LibSegJa_avlHsP4.regs_out0 KS_avlHsP4 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlHsP4_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#7B#1+v21v23#800000000000Nav21v24B#v24#??Na+/v21#8#7???8000#4B#&v21#7#3,,1,4X#:?;14#:?<04Y,T,:v21W,;&v21#7"%pstring.
Lemma avlHsP4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlHsP4] fx R M V avlHsP4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlHsP4] LibSegJa_avlHsP4.regs0 LibSegJa_avlHsP4.kn0 LibSegJa_avlHsP4.BR LibSegJa_avlHsP4.PSS LibSegJa_avlHsP4.NX0 LibSegJa_avlHsP4.F0 719636 LibSegJa_avlHsP4.seg_sound_ax fx R M V avlHsP4_conc_s. Qed.
Definition KS_avlHsP5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlHsP5.regs0 LibSegJa_avlHsP5.regs_out0).
Lemma KS_avlHsP5_ok : BG.kept_ok 60 LibSegJa_avlHsP5.regs0 LibSegJa_avlHsP5.regs_out0 KS_avlHsP5 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlHsP5_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#7B#1+v21v23#800000000000Nav21v24B#v24#??Na+/v21#8#7???8000#5B#&v21#7#4,,1,4X#:?;14#:?<04Y,T,:v21W,;&v21#7"%pstring.
Lemma avlHsP5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlHsP5] fx R M V avlHsP5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlHsP5] LibSegJa_avlHsP5.regs0 LibSegJa_avlHsP5.kn0 LibSegJa_avlHsP5.BR LibSegJa_avlHsP5.PSS LibSegJa_avlHsP5.NX0 LibSegJa_avlHsP5.F0 719636 LibSegJa_avlHsP5.seg_sound_ax fx R M V avlHsP5_conc_s. Qed.
Definition KS_avlHsP6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlHsP6.regs0 LibSegJa_avlHsP6.regs_out0).
Lemma KS_avlHsP6_ok : BG.kept_ok 60 LibSegJa_avlHsP6.regs0 LibSegJa_avlHsP6.regs_out0 KS_avlHsP6 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlHsP6_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#7B#1+v21v23#800000000000Nav21v24B#v24#??Na+/v21#8#7???8000#6B#&v21#7#5,,1,4X#:?;14#:?<04Y,T,:v21W,;&v21#7"%pstring.
Lemma avlHsP6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlHsP6] fx R M V avlHsP6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlHsP6] LibSegJa_avlHsP6.regs0 LibSegJa_avlHsP6.kn0 LibSegJa_avlHsP6.BR LibSegJa_avlHsP6.PSS LibSegJa_avlHsP6.NX0 LibSegJa_avlHsP6.F0 719636 LibSegJa_avlHsP6.seg_sound_ax fx R M V avlHsP6_conc_s. Qed.
Definition KS_avlHsP7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlHsP7.regs0 LibSegJa_avlHsP7.regs_out0).
Lemma KS_avlHsP7_ok : BG.kept_ok 60 LibSegJa_avlHsP7.regs0 LibSegJa_avlHsP7.regs_out0 KS_avlHsP7 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlHsP7_conc_s := ",1?A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#7B#1+v21v23#800000000000Nav21v24B#v24#??Na+/v21#8#7???8000#7B#&v21#7#6,,1,4X#:?;14#:?<04Y,T,:v21W,;&v21#7"%pstring.
Lemma avlHsP7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlHsP7] fx R M V avlHsP7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlHsP7] LibSegJa_avlHsP7.regs0 LibSegJa_avlHsP7.kn0 LibSegJa_avlHsP7.BR LibSegJa_avlHsP7.PSS LibSegJa_avlHsP7.NX0 LibSegJa_avlHsP7.F0 719636 LibSegJa_avlHsP7.seg_sound_ax fx R M V avlHsP7_conc_s. Qed.
Definition KS_avlS : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlS.regs0 LibSegJa_avlS.regs_out0).
Lemma KS_avlS_ok : BG.kept_ok 60 LibSegJa_avlS.regs0 LibSegJa_avlS.regs_out0 KS_avlS = true. Proof. vm_compute. reflexivity. Qed.
Definition avlS_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#4000000B#1+v21v23#800000000000Ka#7???<63<#2<,,1,5X#:?<04#:?<24Y,W,;%+&v24#??#231?=p#2#40T,<#W,18&v24#??"%pstring.
Lemma avlS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avlS] fx R M V avlS_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avlS] LibSegJa_avlS.regs0 LibSegJa_avlS.kn0 LibSegJa_avlS.BR LibSegJa_avlS.PSS LibSegJa_avlS.NX0 LibSegJa_avlS.F0 719876 LibSegJa_avlS.seg_sound_ax fx R M V avlS_conc_s. Qed.
Definition KS_avlT0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlT0.regs0 LibSegJa_avlT0.regs_out0).
Lemma KS_avlT0_0_ok : BG.kept_ok 60 LibSegJa_avlT0.regs0 LibSegJa_avlT0.regs_out0 KS_avlT0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlT0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlT0.regs0 LibSegJa_avlT0.regs_out1).
Lemma KS_avlT0_1_ok : BG.kept_ok 60 LibSegJa_avlT0.regs0 LibSegJa_avlT0.regs_out1 KS_avlT0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlT0_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlT0.regs0 LibSegJa_avlT0.regs_out2).
Lemma KS_avlT0_2_ok : BG.kept_ok 60 LibSegJa_avlT0.regs0 LibSegJa_avlT0.regs_out2 KS_avlT0_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlT0_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,19#S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#4000000B#1+v21v23#800000000000B#v25#??,,3,5X#:?<28#:?=;8Y,T,;#6T,<+v21#1W,17%*#100000000000000v24p#2#40,6X#:?<28#:?<?<Y,1T,;#6T,<+v21#1W,17%*#100000000000000v24p#2#40Cv25#?5,6X#:?<28#:?=;8Y,2T,;#6T,<+v21#1W,17%*#100000000000000v24p#2#40D#?5v25"%pstring.
Lemma avlT0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlT0_0; KS_avlT0_1; KS_avlT0_2] fx R M V avlT0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlT0_0; KS_avlT0_1; KS_avlT0_2] LibSegJa_avlT0.regs0 LibSegJa_avlT0.kn0 LibSegJa_avlT0.BR LibSegJa_avlT0.PSS LibSegJa_avlT0.NX0 LibSegJa_avlT0.F0 719912 LibSegJa_avlT0.seg_sound_ax fx R M V avlT0_conc_s. Qed.
Definition KS_avlT1a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlT1a.regs0 LibSegJa_avlT1a.regs_out0).
Lemma KS_avlT1a_ok : BG.kept_ok 60 LibSegJa_avlT1a.regs0 LibSegJa_avlT1a.regs_out0 KS_avlT1a = true. Proof. vm_compute. reflexivity. Qed.
Definition avlT1a_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,19#1S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#1B#1+v21v23#800000000000B#v25#??,,1,3X#:?<28#:?=;8Y,T,;#5"%pstring.
Lemma avlT1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlT1a] fx R M V avlT1a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlT1a] LibSegJa_avlT1a.regs0 LibSegJa_avlT1a.kn0 LibSegJa_avlT1a.BR LibSegJa_avlT1a.PSS LibSegJa_avlT1a.NX0 LibSegJa_avlT1a.F0 719912 LibSegJa_avlT1a.seg_sound_ax fx R M V avlT1a_conc_s. Qed.
Definition KS_avlT1b : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlT1b.regs0 LibSegJa_avlT1b.regs_out0).
Lemma KS_avlT1b_ok : BG.kept_ok 60 LibSegJa_avlT1b.regs0 LibSegJa_avlT1b.regs_out0 KS_avlT1b = true. Proof. vm_compute. reflexivity. Qed.
Definition avlT1b_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,19#1S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??,,1,5X#:?<28#:?<94Y,T,;#1T,<+v21#2T,=+v21#2"%pstring.
Lemma avlT1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlT1b] fx R M V avlT1b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlT1b] LibSegJa_avlT1b.regs0 LibSegJa_avlT1b.kn0 LibSegJa_avlT1b.BR LibSegJa_avlT1b.PSS LibSegJa_avlT1b.NX0 LibSegJa_avlT1b.F0 719912 LibSegJa_avlT1b.seg_sound_ax fx R M V avlT1b_conc_s. Qed.
Definition KS_avlT2a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlT2a.regs0 LibSegJa_avlT2a.regs_out0).
Lemma KS_avlT2a_ok : BG.kept_ok 60 LibSegJa_avlT2a.regs0 LibSegJa_avlT2a.regs_out0 KS_avlT2a = true. Proof. vm_compute. reflexivity. Qed.
Definition avlT2a_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,19#2S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#2B#1+v21v23#800000000000B#v25#??,,1,3X#:?<28#:?=;8Y,T,;#5"%pstring.
Lemma avlT2a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlT2a] fx R M V avlT2a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlT2a] LibSegJa_avlT2a.regs0 LibSegJa_avlT2a.kn0 LibSegJa_avlT2a.BR LibSegJa_avlT2a.PSS LibSegJa_avlT2a.NX0 LibSegJa_avlT2a.F0 719912 LibSegJa_avlT2a.seg_sound_ax fx R M V avlT2a_conc_s. Qed.
Definition KS_avlT2b : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlT2b.regs0 LibSegJa_avlT2b.regs_out0).
Lemma KS_avlT2b_ok : BG.kept_ok 60 LibSegJa_avlT2b.regs0 LibSegJa_avlT2b.regs_out0 KS_avlT2b = true. Proof. vm_compute. reflexivity. Qed.
Definition avlT2b_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,19#2S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??,,1,6X#:?<28#:?<78Y,T,;#1T,<+v21#3T,=+v21#2T,1:+v21#3"%pstring.
Lemma avlT2b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlT2b] fx R M V avlT2b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlT2b] LibSegJa_avlT2b.regs0 LibSegJa_avlT2b.kn0 LibSegJa_avlT2b.BR LibSegJa_avlT2b.PSS LibSegJa_avlT2b.NX0 LibSegJa_avlT2b.F0 719912 LibSegJa_avlT2b.seg_sound_ax fx R M V avlT2b_conc_s. Qed.
Definition KS_avlT3a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlT3a.regs0 LibSegJa_avlT3a.regs_out0).
Lemma KS_avlT3a_ok : BG.kept_ok 60 LibSegJa_avlT3a.regs0 LibSegJa_avlT3a.regs_out0 KS_avlT3a = true. Proof. vm_compute. reflexivity. Qed.
Definition avlT3a_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,19#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#3B#1+v21v23#800000000000B#v25#??,,1,3X#:?<28#:?=;8Y,T,;#5"%pstring.
Lemma avlT3a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlT3a] fx R M V avlT3a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlT3a] LibSegJa_avlT3a.regs0 LibSegJa_avlT3a.kn0 LibSegJa_avlT3a.BR LibSegJa_avlT3a.PSS LibSegJa_avlT3a.NX0 LibSegJa_avlT3a.F0 719912 LibSegJa_avlT3a.seg_sound_ax fx R M V avlT3a_conc_s. Qed.
Definition KS_avlT3b : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlT3b.regs0 LibSegJa_avlT3b.regs_out0).
Lemma KS_avlT3b_ok : BG.kept_ok 60 LibSegJa_avlT3b.regs0 LibSegJa_avlT3b.regs_out0 KS_avlT3b = true. Proof. vm_compute. reflexivity. Qed.
Definition avlT3b_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,19#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??,,1,6X#:?<28#:?<5<Y,T,;#1T,<+v21#4T,=+v21#3T,1:+v21#4"%pstring.
Lemma avlT3b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlT3b] fx R M V avlT3b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlT3b] LibSegJa_avlT3b.regs0 LibSegJa_avlT3b.kn0 LibSegJa_avlT3b.BR LibSegJa_avlT3b.PSS LibSegJa_avlT3b.NX0 LibSegJa_avlT3b.F0 719912 LibSegJa_avlT3b.seg_sound_ax fx R M V avlT3b_conc_s. Qed.
Definition KS_avlTbig_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlTbig.regs0 LibSegJa_avlTbig.regs_out0).
Lemma KS_avlTbig_0_ok : BG.kept_ok 60 LibSegJa_avlTbig.regs0 LibSegJa_avlTbig.regs_out0 KS_avlTbig_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlTbig_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlTbig.regs0 LibSegJa_avlTbig.regs_out1).
Lemma KS_avlTbig_1_ok : BG.kept_ok 60 LibSegJa_avlTbig.regs0 LibSegJa_avlTbig.regs_out1 KS_avlTbig_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlTbig_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,19v26S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#4000000B#1+v21v23#800000000000B#v25#??B#4v26#??,,2,7X#:?<28#:?=;8Y,T,;#1T,<++v21v26#1T,=+v21v26T,1:++v21v26#1Cv26v23,4X#:?<28#:?=;8Y,1T,;#5Dv23v26"%pstring.
Lemma avlTbig_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlTbig_0; KS_avlTbig_1] fx R M V avlTbig_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlTbig_0; KS_avlTbig_1] LibSegJa_avlTbig.regs0 LibSegJa_avlTbig.kn0 LibSegJa_avlTbig.BR LibSegJa_avlTbig.PSS LibSegJa_avlTbig.NX0 LibSegJa_avlTbig.F0 719912 LibSegJa_avlTbig.seg_sound_ax fx R M V avlTbig_conc_s. Qed.
Definition KS_avlL_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out0).
Lemma KS_avlL_0_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out0 KS_avlL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out1).
Lemma KS_avlL_1_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out1 KS_avlL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out2).
Lemma KS_avlL_2_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out2 KS_avlL_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out3).
Lemma KS_avlL_3_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out3 KS_avlL_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out4).
Lemma KS_avlL_4_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out4 KS_avlL_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out5).
Lemma KS_avlL_5_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out5 KS_avlL_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out6).
Lemma KS_avlL_6_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out6 KS_avlL_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out7).
Lemma KS_avlL_7_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out7 KS_avlL_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out8).
Lemma KS_avlL_8_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out8 KS_avlL_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out9).
Lemma KS_avlL_9_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out9 KS_avlL_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out10).
Lemma KS_avlL_10_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out10 KS_avlL_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_11 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out11).
Lemma KS_avlL_11_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out11 KS_avlL_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_12 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out12).
Lemma KS_avlL_12_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out12 KS_avlL_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlL_13 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out13).
Lemma KS_avlL_13_ok : BG.kept_ok 60 LibSegJa_avlL.regs0 LibSegJa_avlL.regs_out13 KS_avlL_13 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlL_conc_s := ",24A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,:v21S,;v27S,<v22S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,17v24S,18v25S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#1v23#4000000B#1+v21v23#800000000000B#v25#??B#v22#800000000000,,>,5X#:?<;0#:?=;8Y,T,;#6C&v27#??#90C%_v25#?0p#2#40#1,5X#:?<;0#:?<?<Y,1W,;&v27#??D#90&v27#??C%_v25#?0p#2#40#1,6X#:?<;0#:?=;8Y,2T,;#6C#8?&v27#??C%_v25#?4p#2#40#1D#1%_v25#?0p#2#40,6X#:?<;0#:?<?<Y,3W,;&v27#??D&v27#??#8?C%_v25#?4p#2#40#1D#1%_v25#?0p#2#40,6X#:?<;0#:?=;8Y,4T,;#6W,17%*#100000000000000v24p#2#40D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,7X#:?<;0#:?<?<Y,5T,;#6W,17%*#100000000000000v24p#2#40Cv25#?5D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,7X#:?<;0#:?=;8Y,6T,;#6W,17%*#100000000000000v24p#2#40D#?5v25D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,5X#:?<;0#:?=;8Y,7T,;#6C&v27#??#:0C%_v25#>0p#2#40#1,5X#:?<;0#:?<?<Y,8W,;&v27#??D#:0&v27#??C%_v25#>0p#2#40#1,6X#:?<;0#:?=;8Y,9T,;#6C#9?&v27#??C%_v25#>=p#2#40#1D#1%_v25#>0p#2#40,6X#:?<;0#:?<?<Y,:W,;&v27#??D&v27#??#9?C%_v25#>=p#2#40#1D#1%_v25#>0p#2#40,6X#:?<;0#:?=;8Y,;T,;#6W,17%*#100000000000000v24p#2#40D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40,7X#:?<;0#:?<?<Y,<T,;#6W,17%*#100000000000000v24p#2#40Cv25#?5D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40,7X#:?<;0#:?=;8Y,=T,;#6W,17%*#100000000000000v24p#2#40D#?5v25D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40"%pstring.
Lemma avlL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlL_0; KS_avlL_1; KS_avlL_2; KS_avlL_3; KS_avlL_4; KS_avlL_5; KS_avlL_6; KS_avlL_7; KS_avlL_8; KS_avlL_9; KS_avlL_10; KS_avlL_11; KS_avlL_12; KS_avlL_13] fx R M V avlL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlL_0; KS_avlL_1; KS_avlL_2; KS_avlL_3; KS_avlL_4; KS_avlL_5; KS_avlL_6; KS_avlL_7; KS_avlL_8; KS_avlL_9; KS_avlL_10; KS_avlL_11; KS_avlL_12; KS_avlL_13] LibSegJa_avlL.regs0 LibSegJa_avlL.kn0 LibSegJa_avlL.BR LibSegJa_avlL.PSS LibSegJa_avlL.NX0 LibSegJa_avlL.F0 720048 LibSegJa_avlL.seg_sound_ax fx R M V avlL_conc_s. Qed.
Definition KS_avlB_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlB.regs0 LibSegJa_avlB.regs_out0).
Lemma KS_avlB_0_ok : BG.kept_ok 60 LibSegJa_avlB.regs0 LibSegJa_avlB.regs_out0 KS_avlB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avlB_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlB.regs0 LibSegJa_avlB.regs_out1).
Lemma KS_avlB_1_ok : BG.kept_ok 60 LibSegJa_avlB.regs0 LibSegJa_avlB.regs_out1 KS_avlB_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition avlB_conc_s := ",1:A#v2p#2#40A#v21p#2#40A#v23p#2#40S,2_v2#60S,5#?5S,6-41S,7#>?S,8#?0S,9#90S,<v21S,>+v21v23S,?#8S,10#1S,11-3>S,12#7???8000S,13#?4S,14#8?S,15#2S,16#3S,1<#>0S,1=#:0S,1>#>=S,1?#9?B#v21#800000000000B#v23#800000000000B#+v21v23#800000000000,,2,5X#:?<?<#:?=;8Y,T,:+v21v23T,;#C%_v21%+v21v23p#2#40p#2#40#1,3X#:?<?<#:?;14Y,1D#1%_v21%+v21v23p#2#40p#2#40"%pstring.
Lemma avlB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlB_0; KS_avlB_1] fx R M V avlB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlB_0; KS_avlB_1] LibSegJa_avlB.regs0 LibSegJa_avlB.kn0 LibSegJa_avlB.BR LibSegJa_avlB.PSS LibSegJa_avlB.NX0 LibSegJa_avlB.F0 720124 LibSegJa_avlB.seg_sound_ax fx R M V avlB_conc_s. Qed.
Definition KS_avlX : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_avlX.regs0 LibSegJa_avlX.regs_out0).
Lemma KS_avlX_ok : BG.kept_ok 60 LibSegJa_avlX.regs0 LibSegJa_avlX.regs_out0 KS_avlX = true. Proof. vm_compute. reflexivity. Qed.
Definition avlX_conc_s := ",1<A#v2p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40S,2_v2#60B#7???7?801060v2#800000000000Hv2#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?La_v2#48v30La_v2#50v31La_v2#58v32La_v2#60v33,,1,?X#:?=;8#:?=><Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?T,17v30T,18v31T,19v32T,1:v33"%pstring.
Lemma avlX_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avlX] fx R M V avlX_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avlX] LibSegJa_avlX.regs0 LibSegJa_avlX.kn0 LibSegJa_avlX.BR LibSegJa_avlX.PSS LibSegJa_avlX.NX0 LibSegJa_avlX.F0 720312 LibSegJa_avlX.seg_sound_ax fx R M V avlX_conc_s. Qed.
End PMAVALP1.
